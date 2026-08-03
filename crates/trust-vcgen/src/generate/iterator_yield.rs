// Yield-value guards for the iterator shapes whose element bounds are
// recoverable from MIR: integer ranges, `enumerate`, `slice::iter` and
// `str::char_indices`. Tracing a `next()` destination back to the iterator's
// construction site is what turns an opaque loop variable into a bounded one.

use super::*;

// ======================================================================
// Range-iterator yield facts (`for i in start..end { a[i] }`)
// ======================================================================
//
// rustc desugars a `for` loop over an exclusive range into a `Range::next`
// iterator: the loop variable `i` is bound as the `Some` payload of
// `<Range as Iterator>::next(&mut it)`. By the semantics of exclusive-range
// `next`, EVERY yielded value `v` satisfies `original_start <= v < end` (the
// iterator only advances forward, and an out-of-range/empty range yields `None`
// — the `None` arm, never the `Some` arm where `i` is read). So `start <= i <
// end` is a sound, loop-invariant fact about the payload. Emitting it discharges
// the `a[i]` bounds obligation, making the ubiquitous `for i in 0..s.len() {
// s[i] }` idiom PROVE instead of being false-refuted (an inferiority case: rustc
// accepts it). This mirrors the Ord::min/max/clamp call-result modeling above,
// but for the iterator's yielded value rather than a call's return.
//
// SOUNDNESS GATES (any miss → no fact, never a wrong one):
//   * EXCLUSIVE `std::ops::Range` only (yield `< end`). RangeInclusive (`<=
//     end`), RangeFrom (unbounded) have a different aggregate name and are excluded.
//     The `Rev` and `StepBy` adapters ARE traced through (the call-hop below): their
//     `next` yields the SAME `[start, end)` value set or a subset, never outside it.
//   * `end` is read from the ORIGINAL aggregate — `Range::next` never mutates
//     `end`, so it is loop-invariant; the moving `start` field is not relied on.
//   * `into_iter` is treated as the identity ONLY when its argument traces to a
//     literal `Range` aggregate (for any `I: Iterator`, `into_iter(i) == i`, and
//     `Range: Iterator`); a non-Range `into_iter` (e.g. `Vec`) fails the
//     aggregate gate and emits nothing.
//   * The payload local is assigned exactly once (a fresh for-binding temp), so
//     `start <= payload < end` holds at every read — a global invariant — which
//     is why the fact is attached per-block independently of the BFS guard map
//     (whose loop-join weakening would otherwise drop it).
/// `Some(payload)` extraction projection `(_x as Downcast(1)).Field(0)`.
/// In `Option<T>`, `Some` is variant index 1 with a single field 0.
pub(super) fn is_some_payload_projection(projections: &[trust_types::Projection]) -> bool {
    matches!(projections, [trust_types::Projection::Downcast(1), trust_types::Projection::Field(0)])
}

/// Strip every `<…>` group (generic args, `<impl u8>` segments, qualified-self
/// prefixes) and re-join the non-empty `::` segments — the same normalization
/// discipline as trust-ir-bridge's `strip_generics`, local to vcgen because the
/// two crates deliberately share no utility surface.
pub(super) fn vc_strip_generics(callee: &str) -> String {
    let mut out = String::with_capacity(callee.len());
    let mut depth = 0usize;
    for c in callee.chars() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    out.split("::").filter(|seg| !seg.is_empty()).collect::<Vec<_>>().join("::")
}

/// Parse the QUALIFIED impl spelling `<Recv as TraitPath>::method[::<…>]`,
/// returning `(TraitPath, method)`. The trait path may itself contain `::` and
/// nested `<…>`; the receiver/trait split is the LAST top-level-within-the-
/// qualifier ` as `, and the method is everything after the qualifier's closing
/// `>::` (trailing turbofish stripped by the caller via [`vc_strip_generics`]).
pub(super) fn vc_qualified_trait_method(callee: &str) -> Option<(String, String)> {
    let rest = callee.strip_prefix('<')?;
    // Find the matching top-level close of the opening `<`.
    let mut depth = 1usize;
    let mut close = None;
    for (i, c) in rest.char_indices() {
        match c {
            '<' => depth += 1,
            '>' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close?;
    let inner = &rest[..close];
    let method = rest[close + 1..].strip_prefix("::")?;
    // Split `Recv as TraitPath` on the last depth-0 ` as ` inside the qualifier.
    let mut depth = 0usize;
    let bytes = inner.as_bytes();
    let mut split = None;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'<' => depth += 1,
            b'>' => depth = depth.saturating_sub(1),
            b' ' if depth == 0 && inner[i..].starts_with(" as ") => split = Some(i),
            _ => {}
        }
        i += 1;
    }
    let split = split?;
    Some((inner[split + 4..].to_string(), method.to_string()))
}

/// Authenticate a std ITERATOR-PROTOCOL trait method across every spelling the
/// extractor produces:
///  * the GENERIC trait-fn path `…::{Trait}::{method}` — accepted only when the
///    trait path is CRATE-ANCHORED to `core::iter::`/`std::iter::` (the historical
///    bare `ends_with("Iterator::next")` accepted a USER trait named `Iterator`
///    too — a latent unsound-fact accept this rewrite closes);
///  * the QUALIFIED impl spelling `<Recv as TraitPath>::{method}` where
///    `TraitPath` is a `core::iter::`/`std::iter::`-anchored path whose last
///    segment is `{trait_last}` (the definition-path renderer emits
///    `core::iter::traits::iterator::Iterator` — the spelling whose silent
///    mismatch dropped the range/step_by/enumerate yield facts and turned
///    provably-safe loops into FALSE counterexamples).
///
/// A short qualified spelling such as `<Range as Iterator>::next` is not
/// authoritative: a user trait may have that same final segment and may be
/// implemented for the standard Range type. The trailing `::` in each accepted
/// namespace prefix is likewise load-bearing: `core::iteration::Iterator` is
/// not the standard iterator trait.
///
/// NAME-ONLY: every caller keeps its own receiver/aggregate trace as the
/// load-bearing soundness gate, exactly as before.
pub(super) fn vc_callee_is_std_iter_trait_method(callee: &str, trait_last: &str, method: &str) -> bool {
    let normalized = vc_strip_generics(callee);
    let suffix = format!("::{method}");
    if let Some(trait_path) = normalized.strip_suffix(&suffix)
        && (trait_path.starts_with("core::iter::") || trait_path.starts_with("std::iter::"))
        && trait_path.rsplit("::").next() == Some(trait_last)
    {
        return true;
    }
    if let Some((trait_path, m)) = vc_qualified_trait_method(callee) {
        let trait_path = vc_strip_generics(&trait_path);
        let m = vc_strip_generics(&m);
        return m == method
            && (trait_path.starts_with("core::iter::")
                || trait_path.starts_with("std::iter::"))
            && trait_path.rsplit("::").next() == Some(trait_last);
    }
    false
}

/// Authenticate an INHERENT `<[T]>` slice method across both impl spellings:
/// the generic `…::<impl [T]>::{method}` (the historical `contains("[T]")`
/// match, kept) and the MONOMORPHIZED `…::<impl [u8]>::{method}`, which
/// generic-strips to `core::slice::{method}` — anchored to the
/// `core::slice::`/`std::slice::` module root so a user `my::slice::{method}`
/// never matches. Inherent impls on primitives exist only in std, so the
/// anchored form is authoritative.
pub(super) fn vc_callee_is_slice_inherent(callee: &str, method: &str) -> bool {
    let suffix = format!("::{method}");
    if callee.contains(" as ") {
        return false;
    }
    if callee.contains("[T]") && callee.ends_with(&suffix) {
        return true;
    }
    let normalized = vc_strip_generics(callee);
    (normalized.starts_with("core::slice::") || normalized.starts_with("std::slice::"))
        && normalized.ends_with(&suffix)
}

/// Authenticate an inherent method on the canonical `alloc`/`std` `Vec`.
/// A user free function whose path merely mentions `Vec`, or a user trait impl
/// on `Vec`, must not mint empty-start/push/length facts.
pub(super) fn vc_callee_is_std_vec_inherent(callee: &str) -> bool {
    if callee.contains(" as ") {
        return false;
    }
    let normalized = callee.strip_prefix('<').unwrap_or(callee);
    normalized.starts_with("alloc::vec::Vec") || normalized.starts_with("std::vec::Vec")
}

pub(super) fn callee_is_iterator_next(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "next")
}

pub(super) fn callee_is_into_iter(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "IntoIterator", "into_iter")
}

/// `Iterator::rev`. `Rev<Range>::next` yields EXACTLY the values of the inner
/// `[start, end)` range (in reverse order), so the yield invariant
/// `start <= v < end` holds identically — `rev` is transparent for tracing the
/// underlying Range. (Only `rev`: value-transforming adapters like `map`/`filter`
/// would be UNSOUND to hop, and the Range-aggregate gate would not stop them.)
pub(super) fn callee_is_rev(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "rev")
}

/// `Iterator::step_by`. `StepBy<Range>::next` yields a SUBSET of the inner `[start, end)`
/// range (`start`, `start+k`, … while `< end`), so the yield invariant `start <= v < end`
/// holds identically — transparent for tracing the underlying Range like `rev`. Unlike `rev`
/// it is a TWO-arg call (`step_by(self_iter, step)`); the inner iterator is `args[0]`. The
/// `step` never widens the value set (any `step >= 1` yields a subset; `step == 0` PANICS
/// inside `step_by` before any value is yielded, so a yielded `v`'s invariant stays sound).
pub(super) fn callee_is_step_by(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "step_by")
}

/// EXCLUSIVE `std::ops::Range` only — NOT `RangeInclusive` (yield `<= end`),
/// `RangeFrom`, etc. The exclusive-range yield invariant is `start <= v < end`.
pub(super) fn aggregate_is_exclusive_range(name: &str) -> bool {
    range_family_adt_name(name) == Some("Range")
}

/// Canonical Range-family identity across rustc path-printing versions.
///
/// Older extracted MIR used the public re-export spelling `core::ops::RangeTo`;
/// current rustc emits an instantiated defining-module spelling such as
/// `core::ops::range::RangeTo<usize>`. These are the same lang-library ADT.
/// Strip instantiated generic groups, then match only the exact `core`/`std`
/// defining/re-export paths (never a user type whose tail happens to be
/// `RangeTo`) so a compiler path-format change cannot silently delete the
/// slice-index panic obligation or broaden the trusted recognizer.
pub(super) fn range_family_adt_name(name: &str) -> Option<&'static str> {
    let stripped = vc_strip_generics(name);
    let tail = ["core::ops::range::", "std::ops::range::", "core::ops::", "std::ops::"]
        .into_iter()
        .find_map(|prefix| stripped.strip_prefix(prefix))?;
    match tail {
        "Range" => Some("Range"),
        "RangeTo" => Some("RangeTo"),
        "RangeFrom" => Some("RangeFrom"),
        "RangeInclusive" => Some("RangeInclusive"),
        "RangeFull" => Some("RangeFull"),
        _ => None,
    }
}

/// Trace the receiver of an `Iterator::next` call back to the originating
/// exclusive-`Range` aggregate, returning its `(start, end)` operands. Walks the
/// for-loop desugaring `next(&mut it)` -> `it = into_iter(range)` ->
/// `range = Range { start, end }` through whole-local Ref/Use copies and the
/// single `into_iter` call, bounded by `fuel`. Returns None on any ambiguity.
pub(super) fn trace_local_to_range_aggregate(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<(&Operand, &Operand)> {
    if fuel == 0 {
        return None;
    }
    // (a) A statement definition of this whole local.
    if let Some(rvalue) = crate::unique_whole_local_def(func, local) {
        return match rvalue {
            Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, .. },
                operands,
            ) if aggregate_is_exclusive_range(name) && operands.len() == 2 => {
                Some((&operands[0], &operands[1]))
            }
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_range_aggregate(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_range_aggregate(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    // (b) Otherwise the local is a call destination — `into_iter` is the identity
    // for any iterator (incl. `Range`), and `rev` wraps a Range in `Rev<Range>`
    // whose `next` yields the SAME `[start, end)` value set (reversed); both are
    // transparent for tracing to the underlying Range, so hop to the argument.
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
            // `into_iter`/`rev` are 1-arg (inner iterator); `step_by` is 2-arg (inner + step).
            // All three preserve the `[start, end)` value SET (or a subset), so the inner
            // iterator is `args[0]` in every case.
            && ((callee_is_into_iter(callee) || callee_is_rev(callee)) && args.len() == 1
                || callee_is_step_by(callee) && args.len() == 2)
        {
            if let Operand::Copy(p) | Operand::Move(p) = &args[0]
                && p.projections.is_empty()
            {
                return trace_local_to_range_aggregate(func, p.local, fuel - 1);
            }
            return None;
        }
    }
    None
}

/// Trace a local holding a slice-index Range/RangeTo/RangeFrom aggregate to its
/// bound operands, following whole-local `Ref`/`Use` copies (bounded by `fuel`).
/// Returns `None` on any ambiguity — the caller MUST fail closed when the receiver
/// is a real slice (a missing bound here is a missing OOB obligation), never skip.
pub(super) fn trace_local_to_range_family(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<RangeFamilyOperands<'_>> {
    if fuel == 0 {
        return None;
    }
    if let Some(rvalue) = crate::unique_whole_local_def(func, local) {
        return match rvalue {
            Rvalue::Aggregate(
                trust_types::AggregateKind::Adt { name, variant: 0, .. },
                operands,
            ) => {
                let n = name.as_str();
                if aggregate_is_exclusive_range(n) && operands.len() == 2 {
                    Some(RangeFamilyOperands::Exclusive(&operands[0], &operands[1]))
                } else if range_family_adt_name(n) == Some("RangeTo") && operands.len() == 1 {
                    Some(RangeFamilyOperands::To(&operands[0]))
                } else if range_family_adt_name(n) == Some("RangeFrom") && operands.len() == 1 {
                    Some(RangeFamilyOperands::From(&operands[0]))
                } else {
                    None
                }
            }
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_range_family(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_range_family(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    None
}

/// Find the `Iterator::next` call whose destination is `next_result_local` and
/// trace its receiver to the originating exclusive-`Range`'s `(start, end)`.
pub(super) fn next_call_range_operands(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<(&Operand, &Operand)> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == next_result_local
            && dest.projections.is_empty()
            && callee_is_iterator_next(callee)
            && args.len() == 1
        {
            if let Operand::Copy(p) | Operand::Move(p) = &args[0]
                && p.projections.is_empty()
            {
                return trace_local_to_range_aggregate(func, p.local, fuel);
            }
            return None;
        }
    }
    None
}

/// Resolve a range bound operand to the canonical formula the bounds obligation
/// compares against, so the yield fact discharges it. For the `0..s.len()` idiom
/// `end` is a local defined by `PtrMetadata(s)`/`Len(s)`; resolve it to the SAME
/// `slice_len_formula(s)` term the index VC uses. Otherwise fall back to the
/// operand's own formula (sound; connects when the bound is a shared param/const).
pub(super) fn resolve_range_bound_formula(func: &VerifiableFunction, operand: &Operand, fuel: u32) -> Formula {
    if fuel > 0
        && let Operand::Copy(p) | Operand::Move(p) = operand
        && p.projections.is_empty()
    {
        match crate::unique_whole_local_def(func, p.local) {
            Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
                if let Some(len) = crate::slice_len_formula(func, inner) {
                    return len;
                }
            }
            Some(Rvalue::Len(place)) => {
                if let Some(len) = crate::slice_len_formula(func, &Operand::Copy(place.clone())) {
                    return len;
                }
            }
            Some(Rvalue::Use(inner)) => return resolve_range_bound_formula(func, inner, fuel - 1),
            _ => {}
        }
    }
    operand_to_formula(func, operand)
}

/// True iff `local` appears anywhere in `block` (as a place root, an `Index`
/// projection, an operand, or a terminator operand/dest). Used to attach a
/// payload's yield fact only to the blocks that reference it.
pub(super) fn block_mentions_local(block: &trust_types::BasicBlock, local: usize) -> bool {
    fn place_mentions(place: &Place, local: usize) -> bool {
        place.local == local
            || place
                .projections
                .iter()
                .any(|p| matches!(p, trust_types::Projection::Index(i) if *i == local))
    }
    fn operand_mentions(op: &Operand, local: usize) -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if place_mentions(p, local))
    }
    fn rvalue_mentions(rv: &Rvalue, local: usize) -> bool {
        match rv {
            Rvalue::Use(op)
            | Rvalue::UnaryOp(_, op)
            | Rvalue::Cast(op, _)
            | Rvalue::Repeat(op, _) => operand_mentions(op, local),
            Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                operand_mentions(a, local) || operand_mentions(b, local)
            }
            Rvalue::Ref { place, .. }
            | Rvalue::AddressOf(_, place)
            | Rvalue::Discriminant(place)
            | Rvalue::Len(place)
            | Rvalue::CopyForDeref(place) => place_mentions(place, local),
            Rvalue::Aggregate(_, ops) => ops.iter().any(|op| operand_mentions(op, local)),
            Rvalue::Unsupported { operands, .. } => {
                operands.iter().any(|op| operand_mentions(op, local))
            }
            _ => false,
        }
    }
    for stmt in &block.stmts {
        if let Statement::Assign { place, rvalue, .. } = stmt
            && (place_mentions(place, local) || rvalue_mentions(rvalue, local))
        {
            return true;
        }
    }
    match &block.terminator {
        Terminator::Call { args, dest, .. } => {
            dest.local == local || args.iter().any(|op| operand_mentions(op, local))
        }
        Terminator::SwitchInt { discr, .. } => operand_mentions(discr, local),
        Terminator::Assert { cond, .. } => operand_mentions(cond, local),
        _ => false,
    }
}

/// Build the per-block map of range-iterator yield facts. For each payload
/// binding `_p = (next(&mut range) as Some).0`, attach `start <= _p < end` to
/// every block that references `_p`. Independent of the BFS guard map so the
/// loop-join weakening cannot drop the fact. See the module banner above for the
/// soundness argument.
pub(super) fn build_range_yield_guard_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    let mut payloads: Vec<(usize, Formula, Formula)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if !is_some_payload_projection(&src.projections) {
                continue;
            }
            let Some((start_op, end_op)) = next_call_range_operands(func, src.local, TRACE_FUEL)
            else {
                continue;
            };
            let start_f = resolve_range_bound_formula(func, start_op, TRACE_FUEL);
            let end_f = resolve_range_bound_formula(func, end_op, TRACE_FUEL);
            payloads.push((dest.local, start_f, end_f));
        }
    }

    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if payloads.is_empty() {
        return map;
    }
    for block in &func.body.blocks {
        for (payload_local, start_f, end_f) in &payloads {
            if !block_mentions_local(block, *payload_local) {
                continue;
            }
            let payload_var =
                Formula::var(&place_to_var_name(func, &Place::local(*payload_local)), Sort::Int);
            let entry = map.entry(block.id).or_default();
            entry.push(Formula::Ge(Box::new(payload_var.clone()), Box::new(start_f.clone())));
            entry.push(Formula::Lt(Box::new(payload_var), Box::new(end_f.clone())));
        }
    }
    map
}

// ======================================================================
// Enumerate-iterator index yield facts (`for (i, x) in s.iter().enumerate()`)
// ======================================================================
//
// `s.iter().enumerate()` yields `(count, &elem)` where `count` runs 0, 1, …,
// s.len()-1 — exactly the valid indices, each `< s.len()`. So the index payload
// (the tuple's `.0`, read as `(next(..) as Some).0.0`) provably satisfies
// `0 <= i < s.len()`. Emitting that fact discharges an `s[i]` access inside the
// loop, making `for (i, _) in s.iter().enumerate() { … s[i] … }` PROVE instead of
// false-refuting (the index is otherwise havoc'd out of `next()`). Mirrors the
// range-yield fact, but the bound is the UNDERLYING SLICE's length and the payload
// is the tuple's first field. SOUNDNESS: gated on the Enumerate wrapping a
// `<[T]>::iter` over a concrete slice `s` (so the count's upper bound is exactly
// `s.len()`); any other iterator shape ⇒ no fact.
/// In `Option<(usize, _)>`, the enumerate index is `Some.0` then tuple-field `.0`:
/// projection `[Downcast(1), Field(0), Field(0)]`.
pub(super) fn is_enumerate_index_projection(projections: &[trust_types::Projection]) -> bool {
    matches!(
        projections,
        [
            trust_types::Projection::Downcast(1),
            trust_types::Projection::Field(0),
            trust_types::Projection::Field(0)
        ]
    )
}

pub(super) fn callee_is_enumerate(callee: &str) -> bool {
    vc_callee_is_std_iter_trait_method(callee, "Iterator", "enumerate")
}

/// `<[T]>::iter` — the SLICE iterator. Only this guarantees the enumerate count's
/// upper bound is the slice length (`<[T]>::iter` yields exactly `len` items).
pub(super) fn callee_is_slice_iter(callee: &str) -> bool {
    vc_callee_is_slice_inherent(callee, "iter")
}

/// Trace an `Iterator::next` receiver local back to the SLICE that an
/// `s.iter().enumerate()` chain enumerates, returning the slice operand. Walks
/// `next(&mut it)` -> `it = into_iter(enum)` -> `enum = enumerate(iter)` ->
/// `iter = <[T]>::iter(s)` through whole-local Ref/Use copies, bounded by `fuel`.
pub(super) fn trace_local_to_enumerated_slice(
    func: &VerifiableFunction,
    local: usize,
    fuel: u32,
) -> Option<Operand> {
    if fuel == 0 {
        return None;
    }
    if let Some(rvalue) = crate::unique_whole_local_def(func, local) {
        return match rvalue {
            Rvalue::Ref { place, .. } if place.projections.is_empty() => {
                trace_local_to_enumerated_slice(func, place.local, fuel - 1)
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) if p.projections.is_empty() => {
                trace_local_to_enumerated_slice(func, p.local, fuel - 1)
            }
            _ => None,
        };
    }
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
            && args.len() == 1
        {
            // `<[T]>::iter(s)` — the argument IS the slice; return it.
            if callee_is_slice_iter(callee) {
                return Some(args[0].clone());
            }
            // `into_iter`/`enumerate` are transparent for tracing to the slice.
            if (callee_is_into_iter(callee) || callee_is_enumerate(callee))
                && let Operand::Copy(p) | Operand::Move(p) = &args[0]
                && p.projections.is_empty()
            {
                return trace_local_to_enumerated_slice(func, p.local, fuel - 1);
            }
            return None;
        }
    }
    None
}

/// Find the `Iterator::next` call whose destination is `next_result_local` and
/// trace its RECEIVER to the slice an `s.iter().enumerate()` chain enumerates.
pub(super) fn next_call_enumerated_slice(
    func: &VerifiableFunction,
    next_result_local: usize,
    fuel: u32,
) -> Option<Operand> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == next_result_local
            && dest.projections.is_empty()
            && callee_is_iterator_next(callee)
            && args.len() == 1
            && let Operand::Copy(p) | Operand::Move(p) = &args[0]
            && p.projections.is_empty()
        {
            return trace_local_to_enumerated_slice(func, p.local, fuel);
        }
    }
    None
}

/// Build the per-block map of enumerate index yield facts: for each
/// `i = (next(&mut enumerate_iter) as Some).0.0`, attach `0 <= i < s.len()` to
/// every block referencing `i`. Computed independently of the BFS guard map, like
/// the range-yield fact, so loop-join weakening cannot drop it.
pub(super) fn build_enumerate_yield_guard_map(func: &VerifiableFunction) -> FxHashMap<BlockId, Vec<Formula>> {
    const TRACE_FUEL: u32 = 16;
    let mut payloads: Vec<(usize, Formula)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let (Rvalue::Use(Operand::Copy(src)) | Rvalue::Use(Operand::Move(src))) = rvalue else {
                continue;
            };
            if !is_enumerate_index_projection(&src.projections) {
                continue;
            }
            let Some(slice_op) = next_call_enumerated_slice(func, src.local, TRACE_FUEL) else {
                continue;
            };
            if let Some(len) = crate::slice_len_formula(func, &slice_op) {
                payloads.push((dest.local, len));
            }
        }
    }

    let mut map: FxHashMap<BlockId, Vec<Formula>> = FxHashMap::default();
    if payloads.is_empty() {
        return map;
    }
    for block in &func.body.blocks {
        for (payload_local, len_f) in &payloads {
            if !block_mentions_local(block, *payload_local) {
                continue;
            }
            let idx =
                Formula::var(&place_to_var_name(func, &Place::local(*payload_local)), Sort::Int);
            let entry = map.entry(block.id).or_default();
            entry.push(Formula::Ge(Box::new(idx.clone()), Box::new(Formula::Int(0))));
            entry.push(Formula::Lt(Box::new(idx), Box::new(len_f.clone())));
        }
    }
    map
}

// ======================================================================
// CharIndices yield → panic-free str range slicing (R2 corpus family 1)
// ======================================================================
//
// `s.char_indices()` yields `(i, c)` where `i` is the byte offset of the char `c`
// INSIDE `s`: by the `CharIndices` contract every yielded `i` satisfies BOTH
// `i < s.len()` (a char occupies at least one byte at `i`) AND
// `s.is_char_boundary(i)`. So `&s[i..]` / `&s[..i]` at a yielded `i` can NEVER
// panic — neither on bounds nor on the str char-boundary check — and `&s[a..i]`
// can only panic on the `a > i` ordering (when `a` is itself boundary-safe).
// This is the heck `capitalize`/`transform` idiom the corpus measurement found
// FALSE-REFUTED on every str crate.
//
// DESIGN (why a STRUCTURAL discharge at the VC site, not an Int yield fact):
// Trust's range-slice obligation models only the BOUNDS panic; the str
// char-boundary panic is not a formula term. A general Int fact `i < s.len()`
// would let DERIVED indices discharge the bounds VC — `&s[i-1..]` proves bounds
// from `i < len` yet `i-1` may fall mid-char and PANIC (a false proof). The
// structural discharge credits ONLY a bound that IS a yielded index (traced
// through Use-copies with single-def/no-mut-borrow gates at every step), for a
// receiver that IS the iterated string — for exactly those, the boundary panic is
// impossible by contract, so folding the bounds disjunct is a theorem, not an
// approximation. Anything derived (arithmetic, merges, a different string) fails
// the trace and keeps today's refutable VC.
//
// SOUNDNESS GATES (each kills a concrete false-proof channel):
//  * root identity: the sliced receiver and the `char_indices` receiver must trace
//    (Use-copies / `&(*x)` reborrows) to the SAME projection-free root local that
//    is a parameter or single-def, `&str`-typed (shared ref — its referent cannot
//    be resized/mutated in safe Rust), and never `&mut`/`&raw`-borrowed (a
//    `*root = other` rebind would break identity);
//  * iterator integrity: the `CharIndices` local is single-def (the
//    `char_indices` call), never written through a projection, and every
//    `&mut`/`&raw` borrow of it feeds ONLY `Iterator::next` (a `mem::swap(&mut
//    it, &mut other_it)` would splice in yields of a DIFFERENT string);
//  * payload integrity: the `Option` result and the payload binding are
//    single-def, never mut-borrowed, never projection-written (an `as_mut`
//    payload rewrite between `next()` and the read would launder an arbitrary
//    index into a "yield", the hunt-15 class-C channel);
//  * the `next` receiver type must BE `CharIndices` (`std::str::CharIndices` /
//    `core::str::CharIndices` — std-reserved paths), so a user iterator whose
//    `next` yields out-of-range tuples never matches, and adapters (`Peekable`,
//    `Rev`) fail the type gate (their yields are still in-contract, but the
//    trace declines — fail-closed).
/// True iff the ADT path names the std/core `CharIndices` iterator (generic args
/// stripped). `std`/`core` are reserved crate names, so this cannot collide with
/// a user type.
pub(super) fn adt_is_char_indices(name: &str) -> bool {
    let base = name.split('<').next().unwrap_or(name);
    matches!(
        base,
        "std::str::CharIndices" | "core::str::CharIndices" | "core::str::iter::CharIndices"
    )
}

/// True iff `local` is ever written through a projection (`x.f = ..`, `(*x).f = ..`),
/// `SetDiscriminant`, or deinitialized — writes `whole_local_def_count` does NOT see.
pub(super) fn local_has_projected_write(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| match s {
            Statement::Assign { place, .. } => {
                place.local == local && !place.projections.is_empty()
            }
            Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                place.local == local
            }
            _ => false,
        })
    })
}

/// Trace a `Copy`/`Move` operand to its projection-free ROOT local through
/// whole-local Use-copies and `&(*x)` shared reborrows, then gate the root:
/// `&str`/`&[T]`-typed (shared `Ref` to `Slice`), a parameter or single-def, never
/// `&mut`/`&raw`-borrowed, never projection-written. Returns the root local.
pub(super) fn charindices_shared_slice_root(func: &VerifiableFunction, op: &Operand) -> Option<usize> {
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let mut l = p.local;
    for _ in 0..8 {
        match crate::unique_whole_local_def(func, l) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q))) if q.projections.is_empty() => {
                l = q.local;
            }
            Some(Rvalue::Ref { mutable: false, place: q })
                if q.projections.as_slice() == [trust_types::Projection::Deref] =>
            {
                l = q.local;
            }
            _ => break,
        }
    }
    let root_is_shared_slice = matches!(
        crate::place_ty_cow(func, &Place::local(l)).as_deref(),
        Some(Ty::Ref { mutable: false, inner }) if matches!(inner.as_ref(), Ty::Slice { .. })
    );
    if root_is_shared_slice
        && (is_parameter(func, l) || guards::whole_local_def_count(func, l) == 1)
        && !guards::local_is_mutably_borrowed(func, l)
        && !local_has_projected_write(func, l)
    {
        Some(l)
    } else {
        None
    }
}

/// True iff every `&mut`/`&raw` borrow of `iter_local` is a single-def temp used
/// ONLY as the receiver (arg 0) of an `Iterator::next` call — the conduit
/// discipline that forbids `mem::swap`/`replace` re-seating the iterator.
pub(super) fn iter_mut_borrows_only_feed_next(func: &VerifiableFunction, iter_local: usize) -> bool {
    let mut conduits: Vec<usize> = Vec::new();
    for b in &func.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place, rvalue, .. } = s {
                match rvalue {
                    Rvalue::Ref { mutable: true, place: q } | Rvalue::AddressOf(_, q)
                        if q.local == iter_local =>
                    {
                        if !place.projections.is_empty() {
                            return false;
                        }
                        conduits.push(place.local);
                    }
                    _ => {}
                }
            }
        }
    }
    for t in conduits {
        if guards::whole_local_def_count(func, t) != 1 {
            return false;
        }
        // Every use of the conduit must be arg 0 of an `Iterator::next` call.
        for b in &func.body.blocks {
            for s in &b.stmts {
                if let Statement::Assign { rvalue, .. } = s {
                    let mut used = false;
                    for_each_rvalue_operand_place(rvalue, &mut |pl| {
                        if pl.local == t {
                            used = true;
                        }
                    });
                    if used {
                        return false;
                    }
                }
            }
            match &b.terminator {
                Terminator::Call { func: callee, args, .. } => {
                    for (i, a) in args.iter().enumerate() {
                        if let Operand::Copy(pl) | Operand::Move(pl) = a
                            && pl.local == t
                            && !(i == 0 && callee_is_iterator_next(callee))
                        {
                            return false;
                        }
                    }
                }
                Terminator::SwitchInt { discr, .. } => {
                    if matches!(discr, Operand::Copy(pl) | Operand::Move(pl) if pl.local == t) {
                        return false;
                    }
                }
                Terminator::Assert { cond, .. } => {
                    if matches!(cond, Operand::Copy(pl) | Operand::Move(pl) if pl.local == t) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// Invoke `f` on every place read by the rvalue's operands (incl. Ref/AddressOf
/// referents and Index projections' bases are NOT recursed — base places only).
pub(super) fn for_each_rvalue_operand_place(rvalue: &Rvalue, f: &mut impl FnMut(&Place)) {
    let mut on_op = |op: &Operand| {
        if let Operand::Copy(pl) | Operand::Move(pl) = op {
            f(pl);
        }
    };
    match rvalue {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) => {
            on_op(op)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            on_op(a);
            on_op(b);
        }
        Rvalue::Aggregate(_, ops) => ops.iter().for_each(on_op),
        Rvalue::Ref { place, .. }
        | Rvalue::AddressOf(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::Len(place)
        | Rvalue::CopyForDeref(place) => f(place),
        Rvalue::Unsupported { operands, .. } => operands.iter().for_each(on_op),
        _ => {}
    }
}

/// The `CharIndices` iterator local's SOURCE STRING root: `iter_local` must be
/// single-def by a std/core `char_indices` call whose receiver roots via
/// [`charindices_shared_slice_root`].
pub(super) fn charindices_iter_string_root(func: &VerifiableFunction, iter_local: usize) -> Option<usize> {
    if guards::whole_local_def_count(func, iter_local) != 1
        || local_has_projected_write(func, iter_local)
        || !iter_mut_borrows_only_feed_next(func, iter_local)
    {
        return None;
    }
    for b in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &b.terminator
            && dest.local == iter_local
            && dest.projections.is_empty()
        {
            if method_tail(callee) == "char_indices"
                && (callee.starts_with("core::str::") || callee.starts_with("std::str::"))
                && args.len() == 1
            {
                return charindices_shared_slice_root(func, &args[0]);
            }
            return None;
        }
    }
    None
}

/// True iff `op` IS (a single-def Use-copy of) the `.0` byte-index payload of a
/// `CharIndices::next() == Some` yield whose iterated string roots to a local in
/// `receiver_roots` — the full gate chain of the module banner above.
pub(super) fn operand_is_charindices_yield_of(
    func: &VerifiableFunction,
    op: &Operand,
    receiver_roots: &FxHashSet<usize>,
) -> bool {
    if receiver_roots.is_empty() {
        return false;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return false };
    if !p.projections.is_empty() {
        return false;
    }
    if guards::whole_local_def_count(func, p.local) != 1
        || guards::local_is_mutably_borrowed(func, p.local)
        || local_has_projected_write(func, p.local)
    {
        return false;
    }
    // The payload read: `_i = Copy((_opt as Some).0.0)`.
    let Some(Rvalue::Use(Operand::Copy(src) | Operand::Move(src))) =
        crate::unique_whole_local_def(func, p.local)
    else {
        return false;
    };
    if !is_enumerate_index_projection(&src.projections) {
        return false;
    }
    let opt_local = src.local;
    if guards::whole_local_def_count(func, opt_local) != 1
        || guards::local_is_mutably_borrowed(func, opt_local)
        || local_has_projected_write(func, opt_local)
    {
        return false;
    }
    // The producing `next` call, with a `&mut CharIndices` receiver temp.
    for b in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &b.terminator
            && dest.local == opt_local
            && dest.projections.is_empty()
        {
            if !callee_is_iterator_next(callee) || args.len() != 1 {
                return false;
            }
            let (Operand::Copy(r) | Operand::Move(r)) = &args[0] else { return false };
            if !r.projections.is_empty() {
                return false;
            }
            let recv_is_char_indices = matches!(
                crate::place_ty_cow(func, &Place::local(r.local)).as_deref(),
                Some(Ty::Ref { mutable: true, inner })
                    if matches!(inner.as_ref(), Ty::Adt { name, .. } if adt_is_char_indices(name))
            );
            if !recv_is_char_indices || guards::whole_local_def_count(func, r.local) != 1 {
                return false;
            }
            let Some(Rvalue::Ref { mutable: true, place: it }) =
                crate::unique_whole_local_def(func, r.local)
            else {
                return false;
            };
            if !it.projections.is_empty() {
                return false;
            }
            return charindices_iter_string_root(func, it.local)
                .is_some_and(|root| receiver_roots.contains(&root));
        }
    }
    false
}
