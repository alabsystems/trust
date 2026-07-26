// Lifting call sites into MirSem: argument operands through their casts and
// field reads, and the recognizers for the call-shaped bodies that carry a
// return value out of a callee. Certified-callee resolution decides which
// callees may be assumed rather than re-lifted.

use super::*;

/// Trust: discriminant-guard leaf — recognize the extractor's SYNTHESIZED
/// always-true enum-discriminant range fact, and ONLY it: `_d ∈ {t0, t1, …}`
/// spelled as `Eq(Var(v, Int), Int k)` or `Or([Eq(Var(v, Int), Int k), …])`
/// with ONE shared variable `v` across every leaf, where `v` refers to an
/// INTERNAL (non-return, non-argument) local of `body` — the `_d` index
/// spelling of an unnamed temp, or the debug name of a non-argument local —
/// and is NOT any parameter's name. (See
/// `trust-mir-extract::enum_discriminant_range_preconditions`, which emits
/// exactly this shape for single-assignment discriminant temps, which are
/// non-argument locals by its own gate.)
///
/// FAIL-CLOSED BY CONSTRUCTION: this only ever EXCLUDES a conjunct from the
/// caller-facing requires set inside [`CalleeFact::of_certified`]; a
/// misclassification in the conservative direction (a synthesized fact NOT
/// recognized) leaves the completeness gate to return `None` — a declined
/// callee, never a skipped obligation. The other direction (a DECLARED user
/// clause classified internal) requires the user clause to bind a
/// non-parameter body local, which the requires parser cannot produce.
pub(super) fn is_internal_discriminant_range_fact(
    f: &trust_types::Formula,
    body: &trust_types::VerifiableBody,
) -> bool {
    use trust_types::Formula as F;
    let leaves: Vec<&F> = match f {
        F::Or(disjuncts) => disjuncts.iter().collect(),
        other => vec![other],
    };
    if leaves.is_empty() {
        return false;
    }
    let mut shared_var: Option<&str> = None;
    for leaf in leaves {
        let F::Eq(lhs, rhs) = leaf else { return false };
        let (Some(v), Some(trust_types::Sort::Int), F::Int(_)) =
            (lhs.var_name(), lhs.var_sort(), rhs.as_ref())
        else {
            return false;
        };
        match shared_var {
            None => shared_var = Some(v),
            Some(prev) if prev == v => {}
            Some(_) => return false, // two different vars — not the emitted shape.
        }
    }
    let Some(v) = shared_var else { return false };
    // NEVER a parameter's name — a param-named fact would be a genuine
    // call-site obligation (or a user clause); keep it in the declared count.
    let is_param_name =
        (1..=body.arg_count).any(|i| body.locals.get(i).and_then(|l| l.name.as_deref()) == Some(v));
    if is_param_name {
        return false;
    }
    // The `_d` index spelling of an INTERNAL local (non-return, non-argument):
    if let Some(d) = v.strip_prefix('_').and_then(|s| s.parse::<usize>().ok()) {
        return d > body.arg_count && d < body.locals.len();
    }
    // The debug-name spelling of a non-argument local:
    body.locals.iter().any(|l| l.index > body.arg_count && l.name.as_deref() == Some(v))
}

/// Trust: structural-fold rung E — recognize the extractor's SYNTHESIZED
/// always-true INT TYPE-RANGE fact over a PARAMETER name, and ONLY it:
/// `And(Ge(Var(p, Int), Int lo), Le(Var(p, Int), Int hi))` where `p` is a
/// declared parameter whose type is `Ty::Int { width, signed }` and
/// `(lo, hi)` are EXACTLY that type's full bounds (`0..=2^w−1` unsigned,
/// `−2^(w−1)..=2^(w−1)−1` signed). Such a fact holds at every well-typed
/// call site by construction (rustc types the actual), so it is a type
/// tautology, not a caller obligation — the same argument as
/// [`is_internal_discriminant_range_fact`]'s family. FAIL-CLOSED BY
/// CONSTRUCTION (same reading as that function's doc): this only ever
/// EXCLUDES a conjunct from the caller-facing requires set; a narrowed
/// range, a non-parameter variable, a non-Int formal, or an unrepresentable
/// width stays in the declared count and the completeness gate returns
/// `None`.
pub(super) fn is_parameter_type_range_fact(
    f: &trust_types::Formula,
    body: &trust_types::VerifiableBody,
) -> bool {
    use trust_types::Formula as F;
    let F::And(conjs) = f else { return false };
    let [ge, le] = conjs.as_slice() else { return false };
    let F::Ge(ge_lhs, ge_rhs) = ge else { return false };
    let F::Le(le_lhs, le_rhs) = le else { return false };
    let (Some(v1), Some(trust_types::Sort::Int)) = (ge_lhs.var_name(), ge_lhs.var_sort()) else {
        return false;
    };
    let (Some(v2), Some(trust_types::Sort::Int)) = (le_lhs.var_name(), le_lhs.var_sort()) else {
        return false;
    };
    if v1 != v2 {
        return false;
    }
    let (F::Int(lo), F::Int(hi)) = (ge_rhs.as_ref(), le_rhs.as_ref()) else { return false };
    // `v1` must be a PARAMETER whose declared type is a plain integer.
    let Some(param) = (1..=body.arg_count)
        .filter_map(|i| body.locals.get(i))
        .find(|l| l.name.as_deref() == Some(v1))
    else {
        return false;
    };
    let trust_types::Ty::Int { width, signed } = param.ty else { return false };
    if width == 0 || width > 127 {
        return false; // 128-bit bounds are not representable in Formula::Int — fail closed.
    }
    let (ty_lo, ty_hi): (i128, i128) = if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    };
    *lo == ty_lo && *hi == ty_hi
}

/// Trust: Item 4 (wave-a) — recognize the extractor's SYNTHESIZED always-true CHAR
/// VALIDITY-RANGE fact over an INTERNAL local, and ONLY it: the exact shape
///
/// ```text
/// And([ Ge(Var(v,Int), Int 0),
///       Le(Var(v,Int), Int 1_114_111),
///       Not(And([ Ge(Var(v,Int), Int 55_296), Le(Var(v,Int), Int 57_343) ])) ])
/// ```
///
/// i.e. `v ∈ [0, 0x10FFFF] \ [0xD800, 0xDFFF]` — a Unicode SCALAR VALUE. The
/// extractor emits this for a local read out of a `char`-typed place (the
/// `char::is_ascii` leaf's `_3 := (*self)` where `self : &char`, feeding the
/// `_3 as u32` cast). Because rustc's type system guarantees every `char` is a
/// valid scalar value, the fact holds at EVERY well-typed call site BY
/// CONSTRUCTION — a type tautology, NOT a caller obligation — EXACTLY the argument
/// [`is_internal_discriminant_range_fact`] and [`is_parameter_type_range_fact`]
/// make for their synthesized families (and which the [`CalleeFact::of_certified`]
/// doc explicitly flagged this "char-range over internal locals" family for
/// extending). The magic constants ARE the char validity invariant, so the shape
/// is effectively a char-validity fingerprint; the establishment discipline is NOT
/// weakened — a genuine narrowed/param-bound range never matches.
///
/// FAIL-CLOSED BY CONSTRUCTION (same reading as the sibling recognizers): this
/// only ever EXCLUDES a conjunct from the caller-facing requires set; anything
/// off-shape (different bounds, a parameter-named var, a non-Int sort, a missing
/// surrogate exclusion) stays in the declared count and the completeness gate
/// returns `None`. `v` must be an INTERNAL (non-parameter) local — mirroring the
/// discriminant family's internal-only gate exactly.
pub(super) fn is_internal_char_range_fact(
    f: &trust_types::Formula,
    body: &trust_types::VerifiableBody,
) -> bool {
    use trust_types::Formula as F;
    // `g` is `Ge(Var(v,Int), Int k)` (when `want_ge`) or `Le(Var(v,Int), Int k)`
    // (when `!want_ge`): the var name and the integer bound, or `None` off-shape.
    fn int_bound(g: &F, want_ge: bool) -> Option<(&str, i128)> {
        let (lhs, rhs) = match (want_ge, g) {
            (true, F::Ge(l, r)) => (l, r),
            (false, F::Le(l, r)) => (l, r),
            _ => return None,
        };
        let (Some(v), Some(trust_types::Sort::Int), F::Int(k)) =
            (lhs.var_name(), lhs.var_sort(), rhs.as_ref())
        else {
            return None;
        };
        Some((v, *k))
    }
    let F::And(conjs) = f else { return false };
    let [ge, le, not_surr] = conjs.as_slice() else { return false };
    let Some((v0, 0)) = int_bound(ge, true) else { return false };
    let Some((v1, 1_114_111)) = int_bound(le, false) else { return false };
    let F::Not(inner) = not_surr else { return false };
    let F::And(surr) = inner.as_ref() else { return false };
    let [sge, sle] = surr.as_slice() else { return false };
    let Some((v2, 55_296)) = int_bound(sge, true) else { return false };
    let Some((v3, 57_343)) = int_bound(sle, false) else { return false };
    if v0 != v1 || v0 != v2 || v0 != v3 {
        return false; // the four bounds must constrain the SAME variable.
    }
    let v = v0;
    // NEVER a parameter's name — a param-named fact is kept in the declared count
    // (mirrors `is_internal_discriminant_range_fact`).
    let is_param_name =
        (1..=body.arg_count).any(|i| body.locals.get(i).and_then(|l| l.name.as_deref()) == Some(v));
    if is_param_name {
        return false;
    }
    // The `_d` index spelling of an INTERNAL local (non-return, non-argument):
    if let Some(d) = v.strip_prefix('_').and_then(|s| s.parse::<usize>().ok()) {
        return d > body.arg_count && d < body.locals.len();
    }
    // The debug-name spelling of a non-argument local:
    body.locals.iter().any(|l| l.index > body.arg_count && l.name.as_deref() == Some(v))
}

/// Resolve a MIR `Terminator::Call` callee string against the certified-callee
/// registry: EXACT def-path match, else a UNIQUE `::`-suffix match (mirroring
/// `trust_vcgen::build_call_graph`'s resolution), else — Trust: Item 2 — a UNIQUE
/// TRAIT-IMPL CANONICAL-TUPLE match ([`trust_types::call_graph::canonical_trait_method`],
/// bridging the `<SELF as TRAIT>::M` call spelling to the `<impl TRAIT for
/// SELF>::M` dump spelling — the SAME canonicalization `CalleeResolver` uses to
/// order the callee FIRST). AMBIGUITY FAILS CLOSED at every tier: two registry
/// keys sharing the suffix, or two keys canonicalizing to the same tuple, ⇒ `None`
/// (never guess which certified function is being called). Returns `(resolved_key,
/// fact, registry_index)`.
// Trust: W2 INC2 — `pub(crate)` so the iterator-for-loop recognizer's G2-REQUIRES gate
// can consult the resolved header-`next()` `CalleeFact` (fail-closed unless it declares no
// `requires`), mirroring the via_mirsem_call_requires pillar every registry consumer
// carries.
pub(crate) fn resolve_certified_callee<'a>(
    callees: &'a std::collections::BTreeMap<String, CalleeFact>,
    callee: &str,
) -> Option<(&'a str, &'a CalleeFact, u64)> {
    use trust_types::call_graph::canonical_trait_method;
    if let Some((k, f)) = callees.get_key_value(callee) {
        let id = callees.keys().position(|x| x == k)?;
        return Some((k.as_str(), f, u64::try_from(id).ok()?));
    }
    let suffix = format!("::{callee}");
    let mut hits = callees.iter().enumerate().filter(|(_, (k, _))| k.ends_with(&suffix));
    if let Some((id, (k, f))) = hits.next() {
        if hits.next().is_some() {
            return None; // ambiguous suffix — never guess (fail-closed).
        }
        return Some((k.as_str(), f, u64::try_from(id).ok()?));
    }
    // Trust: Item 2 — TRAIT-IMPL CANONICAL-TUPLE match. Only when the callee parses
    // as a trait method (else `canonical_trait_method` returns `None` and we decline,
    // exactly as before). EXACT tuple equality — never substring/fuzzy.
    let query = canonical_trait_method(callee)?;
    let mut canon_hits = callees
        .iter()
        .enumerate()
        .filter(|(_, (k, _))| canonical_trait_method(k).as_ref() == Some(&query));
    let (id, (k, f)) = canon_hits.next()?;
    if canon_hits.next().is_some() {
        return None; // ambiguous canonical tuple — fail-closed.
    }
    Some((k.as_str(), f, u64::try_from(id).ok()?))
}

/// Whether this statement (potentially) WRITES the given local — the fail-closed
/// single-writer discipline of the call-return spine. `Assign`/`SetDiscriminant`/
/// `Deinit`/`Retag` on the local count as writes (Retag is not a value write, but
/// declining it is the conservative side); storage markers and place mentions do
/// not. `Intrinsic` has no destination place; `Unsupported` is handled separately
/// (its mere presence declines the whole shape).
pub(super) fn stmt_writes_local(stmt: &trust_types::Statement, local: usize) -> bool {
    use trust_types::Statement;
    match stmt {
        Statement::Assign { place, .. }
        | Statement::SetDiscriminant { place, .. }
        | Statement::Deinit { place }
        | Statement::Retag { place } => place.local == local,
        _ => false,
    }
}

/// Trust: REASSIGNED-PARAM soundness — whether the PARAMETER local `local`
/// (`1..=arg_count`) is REASSIGNED by any statement in the body: it is the
/// UNPROJECTED `place.local` of any `Assign`/`SetDiscriminant`/`Deinit`/`Retag`
/// (the `stmt_writes_local` write idiom, RESTRICTED to a whole-local write of a
/// parameter).
///
/// This is the load-bearing distinction the straight-line / CALL / requires-
/// establishment recognizers rely on: a `SemOperand::Var(idx)` denotes the
/// ENTRY-TIME value of parameter `idx`, but those recognizers never modeled a
/// reassignment BEFORE the read, so consuming a reassigned parameter as an
/// entry-time `Var` operand certifies a claim about the WRONG value (the entry
/// value, not the post-reassignment one). The gate is threaded through the
/// single operand-resolution chokepoint [`sem_operand_of_mir`], which resolves a
/// bare parameter place to `Var(idx)` — so EVERY entry-time consumer (return
/// leaf, call arguments, the CallThenPureOp `other` operand, guarded arms, casts)
/// fails closed on a reassigned parameter.
///
/// A NON-parameter local (`local == 0` — the return place — or a temp
/// `> arg_count`) is NOT protected here: `sem_operand_of_mir` never resolves a
/// non-parameter place to a `Var` (it declines it outright), so its reassignment
/// is irrelevant to the entry-time reading. The LOOP recognizers model counter
/// EVOLUTION separately (`sem_operand_for_loop`, which does NOT route through
/// [`sem_operand_of_mir`]) and so a reassigned LOOP counter still certifies.
pub(crate) fn param_reassigned_by_stmt(body: &trust_types::VerifiableBody, local: usize) -> bool {
    use trust_types::{Rvalue, Statement, Terminator};
    if local == 0 || local > body.arg_count {
        return false; // not a parameter local — nothing to protect (see doc).
    }
    // A DIRECT statement write to the parameter's own local.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| stmt_writes_local(s, local)) {
        return true;
    }
    // Trust: reassigned-param SOUNDNESS (aliasing) — `stmt_writes_local` only catches a
    // DIRECT `local := …` write; an ALIASING write `(*p) = v` through a `&mut`/`&raw mut`
    // borrow of the parameter has `place.local == p`, invisible to it. Once a MUTABLE alias
    // to the parameter's entry value exists anywhere in the body, the recognizer can no
    // longer track its value, so the entry-time `Var(idx)` model is unsound. Fail-closed:
    // treat a mutable borrow / raw-mut address-of the parameter as a reassignment.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| {
        matches!(s,
            Statement::Assign { rvalue: Rvalue::Ref { mutable: true, place }, .. }
                | Statement::Assign { rvalue: Rvalue::AddressOf(true, place), .. }
            if place.local == local)
    }) {
        return true;
    }
    // Trust: reassigned-param SOUNDNESS (call-dest, recognizer well-formedness campaign,
    // 2026-07-05, closure pass) — the OTHER arm of the same blind spot: a
    // `Terminator::Call { dest }` writing the parameter's own local (`local := helper(...)`)
    // is a REASSIGNMENT that is likewise invisible to `stmt_writes_local` (a terminator, not a
    // statement) — the sibling gap the mutable-alias arm above closed for aliasing writes.
    // Fail-closed: treat a call-dest write to the parameter as a reassignment.
    body.blocks.iter().any(|b| {
        matches!(&b.terminator,
            Terminator::Call { dest, .. } if dest.local == local)
    })
}

/// Complete direct-write profile for a local used by the call-family
/// recognizers. Bare assignments are counted; every other rooted effect fails
/// closed. Call destinations are retained by block id so a recognizer can allow
/// exactly its intended call write without also admitting a disconnected or
/// second call destination.
pub(super) fn call_family_local_writes(
    body: &trust_types::VerifiableBody,
    local: usize,
) -> Option<(usize, Vec<trust_types::BlockId>)> {
    use std::collections::HashSet;

    use trust_types::{Rvalue, Statement, Terminator};

    // Every control-flow/dominance lookup below is block-id based. Duplicate ids
    // would make the selected definition/call ambiguous, so no profile is sound.
    let mut ids = HashSet::new();
    if body.blocks.iter().any(|block| !ids.insert(block.id)) {
        return None;
    }

    let mut assignments = 0usize;
    let mut call_destinations = Vec::new();
    for block in &body.blocks {
        for statement in &block.stmts {
            // A mutable or raw-mutable alias permits a later indirect write whose
            // destination is not syntactically rooted at `local`.
            if matches!(statement,
                Statement::Assign {
                    rvalue:
                        Rvalue::Ref { mutable: true, place }
                        | Rvalue::AddressOf(true, place),
                    ..
                } if place.local == local)
            {
                return None;
            }
            match statement {
                Statement::Assign { place, .. } if place.local == local => {
                    if !place.projections.is_empty() {
                        return None;
                    }
                    assignments += 1;
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                    if place.local == local =>
                {
                    return None;
                }
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { dest, .. } if dest.local == local => {
                if !dest.projections.is_empty() {
                    return None;
                }
                call_destinations.push(block.id);
            }
            // Dropping a rooted place invalidates it just like explicit Deinit.
            Terminator::Drop { place, .. } if place.local == local => return None,
            _ => {}
        }
    }
    Some((assignments, call_destinations))
}

/// Require exactly `assignments` bare statement definitions and exactly the
/// specified unprojected call destinations, with no other rooted/alias write.
pub(super) fn call_family_local_writes_exact(
    body: &trust_types::VerifiableBody,
    local: usize,
    assignments: usize,
    intended_call_blocks: &[trust_types::BlockId],
) -> bool {
    let Some((actual_assignments, mut actual_calls)) = call_family_local_writes(body, local) else {
        return false;
    };
    let mut intended_calls = intended_call_blocks.to_vec();
    actual_calls.sort_unstable_by_key(|id| id.0);
    intended_calls.sort_unstable_by_key(|id| id.0);
    actual_assignments == assignments && actual_calls == intended_calls
}

// ---------------------------------------------------------------------------
// Trust: THE LIFT — the first real-caller-over-real-loop-leaf composition. The
// closure `<arch::all::memchr::OneIter<'a,'h> as Iterator>::count::{closure#0}`
// is the call-return shape EXCEPT its first actual arg to `One::count_raw` is a
// FIELD-READ of the closure environment (`_4 := Copy(_1.[Deref, Field(0)])`),
// not a bare parameter — `sem_operand_of_mir` declines it. Two new fail-closed
// recognizers extend the CALL-ARG fragment (not the return fragment — the
// existing `sem_field_read_operand`/`resolve_cast_source_operand` return-path
// chases are UNTOUCHED):
//   * `sem_call_arg_field_read_operand` — chase a call arg's non-param temp `_t`
//     to its SOLE static assignment `_t := Use(<field-read>)`, admitting TWO
//     base shapes for the field-read (both modeled via the SAME
//     `SemOperand::Field` — REUSE, no new opaque, no new axiom):
//       (1) the EXISTING `&self`-shaped immutable-reference base
//           (`sem_field_read_operand`, unchanged);
//       (2) a MUTABLE reference to a `Ty::Closure` environment (the
//           `FnMut`/`FnOnce` calling convention's `self`) whose PROJECTED
//           UPVAR is ITSELF an immutable reference — the closure captured the
//           value BY SHARED REFERENCE, so copying it out duplicates a
//           Copy-typed shared handle, never granting write access through the
//           outer `&mut`. This is EXACTLY memchr's closure shape.
//   * `sem_call_arg_operand` — the call-arg entry point: `sem_operand_of_mir`
//     (bare param/const, BYTE-IDENTICAL — tried first) else the field-read
//     chase above.
// FAIL-CLOSED: a multiply-assigned temp (not sole-writer), a non-field-read
// assignment, a mutable-ref base whose field is NOT itself an immutable
// reference (the general `&mut self.field` case — aliasing/mutation risk), or
// any base that is neither `&self`-shaped nor this closure-upvar shape all
// decline — NEVER an arbitrary-temp absorption.
// ---------------------------------------------------------------------------
/// Trust: THE LIFT — resolve a CALL-SITE actual argument to a modeled
/// `SemOperand`: the bare param/const fragment (`sem_operand_of_mir`, tried
/// first, BYTE-IDENTICAL), else the field-read-through-a-temp chase
/// ([`sem_call_arg_field_read_operand`]). `None` (fail-closed) for anything
/// outside this fragment.
pub(super) fn sem_call_arg_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Ty};
    if let Some(direct) = sem_operand_of_mir(body, op, param_index) {
        return Some(direct);
    }
    // Call contracts also take shared-reference receivers (`&u8`/`&One`), raw
    // pointer values (`count_raw`'s start/end), and by-value enums (Ordering in
    // the certified `as_raw` family). They are opaque call values, not arithmetic
    // operands, so retain the historical `Var` representation specifically in
    // this lane. A shared referent must remain unchanged; raw pointers and enums
    // remain opaque (never dereferenced or interpreted arithmetically here).
    if let Operand::Copy(place) | Operand::Move(place) = op
        && place.projections.is_empty()
        && !param_reassigned_by_stmt(body, place.local)
    {
        let opaque_call_value = match body.locals.get(place.local).map(|local| &local.ty) {
            Some(Ty::Ref { mutable: false, .. }) => !deref_write_exists(body, place.local),
            Some(Ty::RawPtr { .. }) => true,
            Some(ty) if crate::assignment_types::modeled_enum_variant_count(ty).is_some() => {
                // Unlike a pointer/reference handle, this `Var` denotes the enum
                // parameter's complete entry value. Require the complete call-family
                // write profile to be empty as well as the shared reassignment gate:
                // projected/rooted statements, call destinations, drops, mutable
                // aliases, and duplicate block identities all fail closed.
                call_family_local_writes(body, place.local)
                    .is_some_and(|(assignments, calls)| assignments == 0 && calls.is_empty())
            }
            Some(_) => false,
            None => false,
        };
        if opaque_call_value && let Some(index) = param_index(place.local) {
            let var = SemOperand::Var(index);
            return Some(if matches!(op, Operand::Move(_)) {
                SemOperand::Move(Box::new(var))
            } else {
                var
            });
        }
    }
    if let Some(field) = sem_call_arg_field_read_operand(body, op, use_block, None, param_index) {
        return Some(field);
    }
    if let Some(referent) = sem_call_arg_ref_operand(body, op, use_block, param_index) {
        return Some(referent);
    }
    if let Some(preop) = sem_call_arg_preop_operand(body, op, use_block, param_index) {
        return Some(preop);
    }
    // Trust: W-CAST-ARG — a SAME-WIDTH signedness-reinterpret bitcast fed as the
    // actual argument (signed leading_zeros/swap_bytes/reverse_bits delegate).
    if let Some(bitcast) =
        sem_call_arg_samewidth_bitcast_operand(body, op, use_block, param_index)
    {
        return Some(bitcast);
    }
    // Trust: W-CAST-ARG (WIDTH-CHANGING, Item 3) — a width-changing IntToInt cast
    // fed as the actual argument (`min(self.count, buf.cap as u32)`'s `buf.cap as
    // u32`): the OPAQUE, no-value-claim `SemOperand::Cast` carrier (keyed by dest
    // width). Tried LAST so every same-width case is byte-identical to before.
    sem_call_arg_widthchanging_cast_operand(body, op, use_block, param_index)
}

/// Resolve an immutable address-of call temporary to its referent.  The temp's
/// sole definition must dominate the call; mutable borrows and reassigned bases
/// fail closed.
pub(super) fn sem_call_arg_ref_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Projection, Rvalue, Ty};

    let (Operand::Copy(temp) | Operand::Move(temp)) = op else { return None };
    if !temp.projections.is_empty() || param_index(temp.local).is_some() {
        return None;
    }
    let (_, _, definition) = unique_local_definition_dominating(body, temp.local, use_block, None)?;
    let Rvalue::Ref { mutable: false, place: referent } = definition else {
        return None;
    };
    let Ty::Ref { mutable: false, inner: borrowed_ty } =
        body.locals.get(temp.local).map(|local| &local.ty)?
    else {
        return None;
    };
    if crate::assignment_types::place_type(body, referent).as_ref() != Some(borrowed_ty.as_ref()) {
        return None;
    }
    if param_reassigned_by_stmt(body, referent.local) {
        return None;
    }
    let referent_op = Operand::Copy(referent.clone());
    sem_operand_of_mir(body, &referent_op, param_index)
        .or_else(|| sem_field_read_operand(body, &referent_op, param_index))
        .or_else(|| match referent.projections.as_slice() {
            // A by-value exact enum parameter borrowed for an `&self` method is
            // an opaque complete call value, never an arithmetic operand.
            [] => {
                let index = param_index(referent.local)?;
                let referent_ty = &body.locals.get(referent.local)?.ty;
                if crate::assignment_types::modeled_enum_variant_count(referent_ty).is_none()
                    || !call_family_local_writes(body, referent.local)
                        .is_some_and(|(assignments, calls)| assignments == 0 && calls.is_empty())
                {
                    return None;
                }
                Some(SemOperand::Var(index))
            }
            // Likewise for an exact enum-valued field reached through an
            // immutable aggregate reference. The field token is carried by the
            // established opaque projection; no enum value theory is asserted.
            [Projection::Deref, Projection::Field(field)] => {
                let index = param_index(referent.local)?;
                let Ty::Ref { mutable: false, inner } = &body.locals.get(referent.local)?.ty else {
                    return None;
                };
                let Ty::Adt { fields, .. } = inner.as_ref() else { return None };
                let (_, field_ty) = fields.get(*field)?;
                if crate::assignment_types::modeled_enum_variant_count(field_ty).is_none()
                    || deref_write_exists(body, referent.local)
                {
                    return None;
                }
                Some(SemOperand::Field(
                    Box::new(SemOperand::Var(index)),
                    u64::try_from(*field).ok()?,
                ))
            }
            _ => None,
        })
}

/// Resolve a pure unary operation materialized into a call-argument temp.  Both
/// the temp definition and any chased inner field temp are tied to the concrete
/// call use site; a later or non-dominating definition cannot be selected by
/// block-table order.
pub(super) fn sem_call_arg_preop_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue, Ty, UnOp};

    let (Operand::Copy(temp) | Operand::Move(temp)) = op else { return None };
    if !temp.projections.is_empty() || param_index(temp.local).is_some() {
        return None;
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, temp.local, use_block, None)?;
    let Rvalue::UnaryOp(un_op, inner) = definition else { return None };
    let temp_ty = body.locals.get(temp.local).map(|local| &local.ty);
    let kind = match un_op {
        UnOp::Not if matches!(temp_ty, Some(Ty::Int { .. })) => SemPreOp::Not,
        UnOp::Neg if matches!(temp_ty, Some(Ty::Int { signed: true, .. })) => SemPreOp::Neg,
        _ => return None,
    };
    let inner_sem = sem_operand_of_mir(body, inner, param_index).or_else(|| {
        sem_call_arg_field_read_operand(
            body,
            inner,
            definition_block,
            Some(definition_statement),
            param_index,
        )
    })?;
    Some(SemOperand::PreOp(Box::new(inner_sem), kind))
}

/// Resolve a same-width, opposite-signedness integer reinterpretation fed to a
/// call.  The cast temp must have one definition that dominates the call, and
/// the cast source is resolved at that exact definition site.
pub(super) fn sem_call_arg_samewidth_bitcast_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue, Ty};

    let (Operand::Copy(temp) | Operand::Move(temp)) = op else { return None };
    if !temp.projections.is_empty() || param_index(temp.local).is_some() {
        return None;
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, temp.local, use_block, None)?;
    let Rvalue::Cast(source, dest_ty) = definition else { return None };
    let (Operand::Copy(source_place) | Operand::Move(source_place)) = source else {
        return None;
    };
    if !source_place.projections.is_empty() {
        return None;
    }
    let source_ty = &body.locals.get(source_place.local)?.ty;
    let (
        Ty::Int { width: source_width, signed: source_signed },
        Ty::Int { width: dest_width, signed: dest_signed },
    ) = (source_ty, dest_ty)
    else {
        return None;
    };
    if source_width != dest_width || source_signed == dest_signed {
        return None;
    }
    let resolved = resolve_cast_source_operand(
        body,
        source,
        param_index,
        Some((definition_block, Some(definition_statement))),
    )?;
    Some(SemOperand::Cast(Box::new(resolved), u64::from(*dest_width), *dest_signed))
}

/// Trust: W-CAST-ARG (WIDTH-CHANGING, Item 3, wave-a) — a call-arg `Copy/Move(_t)`
/// whose SOLE assignment is a WIDTH-CHANGING `IntToInt` cast `_t := Cast(src,
/// dest_ty)` (`buf.cap as u32` in `Config::capped_count`: a `u64 -> u32` narrow)
/// → the OPAQUE [`SemOperand::Cast`] carrier. UNLIKE the SAME-WIDTH reinterpret
/// sibling ([`sem_call_arg_samewidth_bitcast_operand`]) this admits `sw != dw`
/// (either signedness).
///
/// SOUNDNESS — WHY WIDTH-CHANGING IS FINE HERE. The same-width sibling's SHARP
/// GATE exists because its target callees (ctlz/bswap/bitreverse) make
/// width-sensitive VALUE claims; the [`SemOperand::Cast`] carrier itself, however,
/// makes NO value claim at all: it is keyed DISTINCTLY per `(dest_width,
/// dest_signed)` ([`mirsem_cast_tag_key`]) and denotes an uninterpreted, total,
/// deterministic `Index base (Const key)` of the resolved source. It NEVER claims
/// `cast == src` (which would be false for a truncating cast — that identity claim
/// stays KernelRejected, and is the WIDENING lane's job, [`resolve_widening_cast_rvalue`],
/// gated to `dw >= sw` same-signedness). The destination width is baked into the
/// opaque key, so a `u64 -> u32` and a `u64 -> u16` cast of the SAME source are
/// never mis-equated. A callee whose `#[requires]` constrains this argument cannot
/// be established from the opaque carrier (it asserts no value), so
/// `function_call_requires_established` still fails closed there — this lane widens
/// only the SHAPE fragment, never a value or requires claim. Non-integer casts,
/// projected/constant sources, SAME-width casts (the sibling's / no-op's job), and
/// non-sole-writer temps all decline.
pub(super) fn sem_call_arg_widthchanging_cast_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Rvalue, Ty};
    let (Operand::Copy(t) | Operand::Move(t)) = op else { return None };
    if !t.projections.is_empty() || param_index(t.local).is_some() {
        return None;
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, t.local, use_block, None)?;
    let Rvalue::Cast(src_op, dest_ty) = definition else { return None };
    let (Operand::Copy(sp) | Operand::Move(sp)) = src_op else { return None };
    if !sp.projections.is_empty() {
        return None;
    }
    let src_ty = &body.locals.get(sp.local)?.ty;
    let (Ty::Int { width: sw, signed: _ss }, Ty::Int { width: dw, signed: ds }) = (src_ty, dest_ty)
    else {
        return None;
    };
    if sw == dw {
        return None; // SAME width — the reinterpret sibling's job (or a no-op identity).
    }
    let resolved = resolve_cast_source_operand(
        body,
        src_op,
        param_index,
        Some((definition_block, Some(definition_statement))),
    )?;
    Some(SemOperand::Cast(Box::new(resolved), u64::from(*dw), *ds))
}

/// Trust: THE LIFT — chase a call-arg operand `Copy/Move(_t)`, `_t` a
/// NON-parameter temp, to its SOLE static assignment `_t := Use(<field-read>)`,
/// admitting the closure-env upvar shape ALONGSIDE the existing `&self`-shaped
/// field read. See the module doc above for the full recognizer contract.
///
/// SOLE-WRITER discipline: `_t` must be assigned EXACTLY ONCE anywhere in the
/// body (mirrors `resolve_cast_source_operand`'s temp chase) — a
/// multiply-assigned temp is a genuine mutable variable, not a field-read
/// alias, and fails closed.
pub(super) fn sem_call_arg_field_read_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    use_block: trust_types::BlockId,
    use_statement: Option<usize>,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{Operand, Projection, Rvalue, Ty};
    let (Operand::Copy(t) | Operand::Move(t)) = op else { return None };
    if !t.projections.is_empty() || param_index(t.local).is_some() {
        return None; // a parameter or a projected operand — outside this chase.
    }
    // Complete sole-definition + exact use-site dominance. A definition on a
    // later/unreachable branch cannot supply an argument read by this Call
    // terminator merely because it appears first in block-vector order.
    let (_, _, found) =
        unique_local_definition_dominating(body, t.local, use_block, use_statement)?;
    let Rvalue::Use(field_op) = found else { return None }; // not a bare field-read.
    // Case 1: the EXISTING `&self`-shaped immutable-ref field read (unchanged).
    if let Some(field) = sem_field_read_operand(body, field_op, param_index) {
        return Some(field);
    }
    let (Operand::Copy(p) | Operand::Move(p)) = field_op else { return None };
    let [Projection::Deref, Projection::Field(fld)] = p.projections.as_slice() else {
        return None;
    };
    let base_idx = param_index(p.local)?;
    // Case 1b: an immutable `&self` field whose complete value is an exact
    // variantless `u64` newtype. This is scoped to CALL arguments: the call
    // model needs only a deterministic opaque token for the value, and makes
    // no scalar-value claim about the wrapped integer. In particular this
    // admits `Expr::has_fvar_quick` forwarding its immutable `ExprMeta` field
    // to `ExprMeta::has_fvar`; mutable references, wider/multi-field wrappers,
    // enums, and layout-marked ADTs still fail closed.
    if let Some(Ty::Ref { mutable: false, inner }) = body.locals.get(p.local).map(|l| &l.ty)
        && let Ty::Adt { fields, .. } = inner.as_ref()
        && fields.get(*fld).is_some_and(|(_, ty)| opaque_guard_newtype_u64(ty))
    {
        if param_reassigned_by_stmt(body, p.local) || deref_write_exists(body, p.local) {
            return None;
        }
        return Some(SemOperand::Field(
            Box::new(SemOperand::Var(base_idx)),
            u64::try_from(*fld).ok()?,
        ));
    }
    // Case 2: Trust: THE LIFT — a closure-environment upvar capture: `base` is a
    // MUTABLE reference to a `Ty::Closure` whose projected upvar is ITSELF an
    // immutable reference.
    let Some(Ty::Ref { mutable: true, inner }) = body.locals.get(p.local).map(|l| &l.ty) else {
        return None; // not a mutable-ref base (the immutable case is Case 1, above).
    };
    let Ty::Closure { upvars, .. } = inner.as_ref() else {
        return None; // a plain `&mut` struct field — declines (alias/mutation risk).
    };
    match upvars.get(*fld) {
        Some(Ty::Ref { mutable: false, .. }) => {}
        _ => return None, // the captured upvar is not itself a shared reference.
    }
    // The field carrier denotes the closure parameter's ENTRY value.  A
    // reassignment of the `&mut Closure` parameter or any write through it can
    // select a different captured reference before this materialization.  The
    // ordinary immutable-`&self` arm above already applies these twin gates;
    // the closure-upvar extension must not be weaker merely because its base
    // reference is mutable.
    if param_reassigned_by_stmt(body, p.local) || deref_write_exists(body, p.local) {
        return None;
    }
    Some(SemOperand::Field(Box::new(SemOperand::Var(base_idx)), u64::try_from(*fld).ok()?))
}

/// Follow only `Goto` edges from MIR entry (`BlockId(0)`) and report whether
/// `target` is reached. Bounded by the block count so a cycle fails closed.
pub(super) fn goto_only_entry_reaches(
    body: &trust_types::VerifiableBody,
    target: trust_types::BlockId,
) -> bool {
    use trust_types::Terminator;

    let mut cur = trust_types::BlockId(0);
    for _ in 0..=body.blocks.len() {
        if cur == target {
            return true;
        }
        let Some(block) = body.blocks.iter().find(|block| block.id == cur) else {
            return false;
        };
        let Terminator::Goto(next) = &block.terminator else {
            return false;
        };
        cur = *next;
    }
    false // a cycle before `target` — no reachable happy path.
}

/// Recognize the CALL-RETURN shape (the FOURTH return shape — call-spine
/// increment): the function's return value is written by a single
/// `Terminator::Call` to a callee in the ALREADY-CERTIFIED registry.
///
/// The admitted shape (everything else fails closed, `None`):
///   * EXACTLY ONE `Call` terminator in the whole body (the sole call step) — a
///     body that also carries a `contract_check_ensures` call, or any second
///     call, is DEFERRED (not this increment);
///   * the call is a direct, non-foreign, non-atomic Rust call with a live
///     return target and a BARE-local destination of integer type, and its block
///     is reached from entry (`BlockId(0)`) through `Goto`s only;
///   * the callee RESOLVES (exact / unique `::`-suffix) to a registry entry,
///     is NOT the function itself (self-recursion fails closed; a mutually-
///     recursive callee is never in the registry — certification is
///     callees-first), and the actual-arg arity matches the registry fact;
///   * EVERY actual argument is a modeled scalar operand (`sem_call_arg_operand`
///     — Trust: THE LIFT — a bare param/const, OR a field-read-through-a-temp
///     chase, admitting the closure-env upvar shape ALONGSIDE the existing
///     `&self`-shaped field read), and there is at least one;
///   * the return spine is LINEAR: the body has a UNIQUE `Return` block, the
///     call's target reaches it through `Goto`s only, every terminator in the
///     body is the recognized Call / `Goto` / `Return`, and no `Unsupported`
///     statement appears anywhere;
///   * the call is the SOLE WRITER of the returned value: either the dest IS
///     `_0` and NOTHING else writes `_0`, or the dest is a non-param temp `_t`
///     whose ONLY other use is the unique `_0 := Use(Copy/Move _t)` in the
///     `Return` block (and nothing else writes `_0` or `_t`).
/// (`pub(crate)` for the trust-ir via-path — Seam B discipline: prove.rs's
/// `call_return_fully_faithful_via_trustir` reuses this recognizer SHAPE-ONLY;
/// its kernel evidence is the trust-ir `callReturnInstance`, and no MirSem
/// kernel certificate is minted on that path.)
pub(crate) fn sem_call_return_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallReturn> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }))
    };
    // Trust: Bool-dest/ret widening — a DIRECT call whose destination is `Bool`
    // (a Rust `bool`-returning callee, e.g. a hypothetical certified predicate)
    // is ALSO admitted at the dest/ret gate. `local_is_int` stays BYTE-IDENTICAL
    // (untouched — it is already width/sign-agnostic for every integer type; the
    // census found 0 functions gated on integer width). The kernel `call_result`
    // denotation is `Int`-valued regardless of the Rust type, so this widening
    // costs nothing on the adequacy axis: a Bool value is modeled, by convention,
    // as 0/1 on the Int carrier — the SAME opaque `call_result` value, no new
    // claim about WHICH of {0,1} it is. HONEST SCOPE: this widens the GATE only —
    // it admits a call that DIRECTLY writes a Bool-typed `_0` (or a bare-Use-passthrough
    // temp), the sole-writer discipline below is unchanged. It does NOT, by
    // itself, admit a call-then-COMPARE shape (`is_empty`'s `len() == 0`), whose
    // dest is an Int temp compared afterward — that is a structurally different,
    // not-yet-modeled shape (named residue).
    let local_is_int_or_bool = |local: usize| -> bool {
        local_is_int(local) || matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Bool))
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY ONE Call terminator; every other terminator must be Goto/Return.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if call.is_some() {
                    return None; // a second call — not the sole-call shape.
                }
                call = Some((
                    block.id,
                    callee,
                    args,
                    dest,
                    *target,
                    atomic,
                    *is_foreign,
                    *is_unsafe_sig,
                ));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None, // any other terminator ⇒ outside the modeled spine.
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign, is_unsafe_sig) = call?;

    // ABI fail-closes: foreign / atomic / diverging (no return target).
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return None;
    }
    let target = target?;

    // Trust: ENTRY-REACHABILITY — a sole Call elsewhere in the block table does
    // not establish that the function executes it. In particular, reject a
    // diverging entry self-loop plus an unreachable Call/Return island. This
    // shape admits only the linear Goto prefix leading from `BlockId(0)` to the
    // recognized Call.
    if !goto_only_entry_reaches(body, call_block_id) {
        return None;
    }
    // Dest must be a BARE local of integer (or, Trust: Bool-dest/ret widening,
    // Bool) type (no projections — an unmodeled dest projection like
    // `_0.0 = call()` fails closed).
    if !dest.projections.is_empty() || !local_is_int_or_bool(dest.local) || !local_is_int_or_bool(0)
    {
        return None;
    }

    // Resolve the callee in the certified registry (exact / UNIQUE suffix).
    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    // Self-recursion fails closed (by def-path AND by resolution): the callee's
    // certificate cannot precede the caller's own.
    if resolved == func.def_path || *callee_str == func.def_path {
        return None;
    }
    // Arity must match the certified callee's declared parameter count.
    if fact.arg_count != args.len() {
        return None;
    }

    // EVERY actual argument must be a modeled scalar operand; at least one.
    if args.is_empty() {
        return None;
    }
    // Trust: THE LIFT — `sem_call_arg_operand` extends `sem_operand_of_mir` with the
    // field-read-through-a-temp chase (the closure-env upvar shape); the bare
    // param/const path stays byte-identical (tried first, unchanged).
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    // The UNIQUE Return block.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    // The call's continuation reaches the Return block through Gotos ONLY.
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear return spine.
        }
    }

    // Complete rooted-write discipline on the returned value. The recognized
    // Call destination is allowed exactly at `call_block_id`; every projected,
    // alias, drop, or additional Call/statement write declines.
    if dest.local == 0 {
        // Case A: `_0 = g(args) -> [return: bb]` — nothing else may write `_0`.
        if !call_family_local_writes_exact(body, 0, 0, &[call_block_id]) {
            return None;
        }
    } else {
        // Case B: `_t = g(args)`, then the Return block's `_0 := Use(Copy/Move _t)`.
        let t = dest.local;
        if param_index(t).is_some() {
            return None; // a call overwriting a parameter place — unmodeled.
        }
        // The ONE write to `_0` is the Return block's bare move/copy of `_t`.
        if !call_family_local_writes_exact(body, 0, 1, &[])
            || !call_family_local_writes_exact(body, t, 0, &[call_block_id])
        {
            return None;
        }
        let last_to_0 = ret_block
            .stmts
            .iter()
            .rev()
            .find_map(|s| crate::assignment_types::assigned_local_rvalue(body, s, 0))?;
        match last_to_0 {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if p.local == t && p.projections.is_empty() => {}
            _ => return None,
        }
    }

    Some(SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args })
}

/// Recognize the W-BITINTRIN return shape: the caller's `_0` (directly, or via a
/// single moved temp) is written by exactly ONE `Terminator::Call` to a PINNED
/// PURE-TOTAL callable ([`PinnedTotalCallable::classify`] — a unary bit-intrinsic,
/// the pinned `count_ones` bit-count method, or a compiler-marked BINARY
/// saturating intrinsic),
/// whose EXACTLY-`arity()` argument(s) are each a modeled scalar operand (Trust:
/// W-PREOP-ARG — INCLUDING a `!self`/`-self` pre-op temp, via
/// [`sem_call_arg_operand`]'s pre-op chase). Returns a [`SemCallReturn`] whose
/// `callee_id` is the callable's synthetic id, so the EXISTING
/// [`call_return_adequacy_witness`] kernel machinery certifies it verbatim — the
/// return denotes the callable's opaque, total `call_result` (the arity-2 case tags
/// the `Call.mk` with the FIRST arg; both args are still Lemma-1A certified — see the
/// W-BITINTRIN module header's ARITY-2 SOUNDNESS note).
///
/// UNLIKE [`sem_call_return_of_mir`] this does NOT consult the certified-callee
/// registry (a body-less intrinsic never appears there); the pinned classification
/// + arity gate is what admits it. Byte-identical sole-call / sole-writer / return-
/// spine discipline otherwise. FAIL-CLOSED on: a non-pinned callee, wrong arity, a
/// foreign/atomic/diverging ABI, a second call, an entry path that does not reach
/// the call through `Goto`s, a projected/non-int dest, an unmodeled argument, a
/// multiply-written return temp, or any non-Goto/Return terminator on the spine.
#[must_use]
pub(crate) fn sem_intrinsic_call_return_of_mir(
    func: &trust_types::VerifiableFunction,
) -> Option<SemCallReturn> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, Ty};
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }) | Some(Ty::Bool))
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY ONE Call terminator; every other terminator must be Goto/Return.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if call.is_some() {
                    return None; // a second call — not the sole-call shape.
                }
                call = Some((
                    block.id,
                    callee,
                    args,
                    dest,
                    *target,
                    atomic,
                    *is_foreign,
                    *is_unsafe_sig,
                ));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None, // any other terminator ⇒ outside the modeled spine.
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign, is_unsafe_sig) = call?;

    // ABI fail-closes: foreign / atomic / diverging (no return target).
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return None;
    }
    let target = target?;

    // Match the certified-callee recognizer's entry-reachability gate exactly:
    // an unreachable intrinsic Call/Return island cannot witness the function's
    // return merely because it is the sole Call present in the serialized body.
    if !goto_only_entry_reaches(body, call_block_id) {
        return None;
    }

    // THE PINNED classification — the ONLY admission gate that replaces the
    // registry lookup. A non-pinned / partial / forged def-path fails closed here.
    let callable = PinnedTotalCallable::classify(callee_str)?;
    // Self-reference can never be a pinned callable, but keep the fail-closed guard.
    if *callee_str == func.def_path {
        return None;
    }
    // EXACT arity — a wrong-arity call (`ctpop(a, b)`) is a forgery; fail closed.
    if args.len() != callable.arity() {
        return None;
    }

    // Dest must be a BARE int/bool local (no projections); `_0` likewise.
    if !dest.projections.is_empty() || !local_is_int_or_bool(dest.local) || !local_is_int_or_bool(0)
    {
        return None;
    }

    // EVERY actual argument a modeled scalar operand (arity guarantees exactly one).
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    // The UNIQUE Return block, reached from the call's target through Gotos only.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear return spine.
        }
    }

    // Complete rooted-write discipline on the returned value (the intended
    // intrinsic Call destination is the sole allowed call write).
    if dest.local == 0 {
        // Case A: `_0 = intrinsic(arg) -> [return: bb]` — nothing else may write `_0`.
        if !call_family_local_writes_exact(body, 0, 0, &[call_block_id]) {
            return None;
        }
    } else {
        // Case B: `_t = intrinsic(arg)`, then the Return block's `_0 := Use(Copy/Move _t)`.
        let t = dest.local;
        if param_index(t).is_some() {
            return None; // an intrinsic overwriting a parameter place — unmodeled.
        }
        if !call_family_local_writes_exact(body, 0, 1, &[])
            || !call_family_local_writes_exact(body, t, 0, &[call_block_id])
        {
            return None;
        }
        let last_to_0 = ret_block.stmts.iter().rev().find_map(|s| match s {
            Statement::Assign { place, rvalue, .. }
                if place.local == 0 && place.projections.is_empty() =>
            {
                Some(rvalue)
            }
            _ => None,
        })?;
        match last_to_0 {
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                if p.local == t && p.projections.is_empty() => {}
            _ => return None,
        }
    }

    Some(SemCallReturn {
        callee: callee_str.clone(),
        callee_id: callable.synthetic_callee_id(),
        args: sem_args,
    })
}

/// Recognize the CALL-THEN-PUREOP shape (closes the "Call-then-Compare" named
/// residue). Mirrors [`sem_call_return_of_mir`] clause-for-clause where it
/// overlaps; the NEW clauses are the dest/`_0`-write gates below.
///
/// The admitted shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere; every terminator is Call/Goto/Return;
///     EXACTLY one `Call` terminator in the whole body.
///   * the call is direct/non-foreign/non-atomic, has a live target, and its
///     destination is a BARE local `_t` — NOT `_0` (that direct-write shape
///     belongs to [`sem_call_return_of_mir`], tried first at every call site) and
///     NOT a parameter — of integer (or Bool) type.
///   * `_t` is SOLE-WRITTEN: the call is its only write (`writes_to(t) == 0`, no
///     statement ALSO assigns it — a multiply-written temp declines).
///   * the callee resolves in the certified registry (exact / unique `::`-suffix,
///     never self-recursive), the arity matches, and EVERY actual argument is a
///     modeled scalar operand ([`sem_call_arg_operand`] — at least one).
///   * the return spine is linear: a UNIQUE `Return` block, reached from the
///     call's target through `Goto`s only (byte-identical chase to
///     `sem_call_return_of_mir`'s own).
///   * `_0` is written EXACTLY ONCE (`writes_to(0) == 1`), by a
///     `Rvalue::BinaryOp(op, a, b)` — a `CheckedBinaryOp` is NOT admitted here (the
///     checked-arith field-return shape is a different, already-modeled pattern) —
///     where `op` resolves via [`sem_binop_of_mir`] (arithmetic) or
///     [`sem_cmpop_of_mir`] (comparison), and EXACTLY ONE of `a`/`b` is a bare
///     `Copy`/`Move` of `_t` (unprojected) while the OTHER resolves via
///     [`sem_operand_of_mir`] to a param/const. NEITHER operand being the call
///     result (both param/const) declines — the op must actually CONSUME `_t`.
///     BOTH operands being the call result ALSO declines (not this shape).
pub(crate) fn sem_call_then_pureop_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallThenPureOp> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }) | Some(Ty::Bool))
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY ONE Call terminator; every other terminator must be Goto/Return.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if call.is_some() {
                    return None; // a second call — not the sole-call shape.
                }
                call = Some((
                    block.id,
                    callee,
                    args,
                    dest,
                    *target,
                    atomic,
                    *is_foreign,
                    *is_unsafe_sig,
                ));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None,
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign, is_unsafe_sig) = call?;
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return None;
    }
    let target = target?;

    // Trust: ENTRY-REACHABILITY — the recognized Call block must be REACHABLE from
    // the entry block `BlockId(0)` along the happy path (Goto-only; every
    // terminator admitted here is Goto/Return/the single Call, so the reachable
    // CFG is a single line). A diverging entry (`Goto(0)` self-loop) with an
    // UNREACHABLE Call+Return island otherwise certifies a call that never runs —
    // mirror `sem_call_op_call_of_mir`'s `BlockId(0)` walk and fail closed.
    {
        let mut cur = trust_types::BlockId(0);
        let mut steps = 0usize;
        while cur != call_block_id {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                _ => return None, // the entry path diverges before reaching the call.
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None; // cycle before the call — unreachable happy path.
            }
        }
    }

    // The dest must be a BARE, non-parameter, non-`_0` temp `_t` of int/bool type —
    // the direct-`_0`-write shape belongs to `sem_call_return_of_mir`.
    if !dest.projections.is_empty() {
        return None;
    }
    let t = dest.local;
    if t == 0 || param_index(t).is_some() || !local_is_int_or_bool(t) {
        return None;
    }

    // Resolve the callee in the certified registry (exact / UNIQUE suffix).
    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    if resolved == func.def_path || *callee_str == func.def_path {
        return None; // self-recursion fails closed.
    }
    if fact.arg_count != args.len() {
        return None;
    }
    if args.is_empty() {
        return None;
    }
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    // Complete sole-writer discipline: `_t`'s only rooted write is this Call.
    if !call_family_local_writes_exact(body, t, 0, &[call_block_id]) {
        return None; // a multiply-written temp — not sole-writer, fail closed.
    }

    // The UNIQUE Return block, reached from the call's target through Gotos only
    // (byte-identical chase to `sem_call_return_of_mir`'s own).
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(g) => cur = *g,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear return spine.
        }
    }

    // `_0`'s SOLE write is a pure `BinaryOp` consuming `_t`.
    if !call_family_local_writes_exact(body, 0, 1, &[]) {
        return None;
    }
    let (return_statement, rv) =
        ret_block.stmts.iter().enumerate().rev().find_map(|(statement, s)| {
            crate::assignment_types::assigned_local_rvalue(body, s, 0)
                .map(|rvalue| (statement, rvalue))
        })?;

    let is_call_result = |o: &Operand| -> bool {
        matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == t && p.projections.is_empty())
    };

    // Trust: Call-then-UnaryOp — `_0 := UnaryOp(Not/Neg, _t)` (`Either::is_right`'s
    // `!is_left(self)` shape: ONE operand, not two). DESUGARED to the EXISTING
    // `CallThenOp` shapes (REUSE — no new kernel proof, no new axiom):
    //   * `Not(_t)`  ≡ `_t == 0`  (the "bool_as_int" 0/1 convention this file already
    //     establishes for a Bool-typed call result — see `bool_as_int`'s doc — means
    //     boolean negation IS exactly the equality test against `0`): modeled as
    //     `CallThenOp::Cmp(Eq)`, `other = Const(0)`, `call_is_lhs = true`. SOUNDNESS:
    //     `!x` on an INTEGER `x` is BITWISE complement, NOT `x == 0` — a totally
    //     different value. So this desugaring requires `_t`'s DECLARED type be
    //     EXACTLY `Ty::Bool` (Rust's `!` on `bool` IS logical negation), never merely
    //     "int or bool" (the wider gate the BinaryOp path above uses, where every
    //     admitted op — `Eq`/arithmetic — is sound on either).
    //   * `Neg(_t)`  ≡ `0 - _t`: modeled as `CallThenOp::Bin(Sub)`, `other = Const(0)`,
    //     `call_is_lhs = false` (so `wrap` computes `op(other, call_result)` =
    //     `Sub(0, x)` = `-x`, matching `arm_value_rvalue_for`'s identical `Neg`-as-
    //     `Sub(Const 0, op)` idiom for the unrelated `abs` guarded-arm shape). `Neg`
    //     is never valid on `bool` in Rust, so requires `_t`'s type be a SIGNED
    //     `Ty::Int` (unsigned negation is not valid Rust either).
    // Both reuse the SAME `call_then_pureop_instance_verdict`/adequacy witness
    // UNCHANGED — this is a RECOGNIZER-LEVEL rewrite, not a new kernel theorem.
    if let Rvalue::UnaryOp(un_op, operand) = rv {
        if !is_call_result(operand) {
            return None; // the unary op's operand is not the call result — decline.
        }
        let t_ty = body.locals.get(t).map(|l| &l.ty);
        let (call_then_op, other, call_is_lhs) = match un_op {
            trust_types::UnOp::Not => {
                if !matches!(t_ty, Some(Ty::Bool)) {
                    return None; // NOT a bool dest — `!x` would be bitwise, not `x==0`.
                }
                (CallThenOp::Cmp(SemCmpOp::Eq), SemOperand::Const(0), true)
            }
            trust_types::UnOp::Neg => {
                if !matches!(t_ty, Some(Ty::Int { signed: true, .. })) {
                    return None; // negation is only valid on a SIGNED integer dest.
                }
                (CallThenOp::Bin(SemBinOp::Sub), SemOperand::Const(0), false)
            }
            // `PtrMetadata` (out of fragment) and any future variant: `UnOp` is
            // `#[non_exhaustive]` (declared in the foreign `trust_types` crate), so a
            // wildcard is required — and correctly fails closed for one too.
            _ => return None,
        };
        return Some(SemCallThenPureOp {
            call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args },
            op: call_then_op,
            other,
            call_is_lhs,
        });
    }

    // A signed bit-method delegate casts the unsigned primary's result back to
    // the same-width signed type. Admit only an integer, opposite-signedness,
    // exactly same-width reinterpretation of the call-result temp.
    if let Rvalue::Cast(cast_source, destination_ty) = rv {
        if !is_call_result(cast_source) {
            return None;
        }
        let Some(Ty::Int { width: source_width, signed: source_signed }) =
            body.locals.get(t).map(|local| &local.ty)
        else {
            return None;
        };
        let Ty::Int { width: destination_width, signed: destination_signed } = destination_ty
        else {
            return None;
        };
        if source_width != destination_width || source_signed == destination_signed {
            return None;
        }
        return Some(SemCallThenPureOp {
            call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args },
            op: CallThenOp::Cast(u64::from(*destination_width), *destination_signed),
            other: SemOperand::Const(0),
            call_is_lhs: true,
        });
    }

    let Rvalue::BinaryOp(op, a, b) = rv else {
        return None; // NOT a pure BinaryOp/UnaryOp/Cast.
    };

    let call_is_lhs = match (is_call_result(a), is_call_result(b)) {
        (true, false) => true,
        (false, true) => false,
        _ => return None, // neither operand (or BOTH) consumes `_t` — decline.
    };
    let other_operand = if call_is_lhs { b } else { a };
    // Trust: REASSIGNED-PARAM soundness — the NON-call operand is an ENTRY-TIME
    // `Var` read; `sem_operand_of_mir` fails closed if it is a reassigned param
    // (the `helper(5) == n` after `n = n + 1` repro compares against `n + 1`, not
    // the entry `n`).
    // Trust: M6 rung 6 — FIELD-READ other operand (closing this shape's own
    // named residue "a field-read … declines"): when the bare-operand leaf
    // declines, fall back to the SAME sole-writer field-read-temp chase the
    // CALL-ARG side already trusts (`sem_call_arg_field_read_operand` — THE
    // LIFT's resolver, which itself delegates to `sem_field_read_operand`'s
    // immutable-`&self` / gated by-value arms). This is the
    // `Lifter::should_descend`-class shape: `_3 := (*self).start; call; _0 :=
    // Lt(_3, _t)` — the non-call operand is an entry-time FIELD read, exactly
    // as fixed a scalar as a param read (the kernel instance ∀-binds it — see
    // `TrustIrOtherOperand`'s Param path). Fail-closed on every clause of the
    // chase (multiply-written temp, `&mut` base, reassigned param, …).
    let other = sem_operand_of_mir(body, other_operand, &param_index).or_else(|| {
        sem_call_arg_field_read_operand(
            body,
            other_operand,
            ret_block.id,
            Some(return_statement),
            &param_index,
        )
    })?;

    let call_then_op = if let Some(bin) = sem_binop_of_mir(op) {
        CallThenOp::Bin(bin)
    } else if let Some(cmp) = sem_cmpop_of_mir(op) {
        CallThenOp::Cmp(cmp)
    } else {
        return None; // an unmodeled binop (shift/bitwise/…) — fail closed.
    };

    Some(SemCallThenPureOp {
        call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args },
        op: call_then_op,
        other,
        call_is_lhs,
    })
}

/// Recognize the CALL-OP-CALL shape (closes the residue [`sem_call_then_pureop_
/// of_mir`] names: "BOTH operands being the call result ALSO declines — not
/// this shape"). Mirrors [`sem_call_then_pureop_of_mir`] clause-for-clause
/// where it overlaps, widened to TWO calls.
///
/// The admitted shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere; every terminator is Call/Goto/
///     Return/Assert (Assert is the checked-arith overflow guard the tuple
///     sub-shape below emits — its `cond`/`msg` are not inspected here, the
///     SAME discipline as [`resolve_checked_field_rvalue`]/[`arm_value_rvalue_for`]:
///     the safety obligation is a SEPARATE, separately-discharged axis);
///     EXACTLY TWO `Call` terminators in the whole body.
///   * walking from the entry block (every terminator admitted here has
///     out-degree ≤ 1, so the reachable CFG is a single line) to the unique
///     `Return` block visits BOTH calls, in program order — a cycle, an
///     unreachable Return, or a walk that does not encounter EXACTLY the two
///     counted calls (e.g. one sits in unreached code) fails closed.
///   * each call is direct/non-foreign/non-atomic, has a live target, and its
///     destination is a BARE local `_a`/`_b` — NOT `_0`, NOT a parameter, of
///     integer (or Bool) type — and the two destinations are DISTINCT.
///   * each callee resolves in the certified registry (exact / unique
///     `::`-suffix, never self-recursive — INCLUDING the SAME callee called
///     twice, `double_len`'s `len()`/`len()`), the arity matches, and EVERY
///     actual argument is a modeled scalar operand ([`sem_call_arg_operand`] —
///     at least one).
///   * `_a`/`_b` are each SOLE-WRITTEN (the call is the only write to them — a
///     multiply-written temp declines).
///   * `_0` is written EXACTLY ONCE, either:
///     (a) DIRECTLY: `_0 := BinaryOp(op, x, y)` with `{x,y}` (bare, unprojected
///         `Copy`/`Move`) EXACTLY `{_a, _b}` in some order — `is_full`'s `Eq`;
///     (b) VIA THE EXISTING CHECKED-ARITH TUPLE MODELING: a temp `_t` (not
///         `_a`/`_b`/`_0`/a parameter) SOLE-WRITTEN by `_t := CheckedBinaryOp
///         (op, x, y)` with `{x,y}` EXACTLY `{_a, _b}`, and `_0 := Use(Copy/
///         Move _t.0)` — `remaining`'s `Sub`, `double_len`'s `Add` (the SAME
///         tuple/`.0`-field shape [`resolve_checked_field_rvalue`] already
///         models for a param/const operand, generalized here to BOTH
///         operands being call-result temps).
///     `op` resolves via [`sem_binop_of_mir`] (arithmetic) or
///     [`sem_cmpop_of_mir`] (comparison). NEITHER operand consuming a call
///     result, or only ONE doing so (that is [`sem_call_then_pureop_of_mir`]'s
///     shape, not this one), declines.
pub(crate) fn sem_call_op_call_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallOpCall> {
    use trust_types::{BlockId, Operand, Projection, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let local_is_int_or_bool = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Int { .. }) | Some(Ty::Bool))
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY TWO Call terminators; every other terminator is Goto/Return/
    // Assert (widened from the single-call recognizers' Goto/Return: the
    // checked-arith tuple sub-shape's overflow guard is an Assert).
    let mut call_count = 0usize;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call { .. } => call_count += 1,
            Terminator::Goto(_) | Terminator::Return | Terminator::Assert { .. } => {}
            _ => return None,
        }
    }
    if call_count != 2 {
        return None;
    }

    // The UNIQUE Return block.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }

    // Walk the (necessarily linear) control flow from the entry block to the
    // Return block, collecting the two Calls in PROGRAM ORDER. Fail-closed on
    // a cycle, a walk that does not reach the Return block, or one that does
    // not encounter EXACTLY the two calls the count above found.
    let mut cur = BlockId(0);
    let mut walked: Vec<(BlockId, &String, &Vec<Operand>, &trust_types::Place)> = Vec::new();
    let mut steps = 0usize;
    loop {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Return => break,
            Terminator::Goto(g) => cur = *g,
            Terminator::Assert { target, .. } => cur = *target,
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if *is_foreign || atomic.is_some() || *is_unsafe_sig {
                    return None;
                }
                walked.push((blk.id, callee, args, dest));
                cur = (*target)?;
            }
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear spine.
        }
    }
    if walked.len() != 2 {
        return None; // not exactly two calls ON the entry-to-return path.
    }
    let (call_block1, callee1, args1, dest1) = walked[0];
    let (call_block2, callee2, args2, dest2) = walked[1];

    // Both dests: bare, non-`_0`, non-parameter, int/bool-typed, and DISTINCT.
    if !dest1.projections.is_empty() || !dest2.projections.is_empty() {
        return None;
    }
    let (t1, t2) = (dest1.local, dest2.local);
    if t1 == t2 {
        return None;
    }
    for t in [t1, t2] {
        if t == 0 || param_index(t).is_some() || !local_is_int_or_bool(t) {
            return None;
        }
    }

    // Resolve both callees in the certified registry (self-recursion declines
    // for either; the SAME callee twice — `double_len` — is fine).
    let (resolved1, fact1, callee_id1) = resolve_certified_callee(callees, callee1)?;
    let (resolved2, fact2, callee_id2) = resolve_certified_callee(callees, callee2)?;
    if resolved1 == func.def_path
        || *callee1 == func.def_path
        || resolved2 == func.def_path
        || *callee2 == func.def_path
    {
        return None; // self-recursion fails closed.
    }
    if fact1.arg_count != args1.len() || fact2.arg_count != args2.len() {
        return None;
    }
    if args1.is_empty() || args2.is_empty() {
        return None;
    }
    let mut sem_args1 = Vec::with_capacity(args1.len());
    for a in args1.iter() {
        sem_args1.push(sem_call_arg_operand(body, a, call_block1, &param_index)?);
    }
    let mut sem_args2 = Vec::with_capacity(args2.len());
    for a in args2.iter() {
        sem_args2.push(sem_call_arg_operand(body, a, call_block2, &param_index)?);
    }

    // Complete rooted-write discipline: each result temp is written only by
    // its own Call, never by an alias/projected effect or the other Call.
    if !call_family_local_writes_exact(body, t1, 0, &[call_block1])
        || !call_family_local_writes_exact(body, t2, 0, &[call_block2])
    {
        return None;
    }

    // `_0`'s SOLE write, either DIRECTLY (a pure `BinaryOp`) or via the
    // EXISTING checked-arith tuple modeling.
    if !call_family_local_writes_exact(body, 0, 1, &[]) {
        return None;
    }
    let (rv0_statement, rv0) =
        ret_block.stmts.iter().enumerate().rev().find_map(|(statement, s)| {
            crate::assignment_types::assigned_local_rvalue(body, s, 0)
                .map(|rvalue| (statement, rvalue))
        })?;

    let is_temp = |o: &Operand, t: usize| -> bool {
        matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == t && p.projections.is_empty())
    };
    // Given the op's two raw operands, determine whether `t1` is the LHS
    // (`Some(true)`) or `t2` is (`Some(false)`) — `None` unless the pair is
    // EXACTLY `{t1, t2}` (each consumed exactly once; neither/only-one being a
    // call result belongs to a DIFFERENT shape and declines here).
    let match_operands = |x: &Operand, y: &Operand| -> Option<bool> {
        match (is_temp(x, t1), is_temp(x, t2), is_temp(y, t1), is_temp(y, t2)) {
            (true, false, false, true) => Some(true), // x=t1: t1 is LHS.
            (false, true, true, false) => Some(false), // x=t2: t2 is LHS.
            _ => None,
        }
    };

    let (op, t1_is_lhs) = match rv0 {
        // (a) DIRECT: `_0 := BinaryOp(op, x, y)`.
        Rvalue::BinaryOp(op, x, y) => (op, match_operands(x, y)?),
        // (b) VIA THE TUPLE: `_0 := Use(Copy/Move _t.0)`, `_t := CheckedBinaryOp(op,x,y)`.
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [Projection::Field(0)])
                && p.local != t1
                && p.local != t2
                && p.local != 0
                && param_index(p.local).is_none() =>
        {
            if !call_family_local_writes_exact(body, p.local, 1, &[]) {
                return None; // `_t` not sole-written — fail closed.
            }
            let checked = unique_local_definition_dominating(
                body,
                p.local,
                ret_block.id,
                Some(rv0_statement),
            )?
            .2;
            let Rvalue::CheckedBinaryOp(op, x, y) = checked else { return None };
            (op, match_operands(x, y)?)
        }
        _ => return None, // an unmodeled `_0` write — fail closed.
    };

    let call_then_op = if let Some(bin) = sem_binop_of_mir(op) {
        CallThenOp::Bin(bin)
    } else if let Some(cmp) = sem_cmpop_of_mir(op) {
        CallThenOp::Cmp(cmp)
    } else {
        return None; // an unmodeled binop (shift/bitwise/…) — fail closed.
    };

    let call1 =
        SemCallReturn { callee: resolved1.to_string(), callee_id: callee_id1, args: sem_args1 };
    let call2 =
        SemCallReturn { callee: resolved2.to_string(), callee_id: callee_id2, args: sem_args2 };
    let (call_a, call_b) = if t1_is_lhs { (call1, call2) } else { (call2, call1) };

    Some(SemCallOpCall { call_a, call_b, op: call_then_op })
}

/// Recognize the CALL-OR-CALL shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere;
///   * EXACTLY ONE `Call` terminator reachable from the entry block along a
///     Goto-only happy path (mirrors `sem_call_then_pureop_of_mir`'s
///     ENTRY-REACHABILITY chase) — `callee_a` — whose dest `_a` is a BARE,
///     non-`_0`, non-parameter, **`Ty::Bool`** local, sole-written by the call;
///   * `callee_a`'s call target is (after a Goto-only chase) a `SwitchInt` whose
///     discriminant is a bare `Copy`/`Move` of `_a` (unprojected) and whose
///     shape is EXACTLY the canonical bool-switch `targets = [(0, false_bb)]`,
///     `otherwise = true_bb` (any other tag/arity — a non-Bool switch, a
///     multi-way switch — declines: not this shape);
///   * `true_bb` is a block whose STATEMENTS are EXACTLY one `_0 := Use(Constant
///     (Bool(true)))` (the short-circuit-to-`true` arm), reaching the unique
///     `Return` block via a Goto-only chase (or `true_bb` IS that block already,
///     terminated `Return` directly);
///   * `false_bb` is a block with NO statements whose SOLE terminator is a
///     SECOND `Call` — `callee_b` — writing `_0` DIRECTLY (bare, unprojected;
///     never a temp — the direct-write shape mirrors
///     [`sem_call_return_of_mir`]'s own `_0`-dest convention), reaching the
///     SAME unique `Return` block via a Goto-only chase;
///   * both callees resolve in the certified registry (exact / unique
///     `::`-suffix, never self-recursive — the SAME callee twice is fine,
///     mirroring [`sem_call_op_call_of_mir`]'s "double_len" precedent), the
///     arity matches, and EVERY actual argument is a modeled scalar operand.
///
/// `_0`'s type must ALSO be `Ty::Bool` (an `||` composes two Bool values; a
/// non-Bool `_0` is a different, unmodeled shape — the flat BITWISE/BOOL-
/// CONNECTIVE `BitOr` fragment declines here too since this scan requires a
/// GENUINE `SwitchInt`, never a flat `BinaryOp`).
pub(crate) fn sem_call_or_call_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallOrCall> {
    use trust_types::{ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // Any `Unsupported` statement anywhere ⇒ unmodeled semantics ⇒ fail closed.
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // `_0` must be Bool-typed (an `||` composes two Bool values).
    if !matches!(body.locals.first().map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }

    // ENTRY-REACHABILITY: walk Goto-only from the entry block to the FIRST Call —
    // `callee_a`. Byte-identical chase to `sem_call_then_pureop_of_mir`'s own.
    let (call_a_block_id, callee_a_str, args_a, dest_a, target_a, atomic_a, foreign_a, unsafe_a) = {
        let mut cur = trust_types::BlockId(0);
        let mut steps = 0usize;
        loop {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                Terminator::Call {
                    func: callee,
                    args,
                    dest,
                    target,
                    atomic,
                    is_foreign,
                    is_unsafe_sig,
                    ..
                } => {
                    break (
                        blk.id,
                        callee,
                        args,
                        dest,
                        (*target)?,
                        atomic,
                        *is_foreign,
                        *is_unsafe_sig,
                    );
                }
                _ => return None, // the entry path diverges before any call.
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None; // cycle before the call.
            }
        }
    };
    if foreign_a || atomic_a.is_some() || unsafe_a {
        return None;
    }
    if !dest_a.projections.is_empty() {
        return None;
    }
    let a_local = dest_a.local;
    if a_local == 0 || param_index(a_local).is_some() {
        return None;
    }
    if !matches!(body.locals.get(a_local).map(|l| &l.ty), Some(Ty::Bool)) {
        return None; // the switch discriminant must be a GENUINE Bool call result.
    }
    if !call_family_local_writes_exact(body, a_local, 0, &[call_a_block_id]) {
        return None; // `_a` written by anything other than the call — fail closed.
    }

    // The call's target must (Goto-only) reach EXACTLY the canonical bool-SwitchInt
    // on `_a`: `targets = [(0, false_bb)]`, `otherwise = true_bb`.
    let (switch_block_id, false_bb, true_bb) = {
        let mut cur = target_a;
        let mut steps = 0usize;
        loop {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) if blk.stmts.is_empty() => cur = *g,
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
                    if dp.local != a_local || !dp.projections.is_empty() {
                        return None; // switching on something other than `_a`.
                    }
                    let [(zero_val, false_target)] = targets.as_slice() else {
                        return None; // not the canonical 2-way bool switch.
                    };
                    if *zero_val != 0 {
                        return None;
                    }
                    break (blk.id, *false_target, *otherwise);
                }
                _ => return None,
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None;
            }
        }
    };
    let _ = switch_block_id;

    // The UNIQUE Return block.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    // Chase a Goto-only (empty-statement) spine from `from` to the Return block.
    let reaches_return = |from: trust_types::BlockId| -> bool {
        let mut cur = from;
        let mut steps = 0usize;
        loop {
            if cur == ret_block.id {
                return true;
            }
            let Some(blk) = body.blocks.iter().find(|b| b.id == cur) else { return false };
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                _ => return false,
            }
            steps += 1;
            if steps > body.blocks.len() {
                return false;
            }
        }
    };

    // TRUE arm: EXACTLY one statement `_0 := Use(Constant(Bool(true)))`, then a
    // Goto-only spine to the Return block (or the block itself terminates Return
    // — `reaches_return` handles both via the `cur == ret_block.id` base case
    // after zero Gotos).
    {
        let blk = body.blocks.iter().find(|b| b.id == true_bb)?;
        let [Statement::Assign { place, rvalue, .. }] = blk.stmts.as_slice() else { return None };
        if place.local != 0 || !place.projections.is_empty() {
            return None;
        }
        if !matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))) {
            return None; // the short-circuit arm must set EXACTLY `true` — never a
            // computed/other value (that would be a different, unmodeled shape).
        }
        match &blk.terminator {
            Terminator::Return => {}
            Terminator::Goto(g) if !reaches_return(*g) => return None,
            Terminator::Goto(_) => {}
            _ => return None,
        }
    }

    // FALSE arm: NO statements; its SOLE terminator is `callee_b`'s Call, writing
    // `_0` DIRECTLY (bare, unprojected — never a temp), reaching Return.
    let (callee_b_str, args_b, target_b, atomic_b, foreign_b, unsafe_b) = {
        let blk = body.blocks.iter().find(|b| b.id == false_bb)?;
        if !blk.stmts.is_empty() {
            return None; // any statement here is outside this shape — fail closed.
        }
        let Terminator::Call {
            func: callee,
            args,
            dest,
            target,
            atomic,
            is_foreign,
            is_unsafe_sig,
            ..
        } = &blk.terminator
        else {
            return None; // the false arm must be EXACTLY a call — not a compare, not
            // a field read, not anything else (the strict "two calls" scope; a
            // compare-embedded arm is `should_descend`'s OWN shape, out of reach
            // of this recognizer by design — see the module doc's honesty note).
        };
        if dest.local != 0 || !dest.projections.is_empty() {
            return None; // must write `_0` DIRECTLY — never a temp.
        }
        (callee, args, (*target)?, atomic, *is_foreign, *is_unsafe_sig)
    };
    if foreign_b || atomic_b.is_some() || unsafe_b {
        return None;
    }
    // `_0` is written once by the true-arm assignment and once by this exact
    // false-arm Call destination, with no projected/aliasing/drop side effects.
    if !call_family_local_writes_exact(body, 0, 1, &[false_bb]) {
        return None;
    }
    if !reaches_return(target_b) {
        return None;
    }

    // Resolve both callees in the certified registry (self-recursion declines for
    // either; the SAME callee twice is fine).
    let (resolved_a, fact_a, callee_id_a) = resolve_certified_callee(callees, callee_a_str)?;
    let (resolved_b, fact_b, callee_id_b) = resolve_certified_callee(callees, callee_b_str)?;
    if resolved_a == func.def_path
        || *callee_a_str == func.def_path
        || resolved_b == func.def_path
        || *callee_b_str == func.def_path
    {
        return None; // self-recursion fails closed.
    }
    if fact_a.arg_count != args_a.len() || fact_b.arg_count != args_b.len() {
        return None;
    }
    if args_a.is_empty() || args_b.is_empty() {
        return None;
    }
    let mut sem_args_a = Vec::with_capacity(args_a.len());
    for a in args_a {
        sem_args_a.push(sem_call_arg_operand(body, a, call_a_block_id, &param_index)?);
    }
    let mut sem_args_b = Vec::with_capacity(args_b.len());
    for a in args_b {
        sem_args_b.push(sem_call_arg_operand(body, a, false_bb, &param_index)?);
    }

    Some(SemCallOrCall {
        call_a: SemCallReturn {
            callee: resolved_a.to_string(),
            callee_id: callee_id_a,
            args: sem_args_a,
        },
        call_b: SemCallReturn {
            callee: resolved_b.to_string(),
            callee_id: callee_id_b,
            args: sem_args_b,
        },
    })
}

/// Recognize the CALL-OR-GUARDED-COMPARE shape (fail-closed on everything else,
/// `None`):
///   * no `Unsupported` statement anywhere; `_0` is `Ty::Bool`;
///   * EXACTLY the SAME `callee_a` / canonical-bool-`SwitchInt` / true-arm
///     (`_0 := true`) recognition [`sem_call_or_call_of_mir`] performs
///     (byte-identical chase);
///   * the FALSE arm is a small guarded sub-computation across (up to) two
///     blocks: the switch's false-target block has EXACTLY one statement — a
///     FIELD READ into a fresh, non-parameter, sole-written temp `_f`
///     ([`sem_field_read_operand`]) — and its SOLE terminator is a SECOND
///     `Call` (`callee_b`), writing a FRESH, sole-written, non-`_0`,
///     non-parameter temp `_c` (never `_0` directly — that bare shape belongs
///     to [`sem_call_or_call_of_mir`]); its target block has EXACTLY one
///     statement — `_0 := BinaryOp(cmp, x, y)` with `{x, y} = {Copy/Move(_f),
///     Copy/Move(_c)}` in either order — reaching the SAME unique `Return`
///     block via a Goto-only chase;
///   * `_0` is written EXACTLY TWICE total (the true arm's `_0 := true` and the
///     compare block's `_0 := cmp(..)`) — a THIRD write anywhere fails closed;
///   * both callees resolve in the certified registry (exact / unique
///     `::`-suffix, never self-recursive — the SAME callee twice is fine), the
///     arity matches, and EVERY actual argument is a modeled scalar operand.
pub(crate) fn sem_call_or_guarded_compare_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallOrGuardedCompare> {
    use trust_types::{ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }
    if !matches!(body.locals.first().map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }

    // ENTRY-REACHABILITY to `callee_a` — byte-identical chase to
    // `sem_call_or_call_of_mir`'s own.
    let (call_a_block_id, callee_a_str, args_a, dest_a, target_a, atomic_a, foreign_a, unsafe_a) = {
        let mut cur = trust_types::BlockId(0);
        let mut steps = 0usize;
        loop {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                Terminator::Call {
                    func: callee,
                    args,
                    dest,
                    target,
                    atomic,
                    is_foreign,
                    is_unsafe_sig,
                    ..
                } => {
                    break (
                        blk.id,
                        callee,
                        args,
                        dest,
                        (*target)?,
                        atomic,
                        *is_foreign,
                        *is_unsafe_sig,
                    );
                }
                _ => return None,
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None;
            }
        }
    };
    if foreign_a || atomic_a.is_some() || unsafe_a {
        return None;
    }
    if !dest_a.projections.is_empty() {
        return None;
    }
    let a_local = dest_a.local;
    if a_local == 0 || param_index(a_local).is_some() {
        return None;
    }
    if !matches!(body.locals.get(a_local).map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }
    if !call_family_local_writes_exact(body, a_local, 0, &[call_a_block_id]) {
        return None;
    }

    // The canonical bool-SwitchInt on `_a`: `targets = [(0, false_bb)]`,
    // `otherwise = true_bb`.
    let (false_bb, true_bb) = {
        let mut cur = target_a;
        let mut steps = 0usize;
        loop {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) if blk.stmts.is_empty() => cur = *g,
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
                    if dp.local != a_local || !dp.projections.is_empty() {
                        return None;
                    }
                    let [(zero_val, false_target)] = targets.as_slice() else { return None };
                    if *zero_val != 0 {
                        return None;
                    }
                    break (*false_target, *otherwise);
                }
                _ => return None,
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None;
            }
        }
    };

    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    let reaches_return = |from: trust_types::BlockId| -> bool {
        let mut cur = from;
        let mut steps = 0usize;
        loop {
            if cur == ret_block.id {
                return true;
            }
            let Some(blk) = body.blocks.iter().find(|b| b.id == cur) else { return false };
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                _ => return false,
            }
            steps += 1;
            if steps > body.blocks.len() {
                return false;
            }
        }
    };

    // TRUE arm — byte-identical to `sem_call_or_call_of_mir`'s own.
    {
        let blk = body.blocks.iter().find(|b| b.id == true_bb)?;
        let [Statement::Assign { place, rvalue, .. }] = blk.stmts.as_slice() else { return None };
        if place.local != 0 || !place.projections.is_empty() {
            return None;
        }
        if !matches!(rvalue, Rvalue::Use(Operand::Constant(ConstValue::Bool(true)))) {
            return None;
        }
        match &blk.terminator {
            Terminator::Return => {}
            Terminator::Goto(g) if !reaches_return(*g) => return None,
            Terminator::Goto(_) => {}
            _ => return None,
        }
    }

    // FALSE ARM — the RICHER shape: EXACTLY one statement (a field read into a
    // fresh temp `_f`), sole terminator a SECOND Call (`callee_b`) writing a
    // FRESH bare temp `_c` (never `_0`/`_f`).
    let false_blk = body.blocks.iter().find(|b| b.id == false_bb)?;
    let [Statement::Assign { place: f_place, rvalue: f_rvalue, .. }] = false_blk.stmts.as_slice()
    else {
        return None; // not exactly one statement — declines (incl. the bare-call shape).
    };
    if !f_place.projections.is_empty() {
        return None;
    }
    let f_local = f_place.local;
    if f_local == 0 || param_index(f_local).is_some() {
        return None;
    }
    let Rvalue::Use(field_op) = f_rvalue else { return None };
    let field = sem_field_read_operand(body, field_op, &param_index)?;
    if !call_family_local_writes_exact(body, f_local, 1, &[]) {
        return None; // sole-writer — the field-read statement itself.
    }

    let (callee_b_str, args_b, c_local, target_b, atomic_b, foreign_b, unsafe_b) = {
        let Terminator::Call {
            func: callee,
            args,
            dest,
            target,
            atomic,
            is_foreign,
            is_unsafe_sig,
            ..
        } = &false_blk.terminator
        else {
            return None;
        };
        if dest.local == 0 || dest.local == f_local || !dest.projections.is_empty() {
            return None; // must write a FRESH bare temp, never `_0`/`_f`.
        }
        if param_index(dest.local).is_some() {
            return None;
        }
        (callee, args, dest.local, (*target)?, atomic, *is_foreign, *is_unsafe_sig)
    };
    if foreign_b || atomic_b.is_some() || unsafe_b {
        return None;
    }
    if !call_family_local_writes_exact(body, c_local, 0, &[false_bb]) {
        return None; // sole-writer — the call itself.
    }

    // The compare block: EXACTLY one statement `_0 := BinaryOp(cmp, x, y)` with
    // `{x, y} = {Copy/Move(_f), Copy/Move(_c)}`, then a Goto-only spine to Return.
    let cmp_blk = body.blocks.iter().find(|b| b.id == target_b)?;
    let [Statement::Assign { place: cmp_place, rvalue: cmp_rvalue, .. }] = cmp_blk.stmts.as_slice()
    else {
        return None;
    };
    if cmp_place.local != 0 || !cmp_place.projections.is_empty() {
        return None;
    }
    let Rvalue::BinaryOp(op, a, b) = cmp_rvalue else { return None };
    let cmp_op = sem_cmpop_of_mir(op)?;
    let is_f = |o: &Operand| matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == f_local && p.projections.is_empty());
    let is_c = |o: &Operand| matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == c_local && p.projections.is_empty());
    let field_is_lhs = match (is_f(a), is_c(b), is_f(b), is_c(a)) {
        (true, true, _, _) => true,
        (_, _, true, true) => false,
        _ => return None, // the compare doesn't consume EXACTLY {field, callB} — decline.
    };
    match &cmp_blk.terminator {
        Terminator::Return => {}
        Terminator::Goto(g) if !reaches_return(*g) => return None,
        Terminator::Goto(_) => {}
        _ => return None,
    }
    // `_0`'s writes total EXACTLY TWO: the true arm's `_0 := true` and this
    // compare — a THIRD write anywhere (a malformed/adversarial body) fails
    // closed here rather than being silently shadowed.
    if !call_family_local_writes_exact(body, 0, 2, &[]) {
        return None;
    }

    // Resolve both callees in the certified registry.
    let (resolved_a, fact_a, callee_id_a) = resolve_certified_callee(callees, callee_a_str)?;
    let (resolved_b, fact_b, callee_id_b) = resolve_certified_callee(callees, callee_b_str)?;
    if resolved_a == func.def_path
        || *callee_a_str == func.def_path
        || resolved_b == func.def_path
        || *callee_b_str == func.def_path
    {
        return None;
    }
    if fact_a.arg_count != args_a.len() || fact_b.arg_count != args_b.len() {
        return None;
    }
    if args_a.is_empty() || args_b.is_empty() {
        return None;
    }
    let mut sem_args_a = Vec::with_capacity(args_a.len());
    for a in args_a {
        sem_args_a.push(sem_call_arg_operand(body, a, call_a_block_id, &param_index)?);
    }
    let mut sem_args_b = Vec::with_capacity(args_b.len());
    for a in args_b {
        sem_args_b.push(sem_call_arg_operand(body, a, false_bb, &param_index)?);
    }

    Some(SemCallOrGuardedCompare {
        call_a: SemCallReturn {
            callee: resolved_a.to_string(),
            callee_id: callee_id_a,
            args: sem_args_a,
        },
        call_b: SemCallReturn {
            callee: resolved_b.to_string(),
            callee_id: callee_id_b,
            args: sem_args_b,
        },
        field,
        cmp_op,
        field_is_lhs,
    })
}

/// Trust: CALL-RESULT-AWARE COMPOSITION — resolve operand `op` to a
/// [`ChainOperand`]: the EXISTING flat leaf ([`resolve_cast_source_operand`])
/// FIRST (BYTE-IDENTICAL — every operand that already resolves keeps
/// resolving exactly as before, wrapped in [`ChainOperand::Base`]); when that
/// declines, either `op` names the call-destination local `call_dest_local`
/// itself (the LEAF, [`ChainOperand::Call`]), or a single-static-assignment
/// non-parameter temp whose SOLE assignment is a bool-source identity `Cast`
/// (see [`ChainOperand::BoolCast`]'s doc), recursed into ONE hop deeper.
///
/// Fail-closed for: a chain deeper than [`CHAIN_OPERAND_MAX_DEPTH`] (the
/// cycle/stack-overflow defense, mirroring [`resolve_cmp_side`]/[`resolve_
/// bitwise_side`]); a multiply-assigned/aliased/call-dest-written intermediate
/// temp (the SAME [`crate::prove::local_soundly_resolvable`] uniqueness gate
/// every other temp-chase in this file applies); a `Cast` whose source is NOT
/// `Ty::Bool` or whose destination is not `Ty::Int` (a genuine int-width cast
/// — named residue); or a `Cast` chain that does NOT eventually reach the call
/// leaf (a plain bool-typed LOCAL cast, unrelated to any call, is not
/// mis-claimed as call-derived).
pub(super) fn resolve_chain_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    call_dest_local: usize,
    call_block: trust_types::BlockId,
    use_block: trust_types::BlockId,
    use_statement: Option<usize>,
    depth: usize,
) -> Option<ChainOperand> {
    use trust_types::{Operand, Rvalue, Ty};
    if let Some(direct) =
        resolve_cast_source_operand(body, op, param_index, Some((use_block, use_statement)))
    {
        return Some(ChainOperand::Base(direct));
    }
    if depth >= CHAIN_OPERAND_MAX_DEPTH {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    // Leaf: `op` IS the call-destination local itself.
    if p.local == call_dest_local {
        // A Call destination becomes available only on its outgoing edge. A
        // same-block statement is necessarily before the terminator, and a
        // non-dominated block can observe no value from this Call.
        if call_block == use_block || !block_dominates(body, call_block, use_block) {
            return None;
        }
        return Some(ChainOperand::Call);
    }
    // Otherwise: a `Cast` temp — the ONLY admitted intermediate hop, and ONLY
    // the bool-source identity case (see this fn's doc).
    let (definition_block, definition_statement, rvalue) =
        unique_local_definition_dominating(body, p.local, use_block, use_statement)?;
    let Rvalue::Cast(src, dest_ty) = rvalue else { return None };
    if !matches!(dest_ty, Ty::Int { .. }) {
        return None; // a non-integer cast destination — outside this fragment.
    }
    let (Operand::Copy(sp) | Operand::Move(sp)) = src else { return None };
    if !sp.projections.is_empty() {
        return None;
    }
    if !matches!(body.locals.get(sp.local).map(|l| &l.ty), Some(Ty::Bool)) {
        return None; // only the bool -> int IDENTITY cast is admitted here.
    }
    let inner = resolve_chain_operand(
        body,
        src,
        param_index,
        call_dest_local,
        call_block,
        definition_block,
        Some(definition_statement),
        depth + 1,
    )?;
    if !inner.involves_call() {
        return None; // a plain bool-typed local cast unrelated to any call.
    }
    Some(ChainOperand::BoolCast(Box::new(inner)))
}

/// Trust: CALL-RESULT-AWARE COMPOSITION — recognize `op` as the checked-arith
/// TUPLE VALUE-FIELD projection `_3 := Use(Move(_6.0))` where `_6 := Checked
/// BinaryOp(op, a, b)` and EXACTLY ONE of `a`/`b` is a [`ChainOperand`] that
/// genuinely reaches the call-destination leaf (`call_dest_local`) — the
/// checked-Mul hop of the 4-hop chain. Mirrors [`resolve_checked_field_
/// rvalue`]'s tuple/`.0`-field shape and [`sem_call_op_call_of_mir`]'s inline
/// `_t.0`-projection arm, generalized: the tuple's OTHER operand here is a
/// FLAT CONSTANT (the `flag * 32` shape), not a second call result (that is
/// `sem_call_op_call_of_mir`'s own territory).
///
/// Returns `(op, chain_side, const_multiplier, chain_is_lhs)` on success.
/// Fail-closed for: a multiply-assigned/aliased `_3`/`_6` (the SAME
/// `local_soundly_resolvable` gate); a projection other than `.0`; a `_6`
/// that is not `CheckedBinaryOp`; NEITHER or BOTH of `a`/`b` reaching the call
/// leaf; or the non-chain side not resolving to a bare constant.
pub(super) fn resolve_chain_checked_mul_operand(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    call_dest_local: usize,
    call_block: trust_types::BlockId,
    use_block: trust_types::BlockId,
    use_statement: Option<usize>,
) -> Option<(SemBinOp, ChainOperand, i128, bool)> {
    use trust_types::{Operand, Projection, Rvalue};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    if !p.projections.is_empty() || param_index(p.local).is_some() {
        return None;
    }
    let (value_block, value_statement, rv) =
        unique_local_definition_dominating(body, p.local, use_block, use_statement)?;
    let Rvalue::Use(Operand::Copy(tp) | Operand::Move(tp)) = rv else { return None };
    let [Projection::Field(0)] = tp.projections.as_slice() else { return None };
    if param_index(tp.local).is_some() {
        return None;
    }
    let (tuple_block, tuple_statement, trv) =
        unique_local_definition_dominating(body, tp.local, value_block, Some(value_statement))?;
    let Rvalue::CheckedBinaryOp(mir_op, a, b) = trv else { return None };
    let bin = sem_binop_of_mir(mir_op)?;
    let chain_a = resolve_chain_operand(
        body,
        a,
        param_index,
        call_dest_local,
        call_block,
        tuple_block,
        Some(tuple_statement),
        0,
    );
    let chain_b = resolve_chain_operand(
        body,
        b,
        param_index,
        call_dest_local,
        call_block,
        tuple_block,
        Some(tuple_statement),
        0,
    );
    match (chain_a, chain_b) {
        (Some(ca), Some(ChainOperand::Base(SemOperand::Const(k)))) if ca.involves_call() => {
            Some((bin, ca, k, true))
        }
        (Some(ChainOperand::Base(SemOperand::Const(k))), Some(cb)) if cb.involves_call() => {
            Some((bin, cb, k, false))
        }
        _ => None,
    }
}

/// Recognize the CALL-RESULT-AWARE COMPOSITION shape — see the module doc
/// above for the exact 4-hop chain and why the three landed call recognizers
/// (`sem_call_return_of_mir`/`sem_call_then_pureop_of_mir`/`sem_call_op_call_
/// of_mir`) all decline on it. Mirrors [`sem_call_then_pureop_of_mir`]
/// clause-for-clause where it overlaps (single-call gate, entry-reachability,
/// sole-writer discipline, linear Goto/Assert-only return spine).
///
/// The admitted shape (fail-closed on everything else, `None`):
///   * no `Unsupported` statement anywhere; every terminator is Call/Goto/
///     Return/Assert (the checked-arith overflow guard — its `cond`/`msg` are
///     not inspected, the SAME discipline [`sem_call_op_call_of_mir`]/
///     [`resolve_checked_field_rvalue`] already apply: the overflow safety
///     obligation is a SEPARATE, separately-discharged axis); EXACTLY ONE
///     `Call` terminator, REACHABLE from the entry block.
///   * the call's destination `_t` is a BARE, non-parameter, non-`_0` temp of
///     `Ty::Bool` type (the ONLY cast this increment models is the bool-to-int
///     IDENTITY — see [`resolve_chain_operand`]'s doc), SOLE-WRITTEN by the
///     call.
///   * the callee resolves in the certified registry (exact / unique
///     `::`-suffix, never self-recursive), the arity matches, and EVERY
///     actual argument is a modeled scalar operand.
///   * `_0` is written EXACTLY ONCE, by a genuine-`Int` `BinaryOp(op, a, b)`
///     with `op` ∈ {`BitOr`, `BitXor`} (the bool-connective shape is ruled
///     out by [`mir_operand_is_bool_typed`], the SAME precedence
///     [`sem_rvalue_of_mir_at_depth`] applies), where EXACTLY ONE of `a`/`b`
///     resolves via [`resolve_chain_checked_mul_operand`] (genuinely reaching
///     the call leaf) and the OTHER resolves via [`resolve_cast_source_
///     operand`] (the existing flat leaf).
pub(crate) fn sem_call_chain_pureop_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemCallChainPureOp> {
    use trust_types::{Rvalue, Statement, Terminator, Ty};
    if callees.is_empty() {
        return None; // no certified callee ⇒ the shape can never be admitted.
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // EXACTLY ONE Call terminator; every other terminator must be Goto/Return/Assert.
    let mut call = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call {
                func: callee,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } => {
                if call.is_some() {
                    return None; // a second call — not the sole-call shape.
                }
                call = Some((
                    block.id,
                    callee,
                    args,
                    dest,
                    *target,
                    atomic,
                    *is_foreign,
                    *is_unsafe_sig,
                ));
            }
            Terminator::Goto(_) | Terminator::Return | Terminator::Assert { .. } => {}
            _ => return None,
        }
    }
    let (call_block_id, callee_str, args, dest, target, atomic, is_foreign, is_unsafe_sig) = call?;
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return None;
    }
    let target = target?;

    // Trust: ENTRY-REACHABILITY — mirrors `sem_call_then_pureop_of_mir`'s own walk.
    {
        let mut cur = trust_types::BlockId(0);
        let mut steps = 0usize;
        while cur != call_block_id {
            let blk = body.blocks.iter().find(|b| b.id == cur)?;
            match &blk.terminator {
                Terminator::Goto(g) => cur = *g,
                _ => return None, // the entry path diverges before reaching the call.
            }
            steps += 1;
            if steps > body.blocks.len() {
                return None; // cycle before the call — unreachable happy path.
            }
        }
    }

    if !dest.projections.is_empty() {
        return None;
    }
    let t = dest.local;
    if t == 0 || param_index(t).is_some() {
        return None;
    }
    // Trust: CALL-RESULT-AWARE COMPOSITION SCOPE — the call's destination must
    // be `Ty::Bool` (the ONLY cast this increment models is the bool-to-int
    // IDENTITY — see `resolve_chain_operand`'s doc; a genuine int-returning
    // call flowing through a real (narrowing/widening) cast is a named
    // residue, out of scope this increment).
    if !matches!(body.locals.get(t).map(|l| &l.ty), Some(Ty::Bool)) {
        return None;
    }

    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    if resolved == func.def_path || *callee_str == func.def_path {
        return None; // self-recursion fails closed.
    }
    if fact.arg_count != args.len() {
        return None;
    }
    if args.is_empty() {
        return None;
    }
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_call_arg_operand(body, a, call_block_id, &param_index)?);
    }

    if !call_family_local_writes_exact(body, t, 0, &[call_block_id]) {
        return None; // a multiply-written temp — not sole-writer, fail closed.
    }

    // The UNIQUE Return block, reached from the call's target through
    // Goto/Assert hops only (the overflow-check Assert sits between the call
    // and the return in the real shape).
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block = rets.next()?;
    if rets.next().is_some() {
        return None;
    }
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        match &blk.terminator {
            Terminator::Goto(g) => cur = *g,
            Terminator::Assert { target: at, .. } => cur = *at,
            _ => return None,
        }
        steps += 1;
        if steps > body.blocks.len() {
            return None; // cycle — not a linear return spine.
        }
    }

    if !call_family_local_writes_exact(body, 0, 1, &[]) {
        return None;
    }
    let (return_statement, rv) =
        ret_block.stmts.iter().enumerate().rev().find_map(|(statement, s)| {
            crate::assignment_types::assigned_local_rvalue(body, s, 0)
                .map(|rvalue| (statement, rvalue))
        })?;
    let Rvalue::BinaryOp(mir_op, a, b) = rv else {
        return None; // a CheckedBinaryOp/Call/… direct `_0` write — not this shape.
    };
    let outer_op = sem_binop_of_mir(mir_op)?;
    if !matches!(outer_op, SemBinOp::BitOr | SemBinOp::BitXor) {
        return None; // scope: the real shapes are BitOr/BitXor; other ops are a residue.
    }
    if mir_operand_is_bool_typed(body, a) && mir_operand_is_bool_typed(body, b) {
        return None; // the Bool-connective shape — a different fragment entirely.
    }

    let chain_a = resolve_chain_checked_mul_operand(
        body,
        a,
        &param_index,
        t,
        call_block_id,
        ret_block.id,
        Some(return_statement),
    );
    let chain_b = resolve_chain_checked_mul_operand(
        body,
        b,
        &param_index,
        t,
        call_block_id,
        ret_block.id,
        Some(return_statement),
    );
    let (inner_op, inner_const, inner_call_is_lhs, other_side, outer_mul_is_lhs) =
        match (chain_a, chain_b) {
            (Some((op, _, k, lhs)), None) => (op, k, lhs, b, true),
            (None, Some((op, _, k, lhs))) => (op, k, lhs, a, false),
            _ => return None, // neither (or both/ambiguous) sides chain — decline.
        };
    let other = resolve_cast_source_operand(
        body,
        other_side,
        &param_index,
        Some((ret_block.id, Some(return_statement))),
    )?;

    Some(SemCallChainPureOp {
        call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args },
        inner_op,
        inner_const,
        inner_call_is_lhs,
        outer_op,
        other,
        outer_mul_is_lhs,
    })
}
