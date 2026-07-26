// Interval analysis over floating-point values, including NaN and infinity
// modes, aggregate and enum-payload elements, and ranges imported from a
// callee's contract. Float intervals must round outward at every step or the
// analysis would claim a tighter bound than the hardware guarantees.

use super::*;

/// True iff `dest` (a float-arithmetic result local) is used EXACTLY ONCE across
/// the whole function, and that use is a float→int `as` cast (`Rvalue::Cast(dest,
/// Ty::Int)`). In that case the float overflow is BENIGN: the cast saturates
/// (`inf as INT` is defined, non-trapping), so the `±inf` can never reach a trap —
/// the only observable result is the saturated integer, which carries its own
/// bounds/cast obligations. A float result used ANY other way (as a float operand,
/// a return value, …) does NOT qualify, so the round-9 numerical overflow
/// obligation is still emitted there.
pub(super) fn v2_float_result_only_feeds_int_cast(func: &VerifiableFunction, dest: usize) -> bool {
    fn is_dest(op: &Operand, dest: usize) -> bool {
        matches!(op, Operand::Copy(p) | Operand::Move(p) if p.local == dest)
    }
    let mut uses = 0usize;
    let mut int_cast_uses = 0usize;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            match rvalue {
                // The benign consumer: `dest as INT` (saturating float→int cast).
                Rvalue::Cast(op, Ty::Int { .. }) if is_dest(op, dest) => {
                    uses += 1;
                    int_cast_uses += 1;
                }
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => uses += usize::from(is_dest(op, dest)),
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    uses += usize::from(is_dest(a, dest)) + usize::from(is_dest(b, dest));
                }
                Rvalue::Aggregate(_, ops) => {
                    uses += ops.iter().filter(|op| is_dest(op, dest)).count();
                }
                // A borrow / length / discriminant of the float result is a
                // disqualifying use (it observes the value some other way).
                Rvalue::Ref { place: p, .. }
                | Rvalue::AddressOf(_, p)
                | Rvalue::Discriminant(p)
                | Rvalue::Len(p)
                | Rvalue::CopyForDeref(p) => uses += usize::from(p.local == dest),
                _ => {}
            }
        }
        if let Terminator::Call { args, .. } = &block.terminator {
            uses += args.iter().filter(|op| is_dest(op, dest)).count();
        }
        if let Terminator::SwitchInt { discr, .. } = &block.terminator {
            uses += usize::from(is_dest(discr, dest));
        }
    }
    uses == 1 && int_cast_uses == 1
}

/// A CONSERVATIVE upper bound on the biased exponent (finite values: 0..=2046;
/// 2047 = inf/NaN) of the f64 `operand`'s value, or `None` when no bound can be
/// proved. LEGACY shim: the tracing now lives in [`float_range`] (mode
/// `NanOrBounded`, the exact contract this function always documented: `Some(e)`
/// means the value is PROVABLY (NaN) ∨ (`|value| < 2^(e - 1022)`), never a FRESH
/// ±inf); this wrapper only converts the signed interval into the biased-exp
/// spelling its remaining (test) callers assert on. Interval composition is
/// tighter than the old per-op exponent arithmetic, so `Some` here is always at
/// least as strong as before — and the old UNSOUND last-def-wins def scan is
/// gone (see `float_range`'s multi-def HULL).
#[cfg(test)]
pub(super) fn float_exp_bound(func: &VerifiableFunction, operand: &Operand, fuel: u32) -> Option<u32> {
    let ctx = FloatRangeCtx::new(func, None);
    let (lo, hi) =
        float_range(&ctx, FloatNanMode::NanOrBounded, None, operand, &mut Vec::new(), fuel)?;
    f64_finite_biased_exp(lo.abs().max(hi.abs()))
}

/// Std `f64` methods whose result magnitude is provably `<= 1` for every input
/// (NaN for non-finite input; never `±inf`). CRATE-ORIGIN anchored via
/// [`f64_std_method_name`] — a bare `::cos` suffix match let ANY user function
/// whose path ends in `cos` (a truncated-Taylor `approx::cos`, unbounded for
/// large inputs) inject a false `[-1, 1]` interval that suppressed real
/// overflow obligations (round-13 false-proof; every sibling recognizer —
/// sqrt/clamp/abs — already carries this gate for exactly that reason). The
/// former `::cos_unchecked`/`::sin_unchecked` suffixes are DROPPED: they are
/// not std names at all, so matching them hardcoded trust in arbitrary
/// downstream crates by suffix.
pub(super) fn is_unit_bounded_float_call(callee: &str) -> bool {
    matches!(f64_std_method_name(callee), Some("cos" | "sin" | "tanh"))
}

/// The f64 value of a literal float constant, or `None` for every other constant.
/// A `width: 32` `FloatBits` is deliberately NOT converted: the callers reason at
/// f64 sort, and an f32-typed constant cannot be the operand of an f64 op anyway.
pub(super) fn f64_const_value(c: &ConstValue) -> Option<f64> {
    match c {
        ConstValue::Float(v) => Some(*v),
        ConstValue::FloatBits { bits, width: 64 } => u64::try_from(*bits).ok().map(f64::from_bits),
        _ => None,
    }
}

/// The biased f64 exponent field of a FINITE `v` — `None` for NaN/±inf.
/// Satisfies the `float_exp_bound` contract exactly: for a normal `v` with raw
/// exponent field `r`, `|v| < 2^(r - 1023 + 1) = 2^(r - 1022)`; for a subnormal
/// (`r == 0`), `|v| < 2^-1022 = 2^(0 - 1022)`. So `Some(r)` is always a valid
/// `e` with `|v| < 2^(e - 1022)`. (Test-only since the interval tracer replaced
/// the exponent lane; the legacy `float_exp_bound`/`contract_exp_bound` shims
/// keep asserting through it.)
#[cfg(test)]
pub(super) fn f64_finite_biased_exp(v: f64) -> Option<u32> {
    if !v.is_finite() {
        return None;
    }
    Some(((v.to_bits() >> 52) & 0x7ff) as u32)
}

/// The `::f64::` std-origin method name (`clamp`, `sqrt`, `abs`, `min`, `max`,
/// …) of `callee`, or `None` for anything not anchored in core/std/alloc's f64
/// impl. A user-defined `mymod::sqrt`/`mymod::clamp` has arbitrary semantics
/// and must NEVER match (a false-PROVE channel); `Ord::clamp` spellings never
/// carry a `::f64::` segment and are excluded with it. This is the exact
/// crate-origin gate the old `fp_clamp_call_exp_bound` recognizer used, hoisted
/// so every std-f64 arm of [`float_call_range`] shares it.
pub(super) fn f64_std_method_name(callee: &str) -> Option<&str> {
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    let std_origin = callee.starts_with("core::")
        || callee.starts_with("std::")
        || callee.starts_with("alloc::");
    (std_origin && callee.contains("::f64::")).then_some(method)
}

/// A signed two-sided contract interval `[l, u]` for a PARAMETER-rooted f64
/// operand `place` — a formal parameter itself, or one of its (possibly
/// deref'd) fields / constant-indexed elements — drawn from a `#[requires]`
/// magnitude precondition of THIS function. `None` unless a genuine,
/// entry-stable, two-sided bound is found. This is what lets a leaf numeric
/// method (`Vec3::dot`, `Vec4::scaled`, …) prove its float
/// `FloatOverflowToInfinity` obligations from a contract magnitude precondition
/// on its own inputs (`#[requires(self.0 <= C && self.0 >= -C && …)]`): the
/// physical scan coordinates are tiny, so a generous `|field| <= C` makes every
/// product finite, and the obligation becomes a per-op proof discharged *given*
/// that caller-proved precondition.
///
/// SOUNDNESS. Returns `Some((l, u))` ONLY when ALL hold:
///  1. `place`'s base local is a FORMAL PARAMETER (`1..=arg_count`) — a precondition
///     speaks about ENTRY values, so only a parameter place qualifies.
///  2. That parameter is ENTRY-STABLE: never reassigned or mutably borrowed in the
///     body (any projection). This is the load-bearing guard the versioned SMT
///     lane gets for free but a STRUCTURAL discharge does not: without it a body
///     `self.x = 1e300; self.x * self.x` would be wrongly discharged from the
///     entry bound. (`param_place_is_entry_stable`.)
///  3. `func.preconditions` — the extraction-GATED set — contains BOTH an upper
///     (`name <= U`) and a lower (`name >= L`) literal bound on the operand's
///     canonical name (via `place_to_var_name` + the F4 index canonicalization),
///     either directly or element-wise under the uniform-index rule. A one-sided
///     bound leaves the opposite side free and yields `None`.
///
/// A TRUE precondition `L <= v <= U` additionally implies `v` is ORDERED (an
/// IEEE comparison involving NaN is false), so the returned interval carries
/// the strict `FloatNanMode::Forbid` reading: finite, in `[l, u]`, never NaN.
///
/// KEYING OFF THE GATED SET (`func.preconditions`, not the raw contract text) is
/// the soundness pairing: a bound is visible to this discharge IFF the assumption
/// survived `contract_assumption_gate`, IFF every caller carries the matching
/// `VcKind::Precondition` PROVE obligation for it (see the `[ASSERT_REFUTE]`
/// contract-consumption note and `generate_callsite_precondition_vcs`). Reading a
/// bound the gate had CLEARED would suppress a VC with no corresponding caller
/// obligation — an unsound free assumption. `place_to_var_name`'s name-collision
/// demotion additionally means a shadowed/aliased base is spelled `_<local>`, not
/// the source-named precondition var, so a demoted operand can never match a
/// `self.0`-shaped bound (fail-closed).
pub(super) fn contract_range(func: &VerifiableFunction, place: &Place) -> Option<(f64, f64)> {
    // Fast exit for the overwhelming common case (no contract at all): no
    // precondition ⇒ no bound, and we skip the entry-stability body scan.
    if func.preconditions.is_empty() {
        return None;
    }
    // (1) base local must be a formal parameter (entry value).
    let base = place.local;
    if base < 1 || base > func.body.arg_count {
        return None;
    }
    // (2) the parameter must retain its entry value at this read. A place that
    // reads THROUGH a raw-pointer deref (`(*p).0` with `p: *mut _`) is NOT
    // entry-stable however unwritten `p` is: two `*mut` params can ALIAS (raw
    // pointers are Copy — an alias needs no borrow statement), so a write
    // through one invalidates the entry fact on the other (round-14 review).
    if !param_place_is_entry_stable(func, base) || place_reads_through_raw_ptr(func, place) {
        return None;
    }
    // (3) find a two-sided bound on this place's CANONICAL contract name. The
    // body-side render of a constant array index (`[k;min=L]`) is rewritten to
    // the contract-side spelling `[k]` first (F4 — the two ends must agree
    // byte-exactly). The bound may be an INTEGER literal
    // (`self.0 <= 1000000000000000000`) or an f64 FLOAT literal
    // (`self.0 <= 1.0e30`, the natural spelling for an f64 field); both are
    // read as finite f64 values.
    let name = canonicalize_contract_index_segments(&crate::place_to_var_name(func, place));
    if let Some(range) = contract_two_sided_range(func, &name) {
        return Some(range);
    }
    // (F4 uniform-index) a RUNTIME-indexed read bounded element-by-element.
    contract_uniform_index_range(func, place, &name)
}

/// LEGACY spelling of [`contract_range`]: the biased-exponent magnitude bound.
/// `l <= v <= u` ⇒ `|v| <= max(|u|, |l|) = C`. Both bounds are finite (the
/// reader rejects non-finite literals), so `C` is finite; `f64_finite_biased_exp`
/// yields `e` with `C < 2^(e-1022)`, hence `|v| <= C < 2^(e-1022)` (sound under
/// the ties-to-even rounding of an integer literal into f64: the biased exponent
/// field only rises when the magnitude does, so `e` still strictly dominates the
/// true bound).
#[cfg(test)]
pub(super) fn contract_exp_bound(func: &VerifiableFunction, place: &Place) -> Option<u32> {
    let (l, u) = contract_range(func, place)?;
    f64_finite_biased_exp(u.abs().max(l.abs()))
}

/// The tightest two-sided contract interval `[l, u]` on the exact variable
/// `name` in this function's GATED preconditions, or `None` when either side is
/// missing, non-finite, or contradictory (`l > u` means the precondition is
/// unsatisfiable — decline rather than mint an empty-interval claim).
pub(super) fn contract_two_sided_range(func: &VerifiableFunction, name: &str) -> Option<(f64, f64)> {
    let mut upper: Option<f64> = None;
    let mut lower: Option<f64> = None;
    for pre in &func.preconditions {
        collect_magnitude_bounds(pre, name, &mut upper, &mut lower);
    }
    let (u, l) = (upper?, lower?);
    (l.is_finite() && u.is_finite() && l <= u).then_some((l, u))
}

/// F4 (vcgen half): canonicalize the BODY-side render of a constant array index
/// to the CONTRACT-side spelling — every `[k;min=L]` segment (both the
/// const-resolved `Projection::Index` render and `ConstantIndex{from_end:false}`,
/// see `constant_array_index_segment`) becomes `[k]`, the spelling the spec
/// parser produces for `arr[k]`. STRING-level and float-lane-LOCAL:
/// `place_to_var_name`'s own render is keyed on by other lanes and must not
/// change. Every other bracket segment (`[_5]` runtime, `[-1;min=4]` from-end,
/// `[0;slice]`, `[2..4]` subslices) is left verbatim — an unrewritten segment
/// simply never matches a contract var (fail-closed).
pub(super) fn canonicalize_contract_index_segments(name: &str) -> String {
    let is_digits = |s: &str| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    let mut out = String::with_capacity(name.len());
    let mut rest = name;
    while let Some(start) = rest.find('[') {
        let Some(end_rel) = rest[start..].find(']') else { break };
        let end = start + end_rel;
        let segment = &rest[start + 1..end];
        out.push_str(&rest[..=start]);
        match segment.split_once(";min=") {
            Some((idx, min)) if is_digits(idx) && is_digits(min) => out.push_str(idx),
            _ => out.push_str(segment),
        }
        out.push(']');
        rest = &rest[end + 1..];
    }
    out.push_str(rest);
    out
}

/// F4 uniform-index rule: for a body place read through ONE runtime index
/// (`arr[_i]`, rendered `[_N]`), if the contract bounds EVERY element
/// (`arr[0]`, …, `arr[L-1]` all two-sided, `L` from the array type at the
/// `Index` position), the read's interval is the HULL over the elements.
/// SOUND: an in-bounds read yields one of those elements' values; an
/// out-of-bounds read PANICS before producing a value (so no value escapes the
/// hull). Multiple DISTINCT runtime index locals fail closed; the SAME local
/// appearing at several positions substitutes consistently (equal runtime
/// values), with `L` the MINIMUM of the array lengths (a read that survives its
/// bounds checks is in-bounds at every position). Slices (no static length) and
/// non-array bases fail closed.
pub(super) fn contract_uniform_index_range(
    func: &VerifiableFunction,
    place: &Place,
    name: &str,
) -> Option<(f64, f64)> {
    // Exactly ONE distinct runtime-index token `[_N]` in the render.
    let mut token: Option<String> = None;
    let mut search = name;
    while let Some(pos) = search.find("[_") {
        let rest = &search[pos + 2..];
        let end = rest.find(']')?;
        let digits = &rest[..end];
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let this = format!("[_{digits}]");
        match &token {
            Some(existing) if *existing != this => return None,
            _ => token = Some(this),
        }
        search = &rest[end + 1..];
    }
    let token = token?;
    let index_local: usize = token[2..token.len() - 1].parse().ok()?;
    // The array length at EVERY `Index(index_local)` projection position of the
    // (pre-canonicalization) place; the minimum bounds the surviving index.
    let mut len: Option<u64> = None;
    for (pos, projection) in place.projections.iter().enumerate() {
        let Projection::Index(i) = projection else { continue };
        if *i != index_local {
            continue;
        }
        let prefix = Place { local: place.local, projections: place.projections[..pos].to_vec() };
        match crate::place_ty_cow(func, &prefix)?.as_ref() {
            Ty::Array { len: l, .. } => len = Some(len.map_or(*l, |cur| cur.min(*l))),
            _ => return None, // slice: no static length — fail closed
        }
    }
    let len = len?;
    // Per-element lookups: 64 covers any honest fixed-size math type; a huge
    // synthetic array is declined rather than scanned.
    if len == 0 || len > 64 {
        return None;
    }
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for k in 0..len {
        let element = name.replace(&token, &format!("[{k}]"));
        let (l, u) = contract_two_sided_range(func, &element)?;
        lo = lo.min(l);
        hi = hi.max(u);
    }
    Some((lo, hi))
}

/// Whether formal-parameter local `base` keeps its ENTRY value at every read in
/// the body — i.e. it is never (whole-or-projected) written and never mutably
/// borrowed. Conservative twin of `contract_assumption_gate::slice_param_length_is_stable`
/// / the BV-mul lane's `v2_local_assigned_anywhere`, but covering FIELD writes and
/// `&mut` aliasing so a `contract_exp_bound` magnitude claim over `self.x` cannot
/// be defeated by a body mutation of `self` (any field) between entry and use.
/// Any write/mut-borrow channel returns false (no discharge; fail-closed).
pub(super) fn param_place_is_entry_stable(func: &VerifiableFunction, base: usize) -> bool {
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place: dest, rvalue, .. } => {
                    if dest.local == base {
                        return false; // whole or field write of the parameter
                    }
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                        && borrowed.local == base
                    {
                        return false; // `&mut self` / `&mut self.x` aliasing channel
                    }
                }
                Statement::SetDiscriminant { place: dest, .. }
                | Statement::Deinit { place: dest } => {
                    if dest.local == base {
                        return false;
                    }
                }
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == base
        {
            return false; // call-destination store to the parameter
        }
        // An Opaque terminator (inline `asm!` with out/inout operands) may write
        // ANY local invisibly — its out-operand places are not modeled here — so
        // a contract magnitude bound (and the round-13 BV witness hypothesis it
        // feeds) over `base` cannot be assumed stable across it. `float_whole_
        // local_defs` already poisons on the same channel; this is its
        // conservative twin, previously missing the arm (fail-closed).
        if matches!(&block.terminator, Terminator::Opaque { .. }) {
            return false;
        }
    }
    true
}

/// The projection chains to every SCALAR f64 leaf reachable from `ty` through
/// STRUCT fields (`.i`, positional — the `place_to_var_name` / contract
/// spelling), tuple fields, and fixed-length array elements (`ConstantIndex`).
/// Enums are not walked (variant-dependent field view — a chain name would be
/// ambiguous); references/raw-pointers/symbolic arrays stop the walk (a raw-ptr
/// leaf is not a stable value anyway — see `place_reads_through_raw_ptr`).
pub(super) fn float_scalar_leaf_suffixes(ty: &Ty, depth: u32) -> Vec<Vec<Projection>> {
    fn walk(ty: &Ty, depth: u32, prefix: &mut Vec<Projection>, out: &mut Vec<Vec<Projection>>) {
        if out.len() >= 256 {
            return;
        }
        match ty {
            Ty::Float { width: 64 } => out.push(prefix.clone()),
            _ if depth == 0 => {}
            Ty::Adt { fields, variants, .. } if variants.is_empty() => {
                for (i, (_, fty)) in fields.iter().enumerate() {
                    prefix.push(Projection::Field(i));
                    walk(fty, depth - 1, prefix, out);
                    prefix.pop();
                }
            }
            Ty::Tuple(items) => {
                for (i, ity) in items.iter().enumerate() {
                    prefix.push(Projection::Field(i));
                    walk(ity, depth - 1, prefix, out);
                    prefix.pop();
                }
            }
            Ty::Array { elem, len } if *len <= FLOAT_STRUCT_LEAF_ARRAY_LIMIT => {
                let Ok(min_length) = usize::try_from(*len) else { return };
                for k in 0..min_length {
                    prefix.push(Projection::ConstantIndex {
                        offset: k,
                        min_length,
                        from_end: false,
                    });
                    walk(elem, depth - 1, prefix, out);
                    prefix.pop();
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(ty, depth, &mut Vec::new(), &mut out);
    out
}

/// Whether reading `place` POSITIVELY dereferences a RAW POINTER at some
/// projection step — `(*p).0` with `p: *const/*mut T`, or a nested raw-ptr
/// field. Such a read is not value-stable from the base local alone: two
/// raw-pointer values may ALIAS (raw pointers are `Copy`, so an alias is
/// created by a plain read, never a borrow the def scan could see), so a write
/// through one pointer changes the pointee another names.
///
/// Walks the place's declared type through its projections; a `Deref` whose
/// current type is a `RawPtr` ⇒ true. FAIL-OPEN on an untypable step (returns
/// false): this is an ADDED refusal layered on the base-local stability checks,
/// not a replacement — a place it cannot type keeps whatever the other checks
/// decide, and real MIR locals are always typable (only simplified test bodies
/// are not, e.g. a self param modeled directly as `f64`). SHARED-ref (`&T`)
/// pointees stay stable (the existing `<p>*` discipline); only raw pointers
/// alias without a visible borrow.
pub(super) fn place_reads_through_raw_ptr(func: &VerifiableFunction, place: &Place) -> bool {
    let Some(mut ty) = func.body.locals.get(place.local).map(|d| d.ty.clone()) else {
        return false;
    };
    for proj in &place.projections {
        match proj {
            Projection::Deref => match ty {
                Ty::RawPtr { .. } => return true,
                Ty::Ref { inner, .. } => ty = *inner,
                _ => match crate::step_place_ty_cow(std::borrow::Cow::Owned(ty), proj) {
                    Some(next) => ty = next.into_owned(),
                    None => return false, // untypable deref: fail-OPEN
                },
            },
            _ => match crate::step_place_ty_cow(std::borrow::Cow::Owned(ty), proj) {
                Some(next) => ty = next.into_owned(),
                None => return false, // untypable step: fail-OPEN (other checks apply)
            },
        }
    }
    false
}

/// Accumulate the tightest upper (`name <= U`) and lower (`name >= L`) magnitude
/// bounds on the variable `name` from a precondition formula, flattening `And`
/// (`#[requires(a && b)]` parses to a single `And`). Each literal bound is read as
/// a finite f64 via [`formula_numeric_value`] — an INTEGER literal
/// (`self.0 <= 1000000000000000000`) or an f64 FLOAT literal (`self.0 <= 1.0e30`).
/// `<`/`>` are treated as their non-strict weakenings (`v < k => v <= k`), sound
/// for a magnitude bound. Every other shape is ignored (fail-closed — an
/// unrecognised clause simply does not tighten a bound, so a missing side leaves
/// `contract_exp_bound` returning `None`).
pub(super) fn collect_magnitude_bounds(
    formula: &Formula,
    name: &str,
    upper: &mut Option<f64>,
    lower: &mut Option<f64>,
) {
    // `k` is finite (guaranteed by `formula_numeric_value`), so `f64::min`/`max`
    // are the ordinary numeric tightenings (no NaN involvement).
    let tighten_upper = |slot: &mut Option<f64>, k: f64| {
        *slot = Some(slot.map_or(k, |cur| cur.min(k)));
    };
    let tighten_lower = |slot: &mut Option<f64>, k: f64| {
        *slot = Some(slot.map_or(k, |cur| cur.max(k)));
    };
    match formula {
        Formula::And(items) => {
            for item in items {
                collect_magnitude_bounds(item, name, upper, lower);
            }
        }
        // `a <= b` / `a < b`: an upper bound when the var is on the left, a lower
        // bound when it is on the right.
        Formula::Le(a, b) | Formula::Lt(a, b) => {
            if formula_is_named_var(a, name) {
                if let Some(k) = formula_numeric_value(b) {
                    tighten_upper(upper, k);
                }
            } else if formula_is_named_var(b, name) {
                if let Some(k) = formula_numeric_value(a) {
                    tighten_lower(lower, k);
                }
            }
        }
        // `a >= b` / `a > b`: mirror image of the above.
        Formula::Ge(a, b) | Formula::Gt(a, b) => {
            if formula_is_named_var(a, name) {
                if let Some(k) = formula_numeric_value(b) {
                    tighten_lower(lower, k);
                }
            } else if formula_is_named_var(b, name) {
                if let Some(k) = formula_numeric_value(a) {
                    tighten_upper(upper, k);
                }
            }
        }
        _ => {}
    }
}

/// Whether `formula` is exactly the variable spelled `name` (either the
/// heap-string `Var` the spec parser emits or the interned `SymVar`).
pub(super) fn formula_is_named_var(formula: &Formula, name: &str) -> bool {
    match formula {
        Formula::Var(n, _) => n == name,
        Formula::SymVar(sym, _) => sym.as_str() == name,
        _ => false,
    }
}

/// The integer value of a literal precondition term: `Int`, a `UInt` that fits
/// `i128`, or a negation thereof (`-C` parses to `Neg(Int(C))`). `None` for any
/// non-literal term.
pub(super) fn formula_int_value(formula: &Formula) -> Option<i128> {
    match formula {
        Formula::Int(v) => Some(*v),
        Formula::UInt(v) => i128::try_from(*v).ok(),
        Formula::Neg(inner) => formula_int_value(inner)?.checked_neg(),
        _ => None,
    }
}

/// The FINITE f64 value of a binary64 float literal term. A spec float literal
/// lowers to `FpConst { eb: 11, sb: 53 }` (the parser folds a leading `-` into the
/// sign bit, so `-1.0e30` arrives as a single signed const, not a `Neg`). A
/// defensive `Neg(FpConst)` wrapper is honoured too. Non-finite literals (`inf`
/// from an over-large decimal, `NaN`) and any non-f64 format return `None`
/// (fail-closed — a non-finite bound never yields a magnitude exponent).
pub(super) fn formula_float_value(formula: &Formula) -> Option<f64> {
    match formula {
        Formula::FpConst { bits, eb: 11, sb: 53 } => {
            let v = f64::from_bits(*bits as u64);
            v.is_finite().then_some(v)
        }
        Formula::Neg(inner) => {
            let v = -formula_float_value(inner)?;
            v.is_finite().then_some(v)
        }
        _ => None,
    }
}

/// The FINITE f64 value of a literal magnitude bound — a float literal, else an
/// integer literal widened to f64. `None` for a non-literal or non-finite term.
/// An integer bound's `as f64` widening rounds to nearest, which is SOUND for the
/// magnitude use: `f64_finite_biased_exp` of the (possibly rounded) `C` still
/// strictly dominates the true integer bound, because the biased exponent field
/// only increases when the magnitude crosses a binade boundary.
pub(super) fn formula_numeric_value(formula: &Formula) -> Option<f64> {
    if let Some(v) = formula_float_value(formula) {
        return Some(v);
    }
    let v = formula_int_value(formula)? as f64;
    v.is_finite().then_some(v)
}

/// EVERY whole-local def of `local`, or `None` when some write channel makes
/// the def set an unsound value model: a PROJECTED store (`t.0 = …`, incl. a
/// projected Call dest), `SetDiscriminant`/`Deinit`, or a `&mut`/`&raw mut`
/// borrow (writes through the alias are invisible to any def scan). These are
/// `param_place_is_entry_stable`'s channels; whole-local stores are the defs
/// being collected, so they are allowed here.
pub(super) fn float_whole_local_defs(
    func: &VerifiableFunction,
    local: usize,
) -> Option<Vec<FloatLocalDef<'_>>> {
    let mut defs = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place: dest, rvalue, .. } => {
                    if dest.local == local {
                        if dest.projections.is_empty() {
                            defs.push(FloatLocalDef::Rvalue { block: block.id, rvalue });
                        } else {
                            return None; // projected store: hull-of-defs model breaks
                        }
                    }
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(true, borrowed) = rvalue
                        && borrowed.local == local
                    {
                        return None; // `&mut` / `&raw mut` aliasing channel
                    }
                }
                Statement::SetDiscriminant { place: dest, .. }
                | Statement::Deinit { place: dest } => {
                    if dest.local == local {
                        return None;
                    }
                }
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } if dest.local == local => {
                if !dest.projections.is_empty() {
                    return None;
                }
                defs.push(FloatLocalDef::Call { block: block.id, callee, args: args.as_slice() });
            }
            // An `Opaque` terminator (inline asm, …) carries NO operand model
            // — it may write ANY local invisibly. One anywhere poisons every
            // def set (fail-closed; such a function already carries an
            // UnsupportedMir obligation, but this lane must not even trace).
            Terminator::Opaque { .. } => return None,
            _ => {}
        }
    }
    Some(defs)
}

/// F0/F1 core — a FINITE signed interval `[lo, hi]` (with `lo <= hi`) that the
/// f64 `operand`'s runtime value ALWAYS lies in — under the `mode` NaN
/// discipline — whenever this function's gated preconditions and the dominating
/// guards of the reading block hold. `block_id` is the block the operand is
/// READ in (guard facts constrain the value there); `None` means no flow
/// context, which is always sound because guards only ADD constraints.
///
/// Sources, all fail-closed to `None`:
///   * literals (exact point interval; NaN/±inf literals refuse);
///   * the multi-def HULL over EVERY whole-local def — any read yields SOME
///     def's value (MIR init-before-use), so the hull encloses it; ONE
///     unboundable def refuses; a self-referential def chain (loop
///     accumulator) is cut by `visiting`; projected/aliased write channels
///     refuse (`float_whole_local_defs`). This REPLACES the old last-def-wins
///     scan, whose `let mut t = 1e308; if c { t = 1.0 } t + t` false proof was
///     reachable (soundness review, float-residuals round);
///   * entry-stable parameter places: F6b caller-proved overrides
///     (`FloatRangeCtx::param_overrides`, consulted first) and contract
///     bounds (`contract_range`, incl. F4 index canonicalization +
///     uniform-index hull);
///   * projected-place tracing (F3, `float_aggregate_range`): same-shape
///     aggregate per-field hulls, enum payload variant hulls, unique-Use-def
///     projection rebase, and per-suffix callee traces;
///   * interval arithmetic over Use/Cast/Add/Sub/Mul/Div/Neg defs, OUTWARD
///     rounded (`next_down`/`next_up`) after every combination;
///   * recognized std f64 calls (sqrt/abs/min/max/clamp/sin/cos/tanh/
///     as_secs_f64), F6 callee interval summaries, and F6b context-sensitive
///     callee re-traces (`float_callee_trace_range`);
///   * dominating float guards of the reading block — direct ordering facts
///     plus abs-guard caps (`float_abs_guard_magnitude_bounds`) —
///     INTERSECTED with the above (the guard constrains the value at the
///     read regardless of which def produced it).
pub(super) fn float_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    block_id: Option<BlockId>,
    operand: &Operand,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    ctx.spend()?;
    if fuel == 0 {
        return None;
    }
    if let Operand::Constant(c) = operand {
        let v = f64_const_value(c)?;
        return v.is_finite().then_some((v, v));
    }
    let place = match operand {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };
    if !place.projections.is_empty() {
        // F6b (struct-argument tracing): a caller-proved FIELD override is the
        // callsite-specific interval of the actual's corresponding field — at
        // least as tight as, and consulted BEFORE, the callee's own contract
        // (which is the callee-GLOBAL bound and too loose for a chain to
        // satisfy a downstream callee precondition). Empty off the callee trace.
        if let Some(range) = ctx.param_field_override(place) {
            return Some(range);
        }
        // Entry-stable parameter chain (`self.0`, `arr[k]`, `self*.2`) against
        // THIS function's own contract…
        if let Some(range) = contract_range(ctx.func, place) {
            return Some(range);
        }
        // …then F3: an element of a locally-constructed unique aggregate.
        return float_aggregate_range(ctx, mode, block_id, place, visiting, fuel);
    }
    let local = place.local;
    // Cycle guard: a def chain that re-reads its own local (loop accumulator)
    // has no closed form here — fail closed.
    if visiting.contains(&local) {
        return None;
    }
    let defs = float_whole_local_defs(ctx.func, local)?;
    let is_param = local >= 1 && local <= ctx.func.body.arg_count;
    let base = if defs.is_empty() {
        // No def ⇒ a formal parameter (entry value): the F6b caller-proved
        // override FIRST (it is callsite-specific, hence at least as tight as
        // any callee-global fact), then contract facts. Both are ENTRY facts
        // and share the same license: this branch is only reached when the
        // formal has NO write/alias channel at all (`float_whole_local_defs`
        // returned an EMPTY def set — no whole/projected store, no `&mut`, no
        // SetDiscriminant/Deinit, no call dest, no Opaque terminator), so the
        // read provably sees the entry value the caller established. (A
        // defless non-parameter is never read; both lookups reject it.)
        ctx.param_override(local).or_else(|| contract_range(ctx.func, place))
    } else if is_param {
        // SOUNDNESS: a REASSIGNED parameter still carries its (statement-
        // invisible) ENTRY value as an additional def source — a read BEFORE
        // the first body write sees it, and the def hull does not enclose it
        // (`fn f(mut x: f64) { let a = x; x = 1.0; a + a }` — `a` is the
        // unbounded entry `x`, not the 1.0). Contract facts are equally
        // unusable (the write defeats entry-stability). Fail closed; the
        // guard intersection below may still bound the read.
        None
    } else {
        visiting.push(local);
        let mut hull: Option<(f64, f64)> = None;
        let mut every_def_bounded = true;
        for def in &defs {
            let range = match def {
                FloatLocalDef::Rvalue { block, rvalue } => {
                    float_rvalue_range(ctx, mode, *block, rvalue, visiting, fuel)
                }
                FloatLocalDef::Call { block, callee, args } => {
                    float_call_range(ctx, mode, *block, callee, args, visiting, fuel)
                }
            };
            match (range, &mut hull) {
                (None, _) => {
                    every_def_bounded = false;
                    break;
                }
                (Some((l, h)), Some((hl, hh))) => {
                    *hl = hl.min(l);
                    *hh = hh.max(h);
                }
                (Some(range), None) => hull = Some(range),
            }
        }
        visiting.pop();
        if every_def_bounded { hull } else { None }
    };
    let guard = match block_id {
        Some(b) => {
            let (mut lo, mut hi) = float_guard_bounds(ctx, b, place);
            // Abs-guard CAP (the `if a.abs() <= 1e300 { … }` idiom): a
            // dominating upper bound `C` on this place's abs TEMP bounds the
            // SIGNED value to `[-C, C]` — `abs` is exact and a NaN value makes
            // the abs result NaN, the guard comparison FALSE, and the path
            // untaken, so the fact's truth implies orderedness too (both NaN
            // modes hold). Same value-identity disciplines as the divisor
            // magnitude FLOOR; see `float_abs_guard_magnitude_bounds`.
            if place.projections.is_empty()
                && let (_, Some(c)) = float_abs_guard_magnitude_bounds(ctx, b, place)
            {
                lo = Some(lo.map_or(-c, |cur: f64| cur.max(-c)));
                hi = Some(hi.map_or(c, |cur: f64| cur.min(c)));
            }
            (lo, hi)
        }
        None => (None, None),
    };
    intersect_float_range(base, guard)
}

/// Intersect a def/contract interval with (possibly one-sided) dominating
/// guard bounds. A guard fact being TRUE implies the value was ORDERED (not
/// NaN) and inside the bound, so intersection is sound in both NaN modes (it
/// only shrinks the claim). With no base interval, BOTH guard sides are
/// required (the tracer's contract is a finite two-sided interval). An empty
/// intersection means the guards contradict the def facts (the read is
/// unreachable) — `None`, never a claim about a value.
pub(super) fn intersect_float_range(
    base: Option<(f64, f64)>,
    (guard_lo, guard_hi): (Option<f64>, Option<f64>),
) -> Option<(f64, f64)> {
    let (lo, hi) = match base {
        Some((l, h)) => (guard_lo.map_or(l, |g| g.max(l)), guard_hi.map_or(h, |g| g.min(h))),
        None => (guard_lo?, guard_hi?),
    };
    (lo.is_finite() && hi.is_finite() && lo <= hi).then_some((lo, hi))
}

/// `2^w` as an exact f64 (`w <= 1023`), the int→f64 cast magnitude bound.
pub(super) fn exp2i(w: u32) -> Option<f64> {
    (w <= 1023).then(|| f64::from_bits((u64::from(w) + 1023) << 52))
}

/// Interval arithmetic in round-to-nearest with OUTWARD one-ulp bumps
/// (`next_down` on the low, `next_up` on the high) after the combination:
/// `|fl(x) − x| <= ulp/2 < ulp`, so the bumped endpoints enclose the exact
/// endpoint values, and fl's weak monotonicity keeps every interior IEEE
/// result inside the enclosure. Any non-finite endpoint → `None` (fail-closed).
/// Finite operands cannot produce a NaN here: Mul/Add/Sub of finite values is
/// finite-or-inf, and Div is gated on a SIGN-DEFINITE divisor interval (no
/// 0/0, no x/0).
pub(super) fn float_interval_binop(
    op: BinOp,
    (la, ha): (f64, f64),
    (lb, hb): (f64, f64),
) -> Option<(f64, f64)> {
    let four = |a: f64, b: f64, c: f64, d: f64| (a.min(b).min(c).min(d), a.max(b).max(c).max(d));
    let (lo, hi) = match op {
        BinOp::Add => (la + lb, ha + hb),
        // a − b is monotone in a, antitone in b.
        BinOp::Sub => (la - hb, ha - lb),
        BinOp::Mul => four(la * lb, la * hb, ha * lb, ha * hb),
        BinOp::Div => {
            // SIGN-DEFINITE divisor required: an interval straddling (or
            // touching) zero admits a ±inf/NaN quotient — no finite enclosure.
            if !(lb > 0.0 || hb < 0.0) {
                return None;
            }
            four(la / lb, la / hb, ha / lb, ha / hb)
        }
        _ => return None,
    };
    finite_outward(lo, hi)
}

/// The outward-rounding step shared by every interval combination.
pub(super) fn finite_outward(lo: f64, hi: f64) -> Option<(f64, f64)> {
    let (lo, hi) = (lo.next_down(), hi.next_up());
    (lo.is_finite() && hi.is_finite() && lo <= hi).then_some((lo, hi))
}

/// Interval of one whole-local `Assign` def. Each operand of the def is read
/// AT THE DEF'S BLOCK, so recursion threads that block for guard facts.
pub(super) fn float_rvalue_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    def_block: BlockId,
    rvalue: &Rvalue,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    match rvalue {
        Rvalue::Use(op) => float_range(ctx, mode, Some(def_block), op, visiting, fuel - 1),
        Rvalue::Cast(op, Ty::Float { width: 64 }) => {
            match crate::operand_ty_cow(ctx.func, op).as_deref() {
                // int→f64: `|result| <= 2^w` exactly (fl is monotone and `2^w`
                // is an exact f64 at every integer width); never NaN/inf —
                // sound in BOTH modes. Outward-bumped per the uniform
                // discipline (pure widening).
                Some(Ty::Int { width, .. }) => {
                    let bound = exp2i(*width)?;
                    finite_outward(-bound, bound)
                }
                // f32→f64 widening is exact and bounded by ±f32::MAX for every
                // FINITE f32 — but an inf/NaN f32 widens to inf/NaN f64. The
                // NaN-tolerant mode keeps the legacy discharge stance (a
                // PROPAGATED non-finite input is not a fresh overflow of this
                // chain, and the finite-operand witness never fires on it);
                // the strict mode cannot prove the f32 source finite (the
                // tracer is f64-only) and refuses.
                Some(Ty::Float { width: 32 }) => match mode {
                    FloatNanMode::NanOrBounded => {
                        finite_outward(-f64::from(f32::MAX), f64::from(f32::MAX))
                    }
                    FloatNanMode::Forbid => None,
                },
                Some(Ty::Float { width: 64 }) => {
                    float_range(ctx, mode, Some(def_block), op, visiting, fuel - 1)
                }
                _ => None,
            }
        }
        Rvalue::BinaryOp(op @ (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div), a, b) => {
            let ra = float_range(ctx, mode, Some(def_block), a, visiting, fuel - 1)?;
            if let Some(rb) = float_range(ctx, mode, Some(def_block), b, visiting, fuel - 1)
                && let Some(full) = float_interval_binop(*op, ra, rb)
            {
                return Some(full);
            }
            // Div with no finite divisor INTERVAL but a guard/contract
            // magnitude FLOOR `|b| >= m > 0` (`let len = ..; if len > 1e-20 {
            // 1.0 / len }` — the divisor's upper end is unbounded, so no
            // two-sided interval exists): `|a / b| <= max(|a|) / m`
            // (fl-monotone), giving the two-sided enclosure `[-q, q]`. NaN
            // discipline holds in BOTH modes: the floor's guard/sign evidence
            // implies an ORDERED divisor, a finite numerator over a
            // nonzero-magnitude divisor is finite-or-(±0 for an inf divisor)
            // — never NaN, and a magnitude above the enclosure is impossible.
            // The sign of the quotient is deliberately not refined (the floor
            // carries magnitude only).
            if *op == BinOp::Div {
                let m = float_divisor_magnitude_floor(
                    ctx,
                    mode,
                    Some(def_block),
                    b,
                    visiting,
                    fuel - 1,
                )?;
                let q = ra.0.abs().max(ra.1.abs()) / m;
                return finite_outward(-q, q);
            }
            None
        }
        // IEEE negation is EXACT (a sign-bit flip): no rounding bump.
        Rvalue::UnaryOp(trust_types::UnOp::Neg, op) => {
            let (l, h) = float_range(ctx, mode, Some(def_block), op, visiting, fuel - 1)?;
            Some((-h, -l))
        }
        _ => None,
    }
}

/// Interval of one whole-local `Call` def — the recognized std f64 surface
/// plus (F6) callee interval summaries.
pub(super) fn float_call_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    def_block: BlockId,
    callee: &str,
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    if fuel == 0 {
        return None;
    }
    // `Duration::as_secs_f64`/`as_secs_f32`: `[0, u64::MAX + 1) ⊂ [0, 2^65]`,
    // always finite, never NaN — sound in both modes. CRATE-ORIGIN anchored
    // (`core::time::Duration::as_secs_f64` / the std re-export): a bare suffix
    // match let any `mymod::as_secs_f64` inject the bound (round-13, same
    // false-proof channel as the un-gated `::cos` suffix).
    if (callee.ends_with("::as_secs_f64") || callee.ends_with("::as_secs_f32"))
        && (callee.starts_with("core::") || callee.starts_with("std::"))
        && callee.contains("::time::")
    {
        return Some((0.0, exp2i(65)?));
    }
    // sin/cos/tanh: `|v| <= 1` for every FINITE input; NaN for a ±inf/NaN
    // input. The NaN-tolerant mode takes the unconditional bound (a NaN is
    // inside its contract — never a fresh ±inf); the strict mode must first
    // prove the ARGUMENT finite and NaN-free.
    if is_unit_bounded_float_call(callee) {
        if mode == FloatNanMode::Forbid {
            float_range(
                ctx,
                FloatNanMode::Forbid,
                Some(def_block),
                args.first()?,
                visiting,
                fuel - 1,
            )?;
        }
        return Some((-1.0, 1.0));
    }
    if let Some(method) = f64_std_method_name(callee)
        && let Some(range) =
            float_std_call_range(ctx, mode, def_block, method, args, visiting, fuel)
    {
        return Some(range);
    }
    // F6 static summary interval first (cheap, no re-trace), then the F6b
    // context-sensitive re-trace of the extracted body for the whole return
    // place (empty suffix).
    if let Some(range) = float_summary_result_range(ctx, def_block, callee, args, visiting, fuel) {
        return Some(range);
    }
    float_callee_trace_range(ctx, def_block, callee, args, &[], visiting, fuel)
}

/// The recognized `::f64::` std-method arms of [`float_call_range`] (origin
/// already gated by `f64_std_method_name`).
pub(super) fn float_std_call_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    def_block: BlockId,
    method: &str,
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    match (method, args) {
        // sqrt is correctly rounded and monotone, so the endpoint images
        // already enclose every result; the bump is uniform-discipline
        // belt-and-braces. `lo < 0` admits a NaN result — refuse in both modes
        // (the NaN-tolerant contract COULD keep `[0, sqrt(hi)]` for the
        // non-negative slice, but the tight gate is simpler to audit). The
        // result is never below +0.0 — floor the bumped low there.
        ("sqrt", [arg]) => {
            let (lo, hi) = float_range(ctx, mode, Some(def_block), arg, visiting, fuel - 1)?;
            if lo < 0.0 {
                return None;
            }
            Some((lo.sqrt().next_down().max(0.0), hi.sqrt().next_up()))
        }
        // |·| is EXACT (a sign-bit clear): no bump. NaN passes through — inside
        // the NaN-tolerant contract; the strict mode's argument is NaN-free.
        ("abs", [arg]) => {
            let (lo, hi) = float_range(ctx, mode, Some(def_block), arg, visiting, fuel - 1)?;
            Some(if lo >= 0.0 {
                (lo, hi)
            } else if hi <= 0.0 {
                (-hi, -lo)
            } else {
                (0.0, (-lo).max(hi))
            })
        }
        // The HULL of both operand intervals — correct for `min` AND `max`,
        // and (load-bearing in the NaN-tolerant mode) for the IEEE NaN
        // fallback `f64::min(NaN, y) == y`, where the result can be EITHER
        // operand. Exact selections: no bump.
        ("min" | "max", [a, b]) => {
            let (la, ha) = float_range(ctx, mode, Some(def_block), a, visiting, fuel - 1)?;
            let (lb, hb) = float_range(ctx, mode, Some(def_block), b, visiting, fuel - 1)?;
            Some((la.min(lb), ha.max(hb)))
        }
        // `self.clamp(lo, hi)` with LITERAL, finite, ordered bounds — the old
        // `fp_clamp_call_exp_bound` gates verbatim: symbolic bounds prove
        // nothing; NaN or inverted bounds PANIC instead of returning (no value
        // flows, so refusing stays trivially sound). `clamp` passes a NaN self
        // THROUGH — allowed by the NaN-tolerant contract, while the strict
        // mode must first prove self NaN-free.
        ("clamp", [self_op, lo_op, hi_op]) => {
            let lo = match lo_op {
                Operand::Constant(c) => f64_const_value(c)?,
                _ => return None,
            };
            let hi = match hi_op {
                Operand::Constant(c) => f64_const_value(c)?,
                _ => return None,
            };
            if !lo.is_finite() || !hi.is_finite() || !(lo <= hi) {
                return None;
            }
            if mode == FloatNanMode::Forbid {
                float_range(
                    ctx,
                    FloatNanMode::Forbid,
                    Some(def_block),
                    self_op,
                    visiting,
                    fuel - 1,
                )?;
            }
            Some((lo, hi))
        }
        _ => None,
    }
}

/// F6 — a callee's derived RESULT interval, honored ONLY when the callee's own
/// preconditions are structurally re-established AT THIS CALL (self-contained
/// assume-guarantee: no reliance on the separately-emitted Precondition VCs).
/// `result_range` is populated exclusively by the verifier-owned derivation
/// (`derive_float_result_range` via `compute_summary`); the production
/// contract-summary builder never sets it, so this arm is fail-closed there.
/// The stored interval is re-validated defensively (`FunctionSummary` is a
/// publicly-constructible struct; a malformed claim is refused, and the
/// interval itself carries no authority beyond suppressing THIS structural
/// discharge's conservatism).
pub(super) fn float_summary_result_range(
    ctx: &FloatRangeCtx<'_>,
    call_block: BlockId,
    callee: &str,
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    let summary = ctx.summaries?.get(callee)?;
    let (lo, hi) = summary.result_range?;
    if !(lo.is_finite() && hi.is_finite() && lo <= hi) {
        return None;
    }
    if !summary.preconditions.is_empty() {
        if summary.param_names.len() != args.len() {
            return None;
        }
        for pre in &summary.preconditions {
            if !precondition_interval_dominance(
                ctx,
                call_block,
                pre,
                &summary.param_names,
                args,
                visiting,
                fuel.checked_sub(1)?,
            ) {
                return None;
            }
        }
    }
    Some((lo, hi))
}

/// F6b — CONTEXT-SENSITIVE callee tracing: evaluate the interval of the
/// callee's return place `_0.<suffix>` by RE-TRACING its extracted body under
/// caller-derived argument intervals, at ONE specific call site. This is what
/// a static per-callee interval cannot do: `result_range` is callee-GLOBAL
/// (valid only under the callee's own preconditions), while chained magnitude
/// reasoning (`a.add(b).scale(s)`) needs the range of THIS call's result under
/// THIS call's argument bounds. The `suffix` selects a projected component of
/// the return value (`.k` fields, `[k]` const indices, `@v.k` enum payloads);
/// empty means the whole (scalar) return.
///
/// SOUNDNESS (assume-guarantee, mirroring `float_summary_result_range`):
///   1. The extracted body carries NO proof authority — everything returned
///      here is RE-DERIVED by the same fail-closed tracer that would have run
///      inside the callee, seeded only with facts proved in the caller.
///   2. Formal overrides are the caller's `float_range` of each actual in
///      STRICT `Forbid` mode at the call block — finite, ordered intervals,
///      exactly the claim strength `contract_range` supplies for a gated
///      precondition (which is how the callee-side reads consume them, under
///      the same defless entry-stability discipline; see
///      `FloatRangeCtx::param_overrides`). Only f64-typed formals are bound;
///      an unbindable actual simply leaves its formal unboundable inside the
///      callee (fail-closed, never wrong).
///   3. The callee-side trace ALSO consumes the body's own gated
///      preconditions (`contract_range` reads `body.preconditions`), so every
///      one of them — and every summary-declared precondition — is
///      structurally re-established at this call first
///      (`precondition_interval_dominance`); any failure refuses the trace.
///   4. The trace result is derived in STRICT `Forbid` mode (finite, in
///      interval, never NaN), the stronger of the two NaN disciplines, so it
///      is a valid claim for consumers in EITHER mode.
///   5. Interprocedural nesting is cut at `FLOAT_INTERPROC_DEPTH` and by the
///      shared callee-name visiting stack (direct/mutual recursion has no
///      closed form), the work budget is SHARED with the caller context, and
///      every refusal is `None` — fail-closed.
pub(super) fn float_callee_trace_range(
    ctx: &FloatRangeCtx<'_>,
    call_block: BlockId,
    callee: &str,
    args: &[Operand],
    suffix: &[Projection],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    ctx.spend()?;
    if fuel == 0 {
        return None;
    }
    // SOUNDNESS (round-14 false-proof): the `suffix` is the CALLER's projection
    // chain, but it is about to be resolved inside the CALLEE's body/namespace.
    // A `Projection::Index(local)` names a caller-runtime index LOCAL — inside
    // the callee that same number is an UNRELATED local, so a GENUINELY runtime
    // index must never cross the boundary (it would silently rebind a runtime
    // `t[i]` to a callee element). But a CONSTANT-valued caller index — e.g.
    // `m.cols[0]` lowered to `Index(_k)` with `_k = const 0` — denotes one fixed
    // element. Resolve it to a `ConstantIndex` HERE, in the CALLER namespace
    // (`index_local_const(ctx.func, ..)` reads the caller's constant and rejects
    // any non-const / conflicting / `&mut`-borrowed index), so the fixed element
    // read can reattach to the callee's return aggregate. The resulting suffix
    // carries only namespace-INDEPENDENT tokens. A runtime index still refuses.
    let resolved_suffix: Vec<Projection> = if suffix.iter().any(|p| matches!(p, Projection::Index(_)))
    {
        let mut out = Vec::with_capacity(suffix.len());
        for proj in suffix {
            match proj {
                Projection::Index(local) => {
                    let offset = crate::index_local_const(ctx.func, *local)?;
                    out.push(Projection::ConstantIndex {
                        offset,
                        min_length: offset.checked_add(1)?,
                        from_end: false,
                    });
                }
                other => out.push(other.clone()),
            }
        }
        out
    } else {
        suffix.to_vec()
    };
    let suffix: &[Projection] = &resolved_suffix;
    let summary = ctx.summaries?.get(callee)?;
    let body = summary.extracted_body.as_deref()?;
    // Positional formal binding requires the extracted arity to match the call.
    if body.body.arg_count != args.len() {
        return None;
    }
    // Trace memo (successful results only — see the field doc).
    let memo_key =
        (call_block, callee.to_string(), format!("{args:?}"), format!("{suffix:?}"));
    if let Some(hit) = ctx.trace_memo.borrow().get(&memo_key) {
        return Some(*hit);
    }
    // Depth + recursion cut (shared across nesting levels).
    {
        let stack = ctx.visiting_callees.borrow();
        if stack.len() >= FLOAT_INTERPROC_DEPTH || stack.iter().any(|name| name == callee) {
            return None;
        }
    }
    // (3) Re-establish EVERY precondition the trace may consume: the body's
    // own gated set (what `contract_range` reads during the re-trace) and the
    // summary's declared set (the interface this interval claim is conditional
    // on). The σ mapping needs the summary's formal names.
    let assumed: Vec<&Formula> =
        body.preconditions.iter().chain(summary.preconditions.iter()).collect();
    if !assumed.is_empty() && summary.param_names.len() != args.len() {
        return None;
    }
    for pre in assumed {
        if !precondition_interval_dominance(
            ctx,
            call_block,
            pre,
            &summary.param_names,
            args,
            visiting,
            fuel.checked_sub(1)?,
        ) {
            return None;
        }
    }
    // (2) Bind each f64 FORMAL's override from the caller-proved interval of
    // its actual, in strict Forbid mode at the call block. Failures bind
    // nothing (the formal stays unboundable inside the callee).
    let mut overrides: FxHashMap<usize, (f64, f64)> = FxHashMap::default();
    let mut field_overrides: FxHashMap<String, (f64, f64)> = FxHashMap::default();
    for (position, actual) in args.iter().enumerate() {
        let formal = position + 1;
        let Some(formal_ty) = body.body.locals.iter().find(|d| d.index == formal).map(|d| &d.ty)
        else {
            continue;
        };
        if matches!(formal_ty, Ty::Float { width: 64 }) {
            // Scalar f64 formal: whole-local override (the `s` of `scale(self, s)`).
            if let Some(range) =
                float_range(ctx, FloatNanMode::Forbid, Some(call_block), actual, visiting, fuel - 1)
            {
                overrides.insert(formal, range);
            }
            continue;
        }
        // STRUCT/vector formal: bind each scalar-f64 LEAF from the caller's
        // interval of the actual's corresponding field. The actual must be a
        // place (a constructed struct literal is handled by the general
        // aggregate lane, not here); its type is walked for f64 leaves and the
        // key is the CALLEE-side name so the in-callee projected read finds it.
        let (Operand::Copy(actual_place) | Operand::Move(actual_place)) = actual else {
            continue;
        };
        for leaf in float_scalar_leaf_suffixes(formal_ty, FLOAT_STRUCT_LEAF_DEPTH) {
            let mut caller_place = actual_place.clone();
            caller_place.projections.extend_from_slice(&leaf);
            let Some(range) = float_range(
                ctx,
                FloatNanMode::Forbid,
                Some(call_block),
                &Operand::Copy(caller_place),
                visiting,
                fuel - 1,
            ) else {
                continue;
            };
            let callee_place = Place { local: formal, projections: leaf };
            let key = canonicalize_contract_index_segments(&crate::place_to_var_name(
                body,
                &callee_place,
            ));
            field_overrides.insert(key, range);
        }
    }
    // (4)(5) Trace `_0.<suffix>` inside the callee: fresh per-function context
    // (fresh LOCAL visiting namespace), shared work budget + callee stack, no
    // top-level flow context (each `_0` def is still evaluated under ITS OWN
    // block's dominating guards, exactly like `derive_float_result_range`).
    ctx.visiting_callees.borrow_mut().push(callee.to_string());
    let callee_ctx = FloatRangeCtx::for_callee(ctx, body, overrides, field_overrides);
    let place = Place { local: 0, projections: suffix.to_vec() };
    let range = float_range(
        &callee_ctx,
        FloatNanMode::Forbid,
        None,
        &Operand::Copy(place),
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    );
    ctx.visiting_callees.borrow_mut().pop();
    if let Some(hit) = range {
        ctx.trace_memo.borrow_mut().insert(memo_key, hit);
    }
    range
}

/// A projection as a CONSTANT identity key, or `None` if it names a runtime
/// value (a symbolic `Index(local)` that is not a compile-time constant). Field
/// / const-index / deref / downcast carry constants; a const-resolved
/// `Index(_k)` (`index_local_const`) folds to the same key as `ConstantIndex`.
/// The leading tag keeps field `k` and index `k` in DISJOINT key spaces.
pub(super) fn proj_const_key(func: &VerifiableFunction, p: &Projection) -> Option<(u8, usize)> {
    match p {
        Projection::Field(f) => Some((0, *f)),
        Projection::ConstantIndex { offset, from_end: false, .. } => Some((1, *offset)),
        Projection::Index(local) => crate::index_local_const(func, *local).map(|k| (1, k)),
        Projection::Deref => Some((2, 0)),
        Projection::Downcast(v) => Some((3, *v)),
        _ => None,
    }
}

/// True when two projection chains (rooted at the SAME local) PROVABLY denote
/// disjoint places: they agree on a common prefix of constant positions and then
/// differ at a position that is CONSTANT on both sides. A symbolic index at or
/// before the divergence, or a pure prefix relationship (one chain is an
/// ancestor of the other), is conservatively NOT disjoint (`false`). Sound: a
/// write to a provably-different constant slot cannot change the value read at
/// this slot.
pub(super) fn projections_provably_disjoint(
    func: &VerifiableFunction,
    a: &[Projection],
    b: &[Projection],
) -> bool {
    for (pa, pb) in a.iter().zip(b.iter()) {
        match (proj_const_key(func, pa), proj_const_key(func, pb)) {
            (Some(ka), Some(kb)) if ka != kb => return true, // differ at a constant position
            (Some(ka), Some(kb)) if ka == kb => continue,    // same constant slot: descend
            _ => return false, // a symbolic index here: cannot prove disjointness
        }
    }
    false // one chain is a prefix of the other: overlapping, not disjoint
}

/// Flow-sensitive "masked init" lane. `float_whole_local_defs` conservatively
/// POISONS any local touched by a projected store (`m.cols[0] = ..`), because
/// the whole-local hull model cannot represent partial mutation. But a read of a
/// single ELEMENT `m.<elem>` still provably sees `m`'s Call-INIT value whenever
/// no store that could alias `<elem>` can reach the reading block — the exact
/// shape of `let mut m = f(); m.cols[0] = m.cols[0].scaled(s); ..` where the
/// `m.cols[k]` READ feeding each store precedes (and is unreachable from) that
/// store. Returns the init Call's element interval, or `None` (fail-closed).
///
/// SOUNDNESS obligations, all fail-closed:
///   * `m` has EXACTLY ONE whole-local def and it is a `Call` (the init); a
///     whole reseat, a second init, or a projected-dest call refuses.
///   * NO `&mut m.*` / `&raw mut m.*`, `SetDiscriminant m`, `Deinit m`, or any
///     `Opaque` terminator anywhere (invisible write channels).
///   * EVERY store whose place is not PROVABLY DISJOINT from the read place
///     (`projections_provably_disjoint` — a symbolic index is treated as
///     aliasing) must be UNABLE to reach the read block (`reachable_avoiding`);
///     a store block that reaches the read could deliver a post-store value the
///     init interval does not bound.
///   * the init block must itself reach the read (init-before-use well-formed).
/// Given all four, every path to the read writes `m.<elem>` only via the init,
/// so the init Call's element interval encloses the read's value. The store's
/// RHS is NEVER evaluated here (only the init is traced), so the common
/// `m.cols[k] = m.cols[k].scaled(..)` self-reference cannot cycle.
pub(super) fn float_masked_init_call_element_range<'a>(
    ctx: &FloatRangeCtx<'a>,
    _mode: FloatNanMode,
    place: &Place,
    read_block: BlockId,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    let m = place.local;
    // Must be an ELEMENT read: at least a field + an index/field beneath it
    // (a bare `m` or single-projection read is not the masked-element shape).
    if place.projections.len() < 2 {
        return None;
    }
    if visiting.contains(&m) {
        return None;
    }
    let func = ctx.func;
    let mut init: Option<(BlockId, &'a str, &'a [Operand])> = None;
    let mut stores: Vec<(BlockId, &'a [Projection])> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place: dest, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: b }
                    | Rvalue::AddressOf(true, b) = rvalue
                        && b.local == m
                    {
                        return None; // `&mut m.*` — an invisible write channel
                    }
                    if dest.local == m {
                        if dest.projections.is_empty() {
                            return None; // a whole reseat: not the single-init shape
                        }
                        stores.push((block.id, dest.projections.as_slice()));
                    }
                }
                Statement::SetDiscriminant { place: d, .. } | Statement::Deinit { place: d }
                    if d.local == m =>
                {
                    return None;
                }
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } if dest.local == m => {
                if !dest.projections.is_empty() || init.is_some() {
                    return None; // projected-dest call, or a SECOND whole def
                }
                init = Some((block.id, callee.as_str(), args.as_slice()));
            }
            Terminator::Opaque { .. } => return None,
            _ => {}
        }
    }
    let (init_block, callee, args) = init?;
    // Every non-disjoint store must be unreachable from the read block. Two
    // projection chains rooted at `m` are PROVABLY DISJOINT when they differ at
    // some position that is CONSTANT on both sides (a `Field`, or a
    // const-resolved index) — `m.cols[0]` vs `m.cols[1]`. A symbolic index, or a
    // prefix relationship, is conservatively NOT disjoint. This resolves the
    // `Index(_k)` locals to their constants (which `place_to_var_name` renders
    // as symbolic `[_..]`, over-aliasing every column), so a store to a
    // DIFFERENT column no longer blocks this column's read.
    let empty = FxHashSet::default();
    for (sblock, sproj) in &stores {
        if projections_provably_disjoint(func, sproj, &place.projections) {
            continue; // provably a different element: cannot affect the read
        }
        if reachable_avoiding(func, sblock.0, &empty).contains(&read_block.0) {
            return None; // an aliasing store can reach the read — could clobber
        }
    }
    // Init-before-use well-formedness: the init must reach the read.
    if !reachable_avoiding(func, init_block.0, &empty).contains(&read_block.0) {
        return None;
    }
    // Safe: the read sees the init Call's element. Trace it (Forbid mode — the
    // strict discipline, valid for consumers in either NaN mode).
    visiting.push(m);
    let range = float_callee_trace_range(
        ctx,
        init_block,
        callee,
        args,
        &place.projections,
        visiting,
        fuel.checked_sub(1)?,
    );
    visiting.pop();
    range
}

/// F3 — projected-place tracing through locally-constructed values. Reading
/// `_t.π` resolves through `_t`'s whole-local defs by one of four lanes, all
/// fail-closed to `None`:
///
///   * UNIQUE `Use` def (`_t = copy X.ρ; read _t.π`): PROJECTION REBASE to
///     `X.ρ.π`, recursing at the copy's block. Sound: the temp is
///     single-assignment (and `float_whole_local_defs` already refused every
///     projected-write / aliasing channel), so every read of `_t.π` yields the
///     value `X.ρ.π` held at the copy — and `float_range`'s claim for the
///     rebased place is a whole-execution enclosure, which contains that value
///     in particular. This is the one-arm fold that connects rustc's
///     materialized field-copy temps (`_3 = copy (_1.0)`) back to contract
///     chains (`a.0.1`) and enum payload hops (`_4 = copy _2@1.0`).
///   * UNIQUE `Call` def: F6b per-suffix callee trace — evaluate `_0.π` inside
///     the callee's extracted body under caller-derived argument intervals
///     (`float_callee_trace_range`).
///   * `Downcast(v)` first projection: enum payload hull over the variant-`v`
///     construction defs (`float_enum_payload_range`).
///   * Aggregate defs (`Aggregate(kind, ops)`, or a unique `Repeat`): per-field
///     recursion into the element operand with the remaining projections
///     REBASED onto it. ONE def or MANY: the hull over every def's element is
///     sound by the same init-before-use argument as the whole-local multi-def
///     hull (any read yields SOME def's frozen element value), PROVIDED every
///     def is an `Aggregate` of the SAME shape (same kind, same variant/union
///     overlay, same field count) — positional `Field(k)` on differently-shaped
///     defs denotes differently-typed slots and is not field-decomposable, so
///     any shape mismatch (or any non-`Aggregate` def in the set) refuses.
///
/// Every element operand is read AT ITS OWN CONSTRUCTION BLOCK, so its guards
/// apply there; its value is frozen into the aggregate (projected stores,
/// `&mut` channels, and `SetDiscriminant`/`Deinit` were refused by
/// `float_whole_local_defs`), making the traced bound valid at every later
/// read of `_t.π`.
pub(super) fn float_aggregate_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    block_id: Option<BlockId>,
    place: &Place,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    let local = place.local;
    if visiting.contains(&local) {
        return None;
    }
    // SOUNDNESS: a parameter's ENTRY value is a statement-invisible extra def
    // — a read before the body write sees the caller's aggregate, not the
    // locally-constructed one — so no def-set lane below can ever hold
    // for a formal parameter (mirrors the whole-local arm's discipline).
    if local >= 1 && local <= ctx.func.body.arg_count {
        return None;
    }
    // Flow-sensitive masked-init lane: `float_whole_local_defs` poisons a local
    // written by ANY projected store, but a read of element `m.<elem>` still
    // sees `m`'s single Call-init value when no aliasing store can reach the
    // read block (`m = f(); m.cols[k] = ..` — the `m.cols[k]` READ that feeds
    // that store sees the init). Fail-closed; only fires with a known read block.
    if let Some(read_block) = block_id
        && let Some(range) =
            float_masked_init_call_element_range(ctx, mode, place, read_block, visiting, fuel)
    {
        return Some(range);
    }
    let defs = float_whole_local_defs(ctx.func, local)?;
    // Unique-def forwarding lanes (Use rebase / per-suffix callee trace).
    match defs.as_slice() {
        [
            FloatLocalDef::Rvalue {
                block,
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
            },
        ] => {
            let mut rebased = src.clone();
            rebased.projections.extend_from_slice(&place.projections);
            visiting.push(local);
            let range =
                float_range(ctx, mode, Some(*block), &Operand::Copy(rebased), visiting, fuel - 1);
            visiting.pop();
            return range;
        }
        [FloatLocalDef::Call { block, callee, args }] => {
            visiting.push(local);
            let range = float_callee_trace_range(
                ctx,
                *block,
                callee,
                args,
                &place.projections,
                visiting,
                fuel - 1,
            );
            visiting.pop();
            return range;
        }
        // `[op; n]` (unique def only): EVERY in-bounds element is `op`'s value
        // (an out-of-bounds read panics before producing one), so any index
        // projection resolves to `op`.
        [FloatLocalDef::Rvalue { block, rvalue: Rvalue::Repeat(op, _) }] => {
            let rest = match place.projections.first()? {
                Projection::Index(_) | Projection::ConstantIndex { .. } => &place.projections[1..],
                _ => return None,
            };
            visiting.push(local);
            let range = float_element_range(ctx, mode, *block, op, rest, visiting, fuel);
            visiting.pop();
            return range;
        }
        [] => return None,
        _ => {}
    }
    // Multi-def HULL over CALL and whole-local USE-copy defs. A reused local
    // slot commonly carries heterogeneous defs — `look_at_rh`'s basis vector
    // `local_5` is a `Vec3::new(..)` CALL on one path and a `Use(Copy(_9))` on
    // another (rustc slot reuse across the f/s/u chain); `row(r)`'s four arms
    // are all `Vec4::new` CALLs. Any read yields SOME def's frozen value — the
    // same init-before-use argument as the Aggregate hull below — and each
    // def's per-suffix trace is a whole-execution enclosure of THAT def's value
    // (evaluated at its OWN block, under its own dominating guards), so the hull
    // over every def encloses every read. Every def must be a CALL (per-suffix
    // F6b callee trace) or a whole-local USE-copy (`_5 = copy(_9)` → rebase the
    // projection onto `_9` and recurse); ANY other def shape (Aggregate — which
    // the same-shape aggregate lane below handles when uniform — or a projected
    // store, or an untraceable def) poisons the lane and it falls through
    // fail-closed. Guarded by `place_source_is_stable` (checked above): no def
    // reaches a mutably-borrowed / raw-escaped local.
    let hullable = defs.len() > 1
        && defs.iter().all(|d| {
            matches!(
                d,
                FloatLocalDef::Call { .. }
                    | FloatLocalDef::Rvalue {
                        rvalue: Rvalue::Use(Operand::Copy(_) | Operand::Move(_)),
                        ..
                    }
            )
        });
    if hullable {
        visiting.push(local);
        let mut hull: Option<(f64, f64)> = None;
        let mut every_def_traced = true;
        for def in &defs {
            let range = match def {
                FloatLocalDef::Call { block, callee, args } => float_callee_trace_range(
                    ctx,
                    *block,
                    callee,
                    args,
                    &place.projections,
                    visiting,
                    fuel - 1,
                ),
                FloatLocalDef::Rvalue {
                    block,
                    rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                } => {
                    // Whole-local copy: rebase the read's projection chain onto
                    // the copied-from place and re-evaluate at the copy's block.
                    let mut rebased = src.clone();
                    rebased.projections.extend_from_slice(&place.projections);
                    float_range(
                        ctx,
                        mode,
                        Some(*block),
                        &Operand::Copy(rebased),
                        visiting,
                        fuel - 1,
                    )
                }
                _ => None,
            };
            let Some((lo, hi)) = range else {
                every_def_traced = false;
                break;
            };
            hull = Some(match hull {
                None => (lo, hi),
                Some((l, h)) => (l.min(lo), h.max(hi)),
            });
        }
        visiting.pop();
        return if every_def_traced { hull } else { None };
    }
    // Enum payload reads (`_t@v.k…`) route to the variant-selecting hull.
    if let Some(Projection::Downcast(v)) = place.projections.first() {
        return float_enum_payload_range(ctx, mode, place, *v, visiting, fuel);
    }
    // Per-field HULL over one-or-many SAME-SHAPE Aggregate defs.
    let FloatLocalDef::Rvalue { rvalue: Rvalue::Aggregate(first_kind, first_ops), .. } = &defs[0]
    else {
        return None;
    };
    // Resolve the element slot ONCE from the (shared) kind + first projection.
    let k = match (first_kind, place.projections.first()?) {
        (AggregateKind::Tuple, Projection::Field(k)) => *k,
        // ADT: positional fields of variant 0 only; enum payloads
        // (variant != 0 needs a Downcast anyway, handled above) and unions
        // (`active_field`) fail closed.
        (AggregateKind::Adt { variant: 0, active_field: None, .. }, Projection::Field(k)) => *k,
        // Array literal: a compile-time-constant element index.
        (AggregateKind::Array, Projection::Index(i)) => crate::index_local_const(ctx.func, *i)?,
        (AggregateKind::Array, Projection::ConstantIndex { offset, from_end: false, .. }) => {
            *offset
        }
        _ => return None,
    };
    let rest = &place.projections[1..];
    let arity = first_ops.len();
    visiting.push(local);
    let mut hull: Option<(f64, f64)> = None;
    let mut every_def_bounded = true;
    for def in &defs {
        // EVERY def must be an Aggregate of the SAME shape; one Call/Use/
        // mismatched def poisons the whole hull (its slot `k` is not the same
        // frozen component, or not a component at all).
        let FloatLocalDef::Rvalue { block, rvalue: Rvalue::Aggregate(kind, ops) } = def else {
            every_def_bounded = false;
            break;
        };
        if !aggregate_same_shape(first_kind, kind) || ops.len() != arity {
            every_def_bounded = false;
            break;
        }
        let range = ops.get(k).and_then(|element| {
            float_element_range(ctx, mode, *block, element, rest, visiting, fuel)
        });
        match (range, &mut hull) {
            (None, _) => {
                every_def_bounded = false;
                break;
            }
            (Some((l, h)), Some((hl, hh))) => {
                *hl = hl.min(l);
                *hh = hh.max(h);
            }
            (Some(range), None) => hull = Some(range),
        }
    }
    visiting.pop();
    if every_def_bounded { hull } else { None }
}

/// One aggregate ELEMENT's interval, read at its construction block with the
/// remaining projections rebased onto the operand (the F3 recursion step,
/// shared by the unique-`Repeat`, multi-def-hull, and enum-payload lanes).
pub(super) fn float_element_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    def_block: BlockId,
    element: &Operand,
    rest: &[Projection],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    match (element, rest.is_empty()) {
        (Operand::Constant(_), true) => {
            float_range(ctx, mode, Some(def_block), element, visiting, fuel - 1)
        }
        (Operand::Constant(_), false) => None,
        (Operand::Copy(p) | Operand::Move(p), _) => {
            let mut rebased = p.clone();
            rebased.projections.extend_from_slice(rest);
            float_range(ctx, mode, Some(def_block), &Operand::Copy(rebased), visiting, fuel - 1)
        }
        _ => None,
    }
}

/// Shape identity for the multi-def per-field hull: identical aggregate KIND
/// — Tuple/Tuple, Array/Array, or ADT with the same name, variant, and union
/// overlay. Everything else (closures, coroutines, cross-kind pairs) is not
/// field-decomposable across defs and fails closed.
pub(super) fn aggregate_same_shape(a: &AggregateKind, b: &AggregateKind) -> bool {
    match (a, b) {
        (AggregateKind::Tuple, AggregateKind::Tuple) => true,
        (AggregateKind::Array, AggregateKind::Array) => true,
        (
            AggregateKind::Adt { name: an, variant: av, active_field: af, args: aa },
            AggregateKind::Adt { name: bn, variant: bv, active_field: bf, args: ba },
        ) => an == bn && av == bv && af == bf && aa == ba,
        _ => false,
    }
}

/// F6b/enum — the payload hull for a `Downcast` read `_t@v.k.π`.
///
/// SOUNDNESS. `float_whole_local_defs` has already refused SetDiscriminant/
/// Deinit, projected stores, and `&mut` channels, so `_t`'s discriminant and
/// payload are established ONLY by whole-value construction defs (or
/// whole-local copies of such — `collect_adt_construction_defs` recurses
/// through those, since a copied value is init-before-use one of the source's
/// construction values). A `Downcast(v)` read is DEFINED only on executions
/// where the discriminant IS `v` (MIR semantics; a mismatched downcast is UB,
/// about which this lane — like the const-index panic case — claims nothing),
/// and every construction def stores a complete value whose discriminant is
/// its `Aggregate` variant. So on every defined execution the value read came
/// from SOME variant-`v` def, and the hull over the variant-`v` defs' `k`-th
/// operands (each frozen at ITS construction block) encloses it. Defs of other
/// variants are therefore excluded from the hull; if NO variant-`v` def
/// exists the read is never defined and no claim is made (`None`). Any
/// non-construction def (a Call, a projected copy, a parameter source with
/// its invisible entry def) refuses the whole collection — fail-closed.
pub(super) fn float_enum_payload_range(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    place: &Place,
    variant: usize,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    let Some(Projection::Field(k)) = place.projections.get(1) else {
        return None;
    };
    let rest = &place.projections[2..];
    let mut construction_defs: Vec<(BlockId, usize, &[Operand])> = Vec::new();
    let mut seen: Vec<usize> = Vec::new();
    collect_adt_construction_defs(ctx.func, place.local, &mut seen, fuel, &mut construction_defs)?;
    let selected: Vec<&(BlockId, usize, &[Operand])> =
        construction_defs.iter().filter(|(_, w, _)| *w == variant).collect();
    if selected.is_empty() {
        return None;
    }
    visiting.push(place.local);
    let mut hull: Option<(f64, f64)> = None;
    let mut every_def_bounded = true;
    for (def_block, _, ops) in selected {
        let range = ops.get(*k).and_then(|element| {
            float_element_range(ctx, mode, *def_block, element, rest, visiting, fuel)
        });
        match (range, &mut hull) {
            (None, _) => {
                every_def_bounded = false;
                break;
            }
            (Some((l, h)), Some((hl, hh))) => {
                *hl = hl.min(l);
                *hh = hh.max(h);
            }
            (Some(range), None) => hull = Some(range),
        }
    }
    visiting.pop();
    if every_def_bounded { hull } else { None }
}

/// Flatten the ADT CONSTRUCTION defs feeding `local` (see
/// [`float_enum_payload_range`] for the value model): every whole-local def
/// must be an `Aggregate(Adt { active_field: None })` of ANY variant, or a
/// whole-local `Use` copy of a NON-PARAMETER local that itself flattens.
/// Anything else — Call defs, projected-source copies, parameter sources
/// (their entry value is a statement-invisible extra def), defless locals,
/// union overlays, revisited locals, exhausted fuel — refuses with `None`.
pub(super) fn collect_adt_construction_defs<'f>(
    func: &'f VerifiableFunction,
    local: usize,
    seen: &mut Vec<usize>,
    fuel: u32,
    out: &mut Vec<(BlockId, usize, &'f [Operand])>,
) -> Option<()> {
    if fuel == 0 || seen.contains(&local) {
        return None;
    }
    if local >= 1 && local <= func.body.arg_count {
        return None;
    }
    seen.push(local);
    let defs = float_whole_local_defs(func, local)?;
    if defs.is_empty() {
        return None;
    }
    for def in defs {
        match def {
            FloatLocalDef::Rvalue {
                block,
                rvalue:
                    Rvalue::Aggregate(AggregateKind::Adt { variant, active_field: None, .. }, ops),
            } => out.push((block, *variant, ops.as_slice())),
            FloatLocalDef::Rvalue {
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            } if src.projections.is_empty() => {
                collect_adt_construction_defs(func, src.local, seen, fuel - 1, out)?;
            }
            _ => return None,
        }
    }
    Some(())
}

/// F2 — dominating float-guard bounds for a PLAIN-local place read at
/// `block_id`: constants `c` with `value >= c` (`.0`) / `value <= c` (`.1`)
/// drawn from POSITIVE fp-ordering facts present on EVERY enumerated path into
/// the block.
///
/// SOUNDNESS (mirrors `v2_bv_mul_dominating_guard_constraints`):
///   * dominance = fact ∈ every recorded path (`FloatRangeCtx::dominating_facts`;
///     saturation/cap-overflow empty the intersection);
///   * the guard resolution itself (`guards::guard_to_formula` →
///     `latest_same_block_bool_definition`) already withholds stale
///     comparisons (`compared_operand_reassigned_after`,
///     `value_local_is_unstable` on the compared operands);
///   * the read local must ALSO be value-stable and not assigned in the
///     reading block (the BV lane's per-operand staleness);
///   * a TRUE fp comparison implies the compared value was ORDERED — the NaN
///     -freedom license. `Not(…)`-wrapped comparisons are deliberately NOT
///     inverted: `¬(x > c)` is satisfied by a NaN, so a false-edge fact yields
///     NO bound (reading it as `x <= c` would be a NaN-driven false-proof
///     channel);
///   * strict facts are weakened to closed bounds (`x > c ⇒ x ∈ [c, …]`),
///     sound for interval containment; the Div consumer separately requires a
///     STRICTLY positive floor, which `c > 0.0` supplies (`x > c ⇒ |x| >= c`,
///     and even `> c`).
pub(super) fn float_guard_bounds(
    ctx: &FloatRangeCtx<'_>,
    block_id: BlockId,
    place: &Place,
) -> (Option<f64>, Option<f64>) {
    let none = (None, None);
    if !place.projections.is_empty() {
        return none;
    }
    if guards::value_local_is_unstable(ctx.func, place.local) {
        return none;
    }
    let Some(block) = ctx.func.body.blocks.get(block_id.0) else { return none };
    if block.id != block_id {
        return none;
    }
    if block
        .stmts
        .iter()
        .any(|stmt| matches!(stmt, Statement::Assign { place: p, .. } if p.local == place.local))
    {
        return none;
    }
    let facts = ctx.dominating_facts(block_id);
    if facts.is_empty() {
        return none;
    }
    let names = ctx.guard_alias_names(place);
    let mut lo: Option<f64> = None;
    let mut hi: Option<f64> = None;
    for fact in facts.iter() {
        for leaf in v2_flatten_guard_conjuncts(fact) {
            let Some((name, cmp, c)) = float_ordering_fact(leaf) else { continue };
            if !names.iter().any(|n| n == name) {
                continue;
            }
            match cmp {
                BvGuardCmp::Ge | BvGuardCmp::Gt => lo = Some(lo.map_or(c, |cur: f64| cur.max(c))),
                BvGuardCmp::Le | BvGuardCmp::Lt => hi = Some(hi.map_or(c, |cur: f64| cur.min(c))),
                // fp.eq TRUE ⇒ ordered and numerically equal (±0 collapse is a
                // value identity) — both sides pinned.
                BvGuardCmp::Eq => {
                    lo = Some(lo.map_or(c, |cur: f64| cur.max(c)));
                    hi = Some(hi.map_or(c, |cur: f64| cur.min(c)));
                }
            }
        }
    }
    (lo, hi)
}

/// Read a POSITIVE fp-ordering fact (the `guards::float_binop_to_formula`
/// shape) as `<var-name> CMP <finite f64 literal>`, either orientation
/// normalized to the var on the left. `Not(…)` is deliberately unmatched — see
/// [`float_guard_bounds`]'s NaN note.
pub(super) fn float_ordering_fact(fact: &Formula) -> Option<(&str, BvGuardCmp, f64)> {
    use BvGuardCmp::{Eq, Ge, Gt, Le, Lt};
    let (a, b, cmp, mirrored) = match fact {
        Formula::FpLt(a, b) => (a, b, Lt, Gt),
        Formula::FpLe(a, b) => (a, b, Le, Ge),
        Formula::FpGt(a, b) => (a, b, Gt, Lt),
        Formula::FpGe(a, b) => (a, b, Ge, Le),
        Formula::FpEq(a, b) => (a, b, Eq, Eq),
        _ => return None,
    };
    if let (Some(name), Some(c)) = (fp_bits_var_name(a), fp_bits_f64_const(b)) {
        return Some((name, cmp, c));
    }
    if let (Some(c), Some(name)) = (fp_bits_f64_const(a), fp_bits_var_name(b)) {
        return Some((name, mirrored, c));
    }
    None
}

/// The bare var name inside a binary64 `FpFromBits` reinterpretation.
pub(super) fn fp_bits_var_name(f: &Formula) -> Option<&str> {
    match f {
        Formula::FpFromBits { bits, eb: 11, sb: 53 } => bits.var_name(),
        _ => None,
    }
}

/// The FINITE f64 value of a binary64 `FpFromBits(BitVec)` literal.
pub(super) fn fp_bits_f64_const(f: &Formula) -> Option<f64> {
    match f {
        Formula::FpFromBits { bits, eb: 11, sb: 53 } => match bits.as_ref() {
            Formula::BitVec { value, width: 64 } => {
                let v = f64::from_bits(u64::try_from(*value).ok()?);
                v.is_finite().then_some(v)
            }
            _ => None,
        },
        _ => None,
    }
}

/// A STRICTLY POSITIVE magnitude floor `m` for a divisor: whenever the value
/// participates in the division as an ordered (non-NaN) number, `|d| >= m > 0`
/// — so `|n / d| <= |n| / m` (fl-monotone), while a NaN divisor yields a NaN
/// quotient (never a fresh infinity). Sources: a sign-definite [`float_range`]
/// interval; else a ONE-SIDED dominating guard (`d > c` with `c > 0`, or
/// `d < c` with `c < 0` — the guard's truth implies orderedness, and the
/// closed floor `|d| >= |c|` holds for the strict and non-strict variants
/// alike). A guard-only floor admits `d = +inf`; the quotient is then ±0,
/// still inside the magnitude bound.
pub(super) fn float_divisor_magnitude_floor(
    ctx: &FloatRangeCtx<'_>,
    mode: FloatNanMode,
    block_id: Option<BlockId>,
    divisor: &Operand,
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<f64> {
    if let Some((lo, hi)) = float_range(ctx, mode, block_id, divisor, visiting, fuel) {
        if lo > 0.0 {
            return Some(lo);
        }
        if hi < 0.0 {
            return Some(-hi);
        }
    }
    let (Operand::Copy(place) | Operand::Move(place)) = divisor else {
        return None;
    };
    let (guard_lo, guard_hi) = float_guard_bounds(ctx, block_id?, place);
    if let Some(c) = guard_lo
        && c > 0.0
    {
        return Some(c);
    }
    if let Some(c) = guard_hi
        && c < 0.0
    {
        return Some(-c);
    }
    float_abs_guard_magnitude_floor(ctx, block_id?, place)
}

/// The abs-INDIRECTED divisor floor: `let m = t.abs(); if m > c { .. n / t }`
/// guards the ABS RESULT local, not the divisor place itself, so the direct
/// [`float_guard_bounds`] lookup above misses — yet this is THE idiomatic Rust
/// divisor guard. The floor half of [`float_abs_guard_magnitude_bounds`].
pub(super) fn float_abs_guard_magnitude_floor(
    ctx: &FloatRangeCtx<'_>,
    block_id: BlockId,
    divisor: &Place,
) -> Option<f64> {
    float_abs_guard_magnitude_bounds(ctx, block_id, divisor).0
}

/// Abs-guard magnitude evidence `(floor, cap)` for `place`, read at `block_id`
/// through its abs TEMPS: `let m = t.abs(); if m >= c && m <= C { … }` guards
/// the ABS RESULT local, not `t` itself. `|t| = m` on the guarded path: `abs`
/// is exact, and a NaN `t` makes `m` NaN, EVERY guard comparison FALSE, and
/// the path untaken — so a positive dominating floor on `m` is a magnitude
/// floor (and an orderedness license) on `t`, and a non-negative dominating
/// cap `C` on `m` bounds the SIGNED value to `[-C, C]` (the range source the
/// tracer's guard intersection consumes). Strict and non-strict facts alike
/// qualify — `float_guard_bounds` already weakens `>`/`<` to closed bounds,
/// sound for containment, and the Div consumer separately requires `c > 0`.
/// Sound only under BOTH value-identity disciplines:
///   * the abs result local's whole-local defs are EXACTLY the one recognized
///     std f64 `abs` call whose single argument is THIS place
///     ([`float_whole_local_defs`]'s poisoning covers projected stores and
///     `&mut` channels), and
///   * the place's BASE local is single-assignment or an unwritten
///     parameter (`float_whole_local_defs` len <= 1), so the value `abs` read
///     is the value the consuming op reads — a reseated local fails closed.
/// Multiple qualifying abs temps each yield sound evidence; the LARGEST floor
/// and the SMALLEST cap win. A negative cap is refused rather than read as an
/// empty interval: `m <= C < 0` can never be true of an abs result, so the
/// dominated block is unreachable and `None` claims nothing about it.
pub(super) fn float_abs_guard_magnitude_bounds(
    ctx: &FloatRangeCtx<'_>,
    block_id: BlockId,
    place: &Place,
) -> (Option<f64>, Option<f64>) {
    // Value stability between the abs read and the consuming op: a PARAMETER
    // base must have NO whole-local def at all (any reseat can interleave), a
    // non-parameter temp must be SINGLE-assignment (its one def precedes every
    // read by init-before-use). `float_whole_local_defs`'s poisoning already
    // rejects projected stores and `&mut` channels.
    let stable_base = |place: &Place| -> bool {
        // A raw-pointer-deref place (`(*p).2`) is never value-stable: an aliasing
        // `*mut` write is invisible to any base-local def scan (round-14 review).
        if place_reads_through_raw_ptr(ctx.func, place) {
            return false;
        }
        let Some(defs) = float_whole_local_defs(ctx.func, place.local) else { return false };
        let base_is_param = place.local >= 1 && place.local <= ctx.func.body.arg_count;
        if base_is_param { defs.is_empty() } else { defs.len() == 1 }
    };
    if !stable_base(place) {
        return (None, None);
    }
    // The consuming op often reads a COPY TEMP of the guarded value (`_t =
    // copy (*self).2; _q = 1.0 / _t`) while the abs call read the source place
    // directly — resolve the place through its single `Use(Copy|Move)` def so
    // both spell the same place. Sound: the temp is single-assignment (checked
    // above) and the RESOLVED source must pass the same stability discipline,
    // so temp and source provably hold the same value at every read.
    let resolve_to_source = |p: &Place| -> Option<Place> {
        if !p.projections.is_empty() {
            return None;
        }
        let defs = float_whole_local_defs(ctx.func, p.local)?;
        if let [
            FloatLocalDef::Rvalue {
                rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
                ..
            },
        ] = defs.as_slice()
            && stable_base(src)
        {
            Some((*src).clone())
        } else {
            None
        }
    };
    let mut candidates: Vec<Place> = vec![place.clone()];
    if let Some(src) = resolve_to_source(place) {
        candidates.push(src);
    }
    let mut floor: Option<f64> = None;
    let mut cap: Option<f64> = None;
    for block in &ctx.func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if fp_abs_call_width(callee) != Some(64) || !dest.projections.is_empty() {
            continue;
        }
        let [Operand::Copy(arg) | Operand::Move(arg)] = args.as_slice() else {
            continue;
        };
        // Match the abs ARG against a candidate DIRECTLY, or through its OWN
        // single stable copy-def source: the abs (`_6 = copy (*self).2`) and the
        // divide (`_7 = copy (*self).2`) frequently read the guarded field
        // through TWO DIFFERENT compiler-inserted copy temps, so canonicalizing
        // both to `(*self).2` is required for them to meet (Transform::inverse's
        // `1.0 / self.scale` under `self.scale.abs() > 1e-20`). Sound by the same
        // single-assignment + `stable_base` discipline that admits the divisor's
        // own source into `candidates`.
        let arg_matches = candidates.iter().any(|candidate| arg == candidate)
            || resolve_to_source(arg).is_some_and(|src| candidates.iter().any(|c| src == *c));
        if !arg_matches {
            continue;
        }
        // The abs temp must have NO other def than this call (a reseated temp
        // would stale the guard fact).
        match float_whole_local_defs(ctx.func, dest.local) {
            Some(defs) if defs.len() == 1 => {}
            _ => continue,
        }
        let (abs_lo, abs_hi) = float_guard_bounds(ctx, block_id, &Place::local(dest.local));
        if let Some(c) = abs_lo
            && c > 0.0
        {
            floor = Some(floor.map_or(c, |f: f64| f.max(c)));
        }
        if let Some(c) = abs_hi
            && c >= 0.0
        {
            cap = Some(cap.map_or(c, |f: f64| f.min(c)));
        }
    }
    (floor, cap)
}

/// Parse a σ-safe projection suffix (the `place_to_var_name` token grammar)
/// into projections: `*` → `Deref`, `.<digits>` → `Field`, `[<digits>]` → a
/// constant element index (`ConstantIndex { offset, min_length: offset + 1,
/// from_end: false }` — the minimal honest length claim; the denoted element
/// is the same). A runtime index `[_5]` or downcast `@1` names a
/// CALLEE-namespace local and must not reattach — `None` (fail-closed).
pub(super) fn parse_projection_suffix(suffix: &str) -> Option<Vec<Projection>> {
    let bytes = suffix.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'*' => {
                out.push(Projection::Deref);
                i += 1;
            }
            b'.' => {
                let start = i + 1;
                let mut end = start;
                while end < bytes.len() && bytes[end].is_ascii_digit() {
                    end += 1;
                }
                if end == start {
                    return None;
                }
                out.push(Projection::Field(suffix[start..end].parse().ok()?));
                i = end;
            }
            b'[' => {
                let start = i + 1;
                let mut end = start;
                while end < bytes.len() && bytes[end].is_ascii_digit() {
                    end += 1;
                }
                if end == start || end >= bytes.len() || bytes[end] != b']' {
                    return None;
                }
                let offset: usize = suffix[start..end].parse().ok()?;
                out.push(Projection::ConstantIndex {
                    offset,
                    min_length: offset.checked_add(1)?,
                    from_end: false,
                });
                i = end + 1;
            }
            _ => return None,
        }
    }
    (!out.is_empty()).then_some(out)
}

/// σ-suffix validator for `rebind_projected_actual`: the WELL-FORMED
/// `place_to_var_name` token sequence (`*` deref | `.<digits>` field |
/// `[<digits>]` const index)+. Replaces the old character-set check (same
/// accepts on every real render, plus the F4 bracket segments); anything else
/// — runtime `[_5]`, downcast `@1`, malformed tails — fails closed to the
/// fresh σ var.
pub(super) fn is_safe_projection_suffix(suffix: &str) -> bool {
    parse_projection_suffix(suffix).is_some()
}

/// Read a callee-precondition conjunct as `<float var> CMP <finite f64
/// literal>` (either orientation, normalized to the var on the left). The var
/// must be FLOAT-SORTED (the retyped contract spelling) and the literal an f64
/// `FpConst` (`formula_float_value` also folds a defensive `Neg`). Anything
/// else → `None`, and F5 then declines the WHOLE precondition (fail-closed).
/// F5 INT lane: decide a callee-precondition conjunct of the shape
/// `<Int var> CMP <Int literal>` at this callsite, `Some(true)` iff it provably
/// HOLDS for the σ-mapped actual, `Some(false)` iff it is an Int conjunct this
/// lane cannot prove (the caller then declines the whole precondition,
/// fail-closed), `None` iff the conjunct is not an Int comparison at all (the
/// float lane owns it).
///
/// Two proofs only:
/// * CONSTANT actual — compare the literal values.
/// * TYPE-RANGE tautology — the actual is a whole-local read of an integer
///   type whose ENTIRE value range satisfies the bound (`0 <= r` /
///   `r <= u64::MAX` on a `usize` formal, the contracts machinery's auto
///   requires). Holds for every well-typed value, no data-flow needed.
pub(super) fn int_pre_conjunct_holds(
    func: &VerifiableFunction,
    param_names: &[String],
    args: &[Operand],
    conjunct: &Formula,
) -> Option<bool> {
    use BvGuardCmp::{Ge, Gt, Le, Lt};
    let (a, b, cmp, mirrored) = match conjunct {
        Formula::Le(a, b) => (a, b, Le, Ge),
        Formula::Lt(a, b) => (a, b, Lt, Gt),
        Formula::Ge(a, b) => (a, b, Ge, Le),
        Formula::Gt(a, b) => (a, b, Gt, Lt),
        _ => return None,
    };
    fn int_var(f: &Formula) -> Option<&str> {
        if matches!(f.var_sort(), Some(Sort::Int)) { f.var_name() } else { None }
    }
    fn int_lit(f: &Formula) -> Option<i128> {
        match f {
            Formula::Int(v) => Some(*v),
            _ => None,
        }
    }
    let (var, cmp, c) = if let (Some(v), Some(c)) = (int_var(a), int_lit(b)) {
        (v, cmp, c)
    } else if let (Some(c), Some(v)) = (int_lit(a), int_var(b)) {
        (v, mirrored, c)
    } else {
        return None;
    };
    // Bare formal names only (a projected int var has no simple actual
    // mapping here — decline, fail-closed).
    let Some(idx) = param_names.iter().position(|p| p == var) else {
        return Some(false);
    };
    let holds_value = |k: i128| match cmp {
        Le => k <= c,
        Lt => k < c,
        Ge => k >= c,
        Gt => k > c,
        BvGuardCmp::Eq => false,
    };
    match args.get(idx) {
        Some(Operand::Constant(cv)) => {
            let k = match cv {
                ConstValue::Int(v) => *v,
                ConstValue::Uint(v, _) => match i128::try_from(*v) {
                    Ok(v) => v,
                    Err(_) => return Some(false),
                },
                _ => return Some(false),
            };
            Some(holds_value(k))
        }
        Some(Operand::Copy(place) | Operand::Move(place)) if place.projections.is_empty() => {
            // Type-range tautology: EVERY value of the actual's integer type
            // satisfies the bound.
            let ty = func.body.locals.get(place.local).map(|l| &l.ty)?;
            let (width, signed) = match ty {
                Ty::Int { width, signed } if *width < 128 && *width > 0 => (*width, *signed),
                Ty::PtrSizedInt { signed } => (64, *signed),
                _ => return Some(false),
            };
            let (ty_lo, ty_hi): (i128, i128) = if signed {
                (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
            } else {
                (0, (1i128 << width) - 1)
            };
            Some(holds_value(ty_lo) && holds_value(ty_hi))
        }
        _ => Some(false),
    }
}

pub(super) fn float_pre_var_const(f: &Formula) -> Option<(&str, BvGuardCmp, f64)> {
    use BvGuardCmp::{Ge, Gt, Le, Lt};
    let (a, b, cmp, mirrored) = match f {
        Formula::Le(a, b) => (a, b, Le, Ge),
        Formula::Lt(a, b) => (a, b, Lt, Gt),
        Formula::Ge(a, b) => (a, b, Ge, Le),
        Formula::Gt(a, b) => (a, b, Gt, Lt),
        _ => return None,
    };
    fn float_var(f: &Formula) -> Option<&str> {
        if matches!(f.var_sort(), Some(Sort::Float { .. })) { f.var_name() } else { None }
    }
    if let (Some(name), Some(c)) = (float_var(a), formula_float_value(b)) {
        return Some((name, cmp, c));
    }
    if let (Some(c), Some(name)) = (formula_float_value(a), float_var(b)) {
        return Some((name, mirrored, c));
    }
    None
}

/// F5 — structural caller-precondition discharge by interval dominance: TRUE
/// iff EVERY conjunct of the callee precondition is a float literal bound over
/// a formal-rooted var, each var carries BOTH a lower and an upper conjunct,
/// and the σ-mapped ACTUAL's proven interval (strict NaN-free mode — a NaN
/// actual falsifies every ordering) satisfies each conjunct with EXACT f64
/// endpoint comparisons — strict requirements (`Lt`/`Gt`) need strictly
/// interior endpoints. A `true` here means the precondition provably HOLDS on
/// every execution reaching `call_block`, so the caller-side obligation cannot
/// fire; any unmatched shape returns `false` and the obligation is emitted as
/// today (fail-closed).
/// Trust (R1 completeness #4, base case): does EVERY call site to `callee` in
/// `func` structurally establish `callee`'s precondition by interval dominance
/// — the exact condition under which
/// [`generate_callsite_precondition_vcs_attributed`] suppresses the
/// obligation (F5)?
///
/// R1's base case needs this because a suppressed obligation is INDISTINGUISH-
/// ABLE from an absent one in the returned VC list, and the two have opposite
/// meanings: suppressed = statically proved here; absent = nothing known.
/// Returns `false` when the caller has no call site to `callee` at all, so an
/// unrelated caller can never be mistaken for a discharged one.
///
/// SOUNDNESS: this re-evaluates the SAME predicate on the SAME inputs the
/// suppressor used. It reports a static proof, never the absence of one.
pub fn all_callsites_precondition_dominated(
    func: &VerifiableFunction,
    summaries: &crate::modular::SummaryDatabase,
    callee: &str,
) -> bool {
    let float_ctx = FloatRangeCtx::new(func, Some(summaries));
    let mut saw_site = false;
    for block in &func.body.blocks {
        let Terminator::Call { func: callee_name, args, .. } = &block.terminator else {
            continue;
        };
        if callee_name != callee {
            continue;
        }
        let Some(summary) = summaries.get(callee_name) else {
            return false;
        };
        if summary.param_names.len() != args.len() {
            return false;
        }
        for precondition in &summary.preconditions {
            if !precondition_interval_dominance(
                &float_ctx,
                block.id,
                precondition,
                &summary.param_names,
                args,
                &mut Vec::new(),
                FLOAT_EXP_BOUND_FUEL,
            ) {
                return false;
            }
        }
        saw_site = true;
    }
    saw_site
}

pub(super) fn precondition_interval_dominance(
    ctx: &FloatRangeCtx<'_>,
    call_block: BlockId,
    precondition: &Formula,
    param_names: &[String],
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> bool {
    if fuel == 0 || param_names.len() != args.len() {
        return false;
    }
    let conjuncts = v2_flatten_guard_conjuncts(precondition);
    if conjuncts.is_empty() {
        return false;
    }
    let mut ranges: FxHashMap<String, (f64, f64)> = FxHashMap::default();
    let mut lower_seen: FxHashSet<String> = FxHashSet::default();
    let mut upper_seen: FxHashSet<String> = FxHashSet::default();
    for conjunct in conjuncts {
        // INT lane (the contracts machinery's auto type-range requires,
        // `0 <= r <= <uN>::MAX` on an integer formal): dischargeable when the
        // σ-mapped actual is a CONSTANT satisfying the bound literally, or a
        // place whose INTEGER TYPE's full value range sits inside the bound (a
        // type-range tautology holds for every well-typed value — sound
        // unconditionally; anything else falls through fail-closed). Handled
        // per-conjunct with no two-sidedness demand: an int conjunct proven
        // this way holds on its own, unlike the float lane whose interval
        // tracer requires two-sided NaN-excluding bounds.
        if let Some(holds) = int_pre_conjunct_holds(ctx.func, param_names, args, conjunct) {
            if holds {
                continue;
            }
            return false;
        }
        let Some((var, cmp, c)) = float_pre_var_const(conjunct) else { return false };
        let (lo, hi) = match ranges.get(var) {
            Some(range) => *range,
            None => {
                let Some(range) =
                    dominance_actual_range(ctx, call_block, var, param_names, args, visiting, fuel)
                else {
                    return false;
                };
                ranges.insert(var.to_string(), range);
                range
            }
        };
        let holds = match cmp {
            BvGuardCmp::Le => hi <= c,
            BvGuardCmp::Lt => hi < c,
            BvGuardCmp::Ge => lo >= c,
            BvGuardCmp::Gt => lo > c,
            BvGuardCmp::Eq => false, // not produced by float_pre_var_const
        };
        if !holds {
            return false;
        }
        match cmp {
            BvGuardCmp::Le | BvGuardCmp::Lt => {
                upper_seen.insert(var.to_string());
            }
            BvGuardCmp::Ge | BvGuardCmp::Gt => {
                lower_seen.insert(var.to_string());
            }
            BvGuardCmp::Eq => {}
        }
    }
    // BOTH sides required per var: this lane is deliberately restricted to the
    // audited two-sided magnitude-bound contract shape.
    ranges.keys().all(|var| lower_seen.contains(var) && upper_seen.contains(var))
}

/// Resolve one F5 precondition var to the ACTUAL's proven interval at the call
/// block: split the var at its first projection token, map the formal to its
/// argument operand, reattach the parsed suffix to the actual's PLACE (a
/// constant actual admits only an empty suffix — `float_range` evaluates it
/// directly; an opaque actual fails closed).
pub(super) fn dominance_actual_range(
    ctx: &FloatRangeCtx<'_>,
    call_block: BlockId,
    var: &str,
    param_names: &[String],
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> Option<(f64, f64)> {
    let (formal, suffix) = match split_projection_base(var) {
        Some((base, suffix)) => (base, suffix),
        None => (var, ""),
    };
    let index = param_names.iter().position(|p| p == formal)?;
    let actual = &args[index];
    if suffix.is_empty() {
        return float_range(
            ctx,
            FloatNanMode::Forbid,
            Some(call_block),
            actual,
            visiting,
            fuel - 1,
        );
    }
    let (Operand::Copy(base_place) | Operand::Move(base_place)) = actual else {
        return None;
    };
    let mut place = base_place.clone();
    place.projections.extend(parse_projection_suffix(suffix)?);
    float_range(
        ctx,
        FloatNanMode::Forbid,
        Some(call_block),
        &Operand::Copy(place),
        visiting,
        fuel - 1,
    )
}

/// F6 derivation half — the hull of [`float_range`] (STRICT NaN-free mode)
/// over the RETURN local's defs: an interval containing every possible return
/// value of an f64-returning function, valid whenever the function's own gated
/// preconditions hold (`contract_range` reads them during the trace).
/// Aggregate returns (structs/tuples of floats) are deferred — `None`. No flow
/// context is needed at the top (`block_id: None`); each `_0` def is still
/// evaluated under ITS OWN block's dominating guards. Recursion is the
/// CALLER's concern (`compute_summary` passes `is_recursive` and skips this).
pub fn derive_float_result_range(func: &VerifiableFunction) -> Option<(f64, f64)> {
    if !matches!(func.body.return_ty, Ty::Float { width: 64 }) {
        return None;
    }
    let ctx = FloatRangeCtx::new(func, None);
    float_range(
        &ctx,
        FloatNanMode::Forbid,
        None,
        &Operand::Copy(Place::local(0)),
        &mut Vec::new(),
        FLOAT_EXP_BOUND_FUEL,
    )
}
