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
            if uses > 1 || uses != int_cast_uses {
                return false;
            }
        }
        if let Terminator::Call { args, .. } = &block.terminator {
            uses += args.iter().filter(|op| is_dest(op, dest)).count();
        }
        if let Terminator::SwitchInt { discr, .. } = &block.terminator {
            uses += usize::from(is_dest(discr, dest));
        }
        if uses > 1 || uses != int_cast_uses {
            return false;
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
pub(super) fn float_exp_bound(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<u32> {
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
pub(super) fn is_unit_bounded_float_call(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> bool {
    matches!(f64_std_method_name(callee, callee_key), Some("cos" | "sin" | "tanh"))
}

/// The exact f64 representation of a binary32 or binary64 literal value.
/// Arithmetic consumers must separately enclose rounding at the operation width.
pub(super) fn f64_const_value(c: &ConstValue) -> Option<f64> {
    match c {
        ConstValue::Float(v) => Some(*v),
        ConstValue::FloatBits { bits, width: 64 } => u64::try_from(*bits).ok().map(f64::from_bits),
        // binary32 widens to f64 EXACTLY (every binary32 value is a binary64
        // value). Admitted since 2026-09-17, when the discharge that consumes
        // these intervals became width-aware; before that, an f32 bound was
        // measured against f64-scaled thresholds and discharged an add that
        // overflowed. See `v2_float_binop_cannot_overflow_at`.
        ConstValue::FloatBits { bits, width: 32 } => {
            u32::try_from(*bits).ok().map(|b| f64::from(f32::from_bits(b)))
        }
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

/// Every inherent `f64` method [`float_call_range`] models, by the exact path the
/// extractor renders: `(path, method)`. Measured on `scratchpad/stage1-w11fix`
/// (2026-10-04): `abs`, `min`, `max`, `clamp` are `core::f64::<impl f64>::{m}`;
/// `sin`, `cos`, `tanh`, `sqrt` are `std::f64::<impl f64>::{m}`. Both roots are
/// listed for each, so a method moving between `core` and `std` keeps its arm.
/// The owner `<impl f64>` has no generic parameter, which is what lets an exact
/// path name the item (the `sysroot_exact_path` doc rule).
const F64_STD_METHOD_PATHS: &[(&str, &str)] = &[
    ("core::f64::<impl f64>::sqrt", "sqrt"),
    ("std::f64::<impl f64>::sqrt", "sqrt"),
    ("core::f64::<impl f64>::abs", "abs"),
    ("std::f64::<impl f64>::abs", "abs"),
    ("core::f64::<impl f64>::min", "min"),
    ("std::f64::<impl f64>::min", "min"),
    ("core::f64::<impl f64>::max", "max"),
    ("std::f64::<impl f64>::max", "max"),
    ("core::f64::<impl f64>::clamp", "clamp"),
    ("std::f64::<impl f64>::clamp", "clamp"),
    ("core::f64::<impl f64>::sin", "sin"),
    ("std::f64::<impl f64>::sin", "sin"),
    ("core::f64::<impl f64>::cos", "cos"),
    ("std::f64::<impl f64>::cos", "cos"),
    ("core::f64::<impl f64>::tanh", "tanh"),
    ("std::f64::<impl f64>::tanh", "tanh"),
];

/// The std `f64` method (`clamp`, `sqrt`, `abs`, `min`, `max`, `sin`, `cos`,
/// `tanh`) that `callee` IS, or `None`. A user-defined `mymod::sqrt` /
/// `mymod::clamp` has arbitrary semantics and must NEVER match (a false-PROVE
/// channel); `Ord::clamp` is not an `<impl f64>` item and is excluded with it.
///
/// Trust (2026-10-04, NUM-METHOD-ANCHOR-1): the callee must be DEFINED in a real
/// sysroot crate (its compiler-minted `callee_key`) and its rendering must be
/// EXACTLY one of [`F64_STD_METHOD_PATHS`], one trailing turbofish allowed
/// (`trust_types::callee_key::sysroot_exact_path`). The test this replaces wanted a
/// `core`/`std`/`alloc` root and `::f64::` ANYWHERE, then took the method from the
/// LAST segment with its `<…>` cut off. `core::cmp::max_by_key::<f64, {closure},
/// PhantomData<m::f64::cos<1>>>` — a real core callee whose generic argument names a
/// user type `m::f64::cos<1>` — passed both halves and came out as `cos`, so its
/// unbounded result got the `[-1, 1]` interval and `v * 4.0` lost its
/// `float_overflow_to_infinity (Mul)` row (measured on `scratchpad/stage1-w11fix`;
/// `lie1(0.5, 1e308)` returns `inf`).
pub(super) fn f64_std_method_name(
    callee: &str,
    callee_key: Option<&trust_types::CalleeKey>,
) -> Option<&'static str> {
    if !callee_key.is_some_and(|k| k.krate_is_real_sysroot) {
        return None;
    }
    F64_STD_METHOD_PATHS
        .iter()
        .find(|(path, _)| {
            trust_types::callee_key::sysroot_exact_path(callee_key, callee, &[*path]).is_some()
        })
        .map(|(_, method)| *method)
}

/// `core::time::Duration::as_secs_f64` / `as_secs_f32` (and the `std::time`
/// re-export spelling), by exact path (NUM-METHOD-ANCHOR-1). `Duration` has no
/// generic parameter. Measured: `d.as_secs_f64()` renders
/// `core::time::Duration::as_secs_f64`, keyed to `core`.
const DURATION_AS_SECS_PATHS: &[&str] = &[
    "core::time::Duration::as_secs_f64",
    "core::time::Duration::as_secs_f32",
    "std::time::Duration::as_secs_f64",
    "std::time::Duration::as_secs_f32",
];

/// The compiler-minted key of the call that terminates `block`, and whether that
/// call's destination is a float-typed place — what [`float_call_range`] needs to
/// name a recognized std callee (NUM-METHOD-ANCHOR-1). `(None, false)` when the
/// block does not end in a call.
fn float_call_site_key(
    func: &VerifiableFunction,
    block: BlockId,
) -> (Option<&trust_types::CalleeKey>, bool) {
    let Some(Terminator::Call { callee_key, dest, .. }) = func
        .body
        .blocks
        .get(block.0)
        .filter(|b| b.id == block)
        .or_else(|| func.body.blocks.iter().find(|b| b.id == block))
        .map(|b| &b.terminator)
    else {
        return (None, false);
    };
    let dest_is_float =
        crate::place_ty_cow(func, dest).is_some_and(|ty| matches!(ty.as_ref(), Ty::Float { .. }));
    (callee_key.as_ref(), dest_is_float)
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
    let name = canonicalize_contract_index_segments_owned(crate::place_to_var_name(func, place));
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
pub(super) fn contract_two_sided_range(
    func: &VerifiableFunction,
    name: &str,
) -> Option<(f64, f64)> {
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
pub(super) fn canonicalize_contract_index_segments_owned(name: String) -> String {
    if !name.contains(";min=") {
        return name;
    }
    canonicalize_contract_index_segments(&name)
}

pub(super) fn canonicalize_contract_index_segments(name: &str) -> String {
    if !name.contains(";min=") {
        return name.to_string();
    }
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
    let mut token: Option<&str> = None;
    let mut search = name;
    while let Some(pos) = search.find("[_") {
        let rest = &search[pos + 2..];
        let end = rest.find(']')?;
        let digits = &rest[..end];
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let this = &search[pos..pos + 3 + end];
        match token {
            Some(existing) if existing != this => return None,
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
        match crate::place_prefix_ty_cow(func, place.local, &place.projections[..pos])?.as_ref() {
            Ty::Array { len: l, .. } => len = Some(len.map_or(*l, |cur| cur.min(*l))),
            _ => return None, // slice: no static length — fail closed
        }
    }
    let len = len?;
    if len == 0 {
        return None;
    }
    // ONE pass over the contract, not one lookup per lane: every bound whose
    // variable is this read's name with the runtime index replaced by a lane
    // literal `[k]` (`k < len`, at EVERY position the token occupies) is
    // accumulated under `k`. A lane with no mention has no bound, so fewer
    // mentioned lanes than `len` declines at once. Cost is linear in the
    // contract's text and never depends on `len`, which is a value (the
    // per-lane scan it replaces was capped at 64 lanes for that reason).
    let segments: Vec<&str> = name.split(token).collect();
    let lane_of = |var: &str| lane_of_element_name(var, &segments).filter(|lane| *lane < len);
    let mut lanes: FxHashMap<u64, (Option<f64>, Option<f64>)> = FxHashMap::default();
    for pre in &func.preconditions {
        collect_lane_magnitude_bounds(pre, &lane_of, &mut lanes);
    }
    if u64::try_from(lanes.len()).map_or(true, |mentioned| mentioned < len) {
        return None;
    }
    let mut lo = f64::INFINITY;
    let mut hi = f64::NEG_INFINITY;
    for (upper, lower) in lanes.values() {
        // `contract_two_sided_range`'s acceptance, lane by lane.
        let (u, l) = ((*upper)?, (*lower)?);
        if !(l.is_finite() && u.is_finite() && l <= u) {
            return None;
        }
        lo = lo.min(l);
        hi = hi.max(u);
    }
    Some((lo, hi))
}

/// The lane `k` for which `name` (a contract variable's name) is
/// `segments.join("[k]")`, i.e. the read's name with every occurrence of its
/// runtime-index token replaced by the literal `[k]` (the contract-side
/// spelling of `arr[k]`, decimal, no leading zero); `None` if `name` is not
/// such a name. Exactly the names `name.replace(token, &format!("[{k}]"))`
/// produces, found by one scan of `name` instead of by generating a name per
/// lane.
fn lane_of_element_name(name: &str, segments: &[&str]) -> Option<u64> {
    let (first, rest) = segments.split_first()?;
    let mut tail = name.strip_prefix(first)?;
    let mut lane: Option<&str> = None;
    for segment in rest {
        let inner = tail.strip_prefix('[')?;
        let end = inner.find(']')?;
        let digits = &inner[..end];
        let canonical = !digits.is_empty()
            && digits.bytes().all(|b| b.is_ascii_digit())
            && (digits == "0" || !digits.starts_with('0'));
        if !canonical || lane.is_some_and(|seen| seen != digits) {
            return None;
        }
        lane = Some(digits);
        tail = inner[end + 1..].strip_prefix(segment)?;
    }
    if !tail.is_empty() {
        return None;
    }
    lane?.parse().ok()
}

/// [`collect_magnitude_bounds`] for every lane at once: the same clauses, the
/// same side-of-the-comparison reading and the same tightening, keyed by the
/// lane `lane_of` reads off the bounded variable's name instead of by one fixed
/// name. For each lane `k` the accumulated pair is exactly what
/// `collect_magnitude_bounds(formula, name_of(k), ..)` accumulates, because a
/// clause's bounded side is a variable, whose numeric value is `None`, so a
/// clause never bounds two lanes.
fn collect_lane_magnitude_bounds(
    formula: &Formula,
    lane_of: &impl Fn(&str) -> Option<u64>,
    lanes: &mut FxHashMap<u64, (Option<f64>, Option<f64>)>,
) {
    fn named_lane(formula: &Formula, lane_of: &impl Fn(&str) -> Option<u64>) -> Option<u64> {
        match formula {
            Formula::Var(n, _) => lane_of(n),
            Formula::SymVar(sym, _) => lane_of(sym.as_str()),
            Formula::FpFromBits { bits, .. } => named_lane(bits, lane_of),
            _ => None,
        }
    }
    fn tighten(
        lanes: &mut FxHashMap<u64, (Option<f64>, Option<f64>)>,
        lane: u64,
        k: f64,
        is_upper: bool,
    ) {
        let (upper, lower) = lanes.entry(lane).or_insert((None, None));
        if is_upper {
            *upper = Some(upper.map_or(k, |cur| cur.min(k)));
        } else {
            *lower = Some(lower.map_or(k, |cur| cur.max(k)));
        }
    }
    match formula {
        Formula::And(items) => {
            for item in items {
                collect_lane_magnitude_bounds(item, lane_of, lanes);
            }
        }
        Formula::FpLe(a, b) | Formula::FpLt(a, b) | Formula::Le(a, b) | Formula::Lt(a, b) => {
            if let Some(lane) = named_lane(a, lane_of) {
                if let Some(k) = formula_numeric_value(b) {
                    tighten(lanes, lane, k, true);
                }
            } else if let Some(lane) = named_lane(b, lane_of)
                && let Some(k) = formula_numeric_value(a)
            {
                tighten(lanes, lane, k, false);
            }
        }
        Formula::FpGe(a, b) | Formula::FpGt(a, b) | Formula::Ge(a, b) | Formula::Gt(a, b) => {
            if let Some(lane) = named_lane(a, lane_of) {
                if let Some(k) = formula_numeric_value(b) {
                    tighten(lanes, lane, k, false);
                }
            } else if let Some(lane) = named_lane(b, lane_of)
                && let Some(k) = formula_numeric_value(a)
            {
                tighten(lanes, lane, k, true);
            }
        }
        _ => {}
    }
}

/// Whether formal-parameter local `base` keeps its ENTRY value at every read in
/// the body — i.e. it is never (whole-or-projected) written and no pointer that
/// can write it or what it points to is taken. Conservative twin of
/// `contract_assumption_gate::slice_param_length_is_stable` / the BV-mul lane's
/// `v2_local_assigned_anywhere`, but covering FIELD writes and pointer aliasing so
/// a `contract_exp_bound` magnitude claim over `self.x` cannot be defeated by a
/// body mutation of `self` (any field) between entry and use. Any write channel
/// returns false (no discharge; fail-closed).
///
/// The channel test is the POINTER rule (`path_defs::borrow_write_target`):
/// `&mut`, `&raw mut` and `&raw const` of ANY place rooted at `base`, a `Deref`
/// included, because the places this guards are what `base` POINTS TO
/// (`(*self).x`). Until 2026-09-30 it counted `&mut` / `&raw mut` only, and a
/// write through `&raw const (*s).x as *mut f64` — defined under Tree Borrows for
/// `s: &mut _` — left the entry contract bound on `s.x` in force, so
/// `s.x * 4.0` had its `FloatOverflowToInfinity` row removed on a body that
/// returns `inf` (tests/raw_const_float_scans.rs).
pub(super) fn param_place_is_entry_stable(func: &VerifiableFunction, base: usize) -> bool {
    !crate::any_local_write_candidate(func, &func.body.blocks, base, |block, item| match item {
        Some(stmt) => match stmt {
            Statement::Assign { place: dest, rvalue, .. } => {
                // `&raw const (*self).x` cast to `*mut` writes too (2026-10-08 H2:
                // `path_defs::borrow_write_target`).
                dest.local == base
                    || super::borrow_write_target(func, rvalue)
                        .is_some_and(|borrowed| borrowed.local == base)
            }
            Statement::SetDiscriminant { place: dest, .. } | Statement::Deinit { place: dest } => {
                dest.local == base
            }
            _ => false,
        },
        None => {
            // An Opaque terminator (inline `asm!` with out/inout operands) may write
            // ANY local invisibly — its out-operand places are not modeled here — so
            // a contract magnitude bound (and the round-13 BV witness hypothesis it
            // feeds) over `base` cannot be assumed stable across it. `float_whole_
            // local_defs` already poisons on the same channel; this is its
            // conservative twin, previously missing the arm (fail-closed).
            matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == base)
                || matches!(&block.terminator, Terminator::Opaque { .. })
        }
    })
}

/// The canonical projection chain of `projections` as a SCALAR f64 leaf of
/// `ty`, or `None` when it is not one. A leaf is reached through STRUCT fields
/// (`.i`, positional — the `place_to_var_name` / contract spelling), tuple
/// fields and fixed-length array elements, in at most `depth` steps. Enums are
/// not walked (variant-dependent field view — a chain name would be
/// ambiguous); references, raw pointers, runtime indices and from-end indices
/// are not leaf steps (a raw-ptr leaf is not a stable value anyway — see
/// `place_reads_through_raw_ptr`).
///
/// An array element step is returned in the ONE spelling the chain's contract
/// name uses, `ConstantIndex { offset: k, min_length: len, from_end: false }`,
/// whether the read spelled it as a constant index (any `min_length`) or as an
/// `Index` of a const-resolved local: all of them render `[k]` once
/// canonicalized (`canonicalize_contract_index_segments`).
///
/// This walks the ONE chain a read names, so its cost is the chain's length.
/// It replaces enumerating every leaf of the type up front, which was sized by
/// the type's array LENGTHS (values: a `[f64; 1 << 20]` field is 2^20 leaves)
/// and so was capped at 16 lanes per array and 256 leaves per formal.
pub(super) fn float_leaf_chain(
    func: &VerifiableFunction,
    ty: &Ty,
    projections: &[Projection],
    depth: u32,
) -> Option<Vec<Projection>> {
    let mut ty = ty;
    let mut depth = depth;
    let mut chain = Vec::with_capacity(projections.len());
    for projection in projections {
        if depth == 0 {
            return None;
        }
        depth -= 1;
        match (ty, projection) {
            (Ty::Adt { fields, variants, .. }, Projection::Field(i)) if variants.is_empty() => {
                ty = &fields.get(*i)?.1;
                chain.push(Projection::Field(*i));
            }
            (Ty::Tuple(items), Projection::Field(i)) => {
                ty = items.get(*i)?;
                chain.push(Projection::Field(*i));
            }
            (Ty::Array { elem, len }, step) => {
                let lane = match step {
                    Projection::ConstantIndex { offset, from_end: false, .. } => *offset,
                    Projection::Index(local) => crate::index_local_const(func, *local)?,
                    _ => return None,
                };
                if u64::try_from(lane).ok()? >= *len {
                    return None;
                }
                let min_length = usize::try_from(*len).ok()?;
                ty = elem;
                chain.push(Projection::ConstantIndex { offset: lane, min_length, from_end: false });
            }
            _ => return None,
        }
    }
    matches!(ty, Ty::Float { width: 64 }).then_some(chain)
}

/// F6b (STRUCT-argument tracing): the CALLER side of one callee trace's
/// struct-formal leaf overrides, resolved when the callee trace READS a leaf.
///
/// A formal leaf's override is the caller's `Forbid`-mode interval of the
/// ACTUAL's corresponding leaf at the call block. It used to be computed for
/// every leaf of every struct formal before the trace began; it is now computed
/// for the leaves the trace actually reads, once each, in exactly the caller
/// context the eager binder used: the parent context, the call block, the
/// caller's `visiting` set and callee stack as they stood at the call, and
/// `fuel - 1`. A leaf the trace never reads costs nothing, so no trace is sized
/// by an array's length.
pub(super) struct FieldOverrideSource<'a> {
    parent: &'a FloatRangeCtx<'a>,
    call_block: BlockId,
    /// Formal local -> the caller's actual place (struct/vector formals only).
    actuals: FxHashMap<usize, Place>,
    /// The caller's `visiting` locals at the call.
    visiting: Vec<usize>,
    /// The shared callee stack at the call (before this callee was pushed).
    callee_stack: Vec<String>,
    fuel: u32,
    /// Resolved leaves, keyed by the callee-side canonical place name.
    resolved: std::cell::RefCell<FxHashMap<String, Option<(f64, f64)>>>,
}

impl<'a> FieldOverrideSource<'a> {
    /// A source binding `actuals` at `call_block` of `parent`'s function, with
    /// an empty `visiting` set and callee stack. Unit tests use it to reach
    /// `FloatRangeCtx::param_field_override` without the binder in
    /// `float_callee_trace_range`.
    #[cfg(test)]
    pub(super) fn for_test(
        parent: &'a FloatRangeCtx<'a>,
        call_block: BlockId,
        actuals: FxHashMap<usize, Place>,
    ) -> Self {
        Self {
            parent,
            call_block,
            actuals,
            visiting: Vec::new(),
            callee_stack: Vec::new(),
            fuel: FLOAT_EXP_BOUND_FUEL,
            resolved: std::cell::RefCell::new(FxHashMap::default()),
        }
    }

    pub(super) fn has_actual(&self, local: usize) -> bool {
        self.actuals.contains_key(&local)
    }

    /// The caller-proved interval of the formal leaf `place` (a place of the
    /// callee `callee`, rooted at a formal), under the callee-side name `key`.
    pub(super) fn resolve(
        &self,
        callee: &VerifiableFunction,
        place: &Place,
        key: String,
    ) -> Option<(f64, f64)> {
        if let Some(hit) = self.resolved.borrow().get(key.as_str()) {
            return *hit;
        }
        let range = self.resolve_uncached(callee, place, &key);
        self.resolved.borrow_mut().insert(key, range);
        range
    }

    fn resolve_uncached(
        &self,
        callee: &VerifiableFunction,
        place: &Place,
        key: &str,
    ) -> Option<(f64, f64)> {
        let actual = self.actuals.get(&place.local)?;
        let formal_ty = crate::local_ty_ref(callee, place.local)?;
        let leaf =
            float_leaf_chain(callee, formal_ty, &place.projections, FLOAT_STRUCT_LEAF_DEPTH)?;
        // The read must name exactly the leaf the chain spells — the eager
        // binder's key equality, kept as the gate.
        let leaf_place = Place { local: place.local, projections: leaf };
        if canonicalize_contract_index_segments_owned(crate::place_to_var_name(
            callee,
            &leaf_place,
        )) != key
        {
            return None;
        }
        let mut caller_place = actual.clone();
        caller_place.projections.extend(leaf_place.projections);
        // Evaluate at the call, as the eager binder did: the callee stack as it
        // stood before this callee was pushed, restored afterwards.
        let during = std::mem::replace(
            &mut *self.parent.visiting_callees.borrow_mut(),
            self.callee_stack.clone(),
        );
        let mut visiting = self.visiting.clone();
        let range = float_range(
            self.parent,
            FloatNanMode::Forbid,
            Some(self.call_block),
            &Operand::Copy(caller_place),
            &mut visiting,
            self.fuel,
        );
        *self.parent.visiting_callees.borrow_mut() = during;
        range
    }
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
    let Some(mut ty) = func.body.locals.get(place.local).map(|d| std::borrow::Cow::Borrowed(&d.ty))
    else {
        return false;
    };
    for proj in &place.projections {
        match proj {
            Projection::Deref => match ty.as_ref() {
                Ty::RawPtr { .. } => return true,
                _ => match crate::step_place_ty_cow(ty, proj) {
                    Some(next) => ty = next,
                    None => return false, // untypable deref: fail-OPEN
                },
            },
            _ => match crate::step_place_ty_cow(ty, proj) {
                Some(next) => ty = next,
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
        // The IEEE comparisons an authored float bound lowers to. Same reading as
        // the arms below, and the NaN case needs no special handling: an IEEE
        // comparison against NaN is false, so a clause that establishes both
        // sides has already established the value is ordered — which is exactly
        // the `FloatNanMode::Forbid` reading this function's caller documents.
        Formula::FpLe(a, b) | Formula::FpLt(a, b) | Formula::Le(a, b) | Formula::Lt(a, b) => {
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
        Formula::FpGe(a, b) | Formula::FpGt(a, b) | Formula::Ge(a, b) | Formula::Gt(a, b) => {
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
        // An authored float bound reads its variable through the IEEE lift: the
        // body spells a float place as its bit vector, so the contract's `x`
        // arrives as `FpFromBits { bits: Var("x") }`. The lift is injective and
        // names the same place, so seeing through it recognizes the SAME
        // variable rather than widening what counts as one.
        Formula::FpFromBits { bits, .. } => formula_is_named_var(bits, name),
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

/// The FINITE f64 value of a binary64 or binary32 float literal term. A spec
/// float literal lowers to `FpConst` (the parser folds a leading `-` into the
/// sign bit, so `-1.0e30` arrives as a single signed const, not a `Neg`). A
/// defensive `Neg(FpConst)` wrapper is honoured too. Non-finite literals (`inf`
/// from an over-large decimal, `NaN`) and any unmodelled format return `None`
/// (fail-closed — a non-finite bound never yields a magnitude exponent).
///
/// The value is returned as `f64` for both widths because widening binary32 is
/// exact; the CONSUMER is responsible for measuring it against thresholds for
/// the operation's own width.
pub(super) fn formula_float_value(formula: &Formula) -> Option<f64> {
    match formula {
        Formula::FpConst { bits, eb: 11, sb: 53 } => {
            let v = f64::from_bits(*bits as u64);
            v.is_finite().then_some(v)
        }
        // binary32, admitted 2026-09-17. Widening an `f32` bound to `f64` is
        // EXACT, and the thresholds this interval is measured against are now
        // chosen per operation width (`float_overflow_discharge_margin`,
        // `float_add_tiny_operand_bound`), so a binary32 bound is compared
        // against a binary32 margin.
        //
        // This arm was added once before and REVERTED as a measured false
        // proof: against the then-f64-scaled thresholds, two `f32` operands
        // around 3e38 read as "tiny" (2^970) and a bounded `f32` add verified
        // when its true result is infinity. The width-aware discharge is what
        // makes the arm sound; do not reinstate one without the other.
        Formula::FpConst { bits, eb: 8, sb: 24 } => {
            let v = f64::from(f32::from_bits(u32::try_from(*bits).ok()?));
            v.is_finite().then_some(v)
        }
        Formula::Neg(inner) => {
            let v = -formula_float_value(inner)?;
            v.is_finite().then_some(v)
        }
        // A negated authored literal (`-1.0`) lowers to the IEEE negation, which
        // is exact on a finite value — it flips the sign bit and nothing else.
        Formula::FpNeg(inner) => {
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
/// projected Call dest), `SetDiscriminant`/`Deinit`, or a borrow that hands out
/// write permission (`&mut`, `&raw mut`, `&raw const` — `path_defs::borrow_write_target`;
/// writes through the alias are invisible to any def scan). These are
/// `param_place_is_entry_stable`'s channels; whole-local stores are the defs
/// being collected, so they are allowed here.
///
/// The POINTER rule, not the slot rule, because callers also read this as the
/// stability of a place BEHIND `local` (`float_abs_guard_magnitude_bounds`'
/// `stable_base` on `(*self).2`). Until 2026-09-30 it counted `&mut` / `&raw mut`
/// only: `let mut v = 2.0; poke(&raw const v as *mut f64); v * 4.0` kept `v`'s
/// def set `{2.0}`, bounded the product by `8.0` and removed its
/// `FloatOverflowToInfinity` row, while the body returns `inf`
/// (tests/raw_const_float_scans.rs).
pub(super) fn float_whole_local_defs(
    func: &VerifiableFunction,
    local: usize,
) -> Option<Vec<FloatLocalDef<'_>>> {
    let mut defs = Vec::new();
    if crate::any_local_write_candidate(func, &func.body.blocks, local, |block, item| match item {
        Some(stmt) => match stmt {
            Statement::Assign { place: dest, rvalue, .. } => {
                if dest.local == local {
                    if dest.projections.is_empty() {
                        defs.push(FloatLocalDef::Rvalue { block: block.id, rvalue });
                    } else {
                        return true; // projected store: hull-of-defs model breaks
                    }
                }
                // `&mut` / `&raw (const|mut)` aliasing channel (H2)
                super::borrow_write_target(func, rvalue)
                    .is_some_and(|borrowed| borrowed.local == local)
            }
            Statement::SetDiscriminant { place: dest, .. } | Statement::Deinit { place: dest } => {
                dest.local == local
            }
            _ => false,
        },
        None => match &block.terminator {
            Terminator::Call { func: callee, args, dest, .. } if dest.local == local => {
                if !dest.projections.is_empty() {
                    return true;
                }
                defs.push(FloatLocalDef::Call {
                    block: block.id,
                    callee,
                    args: args.as_slice(),
                });
                false
            }
            // An `Opaque` terminator (inline asm, …) carries NO operand model
            // — it may write ANY local invisibly. One anywhere poisons every
            // def set (fail-closed; such a function already carries an
            // UnsupportedMir obligation, but this lane must not even trace).
            Terminator::Opaque { .. } => true,
            _ => false,
        },
    }) {
        return None;
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
        // satisfy a downstream callee precondition). Empty off the callee trace,
        // and refused for a formal the body writes or lends write-capably, or a
        // read through a raw pointer — `contract_range`'s gate, applied inside
        // `param_field_override` (F6B-FIELD-OVERRIDE-UNSTABLE-1).
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
///
/// Trust: the bit assembly is the VERIFIED `trust-floatbits` one. This value is
/// conjoined onto float-overflow obligations as a FACT, so a bound below the
/// true `2^w` discharges a real overflow — the exponent bias, the shift distance
/// and the representable-exponent limit used to be three unchecked literals in
/// this one line. The supported-predicate call comes FIRST because
/// `exp2_binary64_bits` saturates to `+inf`'s pattern, which is a legitimate
/// pattern and cannot be told apart from a refusal by its value alone.
pub(super) fn exp2i(w: u32) -> Option<f64> {
    (trust_floatbits::exp2_binary64_supported(w) == 1)
        .then(|| f64::from_bits(trust_floatbits::exp2_binary64_bits(w)))
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

/// Enclose an already outward-rounded f64 interval at the operation's IEEE
/// width. Binary32 arithmetic rounds before later operations consume its value:
/// an f64-only enclosure can otherwise miss a midpoint that rounds upward.
/// Directed endpoint conversion also encloses subnormal underflow. An infinite
/// endpoint refuses rather than presenting an overflowing result as finite.
pub(super) fn float_interval_in_width((lo, hi): (f64, f64), width: u32) -> Option<(f64, f64)> {
    if !(lo.is_finite() && hi.is_finite() && lo <= hi) {
        return None;
    }
    match width {
        64 => Some((lo, hi)),
        32 => {
            let (mut lower, mut upper) = (lo as f32, hi as f32);
            if !lower.is_finite() || !upper.is_finite() {
                return None;
            }
            if f64::from(lower) > lo {
                lower = lower.next_down();
            }
            if f64::from(upper) < hi {
                upper = upper.next_up();
            }
            (lower.is_finite() && upper.is_finite()).then_some((f64::from(lower), f64::from(upper)))
        }
        _ => None,
    }
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
            let width = v2_float_binop_width(ctx.func, a, b)?;
            let ra = float_range(ctx, mode, Some(def_block), a, visiting, fuel - 1)?;
            if let Some(rb) = float_range(ctx, mode, Some(def_block), b, visiting, fuel - 1)
                && let Some(full) = float_interval_binop(*op, ra, rb)
                    .and_then(|range| float_interval_in_width(range, width))
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
                return finite_outward(-q, q)
                    .and_then(|range| float_interval_in_width(range, width));
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
    // NUM-METHOD-ANCHOR-1: every std arm below names its callee by the call's
    // compiler-minted key plus an exact path, and wants a float destination (each
    // modeled method returns `f64`/`f32`; an extraction that disagrees is refused).
    let (callee_key, dest_is_float) = float_call_site_key(ctx.func, def_block);
    // `Duration::as_secs_f64`/`as_secs_f32`: `[0, u64::MAX + 1) ⊂ [0, 2^65]`,
    // always finite, never NaN — sound in both modes. Exact `Duration` path: a bare
    // suffix match let any `mymod::as_secs_f64` inject the bound (round-13, same
    // false-proof channel as the un-gated `::cos` suffix), and a root-plus-substring
    // test admits a generic argument spelling `::time::`.
    if dest_is_float
        && trust_types::callee_key::sysroot_exact_path(callee_key, callee, DURATION_AS_SECS_PATHS)
            .is_some()
    {
        return Some((0.0, exp2i(65)?));
    }
    // sin/cos/tanh: `|v| <= 1` for every FINITE input; NaN for a ±inf/NaN
    // input. The NaN-tolerant mode takes the unconditional bound (a NaN is
    // inside its contract — never a fresh ±inf); the strict mode must first
    // prove the ARGUMENT finite and NaN-free.
    if dest_is_float && is_unit_bounded_float_call(callee, callee_key) {
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
    if dest_is_float
        && let Some(method) = f64_std_method_name(callee, callee_key)
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

/// The recognized std `f64` method arms of [`float_call_range`] (identity
/// already gated by `f64_std_method_name`: key plus exact path).
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
///      `FloatRangeCtx::param_overrides`). Only f64-typed formals are bound,
///      plus the f64 leaves of a struct/tuple formal the body never writes or
///      lends write-capably (`param_place_is_entry_stable`); an unbindable
///      actual simply leaves its formal unboundable inside the callee
///      (fail-closed, never wrong).
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
    let summary = ctx.summaries?.get(callee)?;
    let body = summary.extracted_body.as_deref()?;
    // Positional formal binding requires the extracted arity to match the call.
    if body.body.arg_count != args.len() {
        return None;
    }
    // (3) Precondition arity gate before suffix resolution or memo-key formatting.
    if (!body.preconditions.is_empty() || !summary.preconditions.is_empty())
        && summary.param_names.len() != args.len()
    {
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
    let resolved_suffix: std::borrow::Cow<'_, [Projection]> =
        if suffix.iter().any(|p| matches!(p, Projection::Index(_))) {
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
            std::borrow::Cow::Owned(out)
        } else {
            std::borrow::Cow::Borrowed(suffix)
        };
    let suffix: &[Projection] = &resolved_suffix;
    // Trace memo of THIS context (successful results only). The key is in this
    // context's local names, so the memo is never shared with another context
    // (F6B-TRACE-MEMO-KEY-1; see the field doc). A hit skips the cuts and the
    // precondition re-establishment below: it was made under the same facts.
    let mut memo_key: Option<(BlockId, String, String, String)> = None;
    if !ctx.trace_memo.borrow().is_empty() {
        let key = (call_block, callee.to_string(), format!("{args:?}"), format!("{suffix:?}"));
        if let Some(hit) = ctx.trace_memo.borrow().get(&key) {
            return Some(*hit);
        }
        memo_key = Some(key);
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
    for pre in body.preconditions.iter().chain(summary.preconditions.iter()) {
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
    let _callee_scope = super::FuncAnalysisScope::enter(body);
    let mut overrides: FxHashMap<usize, (f64, f64)> = FxHashMap::default();
    let mut field_actuals: FxHashMap<usize, Place> = FxHashMap::default();
    for (position, actual) in args.iter().enumerate() {
        let formal = position + 1;
        let Some(formal_ty) = crate::local_ty_ref(body, formal) else {
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
        // STRUCT/vector formal: each scalar-f64 LEAF the trace reads is bound to
        // the caller's interval of the actual's corresponding field, resolved
        // on demand (`FieldOverrideSource`). The actual must be a place (a
        // constructed struct literal is handled by the general aggregate lane,
        // not here); the key is the CALLEE-side name so the in-callee projected
        // read finds it.
        let (Operand::Copy(actual_place) | Operand::Move(actual_place)) = actual else {
            continue;
        };
        // ENTRY-fact license (F6B-FIELD-OVERRIDE-UNSTABLE-1): a leaf override is
        // the caller's value of the actual, which a callee read sees only while
        // the formal still holds its entry value. A formal the body writes or
        // lends write-capably ANYWHERE (`p.a = 1e300`, `&mut p.0` handed to a
        // call) binds nothing, so every leaf read of it falls through to the
        // callee's own facts. Base-local granularity, as `contract_range`: a
        // write to `p.b` also refuses `p.a` (a completeness cost, fail-closed;
        // DECISION_QUEUE F6B-FIELD-OVERRIDE-UNSTABLE-1).
        if !param_place_is_entry_stable(body, formal) {
            continue;
        }
        field_actuals.insert(formal, actual_place.clone());
    }
    let field_source = FieldOverrideSource {
        parent: ctx,
        call_block,
        actuals: field_actuals,
        visiting: visiting.clone(),
        callee_stack: ctx.visiting_callees.borrow().clone(),
        fuel: fuel - 1,
        resolved: std::cell::RefCell::new(FxHashMap::default()),
    };
    // (4)(5) Trace `_0.<suffix>` inside the callee: fresh per-function context
    // (fresh LOCAL visiting namespace), shared work budget + callee stack, no
    // top-level flow context (each `_0` def is still evaluated under ITS OWN
    // block's dominating guards, exactly like `derive_float_result_range`).
    ctx.visiting_callees.borrow_mut().push(callee.to_string());
    let callee_ctx = FloatRangeCtx::for_callee(ctx, body, overrides, Some(&field_source));
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
        let key = memo_key
            .unwrap_or_else(|| (call_block, callee.to_string(), format!("{args:?}"), format!("{suffix:?}")));
        ctx.trace_memo.borrow_mut().insert(key, hit);
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
///   * NO pointer that can write under `m` (`&mut m.*`, `&raw mut m.*`, `&raw
///     const m.*` — `path_defs::borrow_write_target`), `SetDiscriminant m`,
///     `Deinit m`, or any `Opaque` terminator anywhere (invisible write channels).
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
    let summaries = ctx.summaries?;
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return None;
    }
    let mut init: Option<(BlockId, &'a str, &'a [Operand])> = None;
    let mut stores: Vec<(BlockId, &'a [Projection])> = Vec::new();
    let mut valid = true;
    crate::visit_local_write_candidates(func, &func.body.blocks, m, |block, item| {
        if !valid {
            return;
        }
        match item {
            Some(stmt) => match stmt {
                Statement::Assign { place: dest, rvalue, .. } => {
                    if let Some(b) = super::borrow_write_target(func, rvalue)
                        && b.local == m
                    {
                        valid = false; // `&mut m.*` / `&raw const m.*` — an invisible write channel
                        return;
                    }
                    if dest.local == m {
                        if dest.projections.is_empty() {
                            valid = false; // a whole reseat: not the single-init shape
                            return;
                        }
                        stores.push((block.id, dest.projections.as_slice()));
                    }
                }
                Statement::SetDiscriminant { place: d, .. } | Statement::Deinit { place: d }
                    if d.local == m =>
                {
                    valid = false;
                }
                _ => {}
            },
            None => match &block.terminator {
                Terminator::Call { func: callee, args, dest, .. } if dest.local == m => {
                    if !dest.projections.is_empty() || init.is_some() {
                        valid = false; // projected-dest call, or a SECOND whole def
                        return;
                    }
                    init = Some((block.id, callee.as_str(), args.as_slice()));
                }
                Terminator::Opaque { .. } => valid = false,
                _ => {}
            },
        }
    });
    if !valid {
        return None;
    }
    let (init_block, callee, args) = init?;
    if !summaries
        .get(callee)
        .and_then(|s| s.extracted_body.as_deref())
        .is_some_and(|b| b.body.arg_count == args.len())
    {
        return None;
    }
    // Every non-disjoint store must be unreachable from the read block. Two
    // projection chains rooted at `m` are PROVABLY DISJOINT when they differ at
    // some position that is CONSTANT on both sides (a `Field`, or a
    // const-resolved index) — `m.cols[0]` vs `m.cols[1]`. A symbolic index, or a
    // prefix relationship, is conservatively NOT disjoint. This resolves the
    // `Index(_k)` locals to their constants (which `place_to_var_name` renders
    // as symbolic `[_..]`, over-aliasing every column), so a store to a
    // DIFFERENT column no longer blocks this column's read.
    for (sblock, sproj) in &stores {
        if projections_provably_disjoint(func, sproj, &place.projections) {
            continue; // provably a different element: cannot affect the read
        }
        if reachable_avoiding_one_contains(func, sblock.0, None, read_block.0) {
            return None; // an aliasing store can reach the read — could clobber
        }
    }
    // Init-before-use well-formedness: the init must reach the read.
    if !reachable_avoiding_one_contains(func, init_block.0, None, read_block.0) {
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
    if !construction_defs.iter().any(|(_, w, _)| *w == variant) {
        return None;
    }
    visiting.push(place.local);
    let mut hull: Option<(f64, f64)> = None;
    let mut every_def_bounded = true;
    for (def_block, w, ops) in &construction_defs {
        if *w != variant {
            continue;
        }
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
    if facts.is_empty() || guards::value_local_is_unstable(ctx.func, place.local) {
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
    if !super::terminator_presence_for(ctx.func).has_bare_dest_call
        || ctx.dominating_facts(block_id).is_empty()
    {
        return (None, None);
    }
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
    // The consuming op often reads a COPY TEMP of the guarded value (`_t =
    // copy (*self).2; _q = 1.0 / _t`) while the abs call read the source place
    // directly — resolve the place through its single `Use(Copy|Move)` def so
    // both spell the same place. Sound: the temp is single-assignment (checked
    // below) and the RESOLVED source must pass the same stability discipline,
    // so temp and source provably hold the same value at every read.
    let resolve_to_source = |p: &Place| -> Option<Place> {
        if !p.projections.is_empty() {
            return None;
        }
        // A PARAMETER's ENTRY value is a def no block scan carries, so its one
        // visible `Use(copy src)` does NOT pin its value at the abs call — the call
        // can read it BEFORE the store. `stable_base` states the same rule for the
        // divisor place (`base_is_param => defs.is_empty()`); this closure is also
        // reached on the abs ARGUMENT, which `stable_base` has not vetted. For a
        // NON-parameter this changes nothing: the match below already demands
        // exactly one def, which is what `stable_base` asks of a non-parameter.
        if p.local >= 1 && p.local <= ctx.func.body.arg_count {
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
    let mut place_is_stable: Option<bool> = None;
    let mut place_source: Option<Option<Place>> = None;
    let mut floor: Option<f64> = None;
    let mut cap: Option<f64> = None;
    for block in &ctx.func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty() {
            continue;
        }
        let [Operand::Copy(arg) | Operand::Move(arg)] = args.as_slice() else {
            continue;
        };
        if fp_abs_call_width(callee) != Some(64) {
            continue;
        }
        if !*place_is_stable.get_or_insert_with(|| stable_base(place)) {
            return (None, None);
        }
        // Match the abs ARG against a candidate DIRECTLY, or through its OWN
        // single stable copy-def source: the abs (`_6 = copy (*self).2`) and the
        // divide (`_7 = copy (*self).2`) frequently read the guarded field
        // through TWO DIFFERENT compiler-inserted copy temps, so canonicalizing
        // both to `(*self).2` is required for them to meet (Transform::inverse's
        // `1.0 / self.scale` under `self.scale.abs() > 1e-20`). Sound by the same
        // single-assignment + `stable_base` discipline that admits the divisor's
        // own source into `candidates`.
        let arg_matches = if arg == place {
            true
        } else {
            let resolved_place_src =
                place_source.get_or_insert_with(|| resolve_to_source(place));
            let matches_candidate =
                |p: &Place| p == place || resolved_place_src.as_ref().is_some_and(|src| p == src);
            resolved_place_src.as_ref().is_some_and(|src| arg == src)
                || resolve_to_source(arg).is_some_and(|src| matches_candidate(&src))
        };
        if !arg_matches {
            continue;
        }
        // The abs temp must have NO other def than this call (a reseated temp
        // would stale the guard fact).
        if crate::local_defs::is_parameter(ctx.func, dest.local) {
            continue;
        }
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
    let Some(summary) = summaries.get(callee) else {
        return false;
    };
    if super::cached_terminator_presence_for_body(&func.body)
        .is_some_and(|tp| !tp.has_call && !tp.has_tail_call)
    {
        return false;
    }
    if super::body_contains_memory_image_for(func) {
        return false;
    }
    let mut memo_scopes = None;
    let float_ctx: std::cell::OnceCell<FloatRangeCtx<'_>> = std::cell::OnceCell::new();
    let mut saw_site = false;
    for block in &func.body.blocks {
        let (callee_name, args) = match &block.terminator {
            Terminator::Call { func, args, .. } | Terminator::TailCall { func, args, .. } => {
                (func, args)
            }
            _ => continue,
        };
        if callee_name != callee {
            continue;
        }
        if summary.param_names.len() != args.len() {
            return false;
        }
        for precondition in &summary.preconditions {
            if !precondition_interval_dominance_lazy(
                func,
                || {
                    memo_scopes.get_or_insert_with(|| {
                        (
                            crate::gen_work_memo_scope_if_unscoped(),
                            super::FuncAnalysisScope::enter(func),
                        )
                    });
                    float_ctx.get_or_init(|| FloatRangeCtx::new(func, Some(summaries)))
                },
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
    precondition_interval_dominance_lazy(
        ctx.func,
        || ctx,
        call_block,
        precondition,
        param_names,
        args,
        visiting,
        fuel,
    )
}

pub(super) fn precondition_interval_dominance_lazy<'a>(
    func: &'a VerifiableFunction,
    mut get_ctx: impl FnMut() -> &'a FloatRangeCtx<'a>,
    call_block: BlockId,
    precondition: &Formula,
    param_names: &[String],
    args: &[Operand],
    visiting: &mut Vec<usize>,
    fuel: u32,
) -> bool {
    const LOWER_SEEN: u8 = 1;
    const UPPER_SEEN: u8 = 2;

    fn check_conjuncts<'a, 'f>(
        func: &'a VerifiableFunction,
        get_ctx: &mut impl FnMut() -> &'a FloatRangeCtx<'a>,
        call_block: BlockId,
        fact: &'f Formula,
        param_names: &[String],
        args: &[Operand],
        visiting: &mut Vec<usize>,
        fuel: u32,
        saw_conjunct: &mut bool,
        ranges: &mut FxHashMap<&'f str, (f64, f64, u8)>,
    ) -> bool {
        if let Formula::And(conjuncts) = fact {
            for c in conjuncts {
                if !check_conjuncts(
                    func,
                    get_ctx,
                    call_block,
                    c,
                    param_names,
                    args,
                    visiting,
                    fuel,
                    saw_conjunct,
                    ranges,
                ) {
                    return false;
                }
            }
            return true;
        }
        *saw_conjunct = true;
        // INT lane (the contracts machinery's auto type-range requires,
        // `0 <= r <= <uN>::MAX` on an integer formal): dischargeable when the
        // σ-mapped actual is a CONSTANT satisfying the bound literally, or a
        // place whose INTEGER TYPE's full value range sits inside the bound (a
        // type-range tautology holds for every well-typed value — sound
        // unconditionally; anything else falls through fail-closed). Handled
        // per-conjunct with no two-sidedness demand: an int conjunct proven
        // this way holds on its own, unlike the float lane whose interval
        // tracer requires two-sided NaN-excluding bounds.
        if let Some(holds) = int_pre_conjunct_holds(func, param_names, args, fact) {
            return holds;
        }
        let Some((var, cmp, c)) = float_pre_var_const(fact) else { return false };
        let side_bit = match cmp {
            BvGuardCmp::Le | BvGuardCmp::Lt => UPPER_SEEN,
            BvGuardCmp::Ge | BvGuardCmp::Gt => LOWER_SEEN,
            BvGuardCmp::Eq => 0,
        };
        let (lo, hi) = match ranges.get_mut(var) {
            Some((lo, hi, sides)) => {
                *sides |= side_bit;
                (*lo, *hi)
            }
            None => {
                let ctx = get_ctx();
                let Some((lo, hi)) =
                    dominance_actual_range(ctx, call_block, var, param_names, args, visiting, fuel)
                else {
                    return false;
                };
                ranges.insert(var, (lo, hi, side_bit));
                (lo, hi)
            }
        };
        match cmp {
            BvGuardCmp::Le => hi <= c,
            BvGuardCmp::Lt => hi < c,
            BvGuardCmp::Ge => lo >= c,
            BvGuardCmp::Gt => lo > c,
            BvGuardCmp::Eq => false, // not produced by float_pre_var_const
        }
    }

    if fuel == 0 || param_names.len() != args.len() {
        return false;
    }
    let mut saw_conjunct = false;
    let mut ranges: FxHashMap<&str, (f64, f64, u8)> = FxHashMap::default();
    if !check_conjuncts(
        func,
        &mut get_ctx,
        call_block,
        precondition,
        param_names,
        args,
        visiting,
        fuel,
        &mut saw_conjunct,
        &mut ranges,
    ) {
        return false;
    }
    // BOTH sides required per var: this lane is deliberately restricted to the
    // audited two-sided magnitude-bound contract shape.
    saw_conjunct && ranges.values().all(|&(_, _, sides)| sides == (LOWER_SEEN | UPPER_SEEN))
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
    let suffix_projections = parse_projection_suffix(suffix)?;
    let mut place = base_place.clone();
    place.projections.extend(suffix_projections);
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
    if super::body_contains_memory_image_for(func) {
        return None;
    }
    // This public summary producer is also invoked directly by the compiler.
    // A TailCall overwrites the implicit return place; project it before the
    // return-def trace so an earlier `_0` assignment cannot masquerade as the
    // function's returned range.
    let tail_call_expanded = func.with_tail_calls_expanded();
    let func = tail_call_expanded.as_ref();
    let _gen_work_memo = crate::gen_work_memo_scope_if_unscoped();
    let _analysis_scope = super::FuncAnalysisScope::enter(func);
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

// Trust (2026-10-04, wave 13): test modules sit at the END of the file, so the
// `local_defs_seam_lint` test-module mask (which runs from a braceless `mod x;` to
// the next closing brace) cannot swallow a production function.
#[cfg(test)]
#[path = "f64_method_anchor_tests.rs"]
mod f64_method_anchor_tests;
