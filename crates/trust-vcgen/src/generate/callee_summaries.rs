// Whole-function summaries computed once per callee and reused at every
// callsite: constant return bounds and return-value sets, trivial setters,
// returned enum discriminants, and boolean predicate returns. These are the
// interprocedural facts that let a caller's VC avoid re-analysing the callee.

use super::*;

// ======================================================================
// Loop-invariant min/max facts (`let n = a.min(b); for i in 0..n { … }`)
// ======================================================================
//
// `Ord::min`/`max` results obey `min(a,b) <= a, <= b` (and the dual for max)
// UNCONDITIONALLY — these methods never panic. The existing BFS semantic-guard
// modeling emits exactly these bounds, but as PATH guards they are weakened to
// nothing at a loop-header join, so they never reach a loop BODY that uses the
// result only transitively (`for i in 0..n` reads `i`, not `n`). The bounded-copy
// idiom `let n = src.len().min(dst.len()); for i in 0..n { dst[i] = src[i]; }`
// then false-refutes: the range-yield fact gives `i < n`, but `n <= dst.len()`
// is gone, so the `dst[i]`/`src[i]` bounds stay satisfiable.
//
// When the result local is SINGLE-ASSIGNMENT and every argument resolves to an
// IMMUTABLE term — a constant, or the `__slice_len` of a PARAMETER slice (a
// slice's length cannot change for the function's lifetime) — the bound is a
// GLOBAL invariant: the result symbol means one value everywhere and the argument
// symbols never change. So it may be conjoined onto every VC, exactly like the
// range-yield fact, reaching the loop body and closing `i < n <= dst.len()`.
//
// SOUNDNESS: min/max are total and panic-free, so `min(a,b) <= a` holds with no
// precondition (unlike clamp, whose `lo <= r <= hi` needs `lo <= hi` — excluded
// here). A non-stable argument (anything but a constant / parameter slice length)
// yields NO fact, never a wrong one. The fact is always TRUE, so it can only help
// PROVE genuinely-safe code; it can never make a real violation vacuously hold.
/// True iff `local` is a function PARAMETER (locals `1..=arg_count`).
pub(super) fn is_parameter(func: &VerifiableFunction, local: usize) -> bool {
    local >= 1 && local <= func.body.arg_count
}

/// SOUNDNESS (P0 false proof, 2026-06-17 hunt-6): true when a `#[ensures]` postcondition
/// references a by-value PARAMETER that the body REASSIGNS. The v2 postcondition VC binds the
/// parameter to its RETURN-block (final, mutated) value via the path/block defs, but the
/// `ensures` semantics snapshot the parameter's ENTRY value (`move |r| *r == a` captures `a` at
/// entry). For `#[ensures(move |r| *r == a)] fn f(mut a:u32){ a = a.wrapping_add(1); a }` the VC
/// checks `r == a_final` (11==11 → vacuously PROVED) while the true `r == a_entry` (11==10) is
/// FALSE — a default-mode false proof (FULL fail-closes soundly). The caller FAIL-CLOSES on this
/// (does not credit the proof) until proper entry-snapshot modeling lands.
pub(super) fn postcondition_references_mutated_param(func: &VerifiableFunction, post: &Formula) -> bool {
    let mut reassigned: FxHashSet<String> = FxHashSet::default();
    let mut note = |func: &VerifiableFunction, local: usize| {
        if is_parameter(func, local) {
            reassigned.insert(place_to_var_name(func, &Place { local, projections: vec![] }));
        }
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if place.projections.is_empty() {
                    note(func, place.local);
                }
                // SOUNDNESS (P0 false proof, 2026-06-17 hunt-15 Class B): a parameter
                // MUTABLY BORROWED (`&mut a` / `&raw mut a`) can be reassigned through the
                // borrow AFTER the entry snapshot — `let p=&mut a; *p=..` (the store's place
                // is `*p`, invisible to the whole-local scan above), `mem::replace(&mut a, k)`,
                // `mem::swap(&mut a, &mut other)`, or a helper `bump(&mut a)`. The `ensures`
                // captures `a` at ENTRY (`move |r| *r == a`) but the body returns the MUTATED
                // value, so `r == a_final` vacuously PROVES while the true `r == a_entry` is
                // false. The hunt-6 whole-local-reassign scan misses this &mut/AddressOf vector
                // exactly as the bounds lane did (hunt-5). Flag the borrowed param so the caller
                // fail-closes (does not credit the postcondition). Mirrors
                // `value_local_is_unstable` / `is_single_static_assignment`'s kill-on-Ref.
                if let Rvalue::Ref { mutable: true, place: bp } | Rvalue::AddressOf(_, bp) = rvalue
                    && bp.projections.is_empty()
                {
                    note(func, bp.local);
                }
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
        {
            note(func, dest.local);
        }
    }
    if reassigned.is_empty() {
        return false;
    }
    let mut post_vars: FxHashSet<String> = FxHashSet::default();
    collect_var_names(post, &mut post_vars);
    post_vars.iter().any(|v| reassigned.iter().any(|n| place_names_overlap(v, n)))
}

/// True iff `local` is assigned EXACTLY ONCE across the whole function (a single
/// whole-local def, by an `Assign` statement OR a `Call` terminator dest), with no
/// field/index store that would make its value ambiguous. A store THROUGH the
/// local (`*local = …`, a `Deref`-first projection) mutates the pointee, not the
/// local, so it does not count. Licenses treating `Var(local)` as a GLOBAL
/// invariant — the symbol has one meaning at every program point.
///
/// SOUNDNESS (P0 false-proof fix, 2026-06-17 hunt skeptic #2): `local` must ALSO not be
/// mutably borrowed or raw-pointed. `let p = &mut i; *p = b;` reassigns `i` through the
/// borrow, but the store's place is `*p` (place.local = `p`, not `i`), so the def scan
/// above does NOT see it and would count `i` as single-assignment — then a stale
/// `Ord::min`/modulo/bitmask/accumulator fact (`i <= 3`) survives and vacuously discharges a
/// violated VC (`let mut i=a.min(3); let p=&mut i; *p=b; arr[i]` PROVED in-bounds in BOTH
/// default and kernel-certified -full, yet `i` becomes `b` and the index goes OOB). So any
/// `&mut local` / `&raw mut local` (`Ref{mutable:true}`/`AddressOf`) of either mutability —
/// a `*const` is a valid `*const→*mut` cast root — kills SSA. A shared `&local` cannot mutate
/// and its cast to `*mut` is rejected by `invalid_reference_casting`, so it is allowed.
pub(super) fn is_single_static_assignment(func: &VerifiableFunction, local: usize) -> bool {
    let mut count = 0u32;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if let Rvalue::Ref { mutable: true, place: borrowed }
                | Rvalue::AddressOf(_, borrowed) = rvalue
                    && borrowed.local == local
                {
                    return false;
                }
                if place.local != local {
                    continue;
                }
                if place.projections.first() == Some(&trust_types::Projection::Deref) {
                    continue;
                }
                if !place.projections.is_empty() {
                    return false;
                }
                count += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            if !dest.projections.is_empty() {
                return false;
            }
            count += 1;
        }
    }
    count == 1
}

/// Trust (countdown-loop piece, P0 root-cause fix): `true` iff `local` is ever
/// MUTABLY borrowed (`&mut local`, `Rvalue::Ref { mutable: true }`) or
/// raw-addressed (`&raw const/mut local`, `Rvalue::AddressOf`) anywhere in the
/// body — the write channels a def-site scan cannot see. A callee receiving
/// `&mut i` can reseat `i` to ANY value, so every induction-style invariant
/// derived from `i`'s visible defs (single init + self-decrements) is void: the
/// pre-fix `build_downward_induction_facts` emitted `_t.0 < s.len()` for
/// `while i > 0 { i -= 1; s[i]; bump(&mut i); }`, a fact that is FALSE at
/// runtime on the second iteration — a confirmed false PROOF of the `s[i]`
/// bounds row (panics rc=101). Raw-const is included fail-closed (a `*const`
/// cast to `*mut` write is UB in sound code, but this scan is not a UB oracle).
/// Shared `&local` borrows of these integer locals are NOT writes (no interior
/// mutability without `UnsafeCell`, which an `Int`-typed local cannot be) and
/// stay allowed.
pub(super) fn local_mut_escapes(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().any(|block| {
        block.stmts.iter().any(|s| {
            matches!(s, Statement::Assign {
                rvalue: Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(_, borrowed),
                ..
            } if borrowed.local == local)
        })
    })
}

/// The `__slice_len` of the PARAMETER slice that `operand` reads the length of,
/// following a `&(*param)` / `&raw const (*param)` reborrow to the parameter root.
/// None unless the root is a parameter whose type is a slice or ref/raw-ptr to a
/// slice — only then is the length immutable and the symbol stable.
pub(super) fn param_slice_len(func: &VerifiableFunction, operand: &Operand, fuel: u32) -> Option<Formula> {
    if fuel == 0 {
        return None;
    }
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    // Direct: the operand IS a parameter slice / ref-to-slice.
    if is_parameter(func, p.local)
        && let Some(len) = crate::slice_len_formula(func, operand)
    {
        return Some(len);
    }
    // Indirect: `_t = &(*param)` / `&raw const (*param)` — follow to the root.
    match crate::unique_whole_local_def(func, p.local)? {
        Rvalue::Ref { place: referent, .. } | Rvalue::AddressOf(_, referent) => {
            let mut root = referent.clone();
            if root.projections.last() == Some(&trust_types::Projection::Deref) {
                root.projections.pop();
            }
            if root.projections.is_empty() && is_parameter(func, root.local) {
                return crate::slice_len_formula(func, &Operand::Copy(root));
            }
            None
        }
        Rvalue::Use(inner) => param_slice_len(func, inner, fuel - 1),
        // Trust (countdown-loop piece, G1): the UNSIZE coercion `&[T; N] -> &[T]`
        // (`_t = move _a as &[T]`), the shape `buf.len()` inlines to on a
        // `&mut [T; N]` parameter (`_a = &(*buf); _t = _a as &[T]; PtrMetadata(_t)`).
        // SOUND: a cast whose TARGET is a reference/raw pointer to a SLICE preserves
        // the fat-pointer metadata verbatim (rustc rejects thin->fat `as` casts, so
        // the source is either an unsize coercion from `&[T; N]` — metadata := N, the
        // exact array length — or an already-fat pointer whose metadata is copied
        // unchanged). Recursing on the SOURCE operand computes the length from the
        // source's own type through the existing param-rooted arms, which only
        // resolve immutable param-anchored lengths — nothing new is trusted.
        Rvalue::Cast(inner, to_ty)
            if matches!(
                to_ty,
                Ty::Ref { inner: t, .. } | Ty::RawPtr { pointee: t, .. }
                    if matches!(t.as_ref(), Ty::Slice { .. })
            ) =>
        {
            param_slice_len(func, inner, fuel - 1)
        }
        _ => None,
    }
}

/// True iff `local`'s single definition is an `Ord::min`/`max` call result. Lets
/// the chained idiom `a.len().min(b.len()).min(c.len())` resolve: the outer min's
/// inner-result argument is a single-assignment local, and `min(inner, c) <= inner`
/// holds unconditionally, so `dest <= Var(inner)` chains through the inner call's
/// own (separately emitted) `inner <= a.len()` / `<= b.len()` facts.
pub(super) fn local_is_min_max_result(func: &VerifiableFunction, local: usize) -> bool {
    func.body.blocks.iter().any(|block| {
        matches!(&block.terminator,
            Terminator::Call { func: callee, dest, .. }
                if dest.local == local
                    && dest.projections.is_empty()
                    && (is_ord_min_call(callee) || is_ord_max_call(callee)))
    })
}

/// Resolve a min/max argument to a STABLE formula (constant or parameter slice
/// length) — see [`param_slice_len`]. None for anything whose value could change
/// between the call site and a use site, so the bound stays a sound global fact.
pub(super) fn stable_min_arg_formula(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<Formula> {
    if fuel == 0 {
        return None;
    }
    if let Operand::Constant(_) = operand {
        return Some(operand_to_formula(func, operand));
    }
    let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Use(inner)) => return stable_min_arg_formula(func, inner, fuel - 1),
        Some(Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)) => {
            return param_slice_len(func, inner, fuel - 1);
        }
        Some(Rvalue::Len(place)) => {
            return param_slice_len(func, &Operand::Copy(place.clone()), fuel - 1);
        }
        // No whole-local Assign def: fall through to the min/max-result case below
        // (the inner result of a chained `.min().min()` is a Call dest, which
        // `unique_whole_local_def` — Assign-only — does not see).
        _ => {}
    }
    // A nested `Ord::min`/`max` RESULT is a single-assignment, stable symbol;
    // `min(inner, c) <= inner` is unconditionally true, so `dest <= Var(inner)` is
    // sound and chains through `inner`'s own emitted bounds.
    if local_is_min_max_result(func, p.local) && is_single_static_assignment(func, p.local) {
        return Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int));
    }
    None
}

/// Global, loop-invariant facts from `Ord::min`/`max` calls with a
/// single-assignment result and immutable arguments. Conjoined onto every VC (the
/// fact is unconditionally true), so a loop body that uses the result only
/// transitively still sees `min(a,b) <= a`. See the section banner for soundness.
/// Recognize a call to the standard-library float `abs` (`f64::abs`/`f32::abs`)
/// and return its IEEE width (64 or 32). CRATE-ORIGIN anchored (`core::`/`std::`/
/// `alloc::`) — mirroring `ord_method`'s std-shape discipline — so a user-defined
/// `mymod::f64::abs` is NOT matched (matching it would inject a false
/// value-definition about an unrelated dest, a false-PROVE). The canonical path
/// is `core::f64::<impl f64>::abs`; integer `i32::abs` (panicking) and the
/// `::math::*` intrinsic delegate are excluded (no `::f64::`/`::f32::` segment).
pub(super) fn fp_abs_call_width(callee: &str) -> Option<u32> {
    let last = callee.rsplit("::").next()?;
    let method = last.split('<').next().unwrap_or(last).trim();
    if method != "abs" {
        return None;
    }
    let std_origin = callee.starts_with("core::")
        || callee.starts_with("std::")
        || callee.starts_with("alloc::");
    if !std_origin {
        return None;
    }
    if callee.contains("::f64::") {
        Some(64)
    } else if callee.contains("::f32::") {
        Some(32)
    } else {
        None
    }
}

/// Global value-definition facts for `dest = arg.abs()` (`f32::abs`/`f64::abs`).
/// abs lowers to a `Terminator::Call` (not an Rvalue), so — like
/// `build_min_max_facts` — we emit the fact `Eq(FpFromBits(dest),
/// FpAbs(FpFromBits(arg)))` GLOBALLY, conjoined onto every VC, gated on
/// single-static-assignment of BOTH the dest and the arg's base local (the bare,
/// unversioned names are only a function-wide invariant when each is assigned
/// once). Fail-closed: any unrecognized/unstable/non-IEEE case emits nothing, so
/// `dest` stays unconstrained (a missed proof, never a false proof).
pub(super) fn build_fp_abs_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty() || args.len() != 1 {
            continue;
        }
        if fp_abs_call_width(callee).is_none() {
            continue;
        }
        if !is_single_static_assignment(func, dest.local) {
            continue;
        }
        // Width from the float TYPE is authoritative; skip non-float / non-IEEE.
        let width = match crate::operand_ty_cow(func, &args[0]).as_deref() {
            Some(trust_types::Ty::Float { width }) if *width == 64 || *width == 32 => *width,
            _ => continue,
        };
        // The arg must be a bare, single-static-assignment local: a global fact
        // names it unversioned, so a reassigned arg would make the equality
        // unsound at a later VC site. Projections / constants / Move-of-temp:
        // skip (fail-closed).
        let arg_local = match &args[0] {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => p.local,
            _ => continue,
        };
        if !is_single_static_assignment(func, arg_local) {
            continue;
        }
        let dest_name = crate::place_to_var_name(func, dest);
        if let Some(def) = guards::fp_abs_value_def(func, &args[0], &dest_name, width) {
            facts.push(def);
        }
    }
    facts
}

/// Global result bounds for value-bounded std intrinsics — each is UNCONDITIONALLY
/// true, so conjoining it everywhere is sound and lets a bounded index discharge:
///   * `n.rem_euclid(c)` for a CONSTANT divisor `c`: the Euclidean remainder is
///     ALWAYS in `[0, |c|-1]` (non-negative, strictly below `|c|`), so
///     `arr[n.rem_euclid(6)]` into `[_; 6]` is in bounds.
///   * `n.{trailing,leading}_zeros()` / `n.count_{ones,zeros}()`: the result is the
///     bit-count of the receiver type, in `[0, bits(T)]` — so `arr[n.count_ones()]`
///     into `[_; bits+1]` is in bounds. These are LINEAR bounds ay discharges
///     directly (unlike an equality contradiction).
pub(super) fn build_intrinsic_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty() || !is_single_static_assignment(func, dest.local) {
            continue;
        }
        let dest_var = || Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
        let ge0 = |facts: &mut Vec<Formula>| {
            facts.push(Formula::Ge(Box::new(dest_var()), Box::new(Formula::Int(0))));
        };
        match method_tail(callee) {
            // `rem_euclid(c)` (receiver + divisor): result in `[0, |c|-1]` for `|c| >= 1`.
            "rem_euclid" if args.len() == 2 => {
                if let Some(c) = operand_const_int(&args[1]) {
                    let m = c.unsigned_abs();
                    if let Ok(m) = i128::try_from(m) {
                        if m >= 1 {
                            ge0(&mut facts);
                            facts
                                .push(Formula::Lt(Box::new(dest_var()), Box::new(Formula::Int(m))));
                        }
                    }
                }
            }
            // bit-count intrinsics: result in `[0, bits(receiver_type)]`.
            "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
                if args.len() == 1 =>
            {
                if let Some(Ty::Int { width, .. }) =
                    crate::operand_ty_cow(func, &args[0]).as_deref()
                {
                    ge0(&mut facts);
                    facts.push(Formula::Le(
                        Box::new(dest_var()),
                        Box::new(Formula::Int(*width as i128)),
                    ));
                }
            }
            _ => {}
        }
    }
    facts
}

/// Global facts propagating a NON-NEGATIVE bounded value's upper bound THROUGH an `as uN` cast.
///
/// `let j = i.clamp(lo,hi); arr[j as usize]` / `arr[n.rem_euclid(C) as usize]` leave the access
/// runtime-checked: the source's bound (`j <= hi`, `rem < |C|`) is on a SEPARATE local from the
/// `as usize` cast result, and ay does not model the signed→unsigned cast as an equality, so the
/// bound never transfers. For a source provably in `[0, C]` (`cast_source_const_upper_nonneg`:
/// const clamp `[lo,hi]` with `lo>=0`, `rem_euclid` `[0,|C|-1]`, bit-counts `[0, width]` — all
/// NON-NEGATIVE), `src as uN = src mod 2^N <= C` holds UNCONDITIONALLY (truncation only lowers;
/// `src>=0` rules out the negative→huge wrap). Emit the GLOBAL fact `(src as uN) <= C`; it
/// discharges the access whenever `C < arr.len()` (via the incompatible-const-bounds discharge:
/// `(cast)<=C ∧ (cast)>=len` is UNSAT when `C < len`). ONLY the upper bound (a lower bound is
/// unsound under truncation; a usize index needs none) — SELF-LIMITING: a `C >= len` source
/// (genuine OOB) leaves compatible bounds and stays runtime-checked.
///
/// SOUNDNESS GATES (any miss → no fact):
///   * the cast SOURCE has a recognized const non-negative upper bound (above);
///   * the target type is an UNSIGNED integer (a signed target re-introduces the sign-bit edge);
///   * BOTH the source and the cast dest are single-static-assignment — so neither is reassigned
///     NOR mutably borrowed after the def (the hunt-5/7/8 staleness gate: a `let p=&mut j; *p=huge`
///     between def and cast would otherwise leave a stale `src as usize <= C`;
///     `is_single_static_assignment` kills on any `Ref{mutable}`/`AddressOf`).
pub(super) fn build_cast_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: cast_dst, rvalue: Rvalue::Cast(operand, to_ty), .. } =
                stmt
            else {
                continue;
            };
            if !cast_dst.projections.is_empty() || !(to_ty.is_integer() && !to_ty.is_signed()) {
                continue;
            }
            let (Operand::Copy(src_p) | Operand::Move(src_p)) = operand else { continue };
            if !src_p.projections.is_empty() {
                continue;
            }
            // Staleness: both the source value and the cast result are single-assignment
            // (and neither is mutably borrowed — SSA kills on Ref{mutable}/AddressOf).
            if !is_single_static_assignment(func, src_p.local)
                || !is_single_static_assignment(func, cast_dst.local)
            {
                continue;
            }
            // A `bool` source casts to `{0, 1}` — a total theorem (a `bool` is 0 or
            // 1, so `bool as <uint>` ≤ 1). Attaching this upper bound lets sums of
            // flag/edge counts — `(a != b) as u32 + (b != c) as u32 + …` — discharge
            // their arithmetic-overflow VCs; without it the cast result was unbounded
            // and the sum spuriously refuted (over-refutation audit: body cast
            // semantics). SOUND: the SSA gate above pins the bool's single definition,
            // and every `bool` value is 0 or 1 by construction. Otherwise fall back to
            // the const-upper-bounded producers (clamp / rem_euclid / bit-count).
            let hi = if crate::operand_ty_cow(func, operand)
                .is_some_and(|t| matches!(t.as_ref(), Ty::Bool))
            {
                1
            } else {
                match cast_source_const_upper_nonneg(func, src_p.local) {
                    Some(h) => h,
                    None => continue,
                }
            };
            let cast_var = Formula::Var(crate::place_to_var_name(func, cast_dst), Sort::Int);
            facts.push(Formula::Le(Box::new(cast_var), Box::new(Formula::Int(hi))));
        }
    }
    facts
}

/// The constant LOWER bound `C` of a call defining `local` whose result is provably
/// `>= C` for ALL inputs, where the carry across a value-preserving widening cast is
/// SOUND: `max(v, C)` is `>= C` unconditionally (`max(v, C) >= C` is a total Ord
/// theorem), so for a value-preserving widening `(max(v,C) as uWider) >= C`. Only
/// `Ord::max(v, c)` with a CONSTANT `c` argument is recognized — the bound is the
/// (largest) constant operand. None for any other call.
///
/// Restricted to a const operand `c` (not a symbolic one) so the emitted bound is a
/// concrete `Ge(cast, c)`; `min`/`clamp` are NOT lower-bound producers in the sense
/// needed here (`min(v,c) <= c` is an UPPER bound, `clamp` lower bound `lo` is already
/// covered by the upper-bound path when relevant) so they are excluded.
pub(super) fn cast_source_const_lower(func: &VerifiableFunction, local: usize) -> Option<i128> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            if is_ord_max_call(callee) && args.len() == 2 {
                // `max(v, c) >= c` for the const operand `c`; if BOTH are const, the
                // result is `>= max(c1, c2)` — take the largest const operand.
                let mut best: Option<i128> = None;
                for arg in args {
                    if let Some(c) = operand_const_int(arg) {
                        best = Some(best.map_or(c, |b: i128| b.max(c)));
                    }
                }
                return best;
            }
            return None;
        }
    }
    None
}

/// Global facts propagating a DYNAMIC LOWER bound of a `max`-with-const source THROUGH
/// a value-preserving widening `as uN` cast: `let n = v.max(C) as u64; h % n`. The
/// `.max(C)` result is `>= C` unconditionally, and a value-preserving widening cast is
/// the IDENTITY on the value, so `(v.max(C) as uWider) >= C` holds UNCONDITIONALLY.
/// Emit the GLOBAL fact `(cast) >= C`, keyed on the CAST DEST var name — which carries
/// e.g. `n >= 1` from `num_partitions.max(1) as u64`, discharging the Rem-by-zero
/// obligation on `h % n` (the divisor is provably non-zero).
///
/// SOUNDNESS GATES (mirror [`build_cast_bound_facts`] EXACTLY — any miss → no fact):
///   * the cast SOURCE is a `max(v, C)` with a CONSTANT operand `C`
///     (`cast_source_const_lower`); `max(v, C) >= C` is a total Ord theorem;
///   * the cast is a VALUE-PRESERVING widening (`is_modeled_identity_cast` of the
///     source/target int types: same width+signedness, or a widening that is NOT
///     signed→unsigned) — so the cast is the identity on the value and the lower
///     bound is preserved; a narrowing/reinterpret/signed→unsigned widening could
///     change the value and is EXCLUDED;
///   * BOTH the source and the cast dest are single-static-assignment — so neither is
///     reassigned NOR mutably borrowed after the def (the SSA staleness gate; a `&mut`
///     reassign of the source between `.max(C)` and the cast would otherwise leave a
///     stale `(cast) >= C`). `is_single_static_assignment` kills on `Ref{mutable}`/
///     `AddressOf`.
/// LOWER bound ONLY (the dual of `build_cast_bound_facts`' upper-bound-only rule): no
/// upper bound is claimed here (the source has none), and the fact is unconditionally
/// true, so it can only ever HELP discharge a real obligation, never false-prove.
pub(super) fn build_cast_lower_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: cast_dst, rvalue: Rvalue::Cast(operand, to_ty), .. } =
                stmt
            else {
                continue;
            };
            if !cast_dst.projections.is_empty() {
                continue;
            }
            let (Operand::Copy(src_p) | Operand::Move(src_p)) = operand else { continue };
            if !src_p.projections.is_empty() {
                continue;
            }
            // Value-preserving widening only — the cast must be the IDENTITY on the
            // value for the source lower bound to carry. Narrowing / signed→unsigned
            // widening / reinterpret change the value and are excluded.
            // verifier-perf: borrow the declared type (no fat-root clone) — only inspected.
            let Some(from_ty) = crate::local_ty_ref(func, src_p.local) else { continue };
            if !crate::is_modeled_identity_cast(from_ty, to_ty) {
                continue;
            }
            // Staleness: both the source value and the cast result are single-assignment
            // (and neither is mutably borrowed — SSA kills on Ref{mutable}/AddressOf).
            if !is_single_static_assignment(func, src_p.local)
                || !is_single_static_assignment(func, cast_dst.local)
            {
                continue;
            }
            let Some(lo) = cast_source_const_lower(func, src_p.local) else { continue };
            let cast_var = Formula::Var(crate::place_to_var_name(func, cast_dst), Sort::Int);
            facts.push(Formula::Ge(Box::new(cast_var), Box::new(Formula::Int(lo))));
        }
    }
    facts
}

/// The constant upper bound `C` of a call defining `local` whose result is a known
/// NON-NEGATIVE value bounded by `C` — so `local as uN` is value-preserving and
/// `(local as uN) <= C` holds (truncation only lowers). Recognizes:
///   * `Ord::clamp(v, lo, hi)` with const `0 <= lo <= hi` → `hi` (a negative `lo` or
///     `lo > hi` is excluded: the former admits a negative source, the latter PANICS);
///   * `n.rem_euclid(c)` with `|c| >= 1` → `|c| - 1` (euclidean remainder is always in
///     `[0, |c|-1]`, REGARDLESS of the sign of `n` — the exact case the unsigned `n % c`
///     already proves but a SIGNED `n.rem_euclid(c) as usize` did not);
///   * `trailing_zeros`/`leading_zeros`/`count_ones`/`count_zeros` on a width-`w` integer
///     → `w` (result in `[0, w]`).
/// None for any other call (unknown bound — fail open, never a wrong fact).
pub(super) fn cast_source_const_upper_nonneg(func: &VerifiableFunction, local: usize) -> Option<i128> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            if is_ord_clamp_call(callee) && args.len() == 3 {
                let lo = operand_const_int(&args[1])?;
                let hi = operand_const_int(&args[2])?;
                return (0 <= lo && lo <= hi).then_some(hi);
            }
            if method_tail(callee) == "rem_euclid" && args.len() == 2 {
                let c = operand_const_int(&args[1])?;
                let m = i128::try_from(c.unsigned_abs()).ok()?;
                return (m >= 1).then_some(m - 1);
            }
            if matches!(
                method_tail(callee),
                "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
            ) && args.len() == 1
            {
                return match crate::operand_ty_cow(func, &args[0]).as_deref() {
                    Some(Ty::Int { width, .. }) => Some(*width as i128),
                    _ => None,
                };
            }
            return None;
        }
    }
    None
}

/// The constant upper bound of a `min(a, b)` call whose dest is `local`:
/// `min(a, b) <= c` for any const argument `c` (the result is at most the
/// smaller operand). None unless `local` is the dest of a 2-arg ordered-min
/// call with at least one constant argument.
pub(super) fn min_call_const_upper_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
            && is_ord_min_call(callee)
            && args.len() == 2
        {
            let mut best: Option<i128> = None;
            for arg in args {
                if let Some(c) = operand_const_int(arg) {
                    best = Some(best.map_or(c, |b: i128| b.min(c)));
                }
            }
            return best;
        }
    }
    None
}

/// Trust (clamp-via-helper, whole-crate summary): the constant UPPER bound this
/// function's return value provably satisfies, or None. SOUND by construction —
/// only Some(b) when EITHER every return site is a constant
/// (`function_return_const_sites`: the bound is the largest one) OR the return
/// local (`_0`) is single-assigned (directly, or through a unique whole-local
/// move/copy chain) from a const-bounded producer (clamp / rem_euclid /
/// bit-count via `cast_source_const_upper_nonneg`, or `min`-with-const). A
/// multi-assigned return whose sites are not all constants — distinct unknown
/// values on different paths — yields None (no summary; the call result stays
/// runtime-checked at use sites). The bound is always >= 0, so it discharges an
/// unsigned index use `arr[helper(..)]` when `bound < arr.len()`.
pub(super) fn function_return_const_upper_bound(func: &VerifiableFunction) -> Option<i128> {
    // Multi-return-site const shape: every return site is a constant, so the
    // LARGEST one bounds the returned value on every path. Same `>= 0` filter
    // as the SSA chain below — preserving the documented "bound is always
    // >= 0" invariant this summary's consumers rely on.
    if let Some(consts) = function_return_const_sites(func) {
        let b = *consts.last()?; // sorted ascending — the max
        return (b >= 0).then_some(b);
    }
    // The return local is `_0`. Trace it through unique whole-local move/copy
    // defs (`_0 = move _k`) to the producing local. Each hop requires single
    // assignment so the traced local's bound is THE bound on every path.
    let mut local = 0usize;
    for _ in 0..8 {
        if !is_single_static_assignment(func, local) {
            return None;
        }
        match crate::unique_whole_local_def(func, local) {
            Some(Rvalue::Use(Operand::Move(p) | Operand::Copy(p))) if p.projections.is_empty() => {
                local = p.local;
            }
            _ => break,
        }
    }
    if !is_single_static_assignment(func, local) {
        return None;
    }
    let b = cast_source_const_upper_nonneg(func, local)
        .or_else(|| min_call_const_upper_bound(func, local))?;
    (b >= 0).then_some(b)
}

/// Trust (const-return summary): the sorted, deduplicated set of integer
/// constants this function can RETURN, provided EVERY write that can define the
/// return local `_0` is a whole-local `_0 = const c` assignment. This is the
/// multi-return-site complement of the single-SSA chain in
/// [`function_return_const_upper_bound`]: a `match`-shaped helper
/// (`match g { 0 => 1, 1 => 2, _ => 4 }`) assigns `_0` a distinct constant per
/// arm, so `is_single_static_assignment(_0)` correctly refuses it — yet on
/// every path that reaches `Return`, `_0` holds the last constant written along
/// that path, which is a member of the collected set. FAIL-CLOSED None on:
///   * any non-const or projected write of `_0` (unknown value on some path);
///   * any `Call` terminator whose dest is `_0` — the written value is the
///     CALLEE's, invisible to this scan. This is also what refuses RECURSION
///     and calls the summary cannot see: a `_0 = f(..)` return site is a call
///     dest, so a self- or cross-call return path yields None;
///   * any `&mut _0` / `&raw _0` (`Rvalue::Ref{mutable}` / `AddressOf`) — a
///     write through the borrow would bypass this def scan (the exact staleness
///     kill `is_single_static_assignment` applies, hunt skeptic #2);
///   * any `SetDiscriminant`/`Deinit` of `_0`, or any `Intrinsic`/`Unsupported`
///     statement anywhere in the body — write channels this scan cannot model
///     (strictly MORE conservative than the SSA chain, which leaves those to
///     the separate fail-closed `UnsupportedMir` lane);
///   * no const write at all (nothing returned / non-int return type).
/// PANIC PATHS need no exclusion — the same argument the upper-bound summary
/// relies on: a diverging path never executes `Return`, so a claim about the
/// RETURNED value is vacuously true there, and the call-site fact is threaded
/// only to the call's SUCCESS target by `build_semantic_guard_map` (an unwind
/// edge never sees it).
pub(super) fn function_return_const_sites(func: &VerifiableFunction) -> Option<Vec<i128>> {
    let mut consts: Vec<i128> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == 0
                    {
                        return None;
                    }
                    if place.local != 0 {
                        continue;
                    }
                    if !place.projections.is_empty() {
                        return None;
                    }
                    let Rvalue::Use(op) = rvalue else { return None };
                    consts.push(operand_const_int(op)?);
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if place.local == 0 {
                        return None;
                    }
                }
                // Opaque write channels — cannot see what they define.
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => return None,
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == 0
        {
            return None;
        }
    }
    if consts.is_empty() {
        return None;
    }
    consts.sort_unstable();
    consts.dedup();
    Some(consts)
}

/// The constant LOWER bound of a call defining `local` whose result is provably
/// `>= c` for ALL inputs — the lower-direction mirror of
/// [`min_call_const_upper_bound`] and [`cast_source_const_upper_nonneg`], with
/// the same fail-closed shape (None for any unrecognized call — never a wrong
/// fact). Recognized producers, each a total theorem:
///   * `Ord::max(a, b)` with a const operand `c` → `c` (`max(v, c) >= c`
///     unconditionally; with BOTH const, the largest — the result is
///     `>= max(c1, c2)`);
///   * `Ord::clamp(v, lo, hi)` with const `0 <= lo <= hi` → `lo` (the IDENTICAL
///     gate the upper direction uses: `lo <= hi` rules out clamp's `lo > hi`
///     panic, so `result >= lo` holds on every completed call; `0 <= lo` is
///     kept so both directions recognize the same producer set);
///   * `n.rem_euclid(c)` with `|c| >= 1` → `0` (euclidean remainder is
///     non-negative regardless of the sign of `n`);
///   * `trailing_zeros`/`leading_zeros`/`count_ones`/`count_zeros` → `0`.
pub(super) fn ret_call_const_lower_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    for block in &func.body.blocks {
        if let Terminator::Call { func: callee, args, dest, .. } = &block.terminator
            && dest.local == local
            && dest.projections.is_empty()
        {
            if is_ord_max_call(callee) && args.len() == 2 {
                let mut best: Option<i128> = None;
                for arg in args {
                    if let Some(c) = operand_const_int(arg) {
                        best = Some(best.map_or(c, |b: i128| b.max(c)));
                    }
                }
                return best;
            }
            if is_ord_clamp_call(callee) && args.len() == 3 {
                let lo = operand_const_int(&args[1])?;
                let hi = operand_const_int(&args[2])?;
                return (0 <= lo && lo <= hi).then_some(lo);
            }
            if method_tail(callee) == "rem_euclid" && args.len() == 2 {
                let c = operand_const_int(&args[1])?;
                return (c != 0).then_some(0);
            }
            if matches!(
                method_tail(callee),
                "trailing_zeros" | "leading_zeros" | "count_ones" | "count_zeros"
            ) && args.len() == 1
            {
                return match crate::operand_ty_cow(func, &args[0]).as_deref() {
                    Some(Ty::Int { .. }) => Some(0),
                    _ => None,
                };
            }
            return None;
        }
    }
    None
}

/// Trust (const-return summary): the constant LOWER bound this function's
/// return value provably satisfies for ALL inputs and EVERY return path, or
/// None — the exact mirror of [`function_return_const_upper_bound`], with the
/// same two provable shapes and the same fail-closed discipline:
///   * every return site is a constant (`function_return_const_sites`) — the
///     bound is the SMALLEST one (the `small_den` shape
///     `match g { 0 => 1, 1 => 2, _ => 4 }` returns `>= 1` on every path);
///   * the single-SSA return chain ends at a call whose result is `>= c` by a
///     total theorem (`ret_call_const_lower_bound`).
/// Unlike the upper direction there is no `>= 0` FILTER on the bound: that
/// filter exists because the upper summary's purpose is unsigned-index
/// discharge (`arr[helper(i)]`), where a negative upper bound is useless; a
/// lower bound of any sign is a sound, potentially useful fact (`>= 1`
/// discharges a Rem/Div-by-zero obligation on `h % helper(..)`).
pub(super) fn function_return_const_lower_bound(func: &VerifiableFunction) -> Option<i128> {
    if let Some(consts) = function_return_const_sites(func) {
        return consts.first().copied(); // sorted ascending — the min
    }
    // Mirror of the upper chain: trace `_0` through unique whole-local
    // move/copy defs to the producing local, each hop single-assigned.
    let mut local = 0usize;
    for _ in 0..8 {
        if !is_single_static_assignment(func, local) {
            return None;
        }
        match crate::unique_whole_local_def(func, local) {
            Some(Rvalue::Use(Operand::Move(p) | Operand::Copy(p))) if p.projections.is_empty() => {
                local = p.local;
            }
            _ => break,
        }
    }
    if !is_single_static_assignment(func, local) {
        return None;
    }
    ret_call_const_lower_bound(func, local)
}

/// Trust (clamp-via-helper): whole-crate map of function name -> constant return
/// upper bound. Computed ONCE at the analysis phase over every local function
/// (see `trust_init_backing_certificates`), then consumed at call sites via the
/// `callee_return_upper_bound` thread-local to discharge a guarded access
/// THROUGH a bounding helper — e.g. `arr[clamp_idx(i)]` where
/// `fn clamp_idx(i: usize) -> usize { i.min(LEN - 1) }`. Sound: only
/// const-certain, single-assigned, non-negative return bounds are recorded; the
/// use-site emission is itself SSA-gated and staleness-versioned.
pub fn compute_return_bound_summaries(funcs: &[VerifiableFunction]) -> FxHashMap<String, i128> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(b) = function_return_const_upper_bound(func) {
            // Key on `def_path` (the full `safe_def_path_str`), NOT `name` (the
            // short item name): a call site renders its callee via
            // `func_operand_name` = `safe_def_path_str(def_id)`, so the lookup at
            // `callee_return_upper_bound(callee)` matches `def_path`, not `name`.
            map.insert(func.def_path.clone(), b);
        }
    }
    map
}

/// Trust (const-return summary): whole-crate map of function name -> constant
/// return LOWER bound — the mirror of [`compute_return_bound_summaries`], with
/// the same keying (`def_path`, matching the call site's `func_operand_name`)
/// and the same consumption shape: a call `dest = callee(..)` whose callee has
/// a recorded lower bound `c` licenses the SSA-gated, staleness-versioned fact
/// `dest >= c` at the call site (e.g. `h % small_den(g)` discharges its
/// Rem-by-zero obligation through `small_den(..) >= 1`). Sound: only bounds
/// that hold for EVERY input and EVERY return path are recorded
/// (`function_return_const_lower_bound` fails closed otherwise).
pub fn compute_return_lower_bound_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, i128> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(b) = function_return_const_lower_bound(func) {
            map.insert(func.def_path.clone(), b);
        }
    }
    map
}

/// Trust (const-return summary): whole-crate map of function name -> the exact
/// SET of constants the function can return — recorded only when EVERY return
/// site is a constant (`function_return_const_sites`, the same fail-closed scan
/// the two bound summaries build on). STRICTLY STRONGER than the bound pair:
/// `dest ∈ {1, 2, 4}` implies `1 <= dest <= 4` and additionally excludes the
/// interior non-members. Encoded at the call site as the disjunction
/// `dest == c1 ∨ … ∨ dest == ck` (sound: the callee returns one of them on
/// every completed call), keyed on `def_path` like its siblings.
pub fn compute_return_const_set_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, Vec<i128>> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(consts) = function_return_const_sites(func)
            && consts.len() <= RETURN_CONST_SET_MAX
        {
            map.insert(func.def_path.clone(), consts);
        }
    }
    map
}

/// Trust (derived trivial-setter summary): the fail-closed recognizer — see
/// [`SetterSummary`] for the soundness argument. ALL gates required; any miss
/// returns `None` (no summary, never a wrong one):
///   * control flow is ONE straight `Goto`-chain from entry to a `Return`
///     covering EVERY block (no `SwitchInt`/`Call`/`Drop`/`Assert`/`Opaque`/
///     `Unreachable`/`Resume` anywhere — no branch can bypass the store, no
///     callee/drop/unwind can run, and an off-chain block cannot hide a write);
///   * exactly ONE value-writing statement in the whole body — the store —
///     with every other statement an allowlisted no-value-effect marker
///     (storage/coverage/counter/nop), so `p` has NO other use;
///   * the store is `(*p) = <operand>` (exactly one `Deref` projection) where
///     `p` is a `&mut Int` PARAMETER of width < 128 (the 128-bit lowering is
///     BV-routed elsewhere; fail closed here);
///   * the operand is a whole (projection-free) DIFFERENT parameter of the
///     exact pointee type, or an integer constant within the pointee's range.
pub(super) fn function_trivial_setter(func: &VerifiableFunction) -> Option<SetterSummary> {
    let arg_count = func.body.arg_count;
    if arg_count == 0 || func.body.blocks.is_empty() {
        return None;
    }

    // 1. Straight entry→return goto-chain covering every block.
    let mut chain: FxHashSet<usize> = FxHashSet::default();
    let mut cur = 0usize;
    let mut returned = false;
    for _ in 0..=func.body.blocks.len() {
        if !chain.insert(cur) {
            return None; // goto cycle — never returns
        }
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::Return => {
                returned = true;
                break;
            }
            _ => return None,
        }
    }
    if !returned || chain.len() != func.body.blocks.len() {
        return None;
    }

    // 2. Classify every Assign. The pre-optimization (analysis-phase) shape of a
    //    `*p = v` setter is NOT the collapsed single store the optimizer produces
    //    (`(*_1) = _2`); it is:
    //        _3 = copy _2;        // a whole-local temp copy of the param
    //        (*_1) = move _3;     // the deref store
    //        _0 = const ();       // the implicit unit return
    //    So allow, besides the ONE deref store: (a) whole-local copies
    //    `_t = copy/move <local>` (tracked so the store source can be traced
    //    through them), and (b) the return-place unit-const assign `_0 = const ZST`.
    //    Anything else (a second deref store, a projected/computed write, a
    //    call-dest) fails closed.
    let mut store: Option<(&Place, &Rvalue)> = None;
    // whole-local copy chain: dst_local -> src_local (from `_dst = copy/move _src`)
    let mut copy_src: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    // The deref store `(*p) = ..`.
                    if matches!(place.projections.as_slice(), [trust_types::Projection::Deref]) {
                        if store.is_some() {
                            return None; // a second store — not a trivial setter
                        }
                        store = Some((place, rvalue));
                        continue;
                    }
                    if !place.projections.is_empty() {
                        return None; // a projected non-deref write (field store): reject
                    }
                    match rvalue {
                        // A whole-local copy `_dst = copy/move _src`: track it so the
                        // store source can be resolved through the chain.
                        Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                            if q.projections.is_empty() =>
                        {
                            if copy_src.insert(place.local, q.local).is_some() {
                                return None; // _dst reassigned — ambiguous
                            }
                        }
                        // The implicit unit return `_0 = const ZST` (return place,
                        // zero-sized value) — inert. Any OTHER constant write to a
                        // non-return local is a computed effect ⇒ reject.
                        Rvalue::Use(Operand::Constant(_)) if place.local == 0 => {}
                        _ => return None,
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::Coverage
                | Statement::ConstEvalCounter => {}
                _ => return None,
            }
        }
    }
    let (place, rvalue) = store?;

    // 3. The store is `(*p) = <operand>` with `p` a `&mut Int{<128}` parameter.
    if !matches!(place.projections.as_slice(), [trust_types::Projection::Deref]) {
        return None;
    }
    let p = place.local;
    if p < 1 || p > arg_count {
        return None;
    }
    let (width, signed) = match &func.body.locals.iter().find(|d| d.index == p)?.ty {
        Ty::Ref { mutable: true, inner } => match inner.as_ref() {
            Ty::Int { width, signed } if (1..128).contains(width) => (*width, *signed),
            _ => return None,
        },
        _ => return None,
    };

    // Resolve a whole-local operand through the copy chain (`_3` <- `_2`) to its
    // root local, bounded by the chain length to avoid a cycle.
    let resolve_root = |mut l: usize| -> usize {
        for _ in 0..=copy_src.len() {
            match copy_src.get(&l) {
                Some(&next) => l = next,
                None => break,
            }
        }
        l
    };

    // 4. The stored operand: a whole DIFFERENT parameter of the exact pointee
    //    type (possibly via the analysis-phase temp copy chain), or a
    //    pointee-range integer constant.
    let src = match rvalue {
        Rvalue::Use(Operand::Copy(q) | Operand::Move(q)) if q.projections.is_empty() => {
            let root = resolve_root(q.local);
            if root >= 1 && root <= arg_count && root != p && func.body.locals.iter().any(|d| {
                d.index == root
                    && matches!(d.ty, Ty::Int { width: w, signed: s } if w == width && s == signed)
            }) {
                SetterSrc::Param(root)
            } else {
                return None;
            }
        }
        Rvalue::Use(op @ Operand::Constant(_)) => {
            let c = operand_const_int(op)?;
            let (lo, hi) = int_type_bounds(width, signed);
            if c < lo || c > hi {
                return None;
            }
            SetterSrc::Const(c)
        }
        _ => return None,
    };

    Some(SetterSummary { param_count: arg_count, ptr_param: p, pointee: (width, signed), src })
}

/// Inclusive value range of an integer type (`width < 128` — guarded by every
/// caller; a 128-bit range does not fit `i128`).
pub(super) fn int_type_bounds(width: u32, signed: bool) -> (i128, i128) {
    if signed {
        (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
    } else {
        (0, (1i128 << width) - 1)
    }
}

/// Trust (derived trivial-setter summary): whole-crate map of function
/// def-path -> trivial-setter effect. Keyed on `def_path` like its const-return
/// siblings (matching the call site's `func_operand_name`); computed once at
/// the analysis phase over every local function and consumed at call sites via
/// the `callee_setter_summary` thread-local. Fail-closed by construction: only
/// bodies [`function_trivial_setter`] fully recognizes are recorded.
pub fn compute_trivial_setter_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, SetterSummary> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(summary) = function_trivial_setter(func) {
            map.insert(func.def_path.clone(), summary);
        }
    }
    map
}

/// Trust (derived trivial-setter summary, call-site half): the caller local a
/// call argument `Move(_t)`/`Copy(_t)` UNAMBIGUOUSLY mut-borrows — `_t`'s ONE
/// whole-local definition is `&mut <bare local>` and nothing can reseat `_t`.
/// ALL gates required (any miss → `None`, no fact):
///   * no `Call` terminator writes `_t` (a call-returned pointer is opaque);
///   * `_t` is never itself borrowed (`& _t` / `&mut _t` / `&raw _t` could
///     reseat the pointer invisibly);
///   * exactly one whole-local def ([`crate::unique_whole_local_def`], which
///     also rejects projected stores), and it is `Ref { mutable: true }` of a
///     PROJECTION-FREE place (a reborrow `&mut *r` / field borrow `&mut s.f`
///     stays fail-closed).
pub(super) fn callsite_unique_mut_borrow_target(func: &VerifiableFunction, temp: usize) -> Option<usize> {
    for block in &func.body.blocks {
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == temp
        {
            return None;
        }
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt
                && let Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) = rvalue
                && place.local == temp
            {
                return None;
            }
        }
    }
    match crate::unique_whole_local_def(func, temp)? {
        Rvalue::Ref { mutable: true, place } if place.projections.is_empty() => Some(place.local),
        _ => None,
    }
}

/// Trust (derived trivial-setter summary): the exact, fully-VERSIONED post-call
/// fact of a recognized trivial-setter call terminating `block`, or `None`
/// (fail-closed). Returns `(target_local, Eq(target#s{b}_t, value))`.
///
/// The fact: after `set(&mut a, v)` returns, `a == v` — the callee's single
/// value write stores exactly the value argument (or the summarized constant)
/// through the pointer argument, and the recognizer admits no other effect
/// channel (see [`SetterSummary`]; the recognizer IS the proof, independent of
/// the callee's own verdict).
///
/// VERSIONING (shared by both consuming lanes): the value operand is read at
/// the block TERMINAL — its PRE-call value, which the callee cannot touch (it
/// receives it by value) — and the target is pinned to the terminator marker
/// `s{b}_t`, the SAME token the terminator-aware oracle gives every post-call
/// read of the mut-borrowed target, and name-disjoint from any later
/// reassignment (`version_terminator_dest_fact`). Both sides name one
/// consistent per-execution snapshot, so the fact is TRUE of every execution
/// that continues past this call — sound to conjoin in both the guard-threading
/// (UNSAT ⇒ proved) and the refutation (SAT ⇒ counterexample) polarity.
///
/// ALL call-site gates fail closed (no fact, never a wrong one): exact arity;
/// the ptr actual a whole local whose ONE def is `&mut <bare local>` with no
/// reseat channel ([`callsite_unique_mut_borrow_target`]); the target's
/// declared type EXACTLY the summarized pointee; the value actual a constant or
/// a whole local distinct from both the target (the `set(&mut a, a)` tautology
/// adds nothing) and the borrow temp.
pub(super) fn trivial_setter_callsite_fact(
    sv: &StmtVersionCtx,
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, Formula)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    let setter = crate::callee_setter_summary(callee)?;
    if args.len() != setter.param_count {
        return None;
    }
    let ptr_idx = setter.ptr_param.checked_sub(1)?;
    let (Operand::Copy(pp) | Operand::Move(pp)) = args.get(ptr_idx)? else {
        return None;
    };
    if !pp.projections.is_empty() {
        return None;
    }
    let target = callsite_unique_mut_borrow_target(func, pp.local)?;
    if dest.local == target
        || !func.body.locals.iter().any(|d| {
            d.index == target
                && matches!(d.ty, Ty::Int { width, signed } if (width, signed) == setter.pointee)
        })
    {
        return None;
    }
    let value = match &setter.src {
        SetterSrc::Const(c) => Formula::Int(*c),
        SetterSrc::Param(j) => match j.checked_sub(1).and_then(|i| args.get(i))? {
            op @ Operand::Constant(_) => Formula::Int(operand_const_int(op)?),
            op @ (Operand::Copy(q) | Operand::Move(q))
                if q.projections.is_empty() && q.local != target && q.local != pp.local =>
            {
                operand_to_formula(func, op)
            }
            _ => return None,
        },
    };
    let target_name = crate::place_to_var_name(func, &Place::local(target));
    let fact = Formula::Eq(Box::new(Formula::Var(target_name.clone(), Sort::Int)), Box::new(value));
    Some((target, version_terminator_dest_fact(sv, func, block, &target_name, fact)))
}

/// The UNVERSIONED trivial-setter post-call fact `(target_local, Eq(target, value))`
/// — the raw form of [`trivial_setter_callsite_fact`] BEFORE `version_terminator_dest_fact`
/// pins the target token. The refute-lane consumer versions it (and its copy-chain
/// links) at the ASSERT use-point via `version_rename_at` instead — the same
/// reaching-def use-point versioning `stmt_defs` rely on, so the target token
/// unifies with the assert formula's own token by construction (a pre-call read
/// gets a different reaching-def token and stays inert, so staleness is still
/// caught). The pre-pinned form's terminator token did NOT match the assert's
/// post-call read token once the trust-ir flip re-versioned the copy, leaving the
/// fact disjoint (the setter-identity fixture's residual).
pub(super) fn trivial_setter_callsite_fact_unversioned(
    func: &VerifiableFunction,
    block: &trust_types::BasicBlock,
) -> Option<(usize, Formula)> {
    let Terminator::Call { func: callee, args, dest, target: Some(_), .. } = &block.terminator
    else {
        return None;
    };
    let setter = crate::callee_setter_summary(callee)?;
    if args.len() != setter.param_count {
        return None;
    }
    let ptr_idx = setter.ptr_param.checked_sub(1)?;
    let (Operand::Copy(pp) | Operand::Move(pp)) = args.get(ptr_idx)? else {
        return None;
    };
    if !pp.projections.is_empty() {
        return None;
    }
    let target = callsite_unique_mut_borrow_target(func, pp.local)?;
    if dest.local == target
        || !func.body.locals.iter().any(|d| {
            d.index == target
                && matches!(d.ty, Ty::Int { width, signed } if (width, signed) == setter.pointee)
        })
    {
        return None;
    }
    let value = match &setter.src {
        SetterSrc::Const(c) => Formula::Int(*c),
        SetterSrc::Param(j) => match j.checked_sub(1).and_then(|i| args.get(i))? {
            op @ Operand::Constant(_) => Formula::Int(operand_const_int(op)?),
            op @ (Operand::Copy(q) | Operand::Move(q))
                if q.projections.is_empty() && q.local != target && q.local != pp.local =>
            {
                operand_to_formula(func, op)
            }
            _ => return None,
        },
    };
    let target_name = crate::place_to_var_name(func, &Place::local(target));
    Some((target, Formula::Eq(Box::new(Formula::Var(target_name, Sort::Int)), Box::new(value))))
}

/// The MODELED flattened std `Option`/`Result` type gate (the `lower_enum_adt`
/// shape): std enum def-path name + the explicit `__tag` slot + BOTH variant
/// defs present with their real discriminant tags. Returns the matched enum
/// name and its variant defs; `None` for every other type — in particular a
/// USER enum named like `Result` (wrong def-path) or a degraded pre-P4
/// lowering (no variant defs) never matches. Shared by the unwrap
/// panic-freedom receiver gate and the return-discriminant summary so the two
/// recognizers can never drift.
pub(crate) fn modeled_std_enum_shape(ty: &Ty) -> Option<(&str, &[trust_types::VariantDef])> {
    const MODELED: &[(&str, [&str; 2])] = &[
        ("core::option::Option", ["None", "Some"]),
        ("std::option::Option", ["None", "Some"]),
        ("core::result::Result", ["Ok", "Err"]),
        ("std::result::Result", ["Ok", "Err"]),
    ];
    let Ty::Adt { name, fields, variants, .. } = ty else { return None };
    let (_, expected) = MODELED.iter().find(|(p, _)| *p == name.as_str())?;
    (fields.iter().any(|(f, _)| f == "__tag")
        && variants.len() == 2
        && expected.iter().all(|v| variants.iter().any(|vd| vd.name == *v)))
    .then(|| (name.as_str(), variants.as_slice()))
}

/// Trust (return-discriminant summary): every `_0` construction site as
/// `(block ordinal, variant index)` — the enum-construction analogue of
/// [`function_return_const_sites`], with the IDENTICAL fail-closed write-channel
/// discipline. `None` on:
///   * any write of `_0` that is not a whole-local ADT aggregate of the
///     callee's own return enum (`Use`/`Cast`/projected store: an unknown tag
///     on some path; a `variant` out of range: a mis-lowered aggregate);
///   * any `Call` dest `_0` (the tag is the CALLEE's — invisible; this also
///     refuses recursion, exactly like the const-return scan);
///   * any `&mut _0` / `&raw _0` borrow, `SetDiscriminant`/`Deinit` of `_0`,
///     or an `Intrinsic`/`Unsupported` statement anywhere (opaque channels);
///   * no construction site at all.
/// PANIC PATHS need no exclusion — a diverging path never executes `Return`,
/// so a claim about the RETURNED tag is vacuously true there (the same
/// argument on `function_return_const_sites`).
pub(super) fn function_return_variant_sites(
    func: &VerifiableFunction,
    enum_name: &str,
    n_variants: usize,
) -> Option<Vec<(usize, usize)>> {
    let mut sites: Vec<(usize, usize)> = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            match stmt {
                Statement::Assign { place, rvalue, .. } => {
                    if let Rvalue::Ref { mutable: true, place: borrowed }
                    | Rvalue::AddressOf(_, borrowed) = rvalue
                        && borrowed.local == 0
                    {
                        return None;
                    }
                    if place.local != 0 {
                        continue;
                    }
                    if !place.projections.is_empty() {
                        return None;
                    }
                    let Rvalue::Aggregate(
                        AggregateKind::Adt { name, variant, active_field: None, .. },
                        _,
                    ) = rvalue
                    else {
                        return None;
                    };
                    if name != enum_name || *variant >= n_variants {
                        return None;
                    }
                    sites.push((block.id.0, *variant));
                }
                Statement::SetDiscriminant { place, .. } | Statement::Deinit { place } => {
                    if place.local == 0 {
                        return None;
                    }
                }
                Statement::Intrinsic { .. } | Statement::Unsupported { .. } => return None,
                _ => {}
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == 0
        {
            return None;
        }
    }
    (!sites.is_empty()).then_some(sites)
}

/// The ordinal of the FIRST branch point reachable from entry, provided the
/// prefix is a STRAIGHT LINE of `Goto`-terminated blocks (no call that could
/// write state the branch reads, no second decision, no early return). `None`
/// for any other prefix shape — including a `Goto` cycle, which exhausts the
/// step bound.
pub(super) fn entry_prefix_switch_ordinal(func: &VerifiableFunction) -> Option<usize> {
    let mut cur = 0usize;
    for _ in 0..=func.body.blocks.len() {
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::SwitchInt { .. } => return Some(cur),
            _ => return None,
        }
    }
    None
}

/// Resolve `op` to a formula denoting a value that is IDENTICAL on every
/// execution and every program point of `func` — the vocabulary a
/// return-discriminant summary may be built from (callee side) or instantiated
/// with (caller side). Exactly three shapes, everything else `None`:
///   * an integer/bool CONSTANT (ground — trivially execution-invariant);
///   * a PINNED parameter, possibly through single-def whole-local copy/move
///     hops: `place_source_is_stable` (no projected store, no `&mut`/`&raw`
///     borrow, no `SetDiscriminant`/`Deinit`) PLUS zero whole-local defs — a
///     parameter is initialized at entry, so ANY body store (statement or call
///     dest, counted by `whole_local_def_count`) would make it two-valued;
///   * a local whose unique stable def is a CONSTANT assignment (`x = const c`
///     — re-executing the def in a loop rewrites the SAME value), folded to
///     that constant.
/// The pinning matters on BOTH sides: the callee's `cond` must read ENTRY
/// parameter values (the values the caller's actuals denote), and a caller
/// actual substituted into the VC must still denote the call-time value at the
/// downstream unwrap block (a reassignable actual could go stale between the
/// two — the S2c staleness class — so it is refused, never versioned here).
pub(super) fn entry_stable_operand_formula(func: &VerifiableFunction, op: &Operand) -> Option<Formula> {
    let ground_const = |f: Formula| matches!(f, Formula::Int(_) | Formula::Bool(_)).then_some(f);
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return ground_const(crate::operand_to_formula(func, op));
    };
    if !p.projections.is_empty() {
        return None;
    }
    let mut cur = p.local;
    for _ in 0..8 {
        if !crate::place_source_is_stable(func, cur) {
            return None;
        }
        if (1..=func.body.arg_count).contains(&cur) {
            if guards::whole_local_def_count(func, cur) > 0 {
                return None;
            }
            return Some(crate::operand_to_formula(func, &Operand::Copy(Place::local(cur))));
        }
        match crate::unique_whole_local_def(func, cur) {
            Some(Rvalue::Use(Operand::Copy(q) | Operand::Move(q)))
                if q.projections.is_empty() && q.local != cur =>
            {
                cur = q.local;
            }
            Some(Rvalue::Use(c @ Operand::Constant(_))) => {
                return ground_const(crate::operand_to_formula(func, c));
            }
            _ => return None,
        }
    }
    None
}

/// The unique stable non-copy defining rvalue of `local`, traced through
/// single-def whole-local copy/move hops (the compiler-inserted temp chain).
/// Every hop and the terminus must be `place_source_is_stable`.
pub(super) fn stable_unique_def_through_copies<'a>(
    func: &'a VerifiableFunction,
    local: usize,
) -> Option<&'a Rvalue> {
    let mut cur = local;
    for _ in 0..8 {
        if !crate::place_source_is_stable(func, cur) {
            return None;
        }
        match crate::unique_whole_local_def(func, cur)? {
            Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                if q.projections.is_empty() && q.local != cur =>
            {
                cur = q.local;
            }
            rv => return Some(rv),
        }
    }
    None
}

/// A comparison `BinOp` as a `Formula` over already-resolved operands; `None`
/// for every non-comparison op (arithmetic feeding a switch is not a shape the
/// summary models).
pub(super) fn comparison_formula(op: BinOp, lhs: Formula, rhs: Formula) -> Option<Formula> {
    let (l, r) = (Box::new(lhs), Box::new(rhs));
    Some(match op {
        BinOp::Eq => Formula::Eq(l, r),
        BinOp::Ne => Formula::Not(Box::new(Formula::Eq(l, r))),
        BinOp::Lt => Formula::Lt(l, r),
        BinOp::Le => Formula::Le(l, r),
        BinOp::Gt => Formula::Gt(l, r),
        BinOp::Ge => Formula::Ge(l, r),
        _ => return None,
    })
}

/// The dominating entry condition of a TWO-WAY switch as a formula over the
/// callee's pinned parameters, plus the `(true arm, false arm)` block ordinals.
/// Recognized discriminee shapes (each fail-closed via
/// [`entry_stable_operand_formula`]):
///   * a BOOL comparison temp (`_c = Eq(den, 0); switchInt(_c)` — the real
///     `if den == 0` lowering, either polarity via [`comparison_formula`]);
///   * an entry-stable BOOL value itself (`if flag`);
///   * an entry-stable INTEGER discriminee (`match den { 0 => .., _ => .. }`):
///     `cond = (den == v0)` with the explicit target as the true arm.
pub(super) fn switch_cond_and_arms(
    func: &VerifiableFunction,
    discr: &Operand,
    v0: u128,
    t0: usize,
    otherwise: usize,
) -> Option<(Formula, usize, usize)> {
    // Bool-polarity arm split: the explicit `(v0, t0)` edge is taken when the
    // bool discriminee EQUALS v0, so v0 == 0 makes t0 the FALSE arm.
    let bool_arms = |v0: u128| match v0 {
        0 => Some((otherwise, t0)),
        1 => Some((t0, otherwise)),
        _ => None,
    };
    if let Some(f) = entry_stable_operand_formula(func, discr) {
        let is_bool = matches!(&f, Formula::Bool(_))
            || matches!(&f, Formula::Var(_, Sort::Bool) | Formula::SymVar(_, Sort::Bool));
        if is_bool {
            let (t_arm, f_arm) = bool_arms(v0)?;
            return Some((f, t_arm, f_arm));
        }
        let is_int = matches!(&f, Formula::Int(_))
            || matches!(&f, Formula::Var(_, Sort::Int) | Formula::SymVar(_, Sort::Int));
        if !is_int {
            return None;
        }
        let v = i128::try_from(v0).ok()?;
        return Some((Formula::Eq(Box::new(f), Box::new(Formula::Int(v))), t0, otherwise));
    }
    let (Operand::Copy(p) | Operand::Move(p)) = discr else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    let Rvalue::BinaryOp(op, a, b) = stable_unique_def_through_copies(func, p.local)? else {
        return None;
    };
    let fa = entry_stable_operand_formula(func, a)?;
    let fb = entry_stable_operand_formula(func, b)?;
    let cond = comparison_formula(*op, fa, fb)?;
    let (t_arm, f_arm) = bool_arms(v0)?;
    Some((cond, t_arm, f_arm))
}

/// Walk the STRAIGHT-LINE continuation from arm block `start` to `Return` and
/// return the variant of the EXACTLY-ONE `_0` construction site the path
/// passes. `None` (fail-closed) on: a revisited block (a loop), a second
/// branch point (`SwitchInt`), any opaque/diverging terminator (`Opaque`,
/// `Unreachable`, `Resume`, a no-target call — an arm that never returns has
/// no returned tag to summarize), zero sites, or two sites on one path. `Goto`
/// / normally-returning `Call` / `Drop` / `Assert` continuations are allowed
/// AFTER the decision: a panicking call/assert never returns (vacuous), the
/// global site scan already refused every `_0`-writing channel they could
/// carry, and the cond parameters are pinned (never written or `&mut`-borrowed
/// anywhere), so no continuation can invalidate the entry condition.
pub(super) fn arm_single_site_variant(
    func: &VerifiableFunction,
    start: usize,
    sites: &[(usize, usize)],
) -> Option<usize> {
    let mut cur = start;
    let mut seen: FxHashSet<usize> = FxHashSet::default();
    let mut found: Option<usize> = None;
    loop {
        if !seen.insert(cur) {
            return None;
        }
        let block = func.body.blocks.get(cur).filter(|b| b.id.0 == cur)?;
        if let Some((_, v)) = sites.iter().find(|(b, _)| *b == cur) {
            if found.is_some() {
                return None;
            }
            found = Some(*v);
        }
        match &block.terminator {
            Terminator::Goto(t) => cur = t.0,
            Terminator::Call { target: Some(t), .. } => cur = t.0,
            Terminator::Drop { target, .. } => cur = target.0,
            Terminator::Assert { target, .. } => cur = target.0,
            Terminator::Return => return found,
            _ => return None,
        }
    }
}

/// Trust (return-discriminant summary): the [`ReturnDiscSummary`] of one local
/// function, or `None` for EVERY shape outside the two provable grades. See
/// the type docs for the soundness argument; the structural guarantees are:
///   * the return type is the modeled flattened std enum
///     ([`modeled_std_enum_shape`]);
///   * every `_0` write channel is a whole-local aggregate construction site
///     ([`function_return_variant_sites`] fails closed otherwise);
///   * UNCONDITIONAL: all sites construct one variant — the returned value at
///     ANY `Return` is that variant (MIR initializes `_0` before `Return`, and
///     no other write channel exists);
///   * GUARD-CONDITIONED: exactly two distinct-variant sites in distinct
///     blocks, and the WHOLE CFG is `entry --straight-line--> switch -->
///     (armT | armF) --straight-line--> Return` — so every returning execution
///     takes exactly one arm, whose single site fixes the returned tag, and
///     the arm taken is decided by `cond` over ENTRY parameter values (the
///     parameters are pinned: never written, never `&mut`-borrowed).
pub(crate) fn function_return_disc_summary(func: &VerifiableFunction) -> Option<ReturnDiscSummary> {
    let ret_ty = crate::local_ty_ref(func, 0)?;
    let (enum_name, variants) = modeled_std_enum_shape(ret_ty)?;
    let sites = function_return_variant_sites(func, enum_name, variants.len())?;
    let params: Vec<String> =
        (1..=func.body.arg_count).map(|i| place_to_var_name(func, &Place::local(i))).collect();
    let enum_name = enum_name.to_string();
    let first_variant = sites[0].1;
    if sites.iter().all(|(_, v)| *v == first_variant) {
        let tag = variants.get(first_variant)?.discriminant;
        return Some(ReturnDiscSummary {
            enum_name,
            params,
            cases: ReturnDiscCases::Unconditional { tag },
        });
    }
    // Two construction sites with distinct variants (in distinct blocks — a
    // double-write block would make "which write returns" order-sensitive).
    let [(blk_a, _), (blk_b, _)] = sites.as_slice() else { return None };
    if blk_a == blk_b {
        return None;
    }
    let sw = entry_prefix_switch_ordinal(func)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &func.body.blocks[sw].terminator
    else {
        return None;
    };
    let [(v0, t0)] = targets.as_slice() else { return None };
    let (cond, true_arm, false_arm) = switch_cond_and_arms(func, discr, *v0, t0.0, otherwise.0)?;
    // Belt: every free var of `cond` must be a formal — the substitution keys —
    // so instantiation can never leave a callee-internal symbol to capture a
    // same-named caller local (the `postcondition_rebindable` discipline).
    if !cond.free_variables().iter().all(|v| params.iter().any(|p| p == v)) {
        return None;
    }
    let vt = arm_single_site_variant(func, true_arm, &sites)?;
    let vf = arm_single_site_variant(func, false_arm, &sites)?;
    if vt == vf {
        // Both arms funnel into ONE shared-tail site — the other site is
        // unreachable, so the returned variant is unconditional after all.
        let tag = variants.get(vt)?.discriminant;
        return Some(ReturnDiscSummary {
            enum_name,
            params,
            cases: ReturnDiscCases::Unconditional { tag },
        });
    }
    Some(ReturnDiscSummary {
        enum_name,
        params,
        cases: ReturnDiscCases::GuardConditioned {
            cond,
            then_tag: variants.get(vt)?.discriminant,
            else_tag: variants.get(vf)?.discriminant,
        },
    })
}

/// Trust (return-discriminant summary): whole-crate map of function def-path ->
/// returned-tag shape — the discriminant sibling of
/// [`compute_return_bound_summaries`], with the same keying (`def_path`,
/// matching the call site's `func_operand_name`) and the same
/// compute-once-per-crate / thread-local-copy consumption discipline. Consumed
/// by the unwrap panic-freedom lane's summary-pinned receiver shape (see
/// `unwrap_panic_freedom_body`); a function outside the two provable grades
/// records nothing (fail-closed).
pub fn compute_return_disc_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, ReturnDiscSummary> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(s) = function_return_disc_summary(func) {
            map.insert(func.def_path.clone(), s);
        }
    }
    map
}

/// Trust (inferred contract): whole-crate map of function def-path ->
/// bool-pred summary — computed once per crate beside its four siblings.
/// Empty map ⇒ zero behavior change.
pub fn compute_return_bool_pred_summaries(
    funcs: &[VerifiableFunction],
) -> FxHashMap<String, ReturnBoolPredSummary> {
    let mut map = FxHashMap::default();
    for func in funcs {
        if let Some(s) = function_return_bool_pred_summary(func) {
            map.insert(func.def_path.clone(), s);
        }
    }
    map
}

/// Trust (inferred contract): derive the bool-pred summary from a callee BODY,
/// fail-closed on everything outside two rigid, whole-CFG-proven shapes:
///
///   * Tier 1 — the single-probe body: `bb0: _b = &(*_1); Call probe(_b) ->
///     dest, bbR; …; Return` where the probe is a modeled std
///     `is_some`/`is_none`/`is_ok`/`is_err` on the one pinned `&Enum` param and
///     `_0` is (or is copied from) the probe result on a straight line to the
///     single Return.
///   * Tier 2a — the discriminant-switch body (`matches!(o, Some(_))`):
///     `_d = discriminant(*_1); switch _d [k → bbA] else bbB` where bbA/bbB
///     assign `_0` opposite Bool constants and converge straight-line to
///     Return. Normalized to `==` via the two-variant complement.
///
/// Common gates: exactly one param, `&`(shared)`Enum` of the modeled flattened
/// std shape; the param is pinned (no writes, no `&mut`); `_0: Ty::Bool`;
/// no other calls in the body; every terminator ∈ {the one Call/Switch, Goto,
/// Return}; exactly one Return. SOUNDNESS: the recorded fact is checked
/// against the WHOLE CFG (any unrecognized block/stmt/terminator ⇒ `None`), a
/// shared-ref pointee's tag cannot change during the body, and the summary is
/// derived per-definition with generics erased — the shape gates are
/// instantiation-invariant (the tag layout is the flattened std shape for
/// every instantiation the extractor models).
pub(super) fn function_return_bool_pred_summary(func: &VerifiableFunction) -> Option<ReturnBoolPredSummary> {
    // Common gates. MULTI-PARAM: the predicate subject is param `_1` (enum-first
    // idiom, incl. `&self`); extra params `_2..` are permitted but the body must
    // STILL bind `_0` solely from `_1`'s probe/discriminant. The entry-block
    // dominance gate (find_param_probe / tier2a) rejects any body where an extra
    // param branches into `_0` (`if flag { false } else { o.is_some() }` puts the
    // probe off-entry ⇒ declined), and the census (calls∈{0,1}, one Return)
    // rejects a second call/return an extra param would need — so
    // `ret ⇔ tag(*_1) REL T` holds for ANY values of the extra params.
    if func.body.arg_count < 1 {
        return None;
    }
    let ret_ty = crate::local_ty_ref(func, 0)?;
    if !matches!(ret_ty, Ty::Bool) {
        return None;
    }
    // Whole-CFG hygiene: exactly one non-{Goto, Return, SwitchInt} terminator
    // (the probe Call, if any), exactly one Return.
    let mut calls = 0usize;
    let mut returns = 0usize;
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::Call { .. } => calls += 1,
            Terminator::Return => returns += 1,
            Terminator::Goto(_) | Terminator::SwitchInt { .. } => {}
            _ => return None,
        }
    }
    if returns != 1 {
        return None;
    }
    // Formal-parameter names at FULL arity — the consumer matches
    // `args.len() == params.len()`, so a multi-param helper only connects at a
    // call of the same arity (the pred actual is `args[pred_param-1]`).
    let params: Vec<String> =
        (1..=func.body.arg_count).map(|i| place_to_var_name(func, &Place::local(i))).collect();

    // The predicate SUBJECT may be ANY parameter, not just `_1` — try each in
    // order and return the first that yields a summary. The body probes/switches
    // on exactly ONE param (find_param_probe / tier2a anchor the receiver /
    // discriminant to `pred_local`), so at most one candidate matches; a body
    // probing a DIFFERENT param than `pred_local` fails closed. Subject shape
    // from the param type:
    //   &Enum   -> whole pointee, BY-REFERENCE (probe receiver `&(*p)`)
    //   Enum    -> whole pointee, BY-VALUE (probe receiver `&p`; Copy param)
    //   &Struct -> a modeled-enum FIELD of the pointee (field subject)
    for pred_local in 1..=func.body.arg_count {
        if !unwrap_receiver_local_is_pinned(func, pred_local) {
            continue;
        }
        let Some(param_ty) = crate::local_ty_ref(func, pred_local) else {
            continue;
        };
        let (whole_enum, by_value) = match param_ty {
            Ty::Ref { mutable: false, inner } => (modeled_std_enum_shape(inner), false),
            other => (modeled_std_enum_shape(other), true),
        };
        let found = if let Some((enum_name, variants)) = whole_enum {
            let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
            if calls == 1 {
                tier1_probe_body_summary(
                    func,
                    enum_name,
                    variants,
                    variant_tags.clone(),
                    params.clone(),
                    by_value,
                    pred_local,
                )
                .or_else(|| {
                    tier2b_probe_switch_body_summary(
                        func,
                        enum_name,
                        variants,
                        variant_tags,
                        params.clone(),
                        by_value,
                        pred_local,
                    )
                })
            } else if calls == 0 {
                tier2a_switch_body_summary(
                    func,
                    enum_name,
                    variants,
                    variant_tags,
                    params.clone(),
                    by_value,
                    pred_local,
                )
            } else {
                None
            }
        } else if !by_value && calls == 1 {
            // Field subject: a `&Struct` param whose PROBED field is a modeled
            // enum (`fn is_ready(&self) -> bool { self.field.is_some() }`).
            tier1_field_probe_body_summary(func, params.clone(), pred_local)
        } else {
            None
        };
        if found.is_some() {
            return found;
        }
    }
    None
}

/// Locate THE probe call (`is_some`/`is_none`/`is_ok`/`is_err` on the modeled
/// enum) whose shared-ref receiver resolves to the param `_1`, and confirm the
/// call block writes neither `_1`/`*_1` nor the result `_0`. Returns the
/// probe's bool dest local, its success block, and the probed variant name.
/// Shared by Tier 1 (result flows straight to `_0`) and Tier 2b (result feeds a
/// switch). Fail-closed on any deviation.
pub(super) fn find_param_probe(
    func: &VerifiableFunction,
    enum_name: &str,
    by_value: bool,
    pred_local: usize,
) -> Option<(usize, BlockId, &'static str)> {
    // SOUNDNESS: the probe must be the ENTRY block so it DOMINATES the Return —
    // every execution binds `_0` from the probe result. A body that branches on
    // an UNRELATED value first (`FLAG || o.is_some()`) puts the probe in a
    // non-entry block behind a bypass arm that stores `_0` a constant; walking
    // only the probe's forward path would then mis-summarize `ret ⇔ tag==T`
    // when `ret` is actually true for a non-`T` tag. Fail-closed on a non-entry
    // probe. (Tier 2b's switch is on the probe RESULT, which still dominates.)
    let call_block = func.body.blocks.first()?;
    let Terminator::Call { func: callee, args, dest, target: Some(target), .. } =
        &call_block.terminator
    else {
        return None;
    };
    let (callee, target) = (callee.as_str(), *target);
    let (probe_paths, probe_variant) = std_option_result_probe_variant(callee)?;
    if !probe_paths.contains(&enum_name) {
        return None;
    }
    // Receiver: the arg passed to the probe must resolve to the param `_1` —
    // passed directly (`is_some(copy _1)`), through bare copy/move hops, or as a
    // shared reborrow temp (`_t = &(*_1)`).
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    fn chained_to_param(func: &VerifiableFunction, mut local: usize, pred_local: usize) -> bool {
        for _ in 0..4 {
            if local == pred_local {
                return true;
            }
            // SOUNDNESS (aliased reseat, audit r3): an unpinned intermediate has
            // a stale copy def (a `&mut`-alias reseat is invisible to
            // `unique_whole_local_def`), so the receiver could actually point
            // elsewhere and the recorded summary would be WRONG. Require each hop
            // pinned before trusting its def.
            if !unwrap_receiver_local_is_pinned(func, local) {
                return false;
            }
            match crate::unique_whole_local_def(func, local) {
                Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                    if p.projections.is_empty() =>
                {
                    local = p.local;
                }
                _ => return false,
            }
        }
        local == pred_local
    }
    // The probe's `&self` receiver borrows the SUBJECT: for a `&Enum` param
    // that is `*_1` (`&(*_1)`, or `_1` passed directly / via copy-hops since
    // `_1` is already a shared ref); for a BY-VALUE `Enum` param it is the whole
    // param `&_1` (referent `_1`, no projection).
    // The reborrow temp whose `&(*_1)`/`&_1` def we trust must itself be PINNED
    // (a `&mut`-reseated temp has a stale borrow def — audit r3 class).
    let recv_pinned = unwrap_receiver_local_is_pinned(func, recv.local);
    let receiver_ok = if by_value {
        recv_pinned
            && matches!(
                crate::unique_whole_local_def(func, recv.local),
                Some(Rvalue::Ref { mutable: false, place: referent })
                    if referent.local == pred_local && referent.projections.is_empty()
            )
    } else {
        chained_to_param(func, recv.local, pred_local)
            || (recv_pinned
                && matches!(
                    crate::unique_whole_local_def(func, recv.local),
                    Some(Rvalue::Ref { mutable: false, place: referent })
                        if referent.local == pred_local
                            && referent.projections.as_slice()
                                == [trust_types::Projection::Deref]
                ))
    };
    if !receiver_ok {
        return None;
    }
    // The call block's own statements may set up the receiver but must NOT write
    // the subject param (or its deref) or the result `_0`. Storage annotations
    // carry no data effect and are skipped.
    for stmt in &call_block.stmts {
        match stmt {
            Statement::StorageLive(_) | Statement::StorageDead(_) => {}
            Statement::Assign { place, .. } if place.local != 0 && place.local != pred_local => {}
            _ => return None,
        }
    }
    if !dest.projections.is_empty() {
        return None;
    }
    Some((dest.local, target, probe_variant))
}

/// Walk a straight-line chain of blocks that assigns `_0` a single Bool
/// constant and converges on a Return, skipping storage annotations. `None` if
/// the arm does anything else. Shared by Tier 2a and Tier 2b.
pub(super) fn straight_line_bool_arm(func: &VerifiableFunction, start: BlockId) -> Option<bool> {
    let mut cur = start;
    let mut value: Option<bool> = None;
    for _ in 0..8 {
        let block = func.body.blocks.get(cur.0)?;
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_) | Statement::StorageDead(_) => continue,
                Statement::Assign { place, rvalue, .. }
                    if place.local == 0
                        && place.projections.is_empty()
                        && value.is_none()
                        && matches!(
                            rvalue,
                            Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(_)))
                        ) =>
                {
                    let Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(b))) = rvalue
                    else {
                        unreachable!()
                    };
                    value = Some(*b);
                }
                _ => return None,
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Return => return value,
            _ => return None,
        }
    }
    None
}

/// Tier 1 of [`function_return_bool_pred_summary`].
pub(super) fn tier1_probe_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    variant_tags: Vec<i128>,
    params: Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let (dest_local, target, probe_variant) =
        find_param_probe(func, enum_name, by_value, pred_local)?;
    if !probe_result_reaches_return(func, dest_local, target) {
        return None;
    }
    let pred_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params,
        pred_param: pred_local,
        pred_field: None,
        kind: ReturnBoolPredKind::Iff,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// The probe result in `dest_local` flows straight-line into `_0` and reaches
/// the single Return, skipping storage annotations. Shared by Tier 1 (whole
/// pointee) and its field-subject sibling.
pub(super) fn probe_result_reaches_return(
    func: &VerifiableFunction,
    dest_local: usize,
    target: BlockId,
) -> bool {
    let mut cur = target;
    let mut ret_bound = dest_local == 0;
    for _ in 0..8 {
        let Some(block) = func.body.blocks.get(cur.0) else {
            return false;
        };
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_) | Statement::StorageDead(_) => continue,
                Statement::Assign { place, rvalue, .. }
                    if place.local == 0
                        && place.projections.is_empty()
                        && matches!(rvalue, Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if p.local == dest_local && p.projections.is_empty())
                        && !ret_bound =>
                {
                    ret_bound = true;
                }
                _ => return false,
            }
        }
        match &block.terminator {
            Terminator::Goto(next) => cur = *next,
            Terminator::Return => return ret_bound,
            _ => return false,
        }
    }
    false
}

/// Tier-1 for a FIELD subject: `fn is_ready(&self) -> bool {
/// self.field.is_some() }`. The `&Struct` param's PROBED field must be a
/// modeled enum; the summary records `pred_field = Some(field_idx)` and the
/// tag term is minted over the projected place `(*self).field_idx`. Fail-closed
/// on any deviation (mirrors Tier 1's gates, with a field-projection receiver).
pub(super) fn tier1_field_probe_body_summary(
    func: &VerifiableFunction,
    params: Vec<String>,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let (field_idx, dest_local, target, probe_paths, probe_variant) =
        find_field_probe(func, pred_local)?;
    // The probed field's type must be a modeled std enum whose flattened shape
    // matches the probe (Option vs Result).
    let field_place = Place {
        local: pred_local,
        projections: vec![
            trust_types::Projection::Deref,
            trust_types::Projection::Field(field_idx),
        ],
    };
    let field_ty = crate::place_ty_cow(func, &field_place)?;
    let (enum_name, variants) = modeled_std_enum_shape(field_ty.as_ref())?;
    if !probe_paths.contains(&enum_name) {
        return None;
    }
    if !probe_result_reaches_return(func, dest_local, target) {
        return None;
    }
    let variant_tags: Vec<i128> = variants.iter().map(|v| v.discriminant).collect();
    let pred_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params,
        pred_param: pred_local,
        pred_field: Some(field_idx),
        kind: ReturnBoolPredKind::Iff,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// Locate THE probe call whose shared-ref receiver is a borrow of a FIELD of
/// the `&Struct` param — `_r = &((*_1).field)`, `is_some(move _r)` — and
/// confirm the call block writes neither `_1` nor `_0`. Returns the field
/// index, the probe's bool dest local, its success block, the probe's enum
/// paths, and the probed variant name. Fail-closed on any deviation.
pub(super) fn find_field_probe(
    func: &VerifiableFunction,
    pred_local: usize,
) -> Option<(usize, usize, BlockId, &'static [&'static str], &'static str)> {
    // SOUNDNESS: the probe must be the ENTRY block so it dominates the Return
    // (see [`find_param_probe`]) — a non-entry field probe behind a bypass arm
    // would be mis-summarized. Fail-closed.
    let call_block = func.body.blocks.first()?;
    let Terminator::Call { func: callee, args, dest, target: Some(target), .. } =
        &call_block.terminator
    else {
        return None;
    };
    let (callee, target) = (callee.as_str(), *target);
    let (probe_paths, probe_variant) = std_option_result_probe_variant(callee)?;
    // Receiver: `&((*_1).field)` — a shared reborrow of a single field of the
    // param's pointee, reached directly or through bare copy/move hops.
    let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else {
        return None;
    };
    if !recv.projections.is_empty() {
        return None;
    }
    let mut cur = recv.local;
    let mut field_idx = None;
    for _ in 0..4 {
        // SOUNDNESS (aliased reseat, audit r3): each hop local must be PINNED
        // before its `&((*_1).f)` / copy def is trusted — a `&mut`-reseated
        // intermediate has a stale def and the field summary would be WRONG.
        if !unwrap_receiver_local_is_pinned(func, cur) {
            return None;
        }
        match crate::unique_whole_local_def(func, cur) {
            Some(Rvalue::Ref { mutable: false, place: referent })
                if referent.local == pred_local =>
            {
                match referent.projections.as_slice() {
                    [trust_types::Projection::Deref, trust_types::Projection::Field(i)] => {
                        field_idx = Some(*i);
                        break;
                    }
                    _ => return None,
                }
            }
            Some(Rvalue::Use(Operand::Copy(p) | Operand::Move(p)))
                if p.projections.is_empty() && p.local != cur =>
            {
                cur = p.local;
            }
            _ => return None,
        }
    }
    let field_idx = field_idx?;
    // The call block's own statements must NOT write the subject param or `_0`.
    for stmt in &call_block.stmts {
        match stmt {
            Statement::StorageLive(_) | Statement::StorageDead(_) => {}
            Statement::Assign { place, .. } if place.local != 0 && place.local != pred_local => {}
            _ => return None,
        }
    }
    if !dest.projections.is_empty() {
        return None;
    }
    Some((field_idx, dest.local, target, probe_paths, probe_variant))
}

/// Tier 2a of [`function_return_bool_pred_summary`].
pub(super) fn tier2a_switch_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    variant_tags: Vec<i128>,
    params: Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    // Entry block: exactly one statement — the discriminant read of the subject
    // (`*_1` for a `&Enum` param, `_1` for a by-value `Enum` param) — and a
    // two-way switch on it.
    let entry = func.body.blocks.first()?;
    let real: Vec<&Statement> = entry
        .stmts
        .iter()
        .filter(|s| !matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_)))
        .collect();
    let [Statement::Assign { place: d, rvalue: Rvalue::Discriminant(src), .. }] = real.as_slice()
    else {
        return None;
    };
    let subject_ok = src.local == pred_local
        && if by_value {
            src.projections.is_empty()
        } else {
            src.projections.as_slice() == [trust_types::Projection::Deref]
        };
    if !d.projections.is_empty() || !subject_ok {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &entry.terminator else {
        return None;
    };
    let (Operand::Copy(sw) | Operand::Move(sw)) = discr else {
        return None;
    };
    if sw.local != d.local || !sw.projections.is_empty() || targets.len() != 1 {
        return None;
    }
    let (case_tag, case_bb) = (targets[0].0, targets[0].1);
    let case_tag = i128::try_from(case_tag).ok()?;
    if !variant_tags.contains(&case_tag) || variants.len() != 2 {
        return None;
    }
    let other_tag = *variant_tags.iter().find(|t| **t != case_tag)?;
    // The case arm is reached iff `tag == case_tag`; the otherwise arm iff
    // `tag == other_tag` (2-variant, exact partition). Classify each arm's
    // return value: `Some(b)` = a provably-const `b` (straight-line to Return),
    // `None` = a non-const / payload-computing arm.
    let fc = straight_line_bool_arm(func, case_bb);
    let fo = straight_line_bool_arm(func, *otherwise);
    // `matches!(o, Some(x) if PRED)` gives `ret ⇒ tag == Some` — the non-`Some`
    // arm is provably const-false, so a `true` result implies the `Some` arm's
    // tag. SOUNDNESS of the one-directional cases: the CONST arm is proven to
    // return exactly one value on every path (straight_line_bool_arm), and the
    // switch fixes the entry tag per arm, so any `true`/`false` result routes
    // through the single non-const arm whose tag is pinned by the switch. The
    // non-const arm is NOT inspected — its structure cannot admit a result under
    // the wrong tag because the const arm cannot produce it.
    let (kind, pred_tag) = match (fc, fo) {
        // IFF: both arms const, distinct — a pure tag predicate.
        (Some(a), Some(b)) => {
            if a == b {
                return None; // constant, not a predicate
            }
            (ReturnBoolPredKind::Iff, if a { case_tag } else { other_tag })
        }
        // ImpliesTrue: exactly one arm is provably const-FALSE ⇒ `true` only from
        // the OTHER arm ⇒ `ret ⇒ tag == other_arm_tag`.
        (Some(false), None) => (ReturnBoolPredKind::ImpliesTrue, other_tag),
        (None, Some(false)) => (ReturnBoolPredKind::ImpliesTrue, case_tag),
        // ImpliesFalse: exactly one arm is provably const-TRUE ⇒ `false` only from
        // the OTHER arm ⇒ `ret == false ⇒ tag == other_arm_tag`.
        (Some(true), None) => (ReturnBoolPredKind::ImpliesFalse, other_tag),
        (None, Some(true)) => (ReturnBoolPredKind::ImpliesFalse, case_tag),
        // Neither arm const — cannot conclude a tag relationship.
        (None, None) => return None,
    };
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params,
        pred_param: pred_local,
        pred_field: None,
        kind,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}

/// Tier 2b of [`function_return_bool_pred_summary`]: a probe call whose Bool
/// result feeds a two-way switch, each arm straight-line assigning `_0` a Bool
/// const — `fn f(o: &Option<u32>) -> bool { if o.is_some() { true } else {
/// false } }` and its polarity/negation variants (e.g. `{ false } else {
/// true }` = `is_none`). The switch is on the PROBE result (a bool), so the
/// value-`0` case is the probe-false arm. Normalizes to `ret ⇔ tag == K`.
pub(super) fn tier2b_probe_switch_body_summary(
    func: &VerifiableFunction,
    enum_name: &str,
    variants: &[trust_types::VariantDef],
    variant_tags: Vec<i128>,
    params: Vec<String>,
    by_value: bool,
    pred_local: usize,
) -> Option<ReturnBoolPredSummary> {
    let (probe_dest, target, probe_variant) =
        find_param_probe(func, enum_name, by_value, pred_local)?;
    // The probe's success block switches on the Bool result; only storage
    // annotations may precede the switch.
    let sw_block = func.body.blocks.get(target.0)?;
    if sw_block
        .stmts
        .iter()
        .any(|s| !matches!(s, Statement::StorageLive(_) | Statement::StorageDead(_)))
    {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &sw_block.terminator else {
        return None;
    };
    let (Operand::Copy(sw) | Operand::Move(sw)) = discr else {
        return None;
    };
    if sw.local != probe_dest || !sw.projections.is_empty() || targets.len() != 1 {
        return None;
    }
    // A Bool switch: case `0` is the probe-false arm, case `1` the probe-true
    // arm — admit either ordering, decline anything else.
    let (case_val, case_bb) = (targets[0].0, targets[0].1);
    let (true_bb, false_bb) = match case_val {
        0 => (*otherwise, case_bb),
        1 => (case_bb, *otherwise),
        _ => return None,
    };
    // The switch fixes: `true_bb` iff probe==true iff `tag == probe_tag`;
    // `false_bb` iff `tag == other_tag` (2-variant complement). This is the
    // tier2a structure with case↔true_bb (probe_tag), otherwise↔false_bb
    // (other_tag) — classify each arm and derive the kind identically.
    let probe_tag = variants.iter().find(|v| v.name == probe_variant)?.discriminant;
    let other_tag = || -> Option<i128> {
        if variants.len() != 2 {
            return None;
        }
        variant_tags.iter().find(|t| **t != probe_tag).copied()
    };
    let v_true = straight_line_bool_arm(func, true_bb);
    let v_false = straight_line_bool_arm(func, false_bb);
    // `o.is_some() && extra`: the probe-FALSE arm is const-false, the probe-true
    // arm computes `extra` (non-const) ⇒ `ret ⇒ tag == Some` (ImpliesTrue).
    // SOUNDNESS mirrors tier2a: the CONST arm is proven single-valued and the
    // switch pins the entry tag per arm (the probe result is EXACTLY
    // `tag == probe_tag`, over the pinned `_1`), so any result routes through
    // the single non-const arm whose tag is fixed; the non-const arm is not
    // inspected.
    let (kind, pred_tag) = match (v_true, v_false) {
        (Some(a), Some(b)) => {
            if a == b {
                return None; // constant, not a predicate
            }
            (ReturnBoolPredKind::Iff, if a { probe_tag } else { other_tag()? })
        }
        // ImpliesTrue: exactly one arm provably const-FALSE ⇒ true only from the
        // other arm.
        (Some(false), None) => (ReturnBoolPredKind::ImpliesTrue, other_tag()?),
        (None, Some(false)) => (ReturnBoolPredKind::ImpliesTrue, probe_tag),
        // ImpliesFalse: exactly one arm provably const-TRUE ⇒ false only from the
        // other arm.
        (Some(true), None) => (ReturnBoolPredKind::ImpliesFalse, other_tag()?),
        (None, Some(true)) => (ReturnBoolPredKind::ImpliesFalse, probe_tag),
        (None, None) => return None,
    };
    Some(ReturnBoolPredSummary {
        enum_name: enum_name.to_string(),
        params,
        pred_param: pred_local,
        pred_field: None,
        kind,
        pred_tag,
        pred_is_eq: true,
        variants: variant_tags,
    })
}
