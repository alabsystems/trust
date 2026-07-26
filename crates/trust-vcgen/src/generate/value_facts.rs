// Value facts derived from a function's own body -- checked-arithmetic
// results, clamped and modulo'd values, division relations, min/max results,
// const-generic parameters, and index/length ties between immutable inputs.
// These are unconditional hypotheses added to every VC in the function.

use super::*;

/// The function-wide invariant fact set: every fact is UNCONDITIONALLY true
/// Trust: for an UNSIGNED operator subtraction `_c = CheckedBinaryOp(Sub, lhs, rhs)`
/// (the `SubWithOverflow` tuple, NOT the `Option`-returning `checked_sub` method) whose
/// result `_c.0` is COPIED into a whole local `_idx = move (_c.0)` — the shape of
/// `v[v.len()-1]`, whose index bound consumes `_idx` (a bare local; `operand_to_formula`
/// does NOT follow the copy, confirmed by instrumentation: the bound is `Ge(Var("_idx"),
/// len)`) — emit `(lhs < rhs) ∨ (_idx == lhs - rhs)` = `lhs >= rhs ⟹ _idx == lhs - rhs`.
/// A guarded `!v.is_empty()` (⟹ `v.len() >= 1`) then discharges `_idx < v.len()`.
/// (The reverse-loop twin is [`build_downward_induction_facts`].)
///
/// SOUNDNESS (0 false-PROVE): the implication is UNCONDITIONALLY TRUE — on an unsigned
/// underflow (`lhs < rhs`) the antecedent is false so the fact is VACUOUS (`_idx` keeps
/// its wrapped/unconstrained value → an UNguarded `v[v.len()-1]` stays REFUTABLE); on
/// `lhs >= rhs` the copied result IS the exact difference. UNSIGNED-ONLY: a signed sub's
/// overflow is NOT `lhs < rhs` (`MAX - (-1)`), so the fact would be false — gated out.
/// Single-assignment gates on `_c`, `_idx`, and both operands keep each fact a
/// function-wide invariant (bare whole-local `_idx` binds the body read via the existing
/// `normalize_ssa_version_tokens` whole-local collapse — no field-token handling needed).
pub(super) fn build_checked_sub_result_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut assign_count: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty()
            {
                *assign_count.entry(place.local).or_insert(0) += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
        {
            *assign_count.entry(dest.local).or_insert(0) += 1;
        }
    }
    let stable = |l: usize| assign_count.get(&l).copied().unwrap_or(0) <= 1;
    let stable_op = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => p.projections.is_empty() && stable(p.local),
        _ => false,
    };
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: sub_place,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Sub, lhs, rhs),
                ..
            } = stmt
            else {
                continue;
            };
            if !sub_place.projections.is_empty()
                || !stable(sub_place.local)
                || !stable_op(lhs)
                || !stable_op(rhs)
            {
                continue;
            }
            // UNSIGNED gate: `lhs < rhs` is the underflow flag ONLY for unsigned ints.
            if !matches!(
                crate::operand_ty_cow(func, lhs).as_deref(),
                Some(Ty::Int { signed: false, .. })
            ) {
                continue;
            }
            // Find whole-local copies `_idx = move/copy (_c.0)` — the index bound uses
            // `_idx`, not the field `_c.0` (operand_to_formula does not follow the copy).
            for b2 in &func.body.blocks {
                for s2 in &b2.stmts {
                    let Statement::Assign {
                        place: dst,
                        rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                        ..
                    } = s2
                    else {
                        continue;
                    };
                    if !dst.projections.is_empty()
                        || !stable(dst.local)
                        || p.local != sub_place.local
                        || !matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                    {
                        continue;
                    }
                    let idx_var = Formula::Var(
                        crate::place_to_var_name(
                            func,
                            &Place { local: dst.local, projections: Vec::new() },
                        ),
                        Sort::Int,
                    );
                    let lhs_f = crate::operand_to_formula(func, lhs);
                    let rhs_f = crate::operand_to_formula(func, rhs);
                    facts.push(Formula::Or(vec![
                        Formula::Lt(Box::new(lhs_f.clone()), Box::new(rhs_f.clone())),
                        Formula::Eq(
                            Box::new(idx_var),
                            Box::new(Formula::Sub(Box::new(lhs_f), Box::new(rhs_f))),
                        ),
                    ]));
                }
            }
        }
    }
    facts
}

/// Trust: the ADD twin of [`build_checked_sub_result_facts`] — for an UNSIGNED
/// `_c = CheckedBinaryOp(Add, lhs, rhs)` (the `AddWithOverflow` tuple) whose result
/// `_c.0` is COPIED into a whole local `_dst = move (_c.0)` — the safe-midpoint
/// shape `low + (high - low) / 2`, whose POSTCONDITION consumes `_dst` (via the
/// Option-return grounding `_0_value = _dst`; `operand_to_formula` does not follow
/// the field copy, so without this fact `_dst` floats free and a TRUE
/// postcondition spuriously refutes — z3-confirmed on the midpoint VC: model set
/// `_dst ≈ 2^127` while the computed sum was in range) — emit
/// `(lhs + rhs > TYPE_MAX) ∨ (_dst == lhs + rhs)`.
///
/// SOUNDNESS (0 false-PROVE): the implication is UNCONDITIONALLY TRUE — on an
/// unsigned overflow (`lhs + rhs > TYPE_MAX`, exactly the `AddWithOverflow` flag
/// semantics) the antecedent is true so the fact is VACUOUS (`_dst` keeps its
/// wrapped/unconstrained value → an unguarded read stays REFUTABLE); otherwise the
/// copied result IS the exact sum. UNSIGNED-ONLY: a signed add's overflow is not
/// `lhs + rhs > MAX` in the Int theory (negative operands), so the fact is gated
/// out. Same single-assignment gates as the sub twin.
pub(super) fn build_checked_add_result_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut assign_count: FxHashMap<usize, usize> = FxHashMap::default();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, .. } = stmt
                && place.projections.is_empty()
            {
                *assign_count.entry(place.local).or_insert(0) += 1;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.projections.is_empty()
        {
            *assign_count.entry(dest.local).or_insert(0) += 1;
        }
    }
    let stable = |l: usize| assign_count.get(&l).copied().unwrap_or(0) <= 1;
    let stable_op = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => p.projections.is_empty() && stable(p.local),
        _ => false,
    };
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign {
                place: add_place,
                rvalue: Rvalue::CheckedBinaryOp(BinOp::Add, lhs, rhs),
                ..
            } = stmt
            else {
                continue;
            };
            if !add_place.projections.is_empty()
                || !stable(add_place.local)
                || !stable_op(lhs)
                || !stable_op(rhs)
            {
                continue;
            }
            // UNSIGNED gate + the type's exact upper bound for the overflow guard.
            let Some(Ty::Int { signed: false, width }) =
                crate::operand_ty_cow(func, lhs).as_deref().cloned()
            else {
                continue;
            };
            if width >= 127 {
                continue;
            }
            let type_max = (1i128 << width) - 1;
            for b2 in &func.body.blocks {
                for s2 in &b2.stmts {
                    let Statement::Assign {
                        place: dst,
                        rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                        ..
                    } = s2
                    else {
                        continue;
                    };
                    if !dst.projections.is_empty()
                        || !stable(dst.local)
                        || p.local != add_place.local
                        || !matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
                    {
                        continue;
                    }
                    let dst_var = Formula::Var(
                        crate::place_to_var_name(
                            func,
                            &Place { local: dst.local, projections: Vec::new() },
                        ),
                        Sort::Int,
                    );
                    let lhs_f = crate::operand_to_formula(func, lhs);
                    let rhs_f = crate::operand_to_formula(func, rhs);
                    let sum = Formula::Add(Box::new(lhs_f), Box::new(rhs_f));
                    facts.push(Formula::Or(vec![
                        Formula::Gt(Box::new(sum.clone()), Box::new(Formula::Int(type_max))),
                        Formula::Eq(Box::new(dst_var), Box::new(sum)),
                    ]));
                }
            }
        }
    }
    facts
}

/// (each builder SSA-gates its result and emits only bounds/identities that
/// hold regardless of path), so conjoining the set onto ANY VC of `func` is
/// sound. Consumed by the v2 block-VC lane and by the call-site precondition
/// emitters (`generate_callsite_precondition_vcs{,_attributed}`) — a callee
/// `requires(1 <= hi)` at `f(1, x.max(1))` is only dischargeable with the
/// `max`-result lower bound in context. Per-builder rationale sits on each
/// builder's own doc.
pub(crate) fn build_global_invariant_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut global_facts = build_min_max_facts(func);
    global_facts.extend(build_checked_sub_result_facts(func));
    global_facts.extend(build_checked_add_result_facts(func));
    global_facts.extend(build_fp_abs_facts(func));
    global_facts.extend(build_modulo_bound_facts(func));
    global_facts.extend(build_additive_bound_facts(func));
    global_facts.extend(build_division_lt_facts(func));
    global_facts.extend(build_division_exact_facts(func));
    global_facts.extend(build_bitmask_bound_facts(func));
    global_facts.extend(build_intrinsic_bound_facts(func));
    global_facts.extend(build_flattened_index_facts(func));
    global_facts.extend(build_cast_bound_facts(func));
    global_facts.extend(build_cast_lower_bound_facts(func));
    global_facts.extend(build_downward_induction_facts(func));
    // Trust (countdown-loop piece): the bounded-countdown-loop trip facts (the
    // itoa family) — division-derived trip bounds on downward-var decrements —
    // plus the B0 infallible const-conversion value pins they resolve through.
    global_facts.extend(build_countdown_trip_facts(func));
    global_facts.extend(build_expect_const_facts(func));
    global_facts.extend(build_accumulator_bound_facts(func));
    global_facts.extend(build_discriminant_cse_facts(func));
    global_facts.extend(build_exhaustive_enum_validity_facts(func));
    global_facts.extend(build_discriminant_variant_range_facts(func));
    global_facts.extend(build_immutable_index_len_tie_facts(func));
    global_facts.extend(build_immutable_read_value_tie_facts(func));
    global_facts.extend(build_vec_index_dest_value_tie_facts(func));
    global_facts.extend(build_const_param_range_facts(func));
    global_facts
}

/// Trust (Vec `Index::index` CALL-DEST deref value tie — the owned-container twin of
/// [`build_immutable_read_value_tie_facts`]): on a `&Vec` the element read is NOT a
/// direct place projection — each `v[i]` lowers to a SEPARATE
/// `<Vec<T> as Index>::index(&v, i)` Call whose dest is a fresh `&T` temp, and the
/// body then reads `(*_11)` / `(*_14)`. Those deref reads are independent SMT vars,
/// so the guarded accumulation `if t<K && v[i]<K { t += v[i] }` FALSE-REFUTES
/// `[overflow:add]` (observed: `_11* = 0, _14* = 4294967295` at the same index).
/// Emit the same McCarthy congruence, one deref deep, per pair of index calls on
/// one immutable root:
///
///   `Or( idx_a != idx_b,  (*dest_a) == (*dest_b) )`
///
/// SOUND BY CONSTRUCTION, same levers as the direct-read builder:
///  * callee is `index` ONLY (never `index_mut` — its `&mut` result could write the
///    element between the derefs), and the traced root's TYPE is a SHARED ref to an
///    owned `Vec` (or a slice/array view): the borrow checker excludes any `&mut`
///    alias for the whole body, so the contents are immutable and `index` at equal
///    index values returns references to the SAME element — equal pointee values, a
///    theorem. Note `Eq(dest_a, dest_b)` (the refs) would NOT give the deref
///    equality; the fact ties the DEREF reads directly.
///  * the root is never reseated (`root_is_never_reseated`) and the trace is
///    unambiguous (`base_collection_local_unique`); each dest is a single-write
///    call temp (a reused dest could straddle a reassignment).
///  * index equality is a HYPOTHESIS (discharged by block-defs within an
///    iteration); unequal or untied indices satisfy the disequality disjunct and
///    force NO tie. Facts are monotone true equalities — a real overflow's
///    counterexample satisfies them too.
pub(super) fn build_vec_index_dest_value_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // root local -> [(dest local, index operand)]
    let mut groups: BTreeMap<usize, Vec<(usize, Operand)>> = BTreeMap::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if method_tail(callee) != "index" || args.len() != 2 || !dest.projections.is_empty() {
            continue;
        }
        if guards::whole_local_def_count(func, dest.local) != 1 {
            continue;
        }
        let (Operand::Copy(bp) | Operand::Move(bp)) = &args[0] else { continue };
        if !bp.projections.is_empty() {
            continue;
        }
        let Some(root) = guards::base_collection_local_unique(func, bp.local) else { continue };
        if !root_is_never_reseated(func, root) {
            continue;
        }
        let root_ok = matches!(
            crate::place_ty_cow(func, &Place::local(root)).as_deref(),
            Some(Ty::Ref { mutable: false, inner })
                if matches!(&**inner, Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
                    || matches!(&**inner, Ty::Adt { name, .. } if is_owned_slice_container_name(name))
        );
        if !root_ok {
            continue;
        }
        groups.entry(root).or_default().push((dest.local, args[1].clone()));
    }
    let mut facts = Vec::new();
    for (_, mut calls) in groups {
        // Bound the pairwise blowup (groups are tiny in practice).
        calls.truncate(6);
        if calls.len() < 2 {
            continue;
        }
        for i in 0..calls.len() {
            for j in (i + 1)..calls.len() {
                let (da, ia) = &calls[i];
                let (db, ib) = &calls[j];
                let deref = |l: usize| {
                    Operand::Copy(Place {
                        local: l,
                        projections: vec![trust_types::Projection::Deref],
                    })
                };
                let read_a = operand_to_formula(func, &deref(*da));
                let read_b = operand_to_formula(func, &deref(*db));
                if read_a == read_b {
                    continue; // same var already — nothing to tie
                }
                let idx_a = operand_to_formula(func, ia);
                let idx_b = operand_to_formula(func, ib);
                let mut disjuncts = Vec::new();
                if idx_a != idx_b {
                    disjuncts.push(Formula::Not(Box::new(Formula::Eq(
                        Box::new(idx_a),
                        Box::new(idx_b),
                    ))));
                }
                disjuncts.push(Formula::Eq(Box::new(read_a), Box::new(read_b)));
                facts.push(if disjuncts.len() == 1 {
                    disjuncts.pop().expect("non-empty")
                } else {
                    Formula::Or(disjuncts)
                });
            }
        }
    }
    facts
}

/// Trust (const-generic TYPE-RANGE pin): a const-generic param value `N` lowers to
/// the deliberately-unconstrained symbol `__trust_constparam_{index}_{name}` — but
/// "unconstrained" must mean "any value OF ITS TYPE", and the symbol carries no
/// type range at all. The solver then instantiates `N` ABOVE the type's maximum
/// (observed: `N = 2^64` for a `usize` param), making `i < N` satisfiable at
/// `i = usize::MAX`, so the loop increment `i += 1` in `while i < N { .. i += 1 }`
/// "overflows" — a FALSE-REFUTE of every const-generic counted loop. Pin each
/// symbol to its Rust type's value range (`N: usize` ⇒ `0 <= N <= u64::MAX`):
/// unconditionally true for every possible monomorphization (the param IS a value
/// of that type), so conjoining onto any VC is sound — it can never exclude a real
/// counterexample, which necessarily uses an in-range `N`. Sources: const-param
/// value operands (which carry `width`/`signed`) and `SymArray` lengths (an array
/// length is a `usize` value by construction). Bool-sorted (width-1 unsigned) and
/// wider-than-64-bit symbols are skipped (no meaningful/representable Int range).
pub(super) fn build_const_param_range_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // symbol -> (width, signed); first sighting wins (a symbol is one param).
    let mut syms: BTreeMap<String, (u32, bool)> = BTreeMap::new();

    fn consider(syms: &mut BTreeMap<String, (u32, bool)>, op: &Operand) {
        if let Operand::Constant(ConstValue::ConstParam { index, name, width, signed }) = op {
            // A bool const-generic lowers Bool-sorted — no integer range applies.
            if *width == 1 && !*signed {
                return;
            }
            syms.entry(trust_types::const_param_symbol(*index, name)).or_insert((*width, *signed));
        }
    }

    fn scan_ty(syms: &mut BTreeMap<String, (u32, bool)>, ty: &Ty) {
        match ty {
            Ty::SymArray { elem, len_sym } => {
                // An array length is a `usize` value by construction.
                syms.entry(trust_types::const_param_symbol(len_sym.index, &len_sym.name))
                    .or_insert((64, false));
                scan_ty(syms, elem);
            }
            Ty::Ref { inner, .. } => scan_ty(syms, inner),
            Ty::RawPtr { pointee, .. } => scan_ty(syms, pointee),
            Ty::Slice { elem } | Ty::Array { elem, .. } => scan_ty(syms, elem),
            Ty::Tuple(ts) => ts.iter().for_each(|t| scan_ty(syms, t)),
            _ => {}
        }
    }

    for decl in &func.body.locals {
        scan_ty(&mut syms, &decl.ty);
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            match rvalue {
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => consider(&mut syms, op),
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    consider(&mut syms, a);
                    consider(&mut syms, b);
                }
                Rvalue::Aggregate(_, ops) => ops.iter().for_each(|op| consider(&mut syms, op)),
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { args, .. } => args.iter().for_each(|op| consider(&mut syms, op)),
            Terminator::SwitchInt { discr, .. } => consider(&mut syms, discr),
            Terminator::Assert { cond, .. } => consider(&mut syms, cond),
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for (sym, (width, signed)) in syms {
        if width > 64 || width == 0 {
            continue; // no i128-representable (or meaningful) bound — leave unconstrained
        }
        let (lo, hi) = if signed {
            (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
        } else {
            (0i128, if width == 64 { u64::MAX as i128 } else { (1i128 << width) - 1 })
        };
        let v = Formula::var_owned(sym, Sort::Int);
        facts.push(Formula::Le(Box::new(Formula::Int(lo)), Box::new(v.clone())));
        facts.push(Formula::Le(Box::new(v), Box::new(Formula::Int(hi))));
    }
    facts
}

/// Trust (2026-07-06, nested `v[i][j]` on an IMMUTABLE `&Vec<Vec>`/`&[[T]]`): the two
/// syntactic `v[i]` reads (one in the `j < v[i].len()` guard, one in the `v[i][j]`
/// access) lower to SEPARATE `Index::index(v,i)` Calls with distinct result temps, so
/// their inner-collection lengths never tie and the access refutes `[slice]`. For a
/// SHARED-ref base the two `v[i]` denote the SAME immutable inner collection, so their
/// abstract lengths are EQUAL — tie `coll_len(dest_a) == coll_len(dest_b)`.
///
/// SOUND BY CONSTRUCTION: a shared `&T` cannot be mutated (no `&mut *v` is formable), so
/// the inner collection cannot be RESIZED between the two reads — there is no
/// resize-staleness hazard. This is the crucial difference from the `&mut Vec` length
/// tie (which needed mut-borrow analysis whose gate proved unreliable and was reverted):
/// here the gate is a STATIC `Ty::Ref { mutable: false }` TYPE check on the traced base
/// root, plus a STABLE index (single-static-assignment local, or a constant) shared by
/// the matched calls — so a differing/reassigned index or a `&mut`/owned base never ties.
/// True iff `local` is a FUNCTION PARAMETER that is never written and never
/// `&mut`/`&raw`-borrowed anywhere in the body — so its value is the entry value,
/// identical at EVERY read (no reassignment can occur between two uses). Used to gate
/// the immutable-index length tie: only a pure-input index guarantees the two `v[i]`
/// reads use the SAME index value.
pub(super) fn local_is_immutable_input_param(func: &VerifiableFunction, local: usize) -> bool {
    if local >= func.body.arg_count {
        return false;
    }
    if guards::local_is_mutably_borrowed(func, local) {
        return false;
    }
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let written = match stmt {
                Statement::Assign { place, .. }
                | Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place } => place.local == local,
                _ => false,
            };
            if written {
                return false;
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            return false;
        }
    }
    true
}

pub(super) fn build_immutable_index_len_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // (base_root_local, idx_is_const, idx_value_or_local) -> dest locals of matching calls.
    let mut groups: BTreeMap<(usize, bool, i128), Vec<usize>> = BTreeMap::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !is_slice_index_call(callee) || !dest.projections.is_empty() || args.len() != 2 {
            continue;
        }
        // Scalar `usize` index only (a range slice has an ADT index — different lane).
        if !operand_is_scalar_usize_index(func, &args[1]) {
            continue;
        }
        // Base receiver traces to a root whose TYPE is a SHARED ref (immutable).
        let (Operand::Copy(bp) | Operand::Move(bp)) = &args[0] else { continue };
        if !bp.projections.is_empty() {
            continue;
        }
        let Some(root) = guards::base_collection_local_unique(func, bp.local) else { continue };
        if !matches!(
            crate::place_ty_cow(func, &Place::local(root)).as_deref(),
            Some(Ty::Ref { mutable: false, .. })
        ) {
            continue;
        }
        // STABLE index: a PURE immutable-input param (never written, never `&mut`-borrowed
        // — value is the entry value, IDENTICAL at every read, no "reassigned between the
        // two index calls" hazard), or a non-negative constant. A non-param or mutated
        // local declines (conservative; `let inner = &v[i]` workaround covers it).
        let idx_key = match &args[1] {
            Operand::Copy(p) | Operand::Move(p)
                if p.projections.is_empty() && local_is_immutable_input_param(func, p.local) =>
            {
                (false, p.local as i128)
            }
            Operand::Constant(ConstValue::Uint(v, _)) if *v <= i128::MAX as u128 => {
                (true, *v as i128)
            }
            Operand::Constant(ConstValue::Int(v)) if *v >= 0 => (true, *v),
            _ => continue,
        };
        groups.entry((root, idx_key.0, idx_key.1)).or_default().push(dest.local);
    }
    let mut facts = Vec::new();
    for (_, dests) in groups {
        if dests.len() < 2 {
            continue;
        }
        let first = guards::coll_len_var(func, dests[0]);
        for &d in &dests[1..] {
            facts.push(Formula::Eq(
                Box::new(first.clone()),
                Box::new(guards::coll_len_var(func, d)),
            ));
        }
    }
    facts
}

/// True iff `root` can NEVER be reseated to a different backing: no whole- or
/// projected-place write, no call dest, and no `&mut`/`&raw` borrow (through
/// which the ref itself could be redirected). A param's entry def is its only
/// def; a non-param must have exactly ONE whole-local def. NOTE: neither
/// `whole_local_def_count` (no param-entry def) nor `is_single_static_assignment`
/// (counts a reassigned param as 1 def) gives this on its own — a `mut p` param
/// reassigned once would slip through either and tie reads across the reseat.
pub(super) fn root_is_never_reseated(func: &VerifiableFunction, root: usize) -> bool {
    let is_param = (1..=func.body.arg_count).contains(&root);
    let mut defs = 0usize;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { place, rvalue, .. } = stmt {
                if let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) = rvalue
                    && b.local == root
                {
                    return false;
                }
                if place.local == root {
                    if place.projections.is_empty() {
                        defs += 1;
                    } else {
                        return false;
                    }
                }
            }
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == root
        {
            return false;
        }
    }
    if is_param { defs == 0 } else { defs == 1 }
}

/// Trust (immutable-element read VALUE tie — the unified "read twice, diverge" gap):
/// two syntactic reads of the SAME element of an IMMUTABLE (shared-ref) array/slice —
/// `if t < K && ps[i].x < K { t += ps[i].x }` (array-of-structs loop), the const-generic
/// `a[i]` loop, `w[0]` on a chunker-yielded slice — are encoded as INDEPENDENT SMT vars
/// (`ps*[_10].0` vs `ps*[_13].0`), so a guard on the first read never constrains the
/// second and the add/index obligation FALSE-REFUTES (counterexamples show the SAME
/// index with two DIFFERENT element values). For an immutable base the McCarthy
/// congruence "same array ∧ same index ⇒ same value" is a theorem, so emit it as a
/// global fact for each pair of same-shape reads:
///
///   `Or( idx_a != idx_b  [one disjunct per Index position],  read_a == read_b )`
///
/// Index equality is a HYPOTHESIS the solver discharges (via the existing block-def
/// layer, e.g. `_10 = i`, `_13 = i` within one iteration) — never an assertion. Two
/// reads at genuinely different indices satisfy the disequality disjunct and force NO
/// value tie (the exact N3 hazard a build-time index-equality decision would carry).
///
/// SOUND BY CONSTRUCTION (no false-PROVE vector):
///  * the base root's TYPE peels through shared refs to an array/slice, with every
///    ref layer `Ty::Ref { mutable: false }` — the borrow checker guarantees no
///    `&mut` alias to the backing exists while the shared ref is live, so element
///    values are physically immutable (the STATIC type-level lever of the landed
///    len-tie fix; never the incomplete may-resize dataflow that missed `clear`);
///  * every `Deref` crossed inside the projection chain is itself through a shared
///    ref (`shared_ref_deref_chain`) — a nested `&mut`/raw-ptr/`Box` deref bails;
///  * both operands are `Operand::Copy` — the leaf type is `Copy`, which excludes
///    `Cell`/`RefCell`/`UnsafeCell`/atomics, closing interior mutability (a `Copy`
///    of a shared ref TO an interior-mutable cell only ties the reference value,
///    which is itself immutable — never the pointee);
///  * the root is NEVER reseated: an immutable-input param or a single-static-
///    assignment local (with no `&mut`/`&raw` borrow), ON TOP of the
///    `base_collection_local_unique` chain check — `whole_local_def_count` does not
///    count a param's entry def, so a reassigned `mut p` param has count 1 and would
///    otherwise slip through with the two reads straddling a base reseat;
///  * facts are only CONJOINED (monotone): a true equality can flip a spurious
///    REFUTE to PROVE but cannot hide a real counterexample (which satisfies it too).
///
/// The `&mut`-captured closure-upvar sibling (`*(_1.0)` read twice under a guard)
/// stays REFUTED: its base is a mutable ref, so the type gate declines — that case
/// needs a flow-sensitive no-intervening-write region query (a separate, later lane).
pub(super) fn build_immutable_read_value_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // Group key: (root local, projection shape with each variable `Index` blanked to
    // its position). `(*ps)[_10].0` and `(*ps)[_13].0` share a key; `.0` vs `.1`, or
    // a different `ConstantIndex` offset, do not. Values: distinct places + their
    // index locals, first-seen order.
    let mut groups: BTreeMap<(usize, String), Vec<(Place, Vec<usize>)>> = BTreeMap::new();

    /// True iff every `Deref` inside `place`'s projection chain dereferences a
    /// SHARED reference (`Ty::Ref { mutable: false }`) — so no `&mut`/raw-pointer/
    /// `Box` hop can smuggle mutable backing under a shared root.
    fn shared_ref_deref_chain(func: &VerifiableFunction, place: &Place) -> bool {
        for (pos, proj) in place.projections.iter().enumerate() {
            if matches!(proj, trust_types::Projection::Deref) {
                let prefix =
                    Place { local: place.local, projections: place.projections[..pos].to_vec() };
                if !matches!(
                    crate::place_ty_cow(func, &prefix).as_deref(),
                    Some(Ty::Ref { mutable: false, .. })
                ) {
                    return false;
                }
            }
        }
        true
    }

    /// True iff `ty` peels through shared refs to an array/slice — the only bases
    /// whose elements are read via direct `Index` place projections.
    fn peels_to_indexable(ty: &Ty) -> bool {
        match ty {
            Ty::Ref { mutable: false, inner } => peels_to_indexable(inner),
            Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } => true,
            _ => false,
        }
    }

    fn consider(
        func: &VerifiableFunction,
        groups: &mut BTreeMap<(usize, String), Vec<(Place, Vec<usize>)>>,
        op: &Operand,
    ) {
        // `Copy` ONLY: a `Move` leaf needn't be `Copy`, and the `Copy` bound is the
        // interior-mutability closure (see the soundness banner).
        let Operand::Copy(place) = op else { return };
        let mut idx_locals = Vec::new();
        let mut shape = String::new();
        for proj in &place.projections {
            match proj {
                trust_types::Projection::Deref => shape.push('*'),
                trust_types::Projection::Field(i) => {
                    shape.push('.');
                    shape.push_str(&i.to_string());
                }
                trust_types::Projection::Index(l) => {
                    idx_locals.push(*l);
                    shape.push_str("[#]");
                }
                trust_types::Projection::ConstantIndex { offset, min_length, from_end } => {
                    shape.push_str(&format!("[c{offset};{min_length};{from_end}]"));
                }
                // Downcast/Subslice/opaque casts: variant-relative or aliasing
                // shapes this lane does not model — bail the whole operand.
                _ => return,
            }
        }
        // A variable `Index` is what makes two syntactic reads distinct-but-equal;
        // all-constant projections already share one SMT var (identical place name).
        if idx_locals.is_empty() {
            return;
        }
        let Some(root) = guards::base_collection_local_unique(func, place.local) else { return };
        if !root_is_never_reseated(func, root) {
            return;
        }
        // Root type: shared ref peeling to an array/slice.
        if !matches!(
            crate::place_ty_cow(func, &Place::local(root)).as_deref(),
            Some(Ty::Ref { mutable: false, inner }) if peels_to_indexable(inner)
        ) {
            return;
        }
        if !shared_ref_deref_chain(func, place) {
            return;
        }
        let entry = groups.entry((root, shape)).or_default();
        if !entry.iter().any(|(p, _)| p == place) {
            entry.push((place.clone(), idx_locals));
        }
    }

    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { rvalue, .. } = stmt else { continue };
            match rvalue {
                Rvalue::Use(op)
                | Rvalue::UnaryOp(_, op)
                | Rvalue::Cast(op, _)
                | Rvalue::Repeat(op, _) => consider(func, &mut groups, op),
                Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                    consider(func, &mut groups, a);
                    consider(func, &mut groups, b);
                }
                Rvalue::Aggregate(_, ops) => {
                    for op in ops {
                        consider(func, &mut groups, op);
                    }
                }
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { args, .. } => {
                for op in args {
                    consider(func, &mut groups, op);
                }
            }
            Terminator::SwitchInt { discr, .. } => consider(func, &mut groups, discr),
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for (_, mut reads) in groups {
        // Bound the pairwise blowup in read-heavy bodies (groups are tiny in practice).
        reads.truncate(6);
        if reads.len() < 2 {
            continue;
        }
        for i in 0..reads.len() {
            for j in (i + 1)..reads.len() {
                let (pa, ia) = &reads[i];
                let (pb, ib) = &reads[j];
                let read_a = operand_to_formula(func, &Operand::Copy(pa.clone()));
                let read_b = operand_to_formula(func, &Operand::Copy(pb.clone()));
                if read_a == read_b {
                    continue; // canonicalized to one var already — nothing to tie
                }
                let mut disjuncts = Vec::new();
                for (la, lb) in ia.iter().zip(ib.iter()) {
                    if la == lb {
                        continue; // literally the same index local — equal by identity
                    }
                    let fa = crate::array_index_formula(func, &trust_types::Projection::Index(*la));
                    let fb = crate::array_index_formula(func, &trust_types::Projection::Index(*lb));
                    if fa == fb {
                        continue; // same canonical index var — equal by identity
                    }
                    disjuncts.push(Formula::Not(Box::new(Formula::Eq(Box::new(fa), Box::new(fb)))));
                }
                disjuncts.push(Formula::Eq(Box::new(read_a), Box::new(read_b)));
                facts.push(if disjuncts.len() == 1 {
                    disjuncts.pop().expect("non-empty")
                } else {
                    Formula::Or(disjuncts)
                });
            }
        }
    }
    facts
}

pub(super) fn build_min_max_facts(func: &VerifiableFunction) -> Vec<Formula> {
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if dest.projections.is_empty()
            && args.len() == 2
            && is_single_static_assignment(func, dest.local)
        {
            let is_min = is_ord_min_call(callee);
            let is_max = is_ord_max_call(callee);
            if !is_min && !is_max {
                continue;
            }
            let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
            // Emit a bound for EACH argument that resolves to a stable term,
            // INDEPENDENTLY: `min(a, b) <= a` and `min(a, b) <= b` each hold on
            // their own, so a stable `b` (e.g. `n.min(g.len())`, where `n` is an
            // unresolvable bare param but `g.len()` is a param slice length) still
            // yields the useful `dest <= g.len()`. Each emitted fact is
            // unconditionally true regardless of the other argument.
            for arg in args {
                if let Some(r) = stable_min_arg_formula(func, arg, FUEL) {
                    facts.push(if is_min {
                        Formula::Le(Box::new(dest_var.clone()), Box::new(r))
                    } else {
                        Formula::Ge(Box::new(dest_var.clone()), Box::new(r))
                    });
                }
            }
        }
    }
    facts
}

/// Trust (countdown-loop piece, B0): GLOBAL value facts for infallible
/// const-int `try_into().expect()` destinations — `dest == C`, the same global
/// lane (and the same SSA gate) as [`build_min_max_facts`]. The versioned
/// call-dest channel cannot carry these into a LOOP body (the loop-head join
/// intersects guard sets away), but the global form is unconditionally sound
/// here: the destination is single-static-assignment, its ONLY def writes the
/// SAME constant on every completed call (success-by-construction — the
/// recognizer's width-exact range check), the call cannot panic, and no read
/// observes the local before its def (MIR init-before-use), so `dest == C` is
/// consistent with every trace valuation — exactly the min/max-result global
/// precedent. This is what lets `remain % scale` / `remain /= scale` discharge
/// their zero-divisor obligations inside the itoa macro loops. The `i64::MAX`
/// magnitude cap keeps every downstream lowering (trust-wp large-int, native
/// Int parser) inside its supported literal range — larger constants simply
/// emit nothing (fail-closed completeness, never soundness).
pub(super) fn build_expect_const_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if let Some(v) = expect_infallible_const_int_conversion(func, callee, args, dest)
            && is_single_static_assignment(func, dest.local)
            && v.unsigned_abs() <= i64::MAX as u128
        {
            facts.push(Formula::Eq(
                Box::new(Formula::Var(crate::place_to_var_name(func, dest), Sort::Int)),
                Box::new(Formula::Int(v)),
            ));
        }
    }
    facts
}

/// Global facts from unsigned `dest = a % b` (`Rvalue::BinaryOp(Rem, _, b)`) with a
/// single-assignment `dest` and a stable divisor `b`. For UNSIGNED operands,
/// `b != 0 ⟹ 0 <= a % b < b` holds unconditionally — so emitting the implication
/// `(b == 0) ∨ (dest < b)` as a global fact is sound and discharges a wrapping
/// access `s[n % s.len()]` on the path where `s.len() != 0` (which the dominating
/// remainder-by-zero assert / `!is_empty()` guard establishes). Signed `%` follows
/// the dividend's sign (so `0 <= r < b` need not hold) and is excluded. Mirrors
/// the constant-modulus interval bound (`arr[n % 4]`), but for a SYMBOLIC divisor.
///
/// The `mod` term itself drives ay to `unknown` (QF_NIA), but the ay bridge's
/// nonlinear-relaxation retry abstracts it away and discharges the LINEAR core that
/// THIS fact supplies. See `incremental_ay::abstract_nonlinear`.
pub(super) fn build_modulo_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(trust_types::BinOp::Rem, _a, b) = rvalue else { continue };
            if !is_single_static_assignment(func, dest.local) {
                continue;
            }
            // Unsigned operands only — signed `%` can be negative.
            if !crate::operand_ty_cow(func, b).is_some_and(|t| t.is_integer() && !t.is_signed()) {
                continue;
            }
            let Some(b_f) = stable_min_arg_formula(func, b, FUEL) else { continue };
            let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
            // `b != 0 ⟹ dest < b`, encoded `(b == 0) ∨ (dest < b)`.
            facts.push(Formula::Or(vec![
                Formula::Eq(Box::new(b_f.clone()), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(dest_var), Box::new(b_f)),
            ]));
        }
    }
    facts
}

/// Global facts from unsigned `dest = a / c` with a CONSTANT divisor `c >= 2`:
/// `a > 0 ⟹ dest < a` (integer division by `>= 2` strictly decreases for `a >= 1`),
/// encoded `(a == 0) ∨ (dest < a)`. Discharges a midpoint/halving index `s[n/2]`
/// (the access needs `n/2 < n == len`, established by `dest < a` on the `n > 0`
/// path the guard provides). Mirrors [`build_modulo_bound_facts`].
pub(super) fn build_division_lt_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use trust_types::{BinOp, ConstValue, Operand};
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(BinOp::Div, a, c) = rvalue else { continue };
            if !is_single_static_assignment(func, dest.local) {
                continue;
            }
            if !crate::operand_ty_cow(func, a).is_some_and(|t| t.is_integer() && !t.is_signed()) {
                continue;
            }
            let cv = match c {
                Operand::Constant(ConstValue::Uint(k, _)) => i128::try_from(*k).ok(),
                Operand::Constant(ConstValue::Int(k)) if *k >= 0 => Some(*k),
                _ => None,
            };
            if cv.is_none_or(|v| v < 2) {
                continue;
            }
            let Some(a_f) = stable_min_arg_formula(func, a, FUEL) else { continue };
            let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
            facts.push(Formula::Or(vec![
                Formula::Eq(Box::new(a_f.clone()), Box::new(Formula::Int(0))),
                Formula::Lt(Box::new(dest_var), Box::new(a_f)),
            ]));
        }
    }
    facts
}

/// Global facts from an unsigned exact division `dest = a / c` with a CONSTANT,
/// non-zero divisor `c`: the material implication `a % c == 0  ⟹  dest * c == a`,
/// encoded `¬(a % c == 0) ∨ (dest * c == a)`.
///
/// SOUNDNESS: this disjunction is a THEOREM of integer arithmetic, VALID ON EVERY
/// PATH regardless of control flow — for any integers `a` and `c != 0`, Rust integer
/// division satisfies `a = c*(a/c) + (a mod c)` with `0 <= a mod c < c` (unsigned),
/// hence `a % c == 0  ⟺  c*(a/c) == a`. Conjoining a valid formula onto the VIOLATION
/// formula (which `certify_vc` / the solver proves UNSAT) removes ONLY models that
/// violate a tautology — i.e. it removes NO genuine model, because every real
/// counterexample (any assignment where `dest` is the actual `a/c`) already satisfies
/// the identity. So it can NEVER turn a SAT (real-violation) formula UNSAT: no
/// false-PROVE. This is the identical basis as the shipped [`build_division_lt_facts`]
/// / [`build_modulo_bound_facts`]. The equality becomes load-bearing only when the
/// solver INDEPENDENTLY learns `a % c == 0` from the REAL dominating path guard (e.g.
/// `a.is_multiple_of(c)`); on any path lacking the guard the antecedent is false and
/// the fact is inert. Emitting the material implication (never the bare equality
/// `dest*c==a`, which is FALSE when `a%c != 0`) puts the entire soundness burden on the
/// tautology and delegates the `a%c==0` hypothesis to the genuine guard — so no
/// dominance/scoping analysis is needed and no false fact is ever asserted.
///
/// Discharges a `from_raw_parts(p, a/c)` byte-bounds obligation whose byte extent
/// `c*(a/c)` must equal the source byte length `a` (the memory-model unsafe beachhead:
/// `<[A]>::try_cast_slice` monomorphized, where `c = size_of::<B>()` is a literal so
/// `dest * c` is LINEAR). Mirrors [`build_division_lt_facts`].
pub(super) fn build_division_exact_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use trust_types::{BinOp, ConstValue, Operand};
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(BinOp::Div, a, c) = rvalue else { continue };
            if !is_single_static_assignment(func, dest.local) {
                continue;
            }
            // Unsigned dividend only: the identity holds for signed too, but restricting
            // to unsigned matches build_division_lt_facts and avoids signed-Rem subtlety.
            if !crate::operand_ty_cow(func, a).is_some_and(|t| t.is_integer() && !t.is_signed()) {
                continue;
            }
            // Non-zero constant divisor `c` (== `size_of::<B>()`, > 0 after the ZST branch).
            let cv = match c {
                Operand::Constant(ConstValue::Uint(k, _)) => i128::try_from(*k).ok(),
                Operand::Constant(ConstValue::Int(k)) if *k >= 0 => Some(*k),
                _ => None,
            };
            let Some(cv) = cv.filter(|v| *v >= 1) else { continue };
            let Some(a_f) = stable_min_arg_formula(func, a, FUEL) else { continue };
            let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
            // ¬(a % c == 0) ∨ (dest * c == a)
            facts.push(Formula::Or(vec![
                Formula::Not(Box::new(Formula::Eq(
                    Box::new(Formula::Rem(Box::new(a_f.clone()), Box::new(Formula::Int(cv)))),
                    Box::new(Formula::Int(0)),
                ))),
                Formula::Eq(
                    Box::new(Formula::Mul(Box::new(dest_var), Box::new(Formula::Int(cv)))),
                    Box::new(a_f),
                ),
            ]));
        }
    }
    facts
}

/// The tight inclusive upper bound `C` of a NON-SSA local `L` whose value is a
/// `min(v, C)` clamp — `L = if cmp(v, C) { C } else { v }` (or the symmetric
/// arm layout) realized in MIR as a SwitchInt diamond:
///
/// ```text
///   _g = cmp(v, C)                 // cmp ∈ {Gt, Ge, Lt, Le}, v a place, C a const
///   SwitchInt(_g) { 0 -> Bf, otherwise -> Bt }
///     Bconst: L = const C;  Goto merge
///     Bvar:   L = Copy(v);  Goto merge   // the SAME v compared against C
/// ```
///
/// Returns `Some(C)` only when the var-arm sits on the edge whose guard forces
/// `v ≤ C` (so the merged value is `min(v, C) ≤ C`), the const-arm assigns
/// EXACTLY `C`, and `L` has precisely these two whole-local definitions, both
/// `Goto`-ing one common merge block. `None` on any deviation (conservative).
///
/// SOUNDNESS: `min(v, C) ≤ C` is a GLOBAL truth — it holds on BOTH arms, so the
/// returned bound needs no path condition (it is sound to assert about `L`
/// everywhere `L` is live). The whole correctness rests on the var-arm edge
/// implying `v ≤ C`; we verify the comparison operator and the SwitchInt
/// true/false routing AGREE on this (an UNSOUND mis-read — taking the var arm
/// where `v > C`, i.e. a `max`/lower-bound clamp — would let `L > C` and is
/// rejected here). The const-arm constant must equal the comparison constant so
/// the bound is exactly `C`; a differing constant bails rather than guess.
pub(super) fn clamp_upper_bound(func: &VerifiableFunction, local: usize) -> Option<i128> {
    use trust_types::{BinOp, ConstValue, Operand as Op};

    // Constant integer value of a comparison RHS / const-arm operand, as i128.
    fn const_i128(op: &Op) -> Option<i128> {
        match op {
            Op::Constant(ConstValue::Uint(k, _)) => i128::try_from(*k).ok(),
            Op::Constant(ConstValue::Int(k)) => Some(*k),
            _ => None,
        }
    }
    // The whole-local place an operand reads, if it is a bare `Copy`/`Move` of a
    // local with no projections.
    fn whole_local(op: &Op) -> Option<usize> {
        match op {
            Op::Copy(p) | Op::Move(p) if p.projections.is_empty() => Some(p.local),
            _ => None,
        }
    }

    // 1) Gather L's whole-local definitions: exactly two, in two distinct blocks,
    //    each the block's SOLE statement-write of L and each block ending in Goto.
    //    (A field/deref/projected store, a Call dest, or a third def disqualifies.)
    let mut defs: Vec<(usize, &Rvalue, usize)> = Vec::new(); // (block_idx, rvalue, goto_target)
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place, rvalue, .. } = stmt else { continue };
            if place.local != local {
                continue;
            }
            if !place.projections.is_empty() {
                return None; // projected store into L — ambiguous value
            }
            let Terminator::Goto(target) = &block.terminator else { return None };
            defs.push((block.id.0, rvalue, target.0));
        }
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            return None; // a call also writes L
        }
    }
    if defs.len() != 2 {
        return None;
    }
    let (b0, rv0, g0) = defs[0];
    let (b1, rv1, g1) = defs[1];
    if b0 == b1 || g0 != g1 {
        return None; // must be two distinct blocks Goto-ing one common merge
    }

    // 2) Split into the const-arm (`L = const C`) and the var-arm (`L = Copy(v)`).
    let arm_const = |rv: &Rvalue| -> Option<i128> {
        match rv {
            Rvalue::Use(op) => const_i128(op),
            _ => None,
        }
    };
    let arm_var = |rv: &Rvalue| -> Option<usize> {
        match rv {
            Rvalue::Use(op) => whole_local(op),
            _ => None,
        }
    };
    let (const_block, const_c, var_block, var_v) =
        match (arm_const(rv0), arm_var(rv0), arm_const(rv1), arm_var(rv1)) {
            (Some(c), _, _, Some(v)) => (b0, c, b1, v),
            (_, Some(v), Some(c), _) => (b1, c, b0, v),
            _ => return None,
        };

    // 3) Find the SwitchInt that routes to these two blocks. Its discr is a bool
    //    `_g = cmp(v, C)` over the SAME var `v` and the SAME constant `C`.
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, otherwise, .. } = &block.terminator else {
            continue;
        };
        // The TRUE / FALSE successor edges of a boolean SwitchInt. A bool discr is
        // switched on `0` (false) and `1` (true); handle either encoding (single
        // target {0,..} with otherwise=true, or {1,..} with otherwise=false).
        let mut false_edge: Option<usize> = None;
        let mut true_edge: Option<usize> = None;
        for (val, tgt) in targets {
            match val {
                0 => false_edge = Some(tgt.0),
                1 => true_edge = Some(tgt.0),
                _ => {}
            }
        }
        let (true_edge, false_edge) = match (true_edge, false_edge) {
            (Some(t), None) => (t, otherwise.0),
            (None, Some(f)) => (otherwise.0, f),
            _ => continue, // not a clean two-way boolean switch
        };
        // Both arm blocks must be the two edges of THIS switch (in some order).
        let edges = [true_edge, false_edge];
        if !(edges.contains(&const_block) && edges.contains(&var_block)) {
            continue;
        }
        let var_on_true = var_block == true_edge;

        // discr must be `_g = cmp(v, C)` — a single-static-assignment bool temp.
        let Some(g) = whole_local(discr) else { continue };
        if !is_single_static_assignment(func, g) {
            continue;
        }
        let Some(Rvalue::BinaryOp(op, lhs, rhs)) = crate::unique_whole_local_def(func, g) else {
            continue;
        };
        // lhs must be the SAME var `v`, rhs the SAME constant `C` as the clamp.
        if whole_local(lhs) != Some(var_v) {
            continue;
        }
        let Some(cmp_c) = const_i128(rhs) else { continue };
        if cmp_c != const_c {
            continue;
        }

        // 4) Directionality: the var arm must sit on the edge whose guard forces
        //    `v ≤ C` (else `min` is not the merged value and the bound is unsound).
        //    Gt/Ge: var arm on the FALSE edge (`!(v>C)`/`!(v>=C)` ⟹ v ≤ C).
        //    Lt/Le: var arm on the TRUE edge  (`v<C`/`v<=C` ⟹ v ≤ C).
        let sound = match op {
            BinOp::Gt | BinOp::Ge => !var_on_true,
            BinOp::Lt | BinOp::Le => var_on_true,
            _ => false,
        };
        if sound {
            return Some(const_c);
        }
    }
    None
}

/// The inclusive upper bound of an UNSIGNED operand's value, resolved through
/// widening/narrowing casts and additive/multiplicative arithmetic down to the
/// source types' ranges. `None` if a component is signed or unresolvable. Sound by
/// construction: a cast result is `≤ min(ub(inner), type_max(target))` (widening
/// preserves the value; narrowing truncates into `[0, type_max(target)]`), and a
/// wrapping `a op b` result is `≤ a op b ≤ ub(a) op ub(b)` (the machine `mod` only
/// decreases), each further capped by the result type's range.
pub(super) fn unsigned_upper_bound(func: &VerifiableFunction, operand: &Operand, fuel: u32) -> Option<i128> {
    use trust_types::{BinOp, ConstValue, Operand as Op, Projection, Ty};
    fn ty_max(t: &Ty) -> Option<i128> {
        match t {
            Ty::Int { width, signed: false } if *width < 127 => Some((1i128 << *width) - 1),
            // A `bool` is 0 or 1, so its unsigned upper bound is 1. This propagates
            // through a `bool as <uint>` cast and — since this fn recurses through
            // additions — through a CHAIN of such casts (flag/edge counts like
            // `(a != b) as u32 + (b != c) as u32 + …`), so each intermediate sum
            // gets a tight `<= k` fact and its arithmetic-overflow VC discharges.
            // Without this the bool cast fell back to the full uint range and the
            // sum spuriously refuted (over-refutation audit: body cast semantics).
            // SOUND: an upper bound only ever turns PROVE into not-proved, and
            // `bool ≤ 1` is exact.
            Ty::Bool => Some(1),
            _ => None,
        }
    }
    let (p, take_field0) = match operand {
        Op::Constant(ConstValue::Uint(k, _)) => return i128::try_from(*k).ok(),
        Op::Constant(ConstValue::Int(k)) if *k >= 0 => return Some(*k),
        Op::Copy(p) | Op::Move(p) if p.projections.is_empty() => (p, false),
        // The value field of a checked op: `_4 = _7.0` where `_7 = CheckedBinaryOp(..)`.
        Op::Copy(p) | Op::Move(p) if p.projections == [Projection::Field(0)] => (p, true),
        _ => return None,
    };
    if fuel == 0 {
        return if take_field0 { None } else { crate::place_ty(func, p).as_ref().and_then(ty_max) };
    }
    // Trust (P0 call-arg &mut staleness): NEVER trace a derived upper bound through a
    // local whose value is UNSTABLE — reassigned, or (the false-proof class here)
    // mutably borrowed and so reassignable through the borrow by an intervening call
    // (`mem::swap`/`replace`/`take`, a `set(&mut x, …)` setter, a `*p = …` store).
    // Tracing `_5 = copy _2`, `_2 = 0` into the constant 0 emitted the STALE global
    // fact `_5 <= 0`, which together with the real violation `_5 >= 4` vacuously
    // discharged the bounds check while `_2` was reassigned to 99 across the call —
    // a confirmed DEFAULT-mode false PROVE of an OOB index. Fall back to the loose
    // type bound (`local_max`) instead of the stale traced value. SOUNDNESS: a
    // looser-or-equal bound can only turn PROVE into not-proved, never the reverse.
    if !take_field0 && crate::guards::value_local_is_unstable(func, p.local) {
        let ty_bound = crate::place_ty(func, p).as_ref().and_then(ty_max);
        // Layered instability (merge of 17433eeacf staleness × 192a3cabb8 clamp):
        // reassignment instability alone does NOT defeat the clamp-diamond bound —
        // `clamp_upper_bound` examines EVERY direct def and call-dest write of the
        // local globally, and a 2-def diamond is inherently "reassigned". But a
        // mutable borrow permits writes that def scan cannot see (through the
        // pointer, across a call), and a PARAM's incoming value is an implicit def
        // it cannot see either — no derived bound may be trusted in those cases.
        let is_param = p.local >= 1 && p.local <= func.body.arg_count;
        if is_param || crate::guards::value_local_is_mut_borrowed(func, p.local) {
            return ty_bound;
        }
        return match clamp_upper_bound(func, p.local) {
            Some(c) => Some(ty_bound.map_or(c, |m| c.min(m))),
            None => ty_bound,
        };
    }
    let bin = |a: &Operand, b: &Operand, mul: bool| -> Option<i128> {
        let ua = unsigned_upper_bound(func, a, fuel - 1)?;
        let ub = unsigned_upper_bound(func, b, fuel - 1)?;
        if mul { ua.checked_mul(ub) } else { ua.checked_add(ub) }
    };
    if take_field0 {
        return match crate::unique_whole_local_def(func, p.local) {
            Some(Rvalue::CheckedBinaryOp(BinOp::Add, a, b)) => bin(a, b, false),
            Some(Rvalue::CheckedBinaryOp(BinOp::Mul, a, b)) => bin(a, b, true),
            _ => None,
        };
    }
    let local_max = crate::place_ty(func, p).as_ref().and_then(ty_max);
    let cap = |v: i128| Some(local_max.map_or(v, |m| v.min(m)));
    match crate::unique_whole_local_def(func, p.local) {
        Some(Rvalue::Cast(inner, to_ty)) => {
            let tmax = ty_max(to_ty)?;
            Some(unsigned_upper_bound(func, inner, fuel - 1).map_or(tmax, |a| a.min(tmax)))
        }
        Some(Rvalue::BinaryOp(BinOp::Add, a, b) | Rvalue::CheckedBinaryOp(BinOp::Add, a, b)) => {
            cap(bin(a, b, false)?)
        }
        Some(Rvalue::BinaryOp(BinOp::Mul, a, b) | Rvalue::CheckedBinaryOp(BinOp::Mul, a, b)) => {
            cap(bin(a, b, true)?)
        }
        // Unsigned division by a positive constant `c`: `ub(a / c) = ub(a) / c`
        // (floor). Sound: `a / c ≤ ub(a) / c` since integer division is monotone
        // in the dividend and `a ≤ ub(a)`. Only a constant divisor `≥ 1` (so the
        // quotient is well-defined and the bound nonincreasing).
        Some(Rvalue::BinaryOp(BinOp::Div, a, c)) => {
            let cv = match c {
                Op::Constant(ConstValue::Uint(k, _)) if *k >= 1 => i128::try_from(*k).ok(),
                Op::Constant(ConstValue::Int(k)) if *k >= 1 => Some(*k),
                _ => None,
            }?;
            cap(unsigned_upper_bound(func, a, fuel - 1)? / cv)
        }
        Some(Rvalue::Use(inner)) => unsigned_upper_bound(func, inner, fuel - 1).or(local_max),
        // A non-SSA local (no unique whole-local def) may still be a `min(v, C)`
        // clamp whose value is bounded by `C`. Resolve that tight bound, capped by
        // the local's own type range. See `clamp_upper_bound` (sound: `min(v,C) ≤ C`
        // globally). Falls back to the loose type bound when not a recognized clamp.
        _ => match clamp_upper_bound(func, p.local) {
            Some(c) => Some(local_max.map_or(c, |m| c.min(m))),
            None => local_max,
        },
    }
}

/// Global facts giving the TIGHT upper bound of an unsigned intermediate
/// `dest = a + b` / `a * b` — `dest ≤ ub(a)+ub(b)` (resp. `·`), resolved through
/// casts/arithmetic by [`unsigned_upper_bound`]. Sound (the value never exceeds the
/// real product/sum, even under machine wrap). Emitted only when strictly tighter
/// than `dest`'s type range, so the OUTER operation that consumes `dest` (e.g. the
/// `_5+_6` in `(a as u32)+(b as u32)+(c as u32)`) sees the real range rather than
/// the loose `u32` type bound — the vcgen intermediate-bound-loss fix.
pub(super) fn build_additive_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use trust_types::{Place, Ty};
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    for (local_idx, local) in func.body.locals.iter().enumerate() {
        let Ty::Int { width, signed: false } = &local.ty else { continue };
        if *width >= 127 || !is_single_static_assignment(func, local_idx) {
            continue;
        }
        // Only COMPUTED locals (those with a defining rvalue) get a derived bound.
        if crate::unique_whole_local_def(func, local_idx).is_none() {
            continue;
        }
        let place = Place { local: local_idx, projections: vec![] };
        let Some(bound) = unsigned_upper_bound(func, &Operand::Copy(place.clone()), FUEL) else {
            continue;
        };
        // Only worth a fact if strictly tighter than the local's type range.
        if bound >= (1i128 << *width) - 1 {
            continue;
        }
        let var = Formula::Var(crate::place_to_var_name(func, &place), Sort::Int);
        facts.push(Formula::Le(Box::new(var), Box::new(Formula::Int(bound))));
    }
    facts
}

/// Discriminant CSE: two `Discriminant` reads of the SAME canonical enum referent,
/// BOTH taken before any code could mutate the referent, have equal values (a real
/// program equality), so tie them with a global fact. A derived `PartialEq::eq` reads
/// the outer `disc(*self)`/`disc(*other)` AND, inside the per-variant match,
/// `disc(*_23)`/`disc(*_24)` where the payload-tuple fields `_23 = _6.0 ≡ self`,
/// `_24 = _6.1 ≡ other`. The `referent_of_source` aggregate-field fold canonicalizes
/// `*_23 → *self`, so this groups the inner reads with the outer and emits
/// `disc(*_23) == disc(*self)` etc. — exactly the facts that discharge the shared
/// per-variant `otherwise → Unreachable`. Emitted with the discriminants' NATIVE names
/// (no rename), so it agrees with the exhaustive-enum validity (`disc ∈ {cases}`) the
/// native CHC translator conjoins.
///
/// SOUNDNESS (two guards, both load-bearing):
/// 1. Only STABLE-source discriminant reads are eligible: either (a) `disc(*L)`
///    through a SHARED reference (`L: &T`), or (b) `disc(_agg.idx)` on an OWNED
///    aggregate field where `_agg` is an `Rvalue::Aggregate` and
///    `place_source_is_stable(_agg)` holds (no projected store / `&mut` /
///    `SetDiscriminant` / deinit / second def / call-dest write into `_agg`). Arm
///    (b) ties the per-field re-reads of a by-value `match (self, other)` so the
///    per-temp range facts discharge the shared `otherwise -> Unreachable`. `&mut`
///    / raw-ptr / Deref-of-mut / nested projections are excluded in both arms.
/// 2. Only reads in the PRE-BARRIER region — not reachable from entry after any
///    `Call`/`Drop`/`Opaque` terminator — are tied. A shared borrow forbids mutation
///    *through L*, but the pointee can still change across program points via a
///    SEPARATE aliasing handle with interior mutability (`let c: &Cell<E>` aliasing
///    `r: &E`; `c.set(..)` between two `*r` reads). Such a mutation can only run inside
///    a `Call`/`Drop`/`Opaque`, so requiring BOTH reads to precede every barrier means
///    the pointee is still in its entry state at each — `disc(*L)` is then genuinely
///    identical. Without guard 2 the fact is a FALSE PROOF (caught by adversarial
///    review: `im_direct_attack`). The derived-`eq` discriminant reads are all
///    pre-barrier (field comparisons / drops come after), so `eq` still discharges.
/// Distinct enum fields keep distinct canonical names and are never merged (so a
/// 2-distinct-enum `eq` keeps its real `Unreachable` and still refutes).
pub(crate) fn build_discriminant_cse_facts(func: &VerifiableFunction) -> Vec<Formula> {
    // Post-barrier taint: blocks reachable from entry AFTER crossing a terminator that
    // can run arbitrary code (`Call`/`Drop`/`Opaque`). A `Discriminant` read in a
    // tainted block may see a pointee an aliasing interior-mutation has changed, so it
    // is NOT eligible for CSE.
    let blocks = &func.body.blocks;
    let mut tainted: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<usize> = blocks
        .iter()
        .filter(|b| {
            matches!(
                b.terminator,
                Terminator::Call { .. } | Terminator::Drop { .. } | Terminator::Opaque { .. }
            )
        })
        .flat_map(|b| terminator_succs(&b.terminator))
        .collect();
    while let Some(b) = stack.pop() {
        if tainted.insert(b) {
            if let Some(blk) = blocks.get(b) {
                stack.extend(terminator_succs(&blk.terminator));
            }
        }
    }

    let mut by_referent: FxHashMap<String, Vec<(String, Sort)>> = FxHashMap::default();
    for (idx, block) in blocks.iter().enumerate() {
        if tainted.contains(&idx) {
            continue; // a read after a barrier: its pointee may have been mutated
        }
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            if !dest.projections.is_empty() {
                continue;
            }
            // Guard 1: the discriminant source must denote a STABLE value at every
            // read. Two admitted shapes:
            //  (a) shared-ref deref `disc(*L)`, `L: &T` (derived-`PartialEq::eq`): a
            //      shared borrow forbids mutation through L; guard 2 (taint) covers
            //      aliasing interior mutation. `&mut` / raw-ptr reads are excluded.
            //  (b) owned aggregate field `disc(_agg.idx)` where `_agg` is built by an
            //      `Rvalue::Aggregate` and `place_source_is_stable(_agg)` holds (no
            //      projected store / `&mut` / `SetDiscriminant` / deinit / 2nd def /
            //      call-dest write into it). This is the by-VALUE `match (self, other)`
            //      shape (e.g. `Multiplicity::mul`): rustc re-reads `_3.0`/`_3.1` into
            //      separate discriminant temps across OR-pattern arms, each switch
            //      covering only a SUBSET of tags; tying the same-field reads lets the
            //      per-temp range facts (`_d ∈ {tags}`) discharge the shared
            //      `otherwise -> Unreachable`. Only a single owned `Field` on a
            //      constructed aggregate is admitted — never Deref/Index/nested — so
            //      genuinely-distinct fields keep distinct canonical names.
            let shared_ref_deref =
                matches!(src.projections.as_slice(), [trust_types::Projection::Deref])
                    && matches!(
                        // verifier-perf: borrow the declared type — only a variant check.
                        crate::local_ty_ref(func, src.local),
                        Some(Ty::Ref { mutable: false, .. })
                    );
            let owned_agg_field =
                matches!(src.projections.as_slice(), [trust_types::Projection::Field(_)])
                    && matches!(
                        crate::unique_whole_local_def(func, src.local),
                        Some(Rvalue::Aggregate(..))
                    )
                    && crate::place_source_is_stable(func, src.local);
            if !(shared_ref_deref || owned_agg_field) {
                continue;
            }
            let canon = crate::place_to_var_name(func, src);
            let dest_name = crate::place_to_var_name(func, dest);
            let sort = crate::place_sort(func, dest).unwrap_or(Sort::Int);
            by_referent.entry(canon).or_default().push((dest_name, sort));
        }
    }
    let mut facts = Vec::new();
    for reads in by_referent.into_values() {
        let Some((anchor_name, anchor_sort)) = reads.first().cloned() else {
            continue;
        };
        for (other_name, _) in reads.iter().skip(1) {
            facts.push(Formula::Eq(
                Box::new(Formula::Var(anchor_name.clone(), anchor_sort.clone())),
                Box::new(Formula::Var(other_name.clone(), anchor_sort.clone())),
            ));
        }
    }
    facts
}

/// Exhaustive-enum discriminant validity. For each `SwitchInt` the extractor
/// TyCtxt-vetted as `exhaustive_enum_unreachable` — its selector is a genuine
/// single-assignment enum-discriminant temp, the case values (`targets.0`) are
/// EXACTLY the enum's full discriminant tag set, and `otherwise` targets an
/// `Unreachable` block — emit the validity fact `disc ∈ {case values}`. The
/// `otherwise → Unreachable` path guard is `disc ∉ {case values}`, so this fact
/// makes it UNSAT, proving the trap. Without it the V1/default lane RUNTIME-CHECKS
/// that trap — e.g. the iterator-exhaustion `Unreachable` after a `for` loop's
/// `Option`-discriminant match (the dominant fuzzer `[unreach]` completeness gap).
///
/// SOUND: the flag's TyCtxt vetting guarantees `disc` is always one of the cased
/// values (an N-variant enum's discriminant is in its tag set), so the membership
/// fact is a true program invariant — never a false proof. This MIRRORS the
/// `disc ∈ {case values}` the native CHC translator already conjoins (per the
/// `exhaustive_enum_unreachable` field doc); it just brings the default lane to
/// parity. Emitted over the discriminant's NATIVE name (no rename), like
/// `build_discriminant_cse_facts`, so it agrees with the path-guard's bare read.
pub(super) fn build_exhaustive_enum_validity_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::SwitchInt { discr, targets, exhaustive_enum_unreachable: true, .. } =
            &block.terminator
        else {
            continue;
        };
        if targets.is_empty() {
            continue;
        }
        let disc = crate::operand_to_formula(func, discr);
        let cases: Vec<Formula> = targets
            .iter()
            .filter_map(|(v, _)| i128::try_from(*v).ok())
            .map(|v| Formula::Eq(Box::new(disc.clone()), Box::new(Formula::Int(v))))
            .collect();
        // Only emit when every case value lowered (a partial set would be unsound).
        if cases.len() != targets.len() {
            continue;
        }
        facts.push(if cases.len() == 1 {
            cases.into_iter().next().expect("len checked")
        } else {
            Formula::Or(cases)
        });
    }
    facts
}

/// Per-ADT discriminant range bound (Lever A). For each `d = Discriminant(src)`
/// read whose SOURCE place resolves to a modeled enum, conjoin the membership fact
/// `d ∈ {variant tags}` — the phantom-tag refutation that collapses the spurious
/// `__type_tag` obligation explosion (a read of a 3-variant enum can only produce
/// a discriminant in its variant tag set, so a solver counterexample with a
/// phantom tag `d = 7` is impossible). Complements
/// `build_exhaustive_enum_validity_facts` (which bounds at `SwitchInt`
/// terminators); this bounds at the `Rvalue::Discriminant` READ, independent of
/// any switch.
///
/// SOUNDNESS: the bound is the enum's OWN TYPE INVARIANT — every inhabitant of the
/// enum carries a discriminant drawn EXACTLY from its variants' tags, so the
/// membership disjunction is a TRUE fact about every value the read can produce. It
/// can only delete IMPOSSIBLE counterexamples (a phantom tag matching no variant),
/// never a real one (whose witness already carries a valid tag) and never a false
/// PROVE: the OOB-index / div-by-zero canaries are violated even with EVERY
/// discriminant in range, so this fact leaves them refuted. The tag set is the
/// ACTUAL per-variant `VariantDef.discriminant` (or the positional `0..n` for a
/// `Ty::Datatype`), NOT a `0..n-1` interval — a `#[repr]` enum with non-contiguous
/// discriminants (`A = 5, B = 10`) is bounded by `d ∈ {5, 10}`, never the unsound
/// `0 <= d <= 1`, so a valid `d = 10` is never (false-)excluded. Emitted over BOTH
/// the dest's native var name (default lane) and the canonical generated
/// discriminant name (native CHC path), so it attaches whichever lane lowered
/// the read; an unmatched name is inert.
pub(super) fn build_discriminant_variant_range_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            // Resolve the SOURCE place's type to a modeled enum and read its
            // actual per-variant discriminant tag set. `None` (struct, by-name
            // datatype ref, unresolvable, or non-ADT) yields no fact — conservative.
            let Some(src_ty) = crate::place_ty_cow(func, src) else {
                continue;
            };
            let Some(tags) = enum_variant_tag_set(src_ty.as_ref()) else {
                continue;
            };
            if tags.is_empty() {
                continue;
            }
            // Build `d ∈ {tags}` over the dest var name (default lane) AND the
            // canonical generated discriminant name (native CHC path). Either
            // name may be the one a VC references; the other is inert.
            let dest_name = crate::place_to_var_name(func, dest);
            let discr_name =
                crate::discriminant_formula_var_name(&crate::place_to_var_name(func, src));
            let mut tag_var_sets: Vec<(String, Vec<i128>)> =
                vec![(dest_name, tags.clone()), (discr_name, tags.clone())];
            // Trust (P0 enum-disc cast false REFUTATION, -full): the discriminant is
            // almost always CAST before use as an index — `arr[e as usize]` lowers to
            //   `_4 = Discriminant(e); _3 = move _4 as usize (IntToInt); arr[_3]`.
            // The bounds VC is about the CAST RESULT `_3`, not `_4`, so a tag-set fact
            // only over `_4` never reaches it. Under `-full` the cast equality
            // `_3 == _4` was decoupled (counterexample `_3 = 3, discr_e = 0`), so
            // `_3 >= len` was SAT and the always-safe `arr[e as usize]` was REFUTED.
            // When EVERY tag is NON-NEGATIVE, emit the tag-set fact over the cast
            // destination as well — rendered through the EXACT `as`-cast semantics.
            //
            // Trust (P0 enumdisc-narrowing-cast FALSE PROOF): the cast-destination
            // fact must be the tags' IMAGE under the cast, `{t as ToTy}` — NOT the
            // raw declared set. A NARROWING cast truncates mod 2^width: for
            // `#[repr(u16)] enum E { A = 0, B = 260, C = 512 }`, `e as u8` yields
            // `{0, 4, 0}`, but the raw fact `_3 ∈ {0, 260, 512}` intersected with
            // the u8 range `[0, 255]` collapses to `{0}` — a VACUOUS premise that
            // false-PROVED the out-of-bounds `a[(e as u8) as usize]` on `[u8; 4]`
            // (E::B: 260 as u8 == 4, runtime panic). `truncate_nonneg_tag_as_int`
            // constant-folds each tag through the destination width/signedness, so
            // the emitted membership is a TRUE fact about the cast result for every
            // input; for a non-narrowing cast it is the identity, preserving the
            // false-refutation fix above. SOUND: the tags are read from the type and
            // folded with Rust's own `as` semantics; the all-non-negative gate keeps
            // the SOURCE value equal to its declared tag under the repr (a negative
            // `repr(iN)` tag, whose `as usize` reinterprets the sign bit, is left to
            // the loose path — no fact, so no false refutation either way).
            if tags.iter().all(|&t| t >= 0) {
                for cast_block in &func.body.blocks {
                    for cast_stmt in &cast_block.stmts {
                        let Statement::Assign {
                            place: cast_dest,
                            rvalue: Rvalue::Cast(cast_src, to_ty),
                            ..
                        } = cast_stmt
                        else {
                            continue;
                        };
                        // The cast must read THIS discriminant result `_4` (whole local)
                        // and target an integer type (so `∈ {tags}` is meaningful).
                        let reads_disc = matches!(
                            cast_src,
                            Operand::Copy(p) | Operand::Move(p)
                                if p.local == dest.local && p.projections.is_empty()
                        );
                        if reads_disc
                            && cast_dest.projections.is_empty()
                            && let Ty::Int { width: to_w, signed: to_s } = to_ty
                        {
                            // Fold each tag through the destination type (mod 2^w +
                            // sign reinterpretation); dedup — a narrowing cast can
                            // collapse distinct tags onto one residue.
                            let mut cast_tags: Vec<i128> = tags
                                .iter()
                                .map(|&t| truncate_nonneg_tag_as_int(t, *to_w, *to_s))
                                .collect();
                            cast_tags.sort_unstable();
                            cast_tags.dedup();
                            tag_var_sets
                                .push((crate::place_to_var_name(func, cast_dest), cast_tags));
                        }
                    }
                }
            }
            for (var_name, tag_set) in tag_var_sets {
                let var = Formula::Var(var_name, Sort::Int);
                let cases: Vec<Formula> = tag_set
                    .iter()
                    .map(|&t| Formula::Eq(Box::new(var.clone()), Box::new(Formula::Int(t))))
                    .collect();
                facts.push(if cases.len() == 1 {
                    cases.into_iter().next().expect("len checked")
                } else {
                    Formula::Or(cases)
                });
            }
        }
    }
    facts
}

/// The actual discriminant tag set of a MODELED enum type, in declaration order.
/// `Ty::Adt` carries the real `VariantDef.discriminant` per variant (so a
/// `#[repr]` enum's explicit non-contiguous tags are honored); a `Ty::Datatype`
/// is built positionally, so its tags are `0..n`. `None` for a struct, a by-name
/// datatype reference (empty variants), or any non-ADT type. SOUNDNESS: this
/// reads the type's own variant tags — it invents nothing.
pub(super) fn enum_variant_tag_set(ty: &Ty) -> Option<Vec<i128>> {
    match ty {
        Ty::Adt { variants, .. } if !variants.is_empty() => {
            Some(variants.iter().map(|v| v.discriminant).collect())
        }
        Ty::Datatype { variants, .. } if !variants.is_empty() => {
            Some((0..variants.len() as i128).collect())
        }
        _ => None,
    }
}

/// Trust (P0 enumdisc-narrowing-cast false proof): the EXACT value of Rust's
/// `t as ToTy` for a NON-NEGATIVE integer `t` and an integer destination of
/// `width` bits / `signed`ness — bit-level truncation mod 2^width, then
/// reinterpretation under the destination's sign bit. This is the constant fold
/// that renders a discriminant tag-set fact onto a cast RESULT: carrying the raw
/// declared tag across a NARROWING cast (`260 as u8`) without the mod produces a
/// value the cast can never yield, and its intersection with the destination's
/// type-range fact vacuously proved an out-of-bounds index. For a destination
/// wide enough to hold `t` the fold is the identity, so non-narrowing behavior
/// is unchanged. SOUNDNESS: mirrors the language semantics exactly — for every
/// input value equal to `t`, the cast result equals the folded value.
pub(super) fn truncate_nonneg_tag_as_int(t: i128, width: u32, signed: bool) -> i128 {
    debug_assert!(t >= 0, "caller gates on an all-non-negative tag set");
    if width >= 128 {
        // Every non-negative i128 value is representable unchanged in both
        // u128 and i128 — the cast is value-preserving.
        return t;
    }
    // width in 1..=127: compute in u128 so `1 << width` cannot overflow the
    // signed domain (e.g. width 127).
    let modulus = 1u128 << width;
    let truncated = (t as u128) % modulus; // truncation IS mod 2^width for t >= 0
    if signed && truncated >= modulus >> 1 {
        // Destination sign bit set: the value wraps negative (truncated - 2^width),
        // computed without leaving the representable range.
        -((modulus - truncated) as i128)
    } else {
        truncated as i128 // < 2^127, always fits
    }
}

/// Global facts from unsigned `dest = a & m` (`Rvalue::BinaryOp(BitAnd, a, m)`)
/// with a CONSTANT mask `m >= 0`: the bitwise-AND can only clear bits, so
/// `a & m <= m` unconditionally for any unsigned `a`. This is the bitmask
/// analogue of [`build_modulo_bound_facts`] — it discharges a power-of-two
/// masked index `s[i & 15]` into `[_; 16]` (`i & 15 <= 15 < 16`), a common
/// ring-buffer / hash-table idiom. The fact is over the masked DEST variable
/// `_3` (the `Eq(_3, BvToInt(BvAnd(..)))` definition carries the bitvector and is
/// soundly dropped by the kernel-cert path), so the existing single-variable
/// interval certification closes `_3 <= 15 ∧ _3 >= 16`.
pub(super) fn build_bitmask_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            let Statement::Assign { place: dest, rvalue, .. } = stmt else { continue };
            if !dest.projections.is_empty() {
                continue;
            }
            let Rvalue::BinaryOp(trust_types::BinOp::BitAnd, a, b) = rvalue else { continue };
            if !is_single_static_assignment(func, dest.local) {
                continue;
            }
            // Unsigned operand — the index value is a non-negative `usize`.
            if !crate::operand_ty_cow(func, a).is_some_and(|t| t.is_integer() && !t.is_signed()) {
                continue;
            }
            // The mask must be a non-negative integer constant.
            let mask = match b {
                Operand::Constant(trust_types::ConstValue::Uint(v, _))
                    if *v <= i128::MAX as u128 =>
                {
                    *v as i128
                }
                Operand::Constant(trust_types::ConstValue::Int(v)) if *v >= 0 => *v,
                _ => continue,
            };
            let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
            // `a & mask <= mask` for unsigned `a`.
            facts.push(Formula::Le(Box::new(dest_var), Box::new(Formula::Int(mask))));
        }
    }
    facts
}

/// Resolve an init RVALUE (`i = s.len()`) to the stable parameter slice-length term
/// it reads — the bound `B` of a downward induction variable. See
/// [`build_downward_induction_facts`].
pub(super) fn init_rvalue_stable_len(
    func: &VerifiableFunction,
    rvalue: &Rvalue,
    fuel: u32,
) -> Option<Formula> {
    if fuel == 0 {
        return None;
    }
    match rvalue {
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner) => {
            param_slice_len(func, inner, fuel)
        }
        Rvalue::Len(place) => param_slice_len(func, &Operand::Copy(place.clone()), fuel),
        Rvalue::Use(op) => stable_min_arg_formula(func, op, fuel),
        _ => None,
    }
}

/// `_t = CheckedSub(Copy/Move(L), c)` with `c >= 1`? Returns the decrement constant
/// `c` (`_t.0` is the decremented value `L - c`) for a self-decrement of `L`.
pub(super) fn checked_self_decrement_const(func: &VerifiableFunction, l: usize, t: usize) -> Option<i128> {
    let Some(Rvalue::CheckedBinaryOp(trust_types::BinOp::Sub, lhs, rhs)) =
        crate::unique_whole_local_def(func, t)
    else {
        return None;
    };
    let lhs_is_l = matches!(lhs, Operand::Copy(p) | Operand::Move(p)
        if p.local == l && p.projections.is_empty());
    if !lhs_is_l {
        return None;
    }
    let c = match rhs {
        Operand::Constant(trust_types::ConstValue::Int(v)) if *v >= 1 => *v,
        Operand::Constant(trust_types::ConstValue::Uint(v, _)) if *v >= 1 => {
            i128::try_from(*v).ok()?
        }
        _ => return None,
    };
    Some(c)
}
