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
    // Trust (LIVE false-PROVE, found by the global-fact reassignment census): a
    // store THROUGH a mutable borrow (`let p = &mut idx; *p = b;` — place.local is
    // `p`, not `idx`) is a write no def scan can see, and `idx` still scores one
    // definition. The emitted `idx == lhs - rhs` is then version-renamed onto the
    // block terminal, i.e. onto the MUTATED `idx`, and pins it to a value it no
    // longer holds. `borrow_reassigned_index_still_refutes` is the witness:
    // `if !v.is_empty() { let mut idx = v.len()-1; let p = &mut idx; *p = b;
    // v[idx] }` verified `2 proved, 0 failed` and indexes out of bounds at
    // runtime. `local_mut_escapes` is the same kill `is_single_static_assignment`
    // carries for exactly this channel.
    //
    // `value_count <= 1` — NOT a hand-rolled `Assign`-place tally against a
    // hardcoded 1. A PARAMETER's definition is the implicit ENTRY one, so one
    // explicit reassignment already gives it two values while a block scan still
    // reads 1. `param_checked_sub_result_still_refutes` /
    // `param_checked_add_result_still_refutes` are the witnesses. `<= 1` rather
    // than `== 1` because an operand that is never whole-defined (a projected
    // read's base) is stable too.
    let stable_memo: std::cell::RefCell<Vec<Option<bool>>> = std::cell::RefCell::new(Vec::new());
    let stable = |l: usize| {
        if let Some(Some(cached)) = stable_memo.borrow().get(l).copied() {
            return cached;
        }
        let val =
            crate::local_defs::value_count(func, l).is_at_most(1) && !local_mut_escapes(func, l);
        let mut memo = stable_memo.borrow_mut();
        if memo.is_empty() {
            memo.resize(func.body.locals.len(), None);
        }
        if let Some(slot) = memo.get_mut(l) {
            *slot = Some(val);
        }
        val
    };
    let stable_op = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => p.projections.is_empty() && stable(p.local),
        _ => false,
    };
    let field0_copies: std::cell::OnceCell<FxHashMap<usize, Vec<usize>>> =
        std::cell::OnceCell::new();
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
            if !sub_place.projections.is_empty() {
                continue;
            }
            // UNSIGNED gate: `lhs < rhs` is the underflow flag ONLY for unsigned ints.
            if !matches!(
                crate::operand_ty_cow(func, lhs).as_deref(),
                Some(Ty::Int { signed: false, .. })
            ) {
                continue;
            }
            // PERF-COMPILER-VCGEN-638: check whether any whole-local `_idx = move/copy (_c.0)`
            // copy of `sub_place.local` exists before querying `stable` (`value_count` +
            // `local_mut_escapes`) on `sub_place.local`, `lhs`, `rhs`, or unrelated `.0` copies.
            let Some(dst_locals) =
                field0_copies.get_or_init(|| collect_field0_copies(func)).get(&sub_place.local)
            else {
                continue;
            };
            if !stable(sub_place.local) || !stable_op(lhs) || !stable_op(rhs) {
                continue;
            }
            let lhs_f = crate::operand_to_formula(func, lhs);
            let rhs_f = crate::operand_to_formula(func, rhs);
            let lt = Formula::Lt(Box::new(lhs_f.clone()), Box::new(rhs_f.clone()));
            let diff = Formula::Sub(Box::new(lhs_f), Box::new(rhs_f));
            for &dst_local in dst_locals {
                if !stable(dst_local) {
                    continue;
                }
                let dst_name = crate::place_to_var_name(func, &Place::local(dst_local));
                // `_dst = move (_c.0)` may write back the very local an operand
                // was read from (`x -= k`), which mints `Eq(x, Sub(x, k))` — a
                // recurrence, not a definition, UNSAT for any nonzero `k`. One
                // such hypothesis vacuously discharges every obligation it
                // reaches. Drop-only, so it can only weaken a prove.
                if trust_types::any_free_variable_name(&diff, &mut |v| v == dst_name) {
                    continue;
                }
                facts.push(Formula::Or(vec![
                    lt.clone(),
                    Formula::Eq(
                        Box::new(Formula::Var(dst_name, Sort::Int)),
                        Box::new(diff.clone()),
                    ),
                ]));
            }
        }
    }
    facts
}

fn collect_field0_copies(func: &VerifiableFunction) -> FxHashMap<usize, Vec<usize>> {
    let mut map: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
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
            if dst.projections.is_empty()
                && matches!(p.projections.as_slice(), [trust_types::Projection::Field(0)])
            {
                map.entry(p.local).or_default().push(dst.local);
            }
        }
    }
    map
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
    // The same gate as the sub twin, for the same two reasons: a store through
    // `&mut` is a write no def scan sees, and a PARAMETER's definition is the
    // implicit ENTRY one. Both are `local_defs::value_count` + `local_mut_escapes`
    // there; see that function for the witnesses.
    let stable_memo: std::cell::RefCell<Vec<Option<bool>>> = std::cell::RefCell::new(Vec::new());
    let stable = |l: usize| {
        if let Some(Some(cached)) = stable_memo.borrow().get(l).copied() {
            return cached;
        }
        let val =
            crate::local_defs::value_count(func, l).is_at_most(1) && !local_mut_escapes(func, l);
        let mut memo = stable_memo.borrow_mut();
        if memo.is_empty() {
            memo.resize(func.body.locals.len(), None);
        }
        if let Some(slot) = memo.get_mut(l) {
            *slot = Some(val);
        }
        val
    };
    let stable_op = |op: &Operand| match op {
        Operand::Constant(_) => true,
        Operand::Copy(p) | Operand::Move(p) => p.projections.is_empty() && stable(p.local),
        _ => false,
    };
    let field0_copies: std::cell::OnceCell<FxHashMap<usize, Vec<usize>>> =
        std::cell::OnceCell::new();
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
            if !add_place.projections.is_empty() {
                continue;
            }
            // UNSIGNED gate + the type's exact upper bound for the overflow guard.
            let Some(&Ty::Int { signed: false, width }) =
                crate::operand_ty_cow(func, lhs).as_deref()
            else {
                continue;
            };
            if width >= 127 {
                continue;
            }
            // PERF-COMPILER-VCGEN-638: check whether any whole-local `_idx = move/copy (_c.0)`
            // copy of `add_place.local` exists before querying `stable` (`value_count` +
            // `local_mut_escapes`) on `add_place.local`, `lhs`, `rhs`, or unrelated `.0` copies.
            let Some(dst_locals) =
                field0_copies.get_or_init(|| collect_field0_copies(func)).get(&add_place.local)
            else {
                continue;
            };
            if !stable(add_place.local) || !stable_op(lhs) || !stable_op(rhs) {
                continue;
            }
            let type_max = (1i128 << width) - 1;
            let lhs_f = crate::operand_to_formula(func, lhs);
            let rhs_f = crate::operand_to_formula(func, rhs);
            let sum = Formula::Add(Box::new(lhs_f), Box::new(rhs_f));
            let gt_max = Formula::Gt(Box::new(sum.clone()), Box::new(Formula::Int(type_max)));
            for &dst_local in dst_locals {
                if !stable(dst_local) {
                    continue;
                }
                let dst_name = crate::place_to_var_name(func, &Place::local(dst_local));
                // `_dst = move (_c.0)` may write back the very local an operand
                // was read from (`i += 100`), which mints `Eq(i, Add(i, 100))` —
                // a recurrence, not a definition, UNSAT for any nonzero addend.
                // MEASURED 2026-08-26: this is the producer that false-PROVED
                // `if i < 4 { i += 100; a[i] }` under certify while the binary
                // died at index 101 (fixture selfadd_guarded_index). Drop-only.
                if trust_types::any_free_variable_name(&sum, &mut |v| v == dst_name) {
                    continue;
                }
                facts.push(Formula::Or(vec![
                    gt_max.clone(),
                    Formula::Eq(
                        Box::new(Formula::Var(dst_name, Sort::Int)),
                        Box::new(sum.clone()),
                    ),
                ]));
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
///
/// The production spelling: the set for `func`, as the per-row view
/// ([`RowGlobalFacts`]), built once per [`super::FuncAnalysisScope`]
/// (`super::row_global_facts_for`, PERF-COMPILER-VCGEN-81). The raw set and the index
/// range of its element-read congruences come from
/// [`build_global_invariant_facts_with_congruence_range`], which only
/// [`RowGlobalFacts::for_function`] calls. Trust: 2026-11-07 (VCGEN-CENSUS-SITE-REDS-1):
/// `tests/global_fact_sites_are_classified.rs` classifies every site that builds the set,
/// under each of these spellings.
pub(crate) fn build_global_invariant_facts(
    func: &VerifiableFunction,
) -> std::rc::Rc<RowGlobalFacts> {
    super::row_global_facts_for(func)
}

#[derive(Default)]
struct BodyFactPresence {
    has_call: bool,
    has_bare_dest_call: bool,
    has_bare_unary_call: bool,
    has_bare_binary_call: bool,
    has_min_call: bool,
    has_min_max_call: bool,
    has_len_call: bool,
    has_abs_call: bool,
    has_nonzero_get_call: bool,
    has_intrinsic_bound_call: bool,
    has_expect_call: bool,
    std_scalar_index_calls: usize,
    has_total_clone_sentinel_call: bool,
    has_checked_sub: bool,
    has_checked_add: bool,
    has_checked_mul_any: bool,
    has_rem: bool,
    has_div: bool,
    has_bitand: bool,
    has_cast: bool,
    has_additive_rvalue: bool,
    has_narrow_uint_local: bool,
    has_field0_readback: bool,
    has_ref_seq_param: bool,
    discr_count: usize,
    bare_discr_count: usize,
    projected_copy_reads: usize,
    has_const_param: bool,
    entry_has_switch: bool,
}

impl BodyFactPresence {
    fn ty_has_sym_array(ty: &Ty) -> bool {
        match ty {
            Ty::SymArray { .. } => true,
            Ty::Ref { inner, .. } => Self::ty_has_sym_array(inner),
            Ty::RawPtr { pointee, .. } => Self::ty_has_sym_array(pointee),
            Ty::Slice { elem } | Ty::Array { elem, .. } => Self::ty_has_sym_array(elem),
            Ty::Tuple(ts) => ts.iter().any(Self::ty_has_sym_array),
            _ => false,
        }
    }

    #[inline]
    fn note_operand(&mut self, op: &Operand, count_projected_copy: bool) {
        match op {
            Operand::Copy(p)
                if count_projected_copy
                    && (matches!(p.projections.first(), Some(trust_types::Projection::Deref))
                        || p.projections
                            .iter()
                            .any(|proj| matches!(proj, trust_types::Projection::Index(_)))) =>
            {
                self.projected_copy_reads += 1;
            }
            Operand::Constant(ConstValue::ConstParam { width, signed, .. })
                if !(*width == 1 && !*signed) =>
            {
                self.has_const_param = true;
            }
            _ => {}
        }
    }

    fn of(func: &VerifiableFunction) -> Self {
        let mut p = Self {
            entry_has_switch: func
                .body
                .blocks
                .first()
                .is_some_and(|b| matches!(b.terminator, Terminator::SwitchInt { .. })),
            ..Self::default()
        };
        for (idx, decl) in func.body.locals.iter().enumerate() {
            if matches!(&decl.ty, Ty::Int { width, signed: false } if *width < 127) {
                p.has_narrow_uint_local = true;
            }
            if !p.has_const_param && Self::ty_has_sym_array(&decl.ty) {
                p.has_const_param = true;
            }
            if (1..=func.body.arg_count).contains(&idx)
                && matches!(
                    &decl.ty,
                    Ty::Ref { inner, .. } if matches!(inner.as_ref(), Ty::Seq { .. })
                )
            {
                p.has_ref_seq_param = true;
            }
        }
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place, rvalue, .. } = stmt else { continue };
                let bare = place.projections.is_empty();
                match rvalue {
                    Rvalue::CheckedBinaryOp(op, a, b) => {
                        p.note_operand(a, true);
                        p.note_operand(b, true);
                        match op {
                            BinOp::Sub => {
                                if bare {
                                    p.has_checked_sub = true;
                                }
                            }
                            BinOp::Add => {
                                if bare {
                                    p.has_checked_add = true;
                                    p.has_additive_rvalue = true;
                                }
                            }
                            BinOp::Mul => {
                                p.has_checked_mul_any = true;
                                if bare {
                                    p.has_additive_rvalue = true;
                                }
                            }
                            _ => {}
                        }
                    }
                    Rvalue::BinaryOp(op, a, b) => {
                        p.note_operand(a, true);
                        p.note_operand(b, true);
                        if bare {
                            match op {
                                BinOp::Rem => p.has_rem = true,
                                BinOp::Div => {
                                    p.has_div = true;
                                    p.has_additive_rvalue = true;
                                }
                                BinOp::BitAnd => p.has_bitand = true,
                                BinOp::Add | BinOp::Mul => p.has_additive_rvalue = true,
                                _ => {}
                            }
                        }
                    }
                    Rvalue::Cast(op, _) => {
                        p.note_operand(op, true);
                        if bare {
                            p.has_cast = true;
                            p.has_additive_rvalue = true;
                        }
                    }
                    Rvalue::Use(op) => {
                        p.note_operand(op, true);
                        if bare {
                            p.has_additive_rvalue = true;
                            if matches!(
                                op,
                                Operand::Copy(src) | Operand::Move(src)
                                    if matches!(
                                        src.projections.as_slice(),
                                        [trust_types::Projection::Field(0)]
                                    )
                            ) {
                                p.has_field0_readback = true;
                            }
                        }
                    }
                    Rvalue::UnaryOp(_, op) | Rvalue::Repeat(op, _) => {
                        p.note_operand(op, true);
                    }
                    Rvalue::Aggregate(_, ops) => {
                        for op in ops {
                            p.note_operand(op, true);
                        }
                    }
                    Rvalue::Discriminant(_) => {
                        p.discr_count += 1;
                        if bare {
                            p.bare_discr_count += 1;
                        }
                    }
                    _ => {}
                }
            }
            match &block.terminator {
                Terminator::Call { func: callee, args, dest, callee_key, .. } => {
                    p.has_call = true;
                    if dest.projections.is_empty() {
                        p.has_bare_dest_call = true;
                        match args.len() {
                            1 => {
                                p.has_bare_unary_call = true;
                                if method_tail(callee) == "len"
                                    || matches!(
                                        callee_key.as_ref().and_then(|k| k.sysroot_item),
                                        Some(
                                            trust_types::SysrootItem::StrLen
                                                | trust_types::SysrootItem::SliceLen
                                        )
                                    )
                                {
                                    p.has_len_call = true;
                                }
                                if callee
                                    .rsplit("::")
                                    .next()
                                    .is_some_and(|last| last.split('<').next().unwrap_or(last).trim() == "abs")
                                {
                                    p.has_abs_call = true;
                                }
                                if is_std_num_intrinsic(callee) {
                                    p.has_intrinsic_bound_call = true;
                                    if is_nonzero_get_call(callee) {
                                        p.has_nonzero_get_call = true;
                                    }
                                }
                            }
                            2 => {
                                p.has_bare_binary_call = true;
                                match ord_method(callee) {
                                    Some("min") => {
                                        p.has_min_call = true;
                                        p.has_min_max_call = true;
                                    }
                                    Some("max") => p.has_min_max_call = true,
                                    _ => {}
                                }
                                if is_std_num_intrinsic(callee) {
                                    p.has_intrinsic_bound_call = true;
                                }
                                if callee.contains("expect") {
                                    p.has_expect_call = true;
                                }
                                if super::unwrap_panic::is_std_scalar_index_call(callee) {
                                    p.std_scalar_index_calls += 1;
                                }
                                if callee == trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL {
                                    p.has_total_clone_sentinel_call = true;
                                }
                            }
                            _ => {}
                        }
                    }
                    for op in args {
                        p.note_operand(op, true);
                    }
                }
                Terminator::SwitchInt { discr, .. } => p.note_operand(discr, true),
                Terminator::Assert { cond, .. } => p.note_operand(cond, false),
                _ => {}
            }
        }
        p
    }
}

/// The raw set [`build_global_invariant_facts`] views, and the index range of its
/// element-read congruences ([`build_element_read_congruence_facts`]), which
/// [`RowGlobalFacts::for_function`] filters per row.
pub(crate) fn build_global_invariant_facts_with_congruence_range(
    func: &VerifiableFunction,
) -> (Vec<Formula>, std::ops::Range<usize>) {
    let p = BodyFactPresence::of(func);
    let mut global_facts =
        if p.has_min_max_call { build_min_max_facts(func) } else { Vec::new() };
    if p.has_len_call {
        global_facts.extend(build_len_call_bound_facts(func));
        // W4 STR-OFFSET (2026-09-25): `s.len()` on a `&str` is a CALL; tie its
        // result to `s`'s length metadata. See `str_offset`.
        global_facts.extend(build_str_len_call_tie_facts(func));
    }
    if p.has_checked_sub && p.has_field0_readback {
        global_facts.extend(build_checked_sub_result_facts(func));
    }
    if p.has_checked_add && p.has_field0_readback {
        global_facts.extend(build_checked_add_result_facts(func));
    }
    if p.has_abs_call {
        global_facts.extend(build_fp_abs_facts(func));
        global_facts.extend(build_int_abs_facts(func));
    }
    if p.has_rem {
        global_facts.extend(build_modulo_bound_facts(func));
    }
    if (p.has_narrow_uint_local && p.has_additive_rvalue)
        || p.has_checked_add
        || (p.has_checked_mul_any && p.has_additive_rvalue)
    {
        global_facts.extend(build_additive_bound_facts(func));
    }
    if p.has_div {
        global_facts.extend(build_division_lt_facts(func));
        global_facts.extend(build_division_exact_facts(func));
    }
    if p.has_bitand {
        global_facts.extend(build_bitmask_bound_facts(func));
    }
    if p.has_intrinsic_bound_call {
        global_facts.extend(build_intrinsic_bound_facts(func));
    }
    if p.has_nonzero_get_call {
        global_facts.extend(build_nonzero_get_dest_facts(func));
    }
    if p.has_checked_add && p.has_checked_mul_any {
        global_facts.extend(build_flattened_index_facts(func));
    }
    if p.has_cast {
        global_facts.extend(build_cast_bound_facts(func));
        global_facts.extend(build_cast_lower_bound_facts(func));
    }
    if p.has_checked_sub && p.has_field0_readback {
        global_facts.extend(build_downward_induction_facts(func));
        // Trust (countdown-loop piece): the bounded-countdown-loop trip facts (the
        // itoa family) — division-derived trip bounds on downward-var decrements —
        // plus the B0 infallible const-conversion value pins they resolve through.
        global_facts.extend(build_countdown_trip_facts(func));
    }
    if p.has_expect_call {
        global_facts.extend(build_expect_const_facts(func));
    }
    if p.has_checked_add {
        global_facts.extend(build_accumulator_bound_facts(func));
    }
    // `min(a, c) <= c` holds everywhere, so it is a global fact like the
    // accumulator bound beside it. Measured 2026-09-19: without it
    // `(0..n.min(8) as u32).collect()` is `[unbounded_allocation] FAILED` with a
    // counterexample of 33554432, because the allocation lane reconstructs the
    // element count from a range end that is a `min` CALL DESTINATION.
    if p.has_min_call {
        global_facts.extend(super::loop_bounds::build_min_upper_bound_facts(func));
    }
    // A same-crate callee's whole-crate return summary (const set / bounds) is a
    // fact about a local whose ONLY value is that call's result, at every program
    // point — so it must reach a loop body the call-site PATH fact never reaches.
    // Measured 2026-09-23: bit-vec 0.9.1's `reverse_bits` (`for i in
    // 0..u8::bits()`, `bits() == 8`) was refuted with `bits() == 9`.
    if p.has_bare_dest_call {
        global_facts.extend(super::callee_summaries::build_callee_return_summary_facts(func));
    }
    if p.bare_discr_count >= 2 {
        global_facts.extend(build_discriminant_cse_facts(func));
    }
    if p.bare_discr_count >= 1 {
        global_facts.extend(crate::enum_entry::global_discriminant_facts(func));
    }
    // A primitive-integer `Ord::cmp` result (extracted as the total-call sentinel) is
    // the integer order of its operands — the `Equal` a derived `Ord::cmp` branches
    // on. Measured 2026-09-25: regex-syntax 0.8.10's derived `Utf8Sequence::cmp` was
    // refuted at its `_ => unreachable` arm with the operands unequal under `Equal`.
    if p.has_total_clone_sentinel_call && p.bare_discr_count >= 1 {
        global_facts.extend(build_primitive_int_cmp_facts(func));
    }
    if p.discr_count >= 1 {
        global_facts.extend(build_discriminant_variant_range_facts(func));
    }
    if p.entry_has_switch {
        global_facts.extend(build_coroutine_resume_state_facts(func));
    }
    if p.std_scalar_index_calls >= 2 {
        global_facts.extend(build_immutable_index_len_tie_facts(func));
    }
    let congruence_start = global_facts.len();
    if p.projected_copy_reads >= 2 {
        global_facts.extend(build_element_read_congruence_facts(func));
    }
    let congruence_end = global_facts.len();
    if p.std_scalar_index_calls >= 2 {
        global_facts.extend(build_vec_index_dest_value_tie_facts(func));
    }
    if p.has_const_param {
        global_facts.extend(build_const_param_range_facts(func));
    }
    if p.has_bare_dest_call && p.has_ref_seq_param {
        global_facts.extend(build_invariant_vec_len_tie_facts(func));
    }
    (global_facts, congruence_start..congruence_end)
}

/// Trust (2026-09-29): `_len == coll_len(v)` as a GLOBAL fact for every `v.len()` whose
/// `Vec` receiver's length is INVARIANT for the whole body.
///
/// THE REFUSAL THIS CLOSES. `for i in 0..v.len() { v[i] = 0 }` over `v: &mut Vec<u32>`
/// (and `let n = v.len(); for i in 0..n { .. }`, and reads through `v[i]`) was refuted
/// with `v = 0` on the ordinary-Rust sweep (c59, c59g, c59h, c87, f05). The tie
/// `_len == coll_len(v)` is a PATH definition (`slice_last_some_nonempty_definitions`),
/// and every call with a `&mut` argument and every opaque store havocs every
/// mutable-pointer local's name — including `v`, which is also the `Vec`'s length
/// name (`guards::coll_len_var`). So the `index_mut(v, i)` call and the `*elem = 0`
/// store in the loop body killed the tie on the first iteration, and the loop header
/// dropped it, although neither can change the length.
///
/// WHY A GLOBAL FACT IS SOUND HERE. A global fact is conjoined before renaming and
/// renamed with the formula at its use point, so it asserts `_len == v#k` for whatever
/// version `v#k` the fabric gives the length there. That is true at every point exactly
/// when the length never changes, which [`vec_length_is_invariant`] establishes
/// syntactically: the receiver is a never-reassigned `&Vec`/`&mut Vec` PARAMETER, no
/// other parameter can reach any `Vec` (so no aliasing premise is needed), and
/// every mention of it — directly or through a single-assignment reborrow `&(*v)` /
/// `&mut (*v)` — is the receiver of a std `len`, `Index::index`, `IndexMut::index_mut`,
/// `Deref::deref` or `DerefMut::deref_mut`. None of those resizes, and what they return
/// (a length, an element reference, a slice) cannot resize a `Vec` either. Anything
/// else — `push`, `clear`, `truncate`, a user function, `mem::swap`, a closure capture,
/// a raw pointer, a whole store to `*v` — leaves the fact out, and the path tie keeps its
/// kill discipline. `_len` must hold one value for the whole body.
fn build_invariant_vec_len_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    let mut invariant: FxHashMap<usize, bool> = FxHashMap::default();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty()
            || args.len() != 1
            || !trust_types::total_call_summaries::total_summary_len_call(callee)
        {
            continue;
        }
        let Some(Operand::Copy(recv) | Operand::Move(recv)) = args.first() else { continue };
        if !recv.projections.is_empty() {
            continue;
        }
        let Some(base) = crate::guards::base_collection_place_unique(func, recv.local) else {
            continue;
        };
        if !base.projections.is_empty() {
            continue;
        }
        // (2026-10-09) or invariant up to a sole, last resize: every `.len()` then
        // runs before it (`vec_sole_mutator_block`).
        if !*invariant.entry(base.local).or_insert_with(|| {
            vec_length_is_invariant(func, base.local)
                || vec_sole_mutator_block(func, base.local).is_some()
        }) || !crate::local_defs::is_single_static_assignment(func, dest.local)
        {
            continue;
        }
        facts.push(Formula::Eq(
            Box::new(Formula::Var(crate::place_to_var_name(func, dest), Sort::Int)),
            Box::new(crate::guards::coll_len_var(func, base.local)),
        ));
    }
    facts
}

/// Is the length of the `Vec` behind PARAMETER `base` (`&Vec<T>` / `&mut Vec<T>`) the
/// same at every point of the body? See [`build_invariant_vec_len_tie_facts`]. Every
/// mention of `base` is counted with the exhaustive place walk and must be an
/// accounted-for benign use; an unrecognized shape answers `false`.
pub(super) fn vec_length_is_invariant(func: &VerifiableFunction, base: usize) -> bool {
    if !crate::local_defs::is_parameter(func, base)
        || !crate::local_defs::is_single_static_assignment(func, base)
        || !matches!(
            crate::local_ty_ref(func, base),
            Some(Ty::Ref { inner, .. }) if matches!(inner.as_ref(), Ty::Seq { .. })
        )
    {
        return false;
    }
    // NO OTHER CHANNEL TO THE SAME VECTOR. The mention count below sees only this
    // parameter. Another parameter that could reach the same `Vec` — a second
    // `&mut Vec`, a raw pointer, a `&RefCell`, a struct holding one — could change its
    // length without mentioning `base`, and trusting that two such arguments do not
    // alias is the premise `docs/DECISION_QUEUE.md` D15 leaves OPEN. So every other
    // parameter must be a plain value, or a shared reference to plain values (which
    // cannot write anything), and the body must launder no address through a raw
    // pointer. `copy`-only scalar and slice-reading helpers keep the fact.
    // (D15 is D96 since the 2026-10-14 merge, decided "adopted, disclosed and demoted"
    // through `NOALIAS_MUT_ARGS`; this fact is not graded under it, so it keeps the
    // refusal. The test is shared with the `Vec` region, D101.)
    if !super::param_is_sole_channel_to_its_pointee(func, base) {
        return false;
    }
    let num_locals = func.body.locals.len();
    let mut benign_receivers = vec![0usize; num_locals];
    let mut mentions = vec![0usize; num_locals];
    let mut reborrows: Vec<usize> = Vec::new();
    let mut record = |p: &Place| {
        if let Some(slot) = mentions.get_mut(p.local) {
            *slot += 1;
        }
    };
    for b in &func.body.blocks {
        for s in &b.stmts {
            if let Statement::Assign { place: t, rvalue: Rvalue::Ref { place: p, .. }, .. } = s
                && p.local == base
            {
                if !t.projections.is_empty()
                    || p.projections.as_slice() != [trust_types::Projection::Deref]
                    || !crate::local_defs::is_single_static_assignment(func, t.local)
                {
                    return false;
                }
                reborrows.push(t.local);
            }
            super::for_each_stmt_copy_move_place(s, &mut record);
        }
        super::for_each_terminator_copy_move_place(&b.terminator, &mut record);
        if let Terminator::Call { func: callee, args, .. } = &b.terminator
            && let Some(Operand::Copy(p) | Operand::Move(p)) = args.first()
            && p.projections.is_empty()
            && p.local < num_locals
            && vec_length_benign_callee(callee)
            && benign_index_argument(func, callee, args)
        {
            benign_receivers[p.local] += 1;
        }
    }
    // Single-assignment reborrows `t = &(*base)` / `&mut (*base)`, each of whose other
    // mentions is the receiver of a benign call.
    let mut accounted = benign_receivers.get(base).copied().unwrap_or(0);
    for t_local in reborrows {
        if mentions.get(t_local).copied().unwrap_or(0)
            != 1 + benign_receivers.get(t_local).copied().unwrap_or(0)
        {
            return false;
        }
        accounted += 1;
    }
    mentions.get(base).copied().unwrap_or(0) == accounted
}

/// Trust (2026-10-09, sweep c05): the block of the ONE resizing call
/// (std's own `Vec::remove`/`swap_remove`/`insert`, by exact path) made through a
/// `&mut Vec` PARAMETER `base`, when everything [`vec_length_is_invariant`] requires
/// holds for every OTHER use of `base`, and
/// no use of `base` — that call included — is reachable from the call's
/// successors. Every use then executes BEFORE the resize on every path, when the
/// length is still the entry length, so each `.len()` there equals `coll_len(v)`
/// and the call's own index precondition is a real `i < coll_len(v)` (`<=` for
/// `insert`). The documented false-accept of the old fail-honest row
/// (`let n = v.len(); v.remove(0); v.remove(n - 1)`) has TWO resizes and is
/// refused, and so is any resize inside a loop.
pub(super) fn vec_sole_mutator_block(func: &VerifiableFunction, base: usize) -> Option<BlockId> {
    let decline = |why: &str| -> Option<BlockId> {
        static VEC_SOLE_TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        if *VEC_SOLE_TRACE
            .get_or_init(|| crate::trust_vcgen_env_var_present("TRUST_VEC_SOLE_TRACE"))
        {
            eprintln!("[VEC_SOLE] fn={} base=_{base} DECLINE {why}", func.def_path);
        }
        None
    };
    // A cheap pre-gate, and only on what the stripped body below cannot change: the
    // parameter set and the declared types. Trust: 2026-11-09
    // (VCGEN-SEAM-PERF-REDS-1) — PERF-464 also asked
    // `is_single_static_assignment(func, base)` here, of the ORIGINAL body, where the
    // receiver's own reborrow `t = &mut (*base)` is a mutable alias of `base`; that
    // refused every reborrow receiver (`vec_panic_freedom::
    // a_reborrow_receiver_must_have_no_other_use`). The single-assignment question
    // is `vec_length_is_invariant`'s, asked below of the body with that reborrow and
    // the mutator removed, after the reborrow is shown to be used only as the receiver.
    if !crate::local_defs::is_parameter(func, base)
        || !matches!(
            crate::local_ty_ref(func, base),
            Some(Ty::Ref { inner, .. }) if matches!(inner.as_ref(), Ty::Seq { .. })
        )
    {
        return decline("parameter is not a &Vec / &mut Vec");
    }
    if !super::terminator_presence_for(func).has_vec_sole_resize_call {
        return decline("no resize call");
    }
    // std's own inherent methods only, by the exact generic-stripped path (review
    // round 98: a substring test admitted a user `<Vec<u32> as Ext>::remove` and a
    // user `crate::vec::Vec::remove`).
    let is_mutator = |callee: &str| {
        (callee.starts_with("alloc::vec::") || callee.starts_with("std::vec::"))
            && (callee.contains("::remove")
                || callee.contains("::swap_remove")
                || callee.contains("::insert"))
            && !trust_types::path_has_unauthenticated_crate_stamp(callee)
            && matches!(
                trust_types::strip_generics(callee).as_str(),
                "alloc::vec::Vec::remove"
                    | "std::vec::Vec::remove"
                    | "alloc::vec::Vec::swap_remove"
                    | "std::vec::Vec::swap_remove"
                    | "alloc::vec::Vec::insert"
                    | "std::vec::Vec::insert"
            )
    };
    // The one reborrow `t = &mut (*base)` whose only other mention is the
    // receiver of one mutator call.
    let mut found: Option<(usize, BlockId)> = None;
    for b in &func.body.blocks {
        let Terminator::Call { func: callee, args, .. } = &b.terminator else { continue };
        if !is_mutator(callee) {
            continue;
        }
        let Some(Operand::Copy(p) | Operand::Move(p)) = args.first() else { continue };
        if !p.projections.is_empty() {
            continue;
        }
        // The receiver is `base` itself (`copy _1`) or a reborrow of it.
        let reaches_base = p.local == base
            || crate::guards::base_collection_place_unique(func, p.local)
                .is_some_and(|root| root.local == base && root.projections.is_empty());
        if !reaches_base {
            continue;
        }
        if found.is_some() {
            return decline("a second resize");
        }
        found = Some((p.local, b.id));
    }
    let Some((temp, mutator_block)) = found else { return decline("no resize call") };
    // A reborrow receiver must be `t = &mut (*base)`, single-assigned, mentioned
    // only there and as that receiver.
    let temp_def_ok = crate::local_defs::is_single_static_assignment(func, temp)
        && (temp == base
            || matches!(
                crate::local_defs::unique_value_def(func, temp),
                Some(Rvalue::Ref { place: src, .. })
                    if src.local == base
                        && src.projections.as_slice() == [trust_types::Projection::Deref]
            ));
    if !temp_def_ok {
        return decline("the receiver is not a single reborrow of the parameter");
    }
    let direct = temp == base;
    // (review round 95) ...and the reborrow is used ONLY as that receiver: a second
    // use (`truncate(copy _t)`) would resize through `_t` while every check below
    // looks only at `base`.
    if !direct {
        let mut uses = 0usize;
        let mut borrowed = false;
        for b in &func.body.blocks {
            for s in &b.stmts {
                if let Statement::Assign {
                    rvalue: Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place),
                    ..
                } = s
                    && place.local == temp
                {
                    borrowed = true;
                }
                super::for_each_stmt_copy_move_place(s, &mut |p: &Place| {
                    if p.local == temp {
                        uses += 1;
                    }
                });
            }
            super::for_each_terminator_copy_move_place(&b.terminator, &mut |p: &Place| {
                if p.local == temp {
                    uses += 1;
                }
            });
        }
        // The place walk also visits the defining assignment's destination, so the
        // definition plus the receiver are exactly two mentions.
        if borrowed || uses != 2 {
            return decline("the reborrow has a use besides the receiver");
        }
    }
    // Every OTHER use of `base` satisfies the invariant discipline: check it on a
    // copy of the body with the mutator's reborrow statement removed and the
    // mutator call replaced by `Goto` (so neither is counted as a use).
    let mut stripped = func.clone();
    for b in &mut stripped.body.blocks {
        if !direct {
            b.stmts
                .retain(|s| !matches!(s, Statement::Assign { place, .. } if place.local == temp));
        }
        if b.id == mutator_block {
            if let Terminator::Call { target: Some(t), .. } = &b.terminator {
                b.terminator = Terminator::Goto(*t);
            } else {
                return None;
            }
        }
    }
    if !vec_length_is_invariant(&stripped, base) {
        return decline("another use of the vector is not a benign length/index read");
    }
    // No use of `base` (nor the mutator itself) is reachable from the mutator's
    // successors.
    let mentions_block = |b: &trust_types::BasicBlock| {
        let borrowed = b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign {
                rvalue: Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place), ..
            } if place.local == base)
        });
        let mut hit = false;
        let mut record = |p: &Place| {
            if p.local == base {
                hit = true;
            }
        };
        for s in &b.stmts {
            super::for_each_stmt_copy_move_place(s, &mut record);
        }
        super::for_each_terminator_copy_move_place(&b.terminator, &mut record);
        hit || borrowed || b.id == mutator_block
    };
    // Normal successors; an unrecognized terminator answers `false` (fail closed).
    // Unwind edges are not followed: a cleanup path runs only after a panic.
    let push_successors = |t: &Terminator, out: &mut Vec<BlockId>| -> bool {
        match t {
            Terminator::Goto(target)
            | Terminator::Assert { target, .. }
            | Terminator::Drop { target, .. } => out.push(*target),
            Terminator::Call { target, .. } => out.extend(target.iter().copied()),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                out.extend(targets.iter().map(|(_, b)| *b));
                out.push(*otherwise);
            }
            Terminator::Return | Terminator::Unreachable | Terminator::Resume => {}
            _ => return false,
        }
        true
    };
    let block_of = |id: BlockId| {
        func.body
            .blocks
            .get(id.0)
            .filter(|b| b.id == id)
            .or_else(|| func.body.blocks.iter().find(|b| b.id == id))
    };
    let mut seen: FxHashSet<BlockId> = FxHashSet::default();
    let mut stack: Vec<BlockId> = Vec::new();
    if !push_successors(&block_of(mutator_block)?.terminator, &mut stack) {
        return None;
    }
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let b = block_of(id)?;
        if mentions_block(b) {
            return decline("a use of the vector is reachable after the resize");
        }
        if !push_successors(&b.terminator, &mut stack) {
            return None;
        }
    }
    Some(mutator_block)
}

/// (2026-10-10, review round 96) An `Index::index` / `IndexMut::index_mut` call is
/// std's own only when its index is `usize` or a std range: `Vec<T>: IndexMut<K>` for
/// a LOCAL `K` is an orphan-legal user impl whose body can resize the vector, and a
/// generic `I` may resolve to one. Any other method passes.
fn benign_index_argument(func: &VerifiableFunction, callee: &str, args: &[Operand]) -> bool {
    if !matches!(method_tail(callee), "index" | "index_mut") {
        return true;
    }
    let Some(index) = args.get(1) else { return false };
    match crate::operand_ty_cow(func, index).as_deref() {
        // `usize` (no user `Index<usize>` impl for `Vec` is orphan-legal).
        Some(ty) if *ty == Ty::usize() => true,
        Some(Ty::PtrSizedInt { signed: false }) => true,
        Some(Ty::Adt { name, .. }) => {
            let base = name.split('<').next().unwrap_or(name);
            let (path, tail) = base.rsplit_once("::").unwrap_or(("", base));
            matches!(path, "core::ops::range" | "core::ops" | "std::ops" | "std::ops::range")
                && matches!(
                    tail,
                    "Range"
                        | "RangeTo"
                        | "RangeFrom"
                        | "RangeInclusive"
                        | "RangeToInclusive"
                        | "RangeFull"
                )
        }
        _ => false,
    }
}

/// A std call that cannot change the length of the `Vec` its receiver points at, and
/// whose result cannot either: `len`, `Index::index`, `IndexMut::index_mut`,
/// `Deref::deref`, `DerefMut::deref_mut`; an unauthenticated crate stamp refuses.
///
/// (2026-10-10, review round 97, a certified false row) The trait methods are matched
/// STRUCTURALLY, never by prefix: either the qualified `<Self as Trait>::method`, whose
/// top-level `Self` is exactly std's `Vec` and whose `Trait` is exactly std's
/// `Index`/`IndexMut`/`Deref`/`DerefMut` with the method that trait declares, or the
/// unqualified std trait method path itself. The prefix test it replaces admitted a
/// user trait's associated fn whose `Self` was a std ops type
/// (`<core::ops::Range<usize> as Evil>::index(v, 0)`, whose body cleared `v`) or whose
/// generic arguments named one (`<Vec<u32> as My<<T as core::ops::Deref>::Target>>`).
fn vec_length_benign_callee(callee: &str) -> bool {
    if trust_types::path_has_unauthenticated_crate_stamp(callee) {
        return false;
    }
    if trust_types::total_call_summaries::total_summary_len_call(callee) {
        return true;
    }
    let trait_for = |trait_path: &str| -> Option<&'static str> {
        Some(match trait_path {
            "core::ops::index::Index"
            | "core::ops::Index"
            | "std::ops::index::Index"
            | "std::ops::Index" => "index",
            "core::ops::index::IndexMut"
            | "core::ops::IndexMut"
            | "std::ops::index::IndexMut"
            | "std::ops::IndexMut" => "index_mut",
            "core::ops::deref::Deref"
            | "core::ops::Deref"
            | "std::ops::deref::Deref"
            | "std::ops::Deref" => "deref",
            "core::ops::deref::DerefMut"
            | "core::ops::DerefMut"
            | "std::ops::deref::DerefMut"
            | "std::ops::DerefMut" => "deref_mut",
            _ => return None,
        })
    };
    if let Some((self_ty, trait_path, method)) = split_top_level_qualified(callee) {
        let self_base = trust_types::strip_generics(self_ty);
        return matches!(self_base.as_str(), "alloc::vec::Vec" | "std::vec::Vec")
            && trait_for(&trust_types::strip_generics(trait_path)) == Some(method);
    }
    let plain = trust_types::strip_generics(callee);
    let Some((trait_path, method)) = plain.rsplit_once("::") else { return false };
    trait_for(trait_path) == Some(method)
}

/// Split `<Self as Trait>::method` at its TOP level: the ` as ` must sit at angle
/// depth 1 of the leading header (exactly once), and the item after the header's
/// closing `>::` must be a bare identifier. `None` for every other shape, so a ` as `
/// nested in a generic argument never splits.
fn split_top_level_qualified(callee: &str) -> Option<(&str, &str, &str)> {
    if !callee.starts_with('<') {
        return None;
    }
    let bytes = callee.as_bytes();
    let mut depth = 0usize;
    let mut as_at = None;
    let mut close = None;
    for (i, &c) in bytes.iter().enumerate() {
        match c {
            b'<' => depth += 1,
            // The `>` of a fn-pointer arrow (`fn() -> u8`) closes nothing.
            b'>' if i > 0 && bytes[i - 1] == b'-' => {}
            b'>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    close = Some(i);
                    break;
                }
            }
            b' ' if depth == 1 && callee[i..].starts_with(" as ") => {
                if as_at.replace(i).is_some() {
                    return None;
                }
            }
            _ => {}
        }
    }
    let (as_at, close) = (as_at?, close?);
    let method = callee.get(close + 1..)?.strip_prefix("::")?;
    if method.is_empty() || !method.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
        return None;
    }
    Some((callee.get(1..as_at)?, callee.get(as_at + 4..close)?, method))
}

// One static definition may run repeatedly in a loop. Trace the SELECTION VALUE
// through stable whole-local copies to an immutable input or literal instead of
// treating that definition count as a body-constant value. Computed/call values,
// projected copies, escapes, ambiguity and cycles decline; no callee name grants
// constancy. This is deliberately narrower than a flow-sensitive value theorem.
fn index_selection_is_body_constant(func: &VerifiableFunction, operand: &Operand) -> bool {
    let mut operand = operand;
    let mut seen = FxHashSet::default();
    for _ in 0..32 {
        if !operand_is_scalar_usize_index(func, operand) {
            return false;
        }
        match operand {
            Operand::Constant(_) => return true,
            Operand::Copy(index) | Operand::Move(index) if index.projections.is_empty() => {
                if !seen.insert(index.local)
                    || !crate::local_defs::is_single_static_assignment(func, index.local)
                {
                    return false;
                }
                if crate::local_defs::is_parameter(func, index.local) {
                    return true;
                }
                match crate::local_defs::unique_value_def(func, index.local) {
                    Some(Rvalue::Use(source)) => operand = source,
                    _ => return false,
                }
            }
            _ => return false,
        }
    }
    false
}

/// Trust (Vec `Index::index` CALL-DEST deref value tie — the owned-container twin of
/// [`build_element_read_congruence_facts`]): on a `&Vec` the element read is NOT a
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
/// This is a SAME-POINT heap equality, not an equality of saved element values.
/// The existing std-index and root gates identify the backing location. They do
/// not establish that its contents survive a call: a shared `&Vec` protects the
/// header, while a callee can write the buffer through a stashed raw pointer.
/// `path_defs::stored_ref_pointee_names` therefore versions each indexed
/// result's contents at EVERY call/drop/opaque effect and opaque pointer store,
/// including calls with no arguments. A read saved before an effect belongs to
/// its old content version and cannot use this equality with a fresh read.
/// There is no purity/totality or rendered-name frame exception.
///
/// The root is never reseated; result references each have one definition; the
/// scalar index operands each hold one stable value. Thus the compared index
/// expressions still denote the values that selected the returned locations.
/// A reassigned, escaped or projected index cannot make a global historical
/// selection fact. The fact equates DEREF contents, not pointer or length names.
/// Same-epoch reads of two acquired references retain their equality.
///
/// GAP, recorded (IDX-TIE-1): the extractor carries a real `Vec<T>` as `Ty::Seq`,
/// which the root gate does not accept, so the `Vec` arm is reached only by a
/// `Ty::Adt` std `Vec` (synthetic fixtures). Admitting `Ty::Seq` is a separate,
/// measured capability change; until then a `&Vec` value tie is not emitted.
pub(super) fn build_vec_index_dest_value_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    if !super::terminator_presence_for(func).has_std_scalar_index_call {
        return Vec::new();
    }
    // root local -> [(dest local, index operand)]
    let mut groups: BTreeMap<usize, Vec<(usize, Operand)>> = BTreeMap::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        // Trust (IDX-TIE-1, 2026-10-03): std's OWN `Index<usize>` on a slice, array or
        // `Vec`, never any method that happens to be named `index`. A user trait method
        // `index` on `[u32]`, or a user `impl Index<LocalKey> for [u32]`, returns
        // whatever its body returns, and the tie below would have equated two reads
        // that differ (measured: certify accepted, overflow check removed).
        if !dest.projections.is_empty()
            || args.len() != 2
            || !super::unwrap_panic::is_std_scalar_index_call(callee)
        {
            continue;
        }
        let (Operand::Copy(bp) | Operand::Move(bp)) = &args[0] else { continue };
        if !bp.projections.is_empty() {
            continue;
        }
        let Some(root) = guards::base_collection_local_unique(func, bp.local) else { continue };
        // Trust (IDX-TIE-1, 2026-10-03): the `Adt` arm names std's `Vec` by its exact
        // path. It read `is_owned_slice_container_name` (last segment `Vec`), which a
        // user type named `Vec` passes; such a type reaches std's `Vec` index through
        // its OWN `Deref`, which need not return the same `Vec` twice, so an anchored
        // callee alone did not make the tie true (measured: a `struct Vec` wrapper
        // whose `deref` alternates two fields was accepted with the overflow check
        // removed). The producer stamps a `Ty::Adt` name whose crate impersonates
        // `alloc`/`std`, so the path is std's. The primitive arms need no anchor.
        let root_ok = matches!(
            crate::local_ty_ref(func, root),
            Some(Ty::Ref { mutable: false, inner })
                if matches!(&**inner, Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. })
                    || matches!(&**inner, Ty::Adt { name, .. }
                        if super::unwrap_panic::is_std_vec_adt_name(name))
        );
        if !root_ok
            || !root_is_never_reseated(func, root)
            || !crate::local_defs::has_one_explicit_def(func, dest.local)
            || !operand_is_scalar_usize_index(func, &args[1])
            || !index_selection_is_body_constant(func, &args[1])
        {
            continue;
        }
        groups.entry(root).or_default().push((dest.local, args[1].clone()));
    }
    if groups.is_empty() {
        return Vec::new();
    }
    let mut facts = Vec::new();
    let mut deref_op = Operand::Copy(Place {
        local: 0,
        projections: vec![trust_types::Projection::Deref],
    });
    for (_, mut calls) in groups {
        // Bound the pairwise blowup (groups are tiny in practice).
        calls.truncate(6);
        if calls.len() < 2 {
            continue;
        }
        let lowered: Vec<(Formula, Formula)> = calls
            .iter()
            .map(|(d, idx)| {
                if let Operand::Copy(p) = &mut deref_op {
                    p.local = *d;
                }
                (operand_to_formula(func, &deref_op), operand_to_formula(func, idx))
            })
            .collect();
        for i in 0..lowered.len().saturating_sub(1) {
            let (read_a, idx_a) = &lowered[i];
            for (read_b, idx_b) in &lowered[(i + 1)..] {
                if read_a == read_b {
                    continue; // same var already — nothing to tie
                }
                let eq = Formula::Eq(Box::new(read_a.clone()), Box::new(read_b.clone()));
                facts.push(if idx_a != idx_b {
                    Formula::Or(vec![
                        Formula::Not(Box::new(Formula::Eq(
                            Box::new(idx_a.clone()),
                            Box::new(idx_b.clone()),
                        ))),
                        eq,
                    ])
                } else {
                    eq
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
    !crate::any_local_write_candidate(func, &func.body.blocks, local, |block, item| match item {
        Some(stmt) => matches!(
            stmt,
            Statement::Assign { place, .. }
            | Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place }
                if place.local == local
        ),
        None => matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local),
    })
}

pub(super) fn build_immutable_index_len_tie_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    if !super::terminator_presence_for(func).has_std_scalar_index_call {
        return Vec::new();
    }
    // (base_root_local, idx_is_const, idx_value_or_local) -> dest locals of matching calls.
    let mut groups: BTreeMap<(usize, bool, i128), Vec<usize>> = BTreeMap::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        // Trust (2026-10-04, IDX-TIE-1, second consumer): std's OWN scalar
        // `<S as Index<usize>>::index` on a slice, array or `Vec` — the value tie's
        // predicate. This read `slice_conversion::is_slice_index_call`, a method-name
        // test (`index`/`index_mut`), so two USER trait methods named `index` on one
        // `&Two` were tied: `if j < LoV::index(t, i).len() { HiV::index(t, i)[j] }`,
        // with `LoV` returning a long `Vec` and `HiV` an empty one, read `slice
        // proved` and the default and strict policies accepted a build that panics
        // (`tests/ui/trust/index_len_tie_requires_std_index.rs`). `index_mut` is
        // dropped with it: a `&mut` result is not a shared-ref read.
        if !dest.projections.is_empty()
            || args.len() != 2
            || !super::unwrap_panic::is_std_scalar_index_call(callee)
        {
            continue;
        }
        // STABLE index pre-check: a PURE immutable-input param (`p.local < arg_count`) or
        // a non-negative constant. Reject non-param locals before running collection
        // root tracing and `operand_is_scalar_usize_index`.
        let (idx_is_const, idx_val_or_local) = match &args[1] {
            Operand::Copy(p) | Operand::Move(p)
                if p.projections.is_empty() && p.local < func.body.arg_count =>
            {
                (false, p.local as i128)
            }
            Operand::Constant(ConstValue::Uint(v, _)) if *v <= i128::MAX as u128 => {
                (true, *v as i128)
            }
            Operand::Constant(ConstValue::Int(v)) if *v >= 0 => (true, *v),
            _ => continue,
        };
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
        // Trust (2026-10-04, IDX-TIE-1): the shared ref must point AT the container —
        // a slice, an array, the extractor's `Seq` (std's `Vec`), or std's `Vec` by
        // exact path. It accepted ANY shared ref, and the trace hops a std-trait
        // `Deref::deref` whatever its self type
        // (`guards::callee_is_length_preserving_deref`), so `w[i]` on a user
        // `W: Deref<Target = Vec<Vec<u32>>>` traced both reads to `w: &W` and tied
        // the two inner `Vec`s a `deref` that alternates fields returns. A std
        // callee does not make the tie true when the container is not std's.
        // (2026-10-04, DEREF-ANCHOR-1: the trace no longer hops a user `Deref` — it
        // takes std's own `Vec`/`String` `Deref` on a std receiver only — so that root
        // is no longer reachable this way; this gate stays as defense in depth.)
        let root_ok = matches!(
            crate::local_ty_ref(func, root),
            Some(Ty::Ref { mutable: false, inner })
                if matches!(
                    &**inner,
                    Ty::Slice { .. } | Ty::Array { .. } | Ty::SymArray { .. } | Ty::Seq { .. }
                ) || matches!(&**inner, Ty::Adt { name, .. }
                        if super::unwrap_panic::is_std_vec_adt_name(name))
        );
        if !root_ok || (!idx_is_const && !local_is_immutable_input_param(func, idx_val_or_local as usize)) {
            continue;
        }
        groups.entry((root, idx_is_const, idx_val_or_local)).or_default().push(dest.local);
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
/// def; a non-param must have exactly ONE whole-local def. STRICTER than
/// [`crate::local_defs::holds_one_value`], which is why the scan is kept: that
/// question counts VALUES, and a single CALL DEST or a projected store is a reseat
/// channel it admits and this rejects outright.
pub(super) fn root_is_never_reseated(func: &VerifiableFunction, root: usize) -> bool {
    let is_param = (1..=func.body.arg_count).contains(&root);
    let max_defs = if is_param { 0usize } else { 1usize };
    let mut defs = 0usize;
    let invalid =
        crate::any_local_write_candidate(func, &func.body.blocks, root, |block, item| match item {
            Some(stmt) => {
                if let Statement::Assign { place, rvalue, .. } = stmt {
                    if let Rvalue::Ref { mutable: true, place: b } | Rvalue::AddressOf(_, b) =
                        rvalue
                        && b.local == root
                    {
                        return true;
                    }
                    if place.local == root {
                        if place.projections.is_empty() {
                            defs += 1;
                            if defs > max_defs {
                                return true;
                            }
                        } else {
                            return true;
                        }
                    }
                }
                false
            }
            None => {
                matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == root)
            }
        });
    !invalid && defs == max_defs
}

/// Trust (element-read CONGRUENCE — the unified "read twice, diverge" gap; VGAPS-G1 of
/// the verifier-gaps design, trust-ir
/// `reports/2026-10-08-session-4b77663c/designs/trust-verifier-gaps-final.md` §2): two
/// syntactic reads of ONE element of ONE base — `if t < K && ps[i].x < K { t += ps[i].x }`,
/// the const-generic `a[i]` loop, `digits[i] -= 1` after `if digits[i] > 0` — are encoded
/// as INDEPENDENT SMT vars (`ps*[_10].0` vs `ps*[_13].0`): an element name keys on the
/// index LOCAL, and rustc mints a fresh index temp per read. So a guard on the first read
/// never constrained the second and the add/index obligation FALSE-REFUTED (the
/// counterexamples show the SAME index with two DIFFERENT element values). Emit the
/// McCarthy congruence for each pair of same-shape reads:
///
///   `Or( idx_a != idx_b  [one disjunct per Index position],  read_a == read_b )`
///
/// Index equality is a HYPOTHESIS the solver discharges (through the block-def layer,
/// e.g. `_10 = i`, `_13 = i` within one iteration) — never an assertion. Two reads at
/// genuinely different indices satisfy the disequality disjunct and force NO value tie.
///
/// WHY IT IS A THEOREM (the design's §2.2; no immutability claim). The rule is about ONE
/// program state Q: `idx_a@Q = idx_b@Q ⇒ read_a@Q = read_b@Q`. Two things make it hold:
///  * (I1) ONE BASE. The group key is the CANONICAL place
///    ([`crate::canonical_place`], the place `place_to_var_name` names a read by): its
///    local plus its projection shape with each `Index` blanked, and the disjuncts pair
///    the CANONICAL index locals (a fold through a reborrow can carry an `Index` of its
///    own). Two names in one group are the same root local and the same projections up
///    to index positions, so at Q every `Deref` on both paths reads the same pointer
///    value once the indices agree: the places are one location exactly when the
///    indices agree, for any root type. (A traced-root key would group DIFFERENT bases —
///    `r1*[..]` with `a*[..]` after `r1 = a; a = b` — and without a reseat gate it would
///    be a false-proof vector; `must_refute_copy_then_reseat` in
///    `tests/element_read_congruence_realmir.rs` is the row.)
///  * (I2) ONE POINT. Every name of the fact is rendered at one point. The fact is a
///    `build_global_invariant_facts` entry, and that set is conjoined at eight sites,
///    each classified by `tests/global_fact_sites_are_classified.rs`: at the ROW point,
///    before the row's version rename (`safety.rs`, `hardened.rs`), where every name
///    takes the version reaching the row; or BARE (`callsite.rs` twice,
///    `callsite_replay.rs`, `contract_vcs.rs`, `unwrap_panic.rs`, `alloc_vcs.rs`), where
///    an element name with no token is the entry/unwritten version
///    (`normalize_ssa_version_tokens` collapses only names that resolve to a WHOLE
///    local), so the fact is a theorem about the entry state and links only names with
///    entry values.
///
/// WHAT IT RELIES ON, NOT ADDS: the version/kill invariant — a fact reaching Q that
/// mentions `n#t`, with `t` the version Q gives `n`, denotes `n`'s value at Q. A write
/// between the two reads (a store, a `&mut` reborrow, a pointer write, a call) re-versions
/// the element names or kills the first read's definition, so the guard read's
/// definition and the congruence do not meet. Across a loop iteration with a conditional
/// store the reaching-set token COLLIDES, and what keeps those rows sound is the
/// path-definition KILL of the guard read's definition, not the token (the design's
/// residual 1; `must_refute_loop_elem_ref_collision` and its siblings are the rows the
/// G1-M7 mutant, which keeps that definition alive, turns PROVED). It also relies on the
/// "Pure-value arguments reach no caller local" TCB row's premise, as every other fact
/// does.
///
/// INTERIOR MUTABILITY is not closed here, and nothing here claims it is: `Copy` does not
/// close it (a `Copy` leaf INSIDE a cell is still the cell's bytes, `(*a)[_14].0.0` for
/// `a: &[Cell<usize>]`). What kills such a fact across a write to cell bytes is G2's write
/// channel (`path_defs::stored_ref_pointee_names`, INTERIOR-MUT-CHANNEL-1): every call
/// names the `UnsafeCell` bytes behind a shared reference, so the second read carries a
/// version the guard read's definition does not.
///
/// THE STATED EXCEPTION is the `Vec` call-destination twin,
/// [`build_vec_index_dest_value_tie_facts`]: its element reads are CALL RESULTS, not
/// places, so no name carries the state, and it keeps its traced root and
/// [`root_is_never_reseated`].
///
/// Facts are only CONJOINED (monotone): a true equality can flip a spurious REFUTE to
/// PROVE but cannot hide a real counterexample (which satisfies it too).
pub(super) fn build_element_read_congruence_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use std::collections::BTreeMap;
    // Group key: (canonical root local, canonical projection shape with each variable
    // `Index` blanked to its position). `(*ps)[_10].0` and `(*ps)[_13].0` share a key;
    // `.0` vs `.1`, or a different `ConstantIndex` offset, do not. Values: distinct
    // canonical places + their index locals, first-seen order.
    let mut groups: BTreeMap<(usize, String), Vec<(Place, Vec<usize>)>> = BTreeMap::new();

    fn consider(
        func: &VerifiableFunction,
        groups: &mut BTreeMap<(usize, String), Vec<(Place, Vec<usize>)>>,
        op: &Operand,
    ) {
        // `Copy` ONLY: a `Move` leaf is not a read the body can repeat.
        let Operand::Copy(place) = op else { return };
        // `canonical_place` only unfolds leading `Deref`s (`canonicalize_deref`) and
        // rebases onto `Downcast`+`Field` sources (`base_value_alias`), keeping non-leading
        // projections intact: a place that neither starts with `Deref` nor carries an
        // `Index` can never gain an `Index` under canonicalization, and any projection
        // outside `Deref`/`Field`/`Index`/`ConstantIndex` survives canonicalization and
        // bails the loop below. Reject both shapes before cloning/memoizing `place`.
        if (!matches!(place.projections.first(), Some(trust_types::Projection::Deref))
            && !place.projections.iter().any(|p| matches!(p, trust_types::Projection::Index(_))))
            || place.projections.iter().any(|p| {
                !matches!(
                    p,
                    trust_types::Projection::Deref
                        | trust_types::Projection::Field(_)
                        | trust_types::Projection::Index(_)
                        | trust_types::Projection::ConstantIndex { .. }
                )
            })
        {
            return;
        }
        let canon = crate::canonical_place(func, place);
        if !canon.projections.iter().any(|p| matches!(p, trust_types::Projection::Index(_))) {
            return;
        }
        let mut idx_locals = Vec::new();
        let mut shape = String::new();
        for proj in &canon.projections {
            match proj {
                trust_types::Projection::Deref => shape.push('*'),
                trust_types::Projection::Field(i) => {
                    use std::fmt::Write;
                    let _ = write!(shape, ".{i}");
                }
                trust_types::Projection::Index(l) => {
                    idx_locals.push(*l);
                    shape.push_str("[#]");
                }
                trust_types::Projection::ConstantIndex { offset, min_length, from_end } => {
                    use std::fmt::Write;
                    let _ = write!(shape, "[c{offset};{min_length};{from_end}]");
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
        let entry = groups.entry((canon.local, shape)).or_default();
        if !entry.iter().any(|(p, _)| *p == canon) {
            entry.push((canon, idx_locals));
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
        // More than six reads of one base may drop the needed pair: a false refutation,
        // never a false proof (the design's residual 3).
        reads.truncate(6);
        if reads.len() < 2 {
            continue;
        }
        let reads: Vec<(Formula, Vec<usize>)> = reads
            .into_iter()
            .map(|(p, idx)| (crate::place_to_formula(func, &p), idx))
            .collect();
        for i in 0..reads.len().saturating_sub(1) {
            let (read_a, ia) = &reads[i];
            for (read_b, ib) in &reads[(i + 1)..] {
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
                let eq = Formula::Eq(Box::new(read_a.clone()), Box::new(read_b.clone()));
                if disjuncts.is_empty() {
                    facts.push(eq);
                } else {
                    disjuncts.push(eq);
                    facts.push(Formula::Or(disjuncts));
                }
            }
        }
    }
    facts
}

/// Trust (2026-10-22; the per-row relevance filter of the verifier-gaps design's §2.5,
/// adopted "only on evidence", and the evidence is VGAPS-G2-FOLLOWUP (2)'s whole-corpus
/// parity sweep in docs/DECISION_QUEUE.md): the global invariant facts ONE row carries. Every fact
/// of [`build_global_invariant_facts`] except an element-read congruence
/// ([`build_element_read_congruence_facts`]) one of whose two reads is named neither by the
/// row, nor by any other global fact, nor by a conjunct the row can receive after its global
/// facts ([`late_conjunct_names`]).
///
/// THE EVIDENCE. G1 (`5600bf48aa`) conjoins every congruence of a body onto every row of
/// it. Over every fixture body, one correct row lost its proof to that, and no other did:
/// `argument_premise_clip`'s `[unreach]` row (aterm-gpu's `clip_textured_quad_x`), PROVED
/// and kernel-certified before G1 and Unknown from G1 on (bisected), whose formula is
/// `_9 ∉ {0, 1} ∧ _9 ∈ {0, 1}` beside six congruences over the `f32` reads `rect*[_]` and
/// `uv*[_]` that nothing else in the row names.
///
/// WHY NO VERDICT A FULL ROW REACHES CHANGES. Dropping a conjunct drops a hypothesis, so
/// the filtered row proves nothing the full row does not (sound by construction). It also
/// refutes nothing the full row proves, because the congruences of one base are PAIRWISE
/// (every pair of its at most six reads, [`build_element_read_congruence_facts`]): take a
/// model of the filtered row and give each read `w` it does not name the value of a read
/// it does name whose indices agree with `w`'s, or one common value per index class where
/// none does. The kept congruences make the named reads of one class agree, so every
/// dropped congruence holds and the full row has a model too. That needs `w` to occur in
/// NO conjunct of the finished row but the dropped congruences, including the conjuncts it
/// receives after this point: the safety and hardened lanes conjoin the preconditions, the
/// dominating path guards and the semantic guards after the global facts (the facts are
/// renamed with the body, the guards are not). A path guard on `switchInt(copy (*a)[_12])`
/// names `a*[_12]`, which no earlier conjunct of `match a[i] { 0 => 0, _ => a[i] - 1 }`'s
/// `Sub` row names; with only the row and the other facts counted, its congruence was
/// dropped and the correct row refuted (review of `95449037cd`,
/// `element_read_congruence_realmir::a_read_only_a_path_guard_names_keeps_its_congruence`).
/// So a read also counts as NAMED when [`late_conjunct_names`] has it. A read counts as
/// named in any SSA version (the name up to its first `#`): a row is filtered before its
/// version rename, and counting two versions as one only keeps more. A read that is not a
/// variable keeps its congruence. A read that only a later conjunct
/// [`late_conjunct_names`] does not foresee names loses the tie to it: a lost proof, never
/// a false one.
pub(crate) struct RowGlobalFacts {
    facts: Vec<Formula>,
    /// Per fact: the two reads' names (up to `#`) when it is an element-read congruence
    /// whose two reads are variables.
    congruence_reads: Vec<Option<(String, String)>>,
    /// Congruence read names not already mentioned by a non-congruence global fact or a
    /// whole-body late conjunct ([`resolve_remaining_late_conjunct_names`]). Any congruence
    /// read absent from this set is unconditionally named on every row; when empty,
    /// `for_row` returns `self.facts.clone()` without walking `row`.
    unresolved_congruence_reads: FxHashSet<String>,
}

impl RowGlobalFacts {
    /// Build [`build_global_invariant_facts_with_congruence_range`] for `func` once and
    /// recognise its element-read congruences directly from the slice where they were
    /// appended, avoiding a second `build_element_read_congruence_facts` pass.
    pub(crate) fn for_function(func: &VerifiableFunction) -> Self {
        let (facts, congruence_range) = build_global_invariant_facts_with_congruence_range(func);
        if facts.is_empty() || congruence_range.is_empty() {
            return RowGlobalFacts {
                facts,
                congruence_reads: Vec::new(),
                unresolved_congruence_reads: FxHashSet::default(),
            };
        }
        Self::from_congruence_slice(func, facts, congruence_range)
    }

    /// `facts` (the result of [`build_global_invariant_facts_with_congruence_range`] for
    /// `func`), with the congruences among them recognised once for every row of `func`.
    /// Test-only since PERF-COMPILER-VCGEN-72: every production site builds the set
    /// through [`RowGlobalFacts::for_function`]; the unit tests pin the filter over
    /// hand-made sets.
    #[cfg(test)]
    pub(crate) fn new(func: &VerifiableFunction, facts: Vec<Formula>) -> Self {
        if facts.is_empty()
            || !facts.iter().any(|f| matches!(f, Formula::Or(_) | Formula::Eq(..)))
        {
            return RowGlobalFacts {
                facts,
                congruence_reads: Vec::new(),
                unresolved_congruence_reads: FxHashSet::default(),
            };
        }
        let congruences = build_element_read_congruence_facts(func);
        if congruences.is_empty() {
            return RowGlobalFacts {
                facts,
                congruence_reads: Vec::new(),
                unresolved_congruence_reads: FxHashSet::default(),
            };
        }
        let congruence_reads: Vec<Option<(String, String)>> = facts
            .iter()
            .map(|f| if congruences.contains(f) { congruence_read_names(f) } else { None })
            .collect();
        Self::finish_with_congruence_reads(func, facts, congruence_reads)
    }

    fn from_congruence_slice(
        func: &VerifiableFunction,
        facts: Vec<Formula>,
        congruence_range: std::ops::Range<usize>,
    ) -> Self {
        let congruence_slice = &facts[congruence_range.clone()];
        let congruence_reads: Vec<Option<(String, String)>> = facts
            .iter()
            .enumerate()
            .map(|(idx, f)| {
                if congruence_range.contains(&idx) || congruence_slice.contains(f) {
                    congruence_read_names(f)
                } else {
                    None
                }
            })
            .collect();
        Self::finish_with_congruence_reads(func, facts, congruence_reads)
    }

    fn finish_with_congruence_reads(
        func: &VerifiableFunction,
        facts: Vec<Formula>,
        congruence_reads: Vec<Option<(String, String)>>,
    ) -> Self {
        let mut unresolved_congruence_reads = FxHashSet::default();
        for (a, b) in congruence_reads.iter().flatten() {
            unresolved_congruence_reads.insert(a.clone());
            unresolved_congruence_reads.insert(b.clone());
        }
        if !unresolved_congruence_reads.is_empty() {
            let strip_formula = |f: &Formula, unresolved: &mut FxHashSet<String>| {
                let _ = trust_types::any_free_variable_name(f, &mut |n| {
                    unresolved.remove(version_base(n));
                    unresolved.is_empty()
                });
            };
            for (fact, reads) in facts.iter().zip(&congruence_reads) {
                if reads.is_none() {
                    strip_formula(fact, &mut unresolved_congruence_reads);
                    if unresolved_congruence_reads.is_empty() {
                        break;
                    }
                }
            }
            if !unresolved_congruence_reads.is_empty() {
                for pre in &func.preconditions {
                    strip_formula(pre, &mut unresolved_congruence_reads);
                    if unresolved_congruence_reads.is_empty() {
                        break;
                    }
                }
            }
            if !unresolved_congruence_reads.is_empty() {
                resolve_remaining_late_conjunct_names(func, &mut unresolved_congruence_reads);
            }
        }
        RowGlobalFacts { facts, congruence_reads, unresolved_congruence_reads }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.facts.is_empty()
    }

    /// The facts `row` (its formula before the global facts are conjoined) carries.
    pub(crate) fn for_row(&self, row: &Formula) -> Vec<Formula> {
        if self.facts.is_empty() {
            return Vec::new();
        }
        if self.unresolved_congruence_reads.is_empty() {
            let mut out = Vec::with_capacity(self.facts.len() + 1);
            out.extend(self.facts.iter().cloned());
            return out;
        }
        let mut row_names: FxHashSet<&str> = FxHashSet::default();
        trust_types::for_each_free_variable_name(row, &mut |n| {
            let base = version_base(n);
            if self.unresolved_congruence_reads.contains(base) {
                row_names.insert(base);
            }
        });
        let named = |n: &str| !self.unresolved_congruence_reads.contains(n) || row_names.contains(n);
        let mut out = Vec::with_capacity(self.facts.len() + 1);
        for (fact, reads) in self.facts.iter().zip(&self.congruence_reads) {
            if reads.as_ref().is_none_or(|(a, b)| named(a) && named(b)) {
                out.push(fact.clone());
            }
        }
        out
    }
}

/// Remove from `unresolved` every name (up to `#`) a conjunct can bring to a row AFTER the
/// row's global facts over `func.body.blocks`: every arm of every `SwitchInt` and every
/// `Assert` as [`crate::guards::guard_to_formula`] spells it (the path guards and
/// assert-passed guards are those formulas, a `bool` temp's same-block definition inlined),
/// and every call argument (a proved callee's rebound `ensures`, a semantic guard, names its
/// actuals). (`func.preconditions` were already stripped before entering.) Stops immediately
/// once `unresolved` becomes empty and allocates no intermediate `FxHashSet<String>`.
fn resolve_remaining_late_conjunct_names(
    func: &VerifiableFunction,
    unresolved: &mut FxHashSet<String>,
) {
    let strip_formula = |f: &Formula, unresolved: &mut FxHashSet<String>| {
        let _ = trust_types::any_free_variable_name(f, &mut |n| {
            unresolved.remove(version_base(n));
            unresolved.is_empty()
        });
    };
    let strip_operand = |op: &Operand, unresolved: &mut FxHashSet<String>| match op {
        Operand::Copy(place) | Operand::Move(place) => {
            let name = crate::place_to_var_name(func, place);
            unresolved.remove(version_base(&name));
        }
        Operand::Constant(
            ConstValue::Bool(_)
            | ConstValue::Int(_)
            | ConstValue::Uint(..)
            | ConstValue::Float(_)
            | ConstValue::Unit,
        ) => {}
        _ => strip_formula(&operand_to_formula(func, op), unresolved),
    };
    for block in &func.body.blocks {
        match &block.terminator {
            Terminator::SwitchInt { discr, targets, .. } => {
                if targets.is_empty() {
                    continue;
                }
                let discr_ty = crate::operand_ty_cow(func, discr);
                if matches!(discr_ty.as_deref(), Some(Ty::Bool)) {
                    for truth_value in [false, true] {
                        strip_formula(
                            &crate::guards::bool_guard_formula(func, discr, truth_value),
                            unresolved,
                        );
                        if unresolved.is_empty() {
                            return;
                        }
                    }
                } else if discr_ty.as_deref().is_some_and(|ty| {
                    targets
                        .iter()
                        .any(|(value, _)| crate::switch_label_to_formula(ty, *value).is_some())
                }) {
                    strip_operand(discr, unresolved);
                }
            }
            Terminator::Assert { cond, .. } => {
                strip_operand(cond, unresolved);
            }
            Terminator::Call { args, .. } => {
                for arg in args {
                    strip_operand(arg, unresolved);
                    if unresolved.is_empty() {
                        return;
                    }
                }
            }
            _ => {}
        }
        if unresolved.is_empty() {
            return;
        }
    }
}

/// The two reads of an element-read congruence (`Or([.., Eq(read_a, read_b)])`, or the
/// bare `Eq` when no index disjunct remained), by name up to the version token, when both
/// are variables.
fn congruence_read_names(fact: &Formula) -> Option<(String, String)> {
    let eq = match fact {
        Formula::Or(disjuncts) => disjuncts.last()?,
        eq => eq,
    };
    let Formula::Eq(a, b) = eq else { return None };
    let name = |f: &Formula| match f {
        Formula::Var(name, _) => Some(version_base(name).to_owned()),
        Formula::SymVar(sym, _) => Some(version_base(sym.as_str()).to_owned()),
        _ => None,
    };
    Some((name(a)?, name(b)?))
}

/// A variable's name up to its SSA version token (`digits*[_9]#e_s2_0` -> `digits*[_9]`).
fn version_base(name: &str) -> &str {
    name.split('#').next().unwrap_or(name)
}

/// Trust (allocation-size bound for a `.len()` CALL result): a well-formed std `[T]`
/// slice with a provably NON-ZST element, or a `String`, can never hold more than
/// `isize::MAX` elements/bytes — every slice/allocation is capped at `isize::MAX`
/// BYTES and `size_of::<elem>() >= 1` forces `len <= isize::MAX` — so `<c>.len()`
/// returns a value in `[0, isize::MAX]`. `.len()` lowers to a Call whose dest is a
/// FRESH `usize` temp, DISTINCT from the `__slice_len` symbols
/// `conjoin_slice_len_bounds` bounds, so `a.len() + b.len()` reads both results as
/// free `usize` and FALSE-REFUTES the add-overflow. Emit the bound as a GLOBAL fact on
/// the single-static-assignment len dest — the same lane and SSA gate as
/// [`build_min_max_facts`].
///
/// SOUNDNESS: `0 <= len <= isize::MAX` is the unconditional allocation-size invariant
/// of a well-formed slice/String; a conjoined true fact only turns a false-FAIL into a
/// PROVE, never an overflow into a false-PROVE. Gated to:
///  * the CRATE-ANCHORED std `len` (`core/std::slice::` receiver-tail `len`, or
///    `alloc/std::string::String::len`) — an extension-trait `fn len` has a DIFFERENT
///    callee root and is excluded (a receiver-type check alone would be spoofable);
///  * a provably NON-ZST element whose type SURVIVES EXTRACTION FAITHFULLY: a `&[T]`
///    slice carries the real element in `Ty::Slice { elem }`, so a ZST element (`[()]`,
///    whose len may reach `usize::MAX`) is correctly excluded; `String`'s element is
///    DEFINITIONALLY `u8` (non-ZST, byte-length capped at `isize::MAX`). A `Vec<T>`
///    receiver is DELIBERATELY NOT accepted: the extractor ERASES the Vec buffer
///    element to `NonNull<u8>` (modern `RawVecInner`) AND the Vec `Ty::Adt` name
///    carries no turbofish, so `Vec<()>` is INDISTINGUISHABLE from `Vec<u8>` — bounding
///    it would be UNSOUND (a `Vec<()>` len can exceed `isize::MAX`). Recovering the
///    real Vec element is an extraction-side change, not a vcgen fact.
///  * a single-static-assignment dest (a reassigned/decremented len carrier would go
///    stale, exactly the `build_min_max_facts` SSA gate).
pub(super) fn build_len_call_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Call { func: callee, args, dest, .. } = &block.terminator else {
            continue;
        };
        if !dest.projections.is_empty() || args.len() != 1 {
            continue;
        }
        let anchored = callee.starts_with("core::slice::")
            || callee.starts_with("std::slice::")
            || callee.starts_with("alloc::string::")
            || callee.starts_with("std::string::");
        if !anchored
            || method_tail(callee) != "len"
            || !is_single_static_assignment(func, dest.local)
        {
            continue;
        }
        // Receiver element must be provably NON-ZST for `len <= isize::MAX` to hold,
        // AND its type must survive extraction faithfully. A `&[T]` slice carries the
        // real `elem`; `String` is definitionally `u8`. A `Vec` receiver is EXCLUDED
        // (buffer element erased to u8 -> `Vec<()>` unrecognizable) — see doc.
        let recv_ty = crate::operand_ty_cow(func, &args[0]);
        let inner = match recv_ty.as_deref() {
            Some(Ty::Ref { inner, .. }) => inner.as_ref(),
            Some(other) => other,
            None => continue,
        };
        let elem_non_zst = match inner {
            Ty::Slice { elem } => trust_types::alloc_model::ty_is_definitely_nonzero_sized(elem),
            Ty::Adt { name, .. } => {
                let base = name.split('<').next().unwrap_or(name);
                base == "std::string::String" || base == "alloc::string::String"
            }
            _ => false,
        };
        if !elem_non_zst {
            continue;
        }
        let dest_var = Formula::Var(crate::place_to_var_name(func, dest), Sort::Int);
        facts.push(Formula::Ge(Box::new(dest_var.clone()), Box::new(Formula::Int(0))));
        facts.push(Formula::Le(Box::new(dest_var), Box::new(Formula::Int(i64::MAX as i128))));
    }
    facts
}

/// Trust (2026-10-17, gate RCA precision T2): a `min`/`max` argument that is a
/// single-static-assignment LENGTH temp (`_7 = PtrMetadata(copy _8)`, `_t = Len(p)`),
/// named by the temp itself when [`stable_min_arg_formula`] declines its root.
///
/// The root's canonical length name is refused for a reseated slice (round A8: the
/// min lane licensed `s__slice_len` by `is_parameter` alone and proved `let n =
/// s.len().min(100); s = b; s[..n]`). The TEMP is not that name: it holds the length
/// read at its one definition, never written again (`is_single_static_assignment`: no
/// second write, no alias, no projected write), and `min(a, t) <= t` is a fact about
/// that one value, the same licence `stable_min_arg_formula` gives a nested `min`
/// result local. After `s = b` the fact still bounds `n` by the OLD length and proves
/// nothing about `b`. In a loop that reseats the slice (`while !s.is_empty() { let n =
/// a.min(s.len()); out.extend_from_slice(&s[..n]); s = &s[n..]; }`, aterm-ctl
/// `redial.rs:1142/1144`) the block that reads `s[..n]` ties the temp to the length
/// the index reads (`_7 == _8__slice_len == s__slice_len#..`), and the row proves.
/// The versioned call-point twin of this fact (`call_point_slice_len_of_arg`) does
/// not reach a loop body: the semantic-guard map collapses every block a loop revisits
/// (`build_semantic_guard_map_impl`). The seal proved both rows through the bare root
/// name the A8 round withdrew; the candidate gate of 2026-10-16 refuted them.
fn single_assignment_length_temp(func: &VerifiableFunction, arg: &Operand) -> Option<Formula> {
    let (Operand::Copy(p) | Operand::Move(p)) = arg else { return None };
    if !p.projections.is_empty()
        || crate::local_defs::is_parameter(func, p.local)
        || !is_single_static_assignment(func, p.local)
    {
        return None;
    }
    match crate::local_defs::unique_value_def(func, p.local)? {
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, inner)
            if matches!(
                crate::ptr_metadata_model(func, inner),
                crate::PtrMetadataModel::Length(_)
            ) => {}
        Rvalue::Len(_) => {}
        _ => return None,
    }
    Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int))
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
            // NAME-ANCHOR-2: a primitive integer `Self` (core's impl), not only
            // std's trait path — a user `Ord` impl may override `min`/`max`.
            let method = primitive_int_ord_method(func, callee, args, dest);
            let is_min = method == Some("min");
            let is_max = method == Some("max");
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
                if let Some(r) = stable_min_arg_formula(func, arg, FUEL)
                    .or_else(|| single_assignment_length_temp(func, arg))
                {
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
            // Trust (2026-10-11, sweep2 n13/b1): a divisor that is a never-written
            // parameter or a single-static-assignment local with a statement def
            // (`fn f(a: u64, b: u64) { .. a % b .. }`) is as stable as the min/max
            // result the resolver admits: its bare name means one value wherever it is
            // read, and the remainder that reads it is defined after it. Without it `b
            // - a % b` was refuted with `b = 1, a % b = 2`. A CALL destination is left
            // out on purpose: a row whose verdict hangs on an unmodelled return is
            // reported Unknown (`UnmodeledCalleeReturn`, "a solver model over it is
            // not an execution"), and a fact naming that return made `x % scale()`'s
            // divide-by-zero row a refutation instead (`census_budget_fmt_inner_u32`).
            let Some(b_f) = stable_min_arg_formula(func, b, FUEL).or_else(|| match b {
                Operand::Copy(p) | Operand::Move(p)
                    if p.projections.is_empty()
                        && is_single_static_assignment(func, p.local)
                        && (crate::local_defs::is_parameter(func, p.local)
                            || crate::local_defs::unique_value_def(func, p.local).is_some()) =>
                {
                    Some(Formula::Var(crate::place_to_var_name(func, p), Sort::Int))
                }
                _ => None,
            }) else {
                continue;
            };
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

    if crate::local_defs::is_parameter(func, local)
        || !super::terminator_presence_for(func).has_switch_int
        || !crate::local_defs::value_count(func, local).is_exactly(2)
    {
        return None;
    }

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
    let mut defs: [Option<(usize, &Rvalue, usize)>; 2] = [None, None]; // (block_idx, rvalue, goto_target)
    let mut def_count = 0usize;
    let disqualified =
        crate::any_local_write_candidate(func, &func.body.blocks, local, |block, stmt| match stmt {
            Some(Statement::Assign { place, rvalue, .. }) => {
                if place.local != local {
                    return false;
                }
                if !place.projections.is_empty() {
                    return true; // projected store into L — ambiguous value
                }
                let Terminator::Goto(target) = &block.terminator else {
                    return true;
                };
                if let Some(slot) = defs.get_mut(def_count) {
                    *slot = Some((block.id.0, rvalue, target.0));
                    def_count += 1;
                    false
                } else {
                    true
                }
            }
            Some(_) => false,
            None => {
                // a call also writes L
                matches!(&block.terminator, Terminator::Call { dest, .. } if dest.local == local)
            }
        });
    if disqualified {
        return None;
    }
    // `def_count` counts what THIS scan saw; `value_count` (checked at entry) counts the
    // local's VALUES, which for a PARAMETER includes the implicit ENTRY definition
    // `body.blocks` never carries. A merged parameter (`fn f(mut k: usize, ..) { if v > C
    // { k = C } else { k = v } .. }`) has three, and `min(v, C) <= C` is false of the
    // entry one — the bound is emitted on the BARE name, so version-renaming would bind
    // it there. For a non-parameter the two agree: the gather already refuses a projected
    // store and a call dest, which are the only other things `value_count` counts.
    let [Some((b0, rv0, g0)), Some((b1, rv1, g1))] = defs else {
        return None;
    };
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
        // Trust (2026-10-10, review round 101): the var arm must be entered ONLY through
        // this switch's edge, and `v` must hold one value, else the edge's `v <= C` says
        // nothing about the copied value. `if w || v <= 5 { v } else { 5 }` also jumps
        // into the var arm from the `w` test, and `k <= 5` was kernel-certified over an
        // index `a[k]` that panics at `v = 9, w = true`.
        if var_block == 0
            || !crate::guards::block_has_sole_predecessor(func, BlockId(var_block), block.id)
            || edges.iter().filter(|&&e| e == var_block).count() != 1
            || !is_single_static_assignment(func, var_v)
        {
            continue;
        }

        // discr must be `_g = cmp(v, C)` — a single-static-assignment bool temp.
        let Some(g) = whole_local(discr) else { continue };
        if crate::local_defs::is_parameter(func, g) || !is_single_static_assignment(func, g) {
            continue;
        }
        let Some(Rvalue::BinaryOp(op, lhs, rhs)) = crate::local_defs::unique_value_def(func, g)
        else {
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
/// source types' ranges. `None` if a component is signed or unresolvable; a cast
/// from such a component is bounded by its target type's range alone. Sound by
/// construction: a cast from an unsigned `inner` is `≤ min(ub(inner),
/// type_max(target))` (widening preserves the value; narrowing truncates into
/// `[0, type_max(target)]`), and a wrapping `a op b` result is `≤ a op b ≤ ub(a) op
/// ub(b)` (the machine `mod` only decreases), each further capped by the result
/// type's range.
pub(super) fn unsigned_upper_bound(
    func: &VerifiableFunction,
    operand: &Operand,
    fuel: u32,
) -> Option<i128> {
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
    // CAST-SIGNED-CLAMP-UB-1: only an UNSIGNED component (an unsigned integer,
    // `bool`, or `char`) has an unsigned upper bound. A bound derived for a SIGNED
    // place is a bound on its signed value, and `as` wraps a negative value to a
    // huge unsigned one, so it bounds nothing the caller asks about. The Cast arm
    // below used to recurse into a signed `inner` and keep the bound:
    // `l = if v > 10 { 10 } else { v }` (`v: i32`) resolved to 10 through
    // `clamp_upper_bound`, `build_additive_bound_facts` published the global fact
    // `(l as usize) <= 10`, and the bounds VC of `arr[l as usize]` (len 11) went
    // UNSAT. The row read Certified while `l = -1` indexes `usize::MAX`. Beneath
    // such a cast the Div/Add/Mul arms carried the signed bound through signed
    // arithmetic too (`(l / 2) as usize`). A Cast is the only rvalue here whose
    // operand type can differ from its result's, but the check sits at entry so
    // every arm, present or future, keeps the contract. Keyed on the SIGN, not on
    // `ty_max`: `u128` has no `ty_max` but its derived bounds are sound. An untyped
    // place fails closed. SOUND: declining only turns a derived bound into the cast
    // target's type range or no fact, i.e. PROVE into not-proved. Uses the
    // borrowing `place_ty_cow`, which meters nothing.
    let p_ty = if take_field0 {
        crate::place_ty_cow(func, p)
    } else {
        crate::local_ty_ref(func, p.local).map(std::borrow::Cow::Borrowed)
    };
    let unsigned_component = p_ty.as_deref().is_some_and(|t| {
        matches!(
            t,
            Ty::Int { signed: false, .. } | Ty::PtrSizedInt { signed: false } | Ty::Bool | Ty::Char
        )
    });
    if !unsigned_component {
        return None;
    }
    // PERF-COMPILER-VCGEN-586: parameters have an implicit entry definition, so
    // `value_local_is_unstable` (when reassigned/mut-borrowed), `unique_value_def`,
    // and `clamp_upper_bound` all decline after scanning the body and always return
    // `None` (for `take_field0`) or `p_ty.as_deref().and_then(ty_max)` (otherwise).
    // Short-circuit parameters alongside `fuel == 0` in O(1).
    if fuel == 0 || crate::local_defs::is_parameter(func, p.local) {
        return if take_field0 { None } else { p_ty.as_deref().and_then(ty_max) };
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
        let ty_bound = p_ty.as_deref().and_then(ty_max);
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
        // Trust (2026-10-10, review round 100): the clamp bound needs an UNSIGNED
        // local (`ty_bound` is `Some` only then). `min(v, C) <= C` holds of a signed
        // `k` too, but this function answers an UNSIGNED bound, which also claims
        // `0 <= k`: `let k: i64 = if n > 5 { 5 } else { n }; (k as u64) + 10` got
        // `k as u64 <= 5`, PROVED kernel-certified, and overflows at `n = -1`.
        //
        // Trust (merge 2026-10-14): the UNSIGNED premise is now the entry guard above
        // (CAST-SIGNED-CLAMP-UB-1, d5f1b201549), which returns `None` for every signed,
        // float or untyped place before this arm runs, so `k: i64` still answers `None`
        // here. `ty_bound` is no longer the proxy for it: it is `None` for `u128` (no
        // `ty_max`) as well, and requiring it dropped the clamp of an unsigned `u128`,
        // `min(v, C) <= C` with `v >= 0`. The type range still caps the clamp where
        // it exists, and a negative `C` (impossible for an unsigned local) declines.
        return match clamp_upper_bound(func, p.local) {
            Some(c) if c >= 0 => Some(ty_bound.map_or(c, |m| c.min(m))),
            _ => ty_bound,
        };
    }
    let bin = |a: &Operand, b: &Operand, mul: bool| -> Option<i128> {
        let ua = unsigned_upper_bound(func, a, fuel - 1)?;
        let ub = unsigned_upper_bound(func, b, fuel - 1)?;
        if mul { ua.checked_mul(ub) } else { ua.checked_add(ub) }
    };
    if take_field0 {
        return match crate::local_defs::unique_value_def(func, p.local) {
            Some(Rvalue::CheckedBinaryOp(BinOp::Add, a, b)) => bin(a, b, false),
            Some(Rvalue::CheckedBinaryOp(BinOp::Mul, a, b)) => bin(a, b, true),
            _ => None,
        };
    }
    let local_max = p_ty.as_deref().and_then(ty_max);
    let cap = |v: i128| Some(local_max.map_or(v, |m| v.min(m)));
    match crate::local_defs::unique_value_def(func, p.local) {
        Some(Rvalue::Cast(inner, to_ty)) => {
            let tmax = ty_max(to_ty)?;
            // A signed (or float, or untyped) `inner` answers `None` at the guard
            // above, so its cast keeps only `tmax` (CAST-SIGNED-CLAMP-UB-1).
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
        Some(_) => local_max,
        // A non-SSA local (no unique whole-local def) may still be a `min(v, C)`
        // clamp whose value is bounded by `C`. Resolve that tight bound, capped by
        // the local's own type range. See `clamp_upper_bound` (sound: `min(v,C) ≤ C`
        // globally). Falls back to the loose type bound when not a recognized clamp.
        // A signed clamp is no unsigned bound (it may be negative); the entry guard
        // above has already returned `None` for a signed local, so this local is
        // unsigned (a `u128` too, whose `local_max` is `None`). See the unstable arm
        // above.
        None => match clamp_upper_bound(func, p.local) {
            Some(c) if c >= 0 => Some(local_max.map_or(c, |m| c.min(m))),
            _ => local_max,
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
///
/// TWO EMISSION SITES, ONE THEOREM. The whole-local pass below names a computed
/// local `_dst`; the field pass names the checked-op RESULT FIELD `_c.0` of
/// `_c = CheckedBinaryOp(Add|Mul, a, b)` directly. Both ask
/// [`unsigned_upper_bound`] the same question and both publish the same
/// inequality — the field pass exists because a chained sum's SECOND and later
/// adds read `_c.0` as an OPERAND with no intervening whole-local copy, so the
/// whole-local pass has no place to hang the bound on and the outer add sees only
/// the loose `0 ≤ _c.0 ≤ TYPE_MAX` type range. Measured on
/// `(s0!=s1) as u32 + (s1!=s2) as u32 + (s2!=s3) as u32 + (s3!=s0) as u32`: the
/// first add is kernel-certified and every later one comes back
/// `overflow:add → runtime_checked`, because the pool holds `_6 ≤ 1`, `_8 ≤ 1`,
/// `_10 ≤ 1` and `Le(_13.0, 4294967295)` but no tight fact about `_13.0` itself.
pub(super) fn build_additive_bound_facts(func: &VerifiableFunction) -> Vec<Formula> {
    use trust_types::{Place, Projection, Ty};
    const FUEL: u32 = 16;
    let mut facts = Vec::new();
    let mut checked_op_locals: Vec<usize> = Vec::new();
    for (local_idx, local) in func.body.locals.iter().enumerate() {
        let Ty::Int { width, signed: false } = &local.ty else {
            if !crate::local_defs::is_parameter(func, local_idx)
                && matches!(
                    crate::local_defs::unique_value_def(func, local_idx),
                    Some(Rvalue::CheckedBinaryOp(BinOp::Add | BinOp::Mul, _, _))
                )
            {
                checked_op_locals.push(local_idx);
            }
            continue;
        };
        if *width >= 127
            || crate::local_defs::is_parameter(func, local_idx)
            || !is_single_static_assignment(func, local_idx)
        {
            continue;
        }
        // Only COMPUTED locals whose defining rvalue can tighten `local_max` get a derived bound.
        if !matches!(
            crate::local_defs::unique_value_def(func, local_idx),
            Some(
                Rvalue::Cast(..)
                    | Rvalue::BinaryOp(BinOp::Add | BinOp::Mul | BinOp::Div, ..)
                    | Rvalue::CheckedBinaryOp(BinOp::Add | BinOp::Mul, ..)
                    | Rvalue::Use(..)
            )
        ) {
            continue;
        }
        let op = Operand::Copy(Place::local(local_idx));
        let Some(bound) = unsigned_upper_bound(func, &op, FUEL) else {
            continue;
        };
        // Only worth a fact if strictly tighter than the local's type range.
        if bound >= (1i128 << *width) - 1 {
            continue;
        }
        let Operand::Copy(place) = &op else { continue };
        let var = Formula::Var(crate::place_to_var_name(func, place), Sort::Int);
        facts.push(Formula::Le(Box::new(var), Box::new(Formula::Int(bound))));
    }
    // The checked-op RESULT FIELD `_c.0`. Same bound, same guard, named where the
    // consuming operation actually reads it.
    //
    // SOUNDNESS — the emit guard IS the no-wrap proof, not a heuristic. Let `w` be
    // the width of `_c.0` and `bound = ub(a) + ub(b)` (resp. `ub(a)·ub(b)`), computed
    // in `i128` with `checked_{add,mul}` so an overflowing product declines outright.
    // The machine semantics of `CheckedBinaryOp` are `_c.0 = (a ⊕ b) mod 2^w`, so a
    // bound on the MATHEMATICAL result transfers to `_c.0` only when no wrap occurs.
    // The fact is emitted ONLY when `bound < 2^w − 1`, hence `bound < 2^w`; with
    // `a ≤ ub(a)` and `b ≤ ub(b)` that gives `a ⊕ b ≤ bound < 2^w`, so the modulus is
    // inert and `_c.0 = a ⊕ b ≤ bound`. Exactly at the boundary (`bound = 2^w − 1`,
    // e.g. `(x/2) + (y/2)` on `u8`) nothing is emitted, and above it the wrap is real
    // — in both cases the outer operation keeps the loose type range and stays
    // refutable. Fixture `o05_u8_boundary` is that case.
    //
    // NOT A NEW THEOREM. `unsigned_upper_bound`'s `take_field0` arm already returns
    // this bound, and the whole-local pass above already publishes it whenever MIR
    // happens to materialise a copy `_dst = move (_c.0)` (`Rvalue::Use` arm). This
    // pass removes the dependence on that copy existing; the inequality, its
    // derivation and its guard are unchanged.
    //
    // STABILITY GATES on the tuple local, both drop-only: `is_single_static_assignment`
    // (one whole-local def, no field store, no `SetDiscriminant`/`Deinit`, no
    // `&mut`/raw borrow, no call-dest write) and `value_local_is_unstable` (adds the
    // `&mut _c` passed as a Call ARGUMENT channel). `unsigned_upper_bound` itself
    // re-derives through `local_defs::unique_value_def`, so a second def declines anyway.
    let mut field0_op: Option<Operand> = None;
    for ck_local in checked_op_locals {
        if !is_single_static_assignment(func, ck_local)
            || crate::guards::value_local_is_unstable(func, ck_local)
        {
            continue;
        }
        let op = field0_op.get_or_insert_with(|| {
            Operand::Copy(Place { local: 0, projections: vec![Projection::Field(0)] })
        });
        let Operand::Copy(field0) = op else { continue };
        field0.local = ck_local;
        let Some(&Ty::Int { width, signed: false }) =
            crate::place_ty_cow(func, field0).as_deref()
        else {
            continue;
        };
        if width >= 127 {
            continue;
        }
        let Some(bound) = unsigned_upper_bound(func, op, FUEL) else {
            continue;
        };
        if bound >= (1i128 << width) - 1 {
            continue;
        }
        let Operand::Copy(field0) = op else { continue };
        let var = Formula::Var(crate::place_to_var_name(func, field0), Sort::Int);
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
/// 2. Arm (a) reads are tied only when nothing between them can change the
///    referent. There are two channels, and each half of this guard closes one:
///
///    * A BARRIER. A shared borrow forbids mutation *through L*, but the pointee can
///      still change across program points via a SEPARATE aliasing handle with
///      interior mutability (`let c: &Cell<E>` aliasing `r: &E`; `c.set(..)` between
///      two `*r` reads), and that code runs only inside a `Call`/`Drop`/`Opaque`. So
///      a read is tied only in the PRE-BARRIER region — not reachable from entry
///      after any such terminator — unless the post-barrier rule below admits it.
///      Without this half the fact is a FALSE PROOF (caught by adversarial review:
///      `im_direct_attack`).
///    * A STATEMENT. The two reads need not go through ONE live borrow: they are
///      grouped by their CANONICAL referent, so `_3 = &_2; disc(*_3)` and
///      `_6 = &_2; disc(*_6)` share the key `_2` although `_3` is dead by the time
///      `_6` is minted. A plain statement between them changes the referent with no
///      barrier at all. DISC-CSE-PRE-BARRIER-WRITE-1 (2026-10-12): the old claim
///      here, that such a mutation can only run inside a `Call`/`Drop`/`Opaque`, was
///      false, and in safe Rust the tie made the second arm infeasible, so its
///      overflow row was kernel-certified and its check elided. The five channels:
///        - a whole re-assignment of the referent (`cur = None`);
///        - a store through a `&mut` borrow of it (`let m = &mut e; *m = None`);
///        - a store through a `&mut` parameter (`*e = None`);
///        - a field store through `&mut self` (`self.st = Busy`);
///        - a reseat of the shared reference itself (`r = &b`): the fold cannot
///          resolve a two-valued `r`, so the key stays `*r` and names whatever `r`
///          holds at each read.
///
///      A pre-barrier read is therefore tied only when its canonical referent is
///      BODY-STABLE (`crate::place_is_body_stable`: the root holds at most one value,
///      with no projected store, `&mut`/`&raw` borrow, `SetDiscriminant`/`Deinit` or
///      call-destination write anywhere in the body; at most one `Deref`, as the first
///      projection, of a reference root under which no write-capable pointer is
///      minted; no `Field` hop into an interior-mutability wrapper), OR is the
///      pointee of a FROZEN shared-reference PARAMETER
///      ([`frozen_shared_param_referent`]; the post-barrier argument below, a
///      fortiori — no statement can write it without undefined behaviour, and a
///      pinned `P` is never reseated). The second disjunct keeps derived
///      `PartialEq::eq` / `Ord::cmp` tying `*self`/`*other` in a body that also takes
///      `&raw const (*self)`, which the body-stable scan refuses. The rule is
///      flow-insensitive: a referent written anywhere in the body loses its tie even
///      where no write lies between the two reads (precision only; a flow-sensitive
///      "no write between the reads" refinement is recorded as a possible follow-up
///      in DECISION_QUEUE DISC-CSE-PRE-BARRIER-WRITE-1).
///
///    The derived-`eq` discriminant reads are all pre-barrier (field comparisons /
///    drops come after) and read a frozen parameter's pointee, so `eq` still
///    discharges.
///
///    Arm (a) reads after a barrier are tied only when the read's canonical referent
///    is `*P` for a shared-reference PARAMETER `P: &T` of THIS function
///    ([`frozen_shared_param_referent`]): `P` pinned (never written, no alias of its
///    own storage), `T` free of `UnsafeCell` at every inline position
///    ([`ty_is_inline_freeze`]), and every barrier in the body a call of a safe,
///    non-foreign Rust function with no atomic write, or a `Drop`. A reference
///    passed as a function argument is protected for the whole call (Stacked and
///    Tree Borrows alike; the Reference's liveness rule; rustc's `noalias readonly`
///    on a `&Freeze` argument), so while this body runs, a write to any byte of `*P`
///    outside an `UnsafeCell` — through `im_direct_attack`'s separate `&Cell` handle
///    or any other pointer — is undefined behaviour. With no `UnsafeCell` in `T`,
///    `disc(*P)` is then one value for the whole body. The protector covers only
///    the function's OWN parameters, which is why a shared reference that is a
///    local (`let r = &*guard;`) keeps the pre-barrier restriction. The same
///    premise licenses `callee_write_set::refine_shared_reborrow_havoc` and
///    `contracts::safe_shared_collection_call_preserves_local`, whose conservatism
///    about the barriers (safe, non-foreign, no atomic write) this copies.
///    TRUST-09, 2026-09-25: a `#[derive(Ord)]` enum with two data-carrying
///    variants — regex-syntax 0.8.10's `Utf8Sequence` — reads `disc(*self)` before
///    the `<isize as Ord>::cmp` call and `disc(*(_9.0))` (canonically `*self`)
///    after it, and its `_ => unreachable` arm was REFUTED with the two reads
///    disagreeing. `tests/derived_ord_cmp_realmir.rs` is that shape end to end.
///
///    Arm (b) reads after a barrier are tied too, but only when NO code can reach
///    the aggregate's storage at all: the seam question
///    `local_defs::storage_never_aliased` — no borrow of it, shared or mutable,
///    whole or projected; no raw address; no `Unsupported` rvalue naming it; no
///    write but its whole named assignment (so no `Drop` of it, and no
///    `Unlocatable` write anywhere in the body). A `Call`/`Drop`/`Opaque` can only
///    change memory it has a pointer to, and every pointer to a local's storage is
///    minted by one of those rvalues, so an unaliased owned aggregate holds, at
///    every read, exactly what its one `Aggregate` stored. TRUST-10, 2026-09-23: bit-vec 0.9.1's
///    `impl Ord for BitVec` reads `discriminant(_5.1)` into three temps after the
///    `a.next()`/`b.next()` calls that build `_5 = (move _6, move _8)`, and its
///    shared `otherwise -> unreachable` was REFUTED with `_10 = 0, _13 = 1` — two
///    reads of one unwritten field disagreeing, which no execution does.
///    `tests/discriminant_cse_after_call_realmir.rs` is that shape end to end.
///
///    IN A LOOP the aggregate is rebuilt each iteration — and so is an arm-(a)
///    body-stable referent whose root is a local with its one definition inside the
///    loop — so a temp read in an earlier iteration can hold a stale value at a
///    later point. The tie is still sound there, in both arms: guard 3 makes each
///    temp's value the read of ONE statement, a MIR temp is never read before its
///    own read in the same iteration, and the path
///    facts that could pin a stale value do not survive the loop-header join — so
///    at every row the stale side of an equality is unconstrained by anything but
///    the same type-range facts the fresh side satisfies.
/// 3. Each tied temp's ONE value is this read: `unique_value_def(dest)` is the same
///    `Discriminant(src)`. A temp a later statement reuses (destination
///    propagation can merge temps in optimised MIR) holds a second value the
///    equality would be false of.
///
/// Distinct enum fields keep distinct canonical names and are never merged (so a
/// 2-distinct-enum `eq` keeps its real `Unreachable` and still refutes).
///
/// Trust (2026-09-27, class `v-refuted-unreachable`) — a THIRD admission, arm (c),
/// for the owned-aggregate reads arm (b) still refuses after a barrier. Arm (b) asks
/// `storage_never_aliased` of the WHOLE local, which a `Drop` of any part of it fails,
/// and it admits a single `Field` only. So a by-value `match` whose drop-elaboration
/// ladder drops the payloads the arms did not move (`winnow::error::ErrMode::or`:
/// `match (self, other)`), or one whose arm moves a payload out, or a read of an enum
/// nested in a variant payload (`(_3.1 as Err).0`), kept its re-reads untied and its
/// shared `otherwise -> Unreachable` REFUTED with one field read as two tags. Arm (c)
/// is licensed per READ by [`unaliased_aggregate_licensed_reads`]: no borrow of the
/// aggregate anywhere, its one construction its only whole write, and no entry /
/// storage marker / move-out / drop of it on any path into the read that does not
/// re-run the construction — so the ladder's reads after a drop stay untied while the
/// match's own re-reads before it are tied. The destination must be single-assignment.
/// See `tests/discriminant_cse_owned_aggregate_realmir.rs`.
pub(crate) fn build_discriminant_cse_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    for reads in discriminant_cse_groups(func) {
        let Some((anchor_name, anchor_sort, _)) = reads.first() else {
            continue;
        };
        for (other_name, _, _) in reads.iter().skip(1) {
            facts.push(Formula::Eq(
                Box::new(Formula::Var(anchor_name.clone(), anchor_sort.clone())),
                Box::new(Formula::Var(other_name.clone(), anchor_sort.clone())),
            ));
        }
    }
    facts
}

/// Trust (2026-09-27, class `v-refuted-unreachable`): the tie map
/// `{discriminant temp -> the first temp of its CSE group}` over the members of each
/// [`build_discriminant_cse_facts`] group whose destination is SINGLE-ASSIGNMENT
/// (a multiply-written temp keeps its tie fact and nothing more), memoized per
/// function. The path-guard splice (`safety::v2_formula_with_path_guards_recorded`)
/// renders a switch guard over a tied temp through its anchor.
///
/// WHY. The tie `d == a` lets the SOLVER join a subset switch's `otherwise` edge to
/// the earlier switch that tested the same field, but each path then carries its
/// contradiction only up to that equality (`a = 1`, `d = a`, `d ∉ {1}`), which the
/// clean-kernel re-check's syntactic resolution cannot see through; rendered through
/// the anchor the same path reads `a = 1 ∧ ¬(a = 1)`.
///
/// SOUND: every pair `(d, a)` of the map is a pair [`build_discriminant_cse_facts`]
/// ties, under the same admission. The splice conjoins the tie `a == d` to every
/// guard it renders, BEFORE the guard is spelled at its source block
/// (`guard_value_spelling::spell_path_guard`), so both sides of the carried tie are
/// spelled at the same point as the rendered read: a rendered guard is EQUIVALENT to
/// the original one conjoined with the tie at that point, and asserts nothing more.
/// The tie is the one `build_discriminant_cse_facts` asserts, and it is NOT a fact
/// about the anchor's own read on every execution: the anchor is the group's first
/// read in block order, which can sit in a sibling branch the row's path never runs
/// (`pair`'s `_6` is rendered through bb3's `_9`, and the path through bb4 never
/// assigns `_9`). It is sound by the admission's argument (DISC-CSE-ARM-C-1): on a
/// path that does not run the anchor's read, the anchor's spelling is constrained by
/// nothing real there — its range fact is pinned to its establish name, a real use of
/// it is dominated by its definition — so the tie only gives an otherwise free name the
/// value of a read of the same construction, which the fresh side's own facts already
/// satisfy; on one loop-erased path every licensed read observes the same
/// construction. A future fact that constrains a temp's ENTRY or loop-header value
/// would break that, and this rendering must then be revisited. It does not depend on
/// the splicing lane also conjoining the function's global facts (the termination
/// lanes conjoin none). Where the spelling gives the anchor a guard-local name, the
/// carried tie binds that name and nothing else, so the rendering only loses
/// precision there, never soundness.
pub(crate) fn discriminant_cse_anchor_map(
    func: &VerifiableFunction,
) -> std::rc::Rc<trust_types::fx::FxHashMap<String, String>> {
    crate::fn_memo::discriminant_cse_anchors(func, || {
        let mut map = trust_types::fx::FxHashMap::default();
        for reads in discriminant_cse_groups(func) {
            let mut ssa = reads.iter().filter(|(_, _, single)| *single);
            let Some((anchor, _, _)) = ssa.next() else {
                continue;
            };
            for (name, _, _) in ssa {
                map.insert(name.clone(), anchor.clone());
            }
        }
        map
    })
}

/// The groups [`build_discriminant_cse_facts`] ties: per canonical referent, its
/// admitted reads as `(dest var name, dest sort, dest is single-assignment)`, in
/// block order. See [`build_discriminant_cse_facts`] for the admission.
fn discriminant_cse_groups(func: &VerifiableFunction) -> Vec<Vec<(String, Sort, bool)>> {
    // Post-barrier taint: blocks reachable from entry AFTER crossing a terminator that
    // can run arbitrary code (`Call`/`Drop`/`Opaque`). A `Discriminant` read in a
    // tainted block may see a pointee an aliasing interior-mutation has changed, so it
    // is eligible only under its arm's post-barrier condition (below): a frozen
    // shared-reference parameter for arm (a), an aggregate no pointer reaches for
    // arm (b), a per-read license for arm (c).
    let blocks = &func.body.blocks;
    // PERF-COMPILER-VCGEN-637: every admitted CSE read requires `src` to have either
    // `[Projection::Deref]` (arm a) or a `Field`/`Downcast` projection chain starting
    // with `Field(_)` (arms b/c). Pre-filter the >= 2 discriminant check and per-stmt
    // loop by that projection shape before running post-barrier taint, `every_barrier_is_a_safe_rust_call`,
    // or `local_defs` queries.
    let is_cse_discr_src = |src: &Place| {
        matches!(src.projections.as_slice(), [trust_types::Projection::Deref])
            || (matches!(src.projections.first(), Some(trust_types::Projection::Field(_)))
                && src.projections.iter().all(|p| {
                    matches!(
                        p,
                        trust_types::Projection::Field(_) | trust_types::Projection::Downcast(_)
                    )
                }))
    };
    let mut discr_assigns = blocks.iter().flat_map(|b| &b.stmts).filter(|stmt| {
        matches!(
            stmt,
            Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. }
                if dest.projections.is_empty()
                    && !crate::local_defs::is_parameter(func, dest.local)
                    && is_cse_discr_src(src)
        )
    });
    if discr_assigns.nth(1).is_none() {
        return Vec::new();
    }
    let mut tainted: FxHashSet<usize> = FxHashSet::default();
    let mut stack: Vec<usize> = Vec::new();
    for b in blocks {
        if matches!(
            b.terminator,
            Terminator::Call { .. } | Terminator::Drop { .. } | Terminator::Opaque { .. }
        ) {
            super::loop_bounds::for_each_terminator_succ(&b.terminator, |s| stack.push(s));
        }
    }
    while let Some(b) = stack.pop() {
        if tainted.insert(b) {
            if let Some(blk) = blocks.get(b) {
                super::loop_bounds::for_each_terminator_succ(&blk.terminator, |s| stack.push(s));
            }
        }
    }

    // Arm (a) after a barrier needs every barrier to be one the argument protector
    // covers; computed once, and only when a post-barrier read exists at all.
    let barriers_are_safe_rust = !tainted.is_empty() && every_barrier_is_a_safe_rust_call(func);

    let mut by_referent: FxHashMap<String, Vec<(String, Sort, bool)>> = FxHashMap::default();
    // Arm (c)'s per-aggregate license, computed once per aggregate local.
    let mut licensed: FxHashMap<usize, Option<FxHashSet<StmtPoint>>> = FxHashMap::default();
    for (idx, block) in blocks.iter().enumerate() {
        // A read after a barrier: a shared-ref pointee may have been mutated
        // (guard 2); only a frozen shared-reference PARAMETER's pointee, an
        // unexposed owned aggregate, or an arm-(c)-licensed read stays eligible.
        let after_barrier = tainted.contains(&idx);
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            // PERF-COMPILER-VCGEN-586 / 637: parameters never have `unique_value_def == Some(..)`,
            // and unprojected `Discriminant` reads cannot match arms (a)/(b)/(c).
            if !dest.projections.is_empty()
                || !is_cse_discr_src(src)
                || crate::local_defs::is_parameter(func, dest.local)
            {
                continue;
            }
            // Guard 3: the temp holds this read and nothing else.
            if !matches!(
                crate::local_defs::unique_value_def(func, dest.local),
                Some(Rvalue::Discriminant(read)) if read == src
            ) {
                continue;
            }
            // Arm (c)'s source: a field of the aggregate, or an enum nested in a
            // variant payload of one (`(_3.1 as Err).0` — the `VarError` inside
            // `Result<String, VarError>`), reached through `Field`/`Downcast` only. Each
            // such path is a fixed part of the aggregate's value, and
            // `place_to_var_name` spells distinct paths distinctly (`_3.1@1.0`), so
            // two reads group together only when they read the same bytes.
            let owned_field_path =
                matches!(src.projections.first(), Some(trust_types::Projection::Field(_)));
            // Arm (c), see the function doc and `unaliased_aggregate_licensed_reads`.
            // The DESTINATION must be single-assignment: the tie is keyed on its bare
            // name, and a second definition would let the version rename bind the
            // fact to a value this read never produced.
            let single = crate::local_defs::is_single_static_assignment(func, dest.local);
            // Guard 1: the discriminant source must denote a STABLE value at every
            // read. Two admitted shapes:
            //  (a) shared-ref deref `disc(*L)`, `L: &T` (derived-`PartialEq::eq`): a
            //      shared borrow forbids mutation through L, but not a STATEMENT
            //      write of the referent while no such borrow is live (`cur = None`
            //      between `&cur` and a fresh `&cur`) or a reseat of L; guard 2
            //      covers both (taint for a barrier, a body-stable referent for a
            //      statement). `&mut` / raw-ptr reads are excluded.
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
            // Guard 2 for arm (a) (DISC-CSE-PRE-BARRIER-WRITE-1): before any barrier
            // the canonical referent must still be one no statement writes or
            // reseats — body-stable, or a frozen shared-reference parameter's pointee.
            let shared_ref_deref =
                matches!(src.projections.as_slice(), [trust_types::Projection::Deref])
                    && matches!(
                        // verifier-perf: borrow the declared type — only a variant check.
                        crate::local_ty_ref(func, src.local),
                        Some(Ty::Ref { mutable: false, .. })
                    )
                    && if after_barrier {
                        barriers_are_safe_rust && frozen_shared_param_referent(func, src)
                    } else {
                        let canon = crate::canonical_place(func, src);
                        crate::place_is_body_stable(func, &canon)
                            || frozen_shared_param_referent_canon(func, &canon)
                    };
            let owned_agg_field =
                matches!(src.projections.as_slice(), [trust_types::Projection::Field(_)])
                    && !crate::local_defs::is_parameter(func, src.local)
                    && matches!(
                        crate::local_defs::unique_value_def(func, src.local),
                        Some(Rvalue::Aggregate(..))
                    )
                    && crate::place_source_is_stable(func, src.local)
                    && (!after_barrier
                        || crate::local_defs::storage_never_aliased(func, src.local));
            if !(shared_ref_deref
                || owned_agg_field
                || (owned_field_path
                    && single
                    && src.local != 0
                    && !crate::local_defs::is_parameter(func, src.local)
                    && licensed
                        .entry(src.local)
                        .or_insert_with(|| unaliased_aggregate_licensed_reads(func, src.local))
                        .as_ref()
                        .is_some_and(|reads| reads.contains(&(idx, stmt_idx)))))
            {
                continue;
            }
            let canon = crate::place_to_var_name(func, src);
            let dest_name = crate::place_to_var_name(func, dest);
            let sort = crate::place_sort(func, dest).unwrap_or(Sort::Int);
            by_referent.entry(canon).or_default().push((dest_name, sort, single));
        }
    }
    by_referent.into_values().collect()
}

/// A program point in `func.body.blocks`: `(block index, statement index)`.
pub(super) type StmtPoint = (usize, usize);

/// Trust (2026-09-27, class `v-refuted-unreachable`): the `Discriminant` reads of an
/// OWNED aggregate `local` that provably observe the value of its ONE construction,
/// however many calls, drops or loop iterations lie between them — the license of
/// arm (c) of [`build_discriminant_cse_facts`].
///
/// `None` (no read licensed) unless ALL of:
///  1. `local` is neither the return place nor a parameter, and the exhaustive
///     [`trust_types::LocalWrite`] oracle reports exactly one whole write for it, an
///     `Assign(local, Aggregate(..))` — the construction `S`;
///  2. every OTHER channel that oracle reports, on every statement and terminator, is
///     `Untouched`, except a `Drop` terminator of a place rooted at `local` (an
///     invalidating event, below). A projected store, `SetDiscriminant`, `Deinit`, a
///     call destination, an `Opaque` terminator or pointer-writing statement
///     (`Unlocatable`), or any second whole write refuses;
///  3. NO borrow of any place rooted at `local` exists anywhere — shared `&`, `&mut`
///     and `&raw` alike, and the reborrow / fake-borrow sentinels that carry the place
///     as an operand of `Rvalue::Unsupported` — and no operand this scan cannot see
///     into (`Operand::Symbolic`, an rvalue or terminator it does not know) touches the
///     body.
///
/// WHY THAT IS ENOUGH. With no pointer to `local` in existence, nothing can change it
/// but a statement or terminator that NAMES it: a callee, another place's drop glue or
/// a store through a pointer cannot reach it. Of those, 1-2 leave exactly these, the
/// INVALIDATING EVENTS — the points after which `local` need not hold what `S` wrote:
///  * function ENTRY (`local` is uninitialized until `S` runs);
///  * `StorageLive(local)` and `StorageDead(local)`;
///  * a `Move` out of any place rooted at `local` — the MIR semantics of a move
///    operand may leave the source de-initialized (UCG#188, undecided), and for a
///    niche-encoded enum the tag lives in the moved payload's bytes, so it is counted
///    rather than argued away;
///  * a `Drop` of any place rooted at `local` — its glue receives `&mut` to that place.
///
/// A read is licensed iff NO path — normal or unwind — from an event reaches it
/// without passing `S`. At a licensed read `local` therefore holds exactly the value
/// the most recent execution of `S` wrote, and two licensed reads of the same field
/// that follow the same execution of `S` produce the same discriminant: the
/// per-execution equality arms (a) and (b) assert for their reads, and the one the
/// v2 lane's acyclic path guards consume — a VC path crosses a loop header once, and
/// since every path from ENTRY (an event) to a licensed read passes `S` since the last
/// event, the licensed reads one VC path constrains observe one and the same `S`
/// (`reads_of_different_iterations_are_not_tied` in
/// `tests/discriminant_cse_owned_aggregate_realmir.rs` pins the cross-iteration
/// direction).
///
/// The license is per READ, not per aggregate: the drop-elaboration ladder's reads
/// after an arm body moved a payload out are refused, while the match's own re-reads
/// before it are licensed.
pub(super) fn unaliased_aggregate_licensed_reads(
    func: &VerifiableFunction,
    local: usize,
) -> Option<FxHashSet<StmtPoint>> {
    use trust_types::LocalWrite;

    fn roots_at(place: &Place, local: usize) -> bool {
        place.local == local
    }
    /// `Some(true)` if `op` moves out of a place rooted at `local`; `None` for an
    /// operand this scan cannot see into (fail closed).
    fn operand_moves(op: &Operand, local: usize) -> Option<bool> {
        match op {
            Operand::Move(p) => Some(roots_at(p, local)),
            Operand::Copy(_) | Operand::Constant(_) | Operand::Unsupported { .. } => Some(false),
            // A lifted machine-semantics formula may name anything; and
            // `#[non_exhaustive]`: an operand this scan does not know.
            _ => None,
        }
    }
    fn any_move<'a>(ops: impl IntoIterator<Item = &'a Operand>, local: usize) -> Option<bool> {
        let mut moved = false;
        for op in ops {
            moved |= operand_moves(op, local)?;
        }
        Some(moved)
    }

    if local == 0 || crate::local_defs::is_parameter(func, local) {
        return None;
    }
    let blocks = &func.body.blocks;
    // The id==index invariant every whole-CFG walk here relies on.
    if blocks.iter().enumerate().any(|(i, b)| b.id.0 != i) {
        return None;
    }
    let mut construction: Option<StmtPoint> = None;
    // Where an invalidation takes effect: the program point it reaches first.
    // ENTRY is the first event.
    let mut starts: Vec<StmtPoint> = vec![(0, 0)];
    for (b, block) in blocks.iter().enumerate() {
        for (i, stmt) in block.stmts.iter().enumerate() {
            match stmt.local_write(local) {
                LocalWrite::Untouched => {}
                LocalWrite::WholeNamed(Rvalue::Aggregate(..)) if construction.is_none() => {
                    construction = Some((b, i));
                }
                LocalWrite::WholeNamed(_)
                | LocalWrite::WholeOpaque
                | LocalWrite::Partial
                | LocalWrite::Escape
                | LocalWrite::Unlocatable => return None,
            }
            // The cell-aware escape question (INTERIOR-MUT-CHANNEL-1); every borrow is
            // refused below in any case.
            if crate::stmt_escapes_local(func, stmt, local) {
                return None;
            }
            let event = match stmt {
                Statement::Assign { rvalue, .. } => match rvalue {
                    // Condition 3: no borrow of it, of ANY kind.
                    Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place)
                        if roots_at(place, local) =>
                    {
                        return None;
                    }
                    Rvalue::Unsupported { operands, .. } => {
                        // A reborrow / fake borrow of the place travels as an operand.
                        if operands.iter().any(|op| {
                            matches!(op, Operand::Copy(p) | Operand::Move(p) if roots_at(p, local))
                        }) {
                            return None;
                        }
                        any_move(operands, local)?
                    }
                    Rvalue::Use(op)
                    | Rvalue::UnaryOp(_, op)
                    | Rvalue::Cast(op, _)
                    | Rvalue::Repeat(op, _) => any_move([op], local)?,
                    Rvalue::BinaryOp(_, a, c)
                    | Rvalue::CheckedBinaryOp(_, a, c)
                    | Rvalue::UncheckedBinaryOp(_, a, c) => any_move([a, c], local)?,
                    Rvalue::PtrOffset { ptr, count } => any_move([ptr, count], local)?,
                    Rvalue::Aggregate(_, ops) => any_move(ops, local)?,
                    Rvalue::Ref { .. }
                    | Rvalue::AddressOf(..)
                    | Rvalue::Discriminant(_)
                    | Rvalue::Len(_)
                    | Rvalue::CopyForDeref(_) => false,
                    // `#[non_exhaustive]`: an rvalue this scan does not know may do
                    // anything with the place.
                    _ => return None,
                },
                Statement::StorageLive(l) | Statement::StorageDead(l) => *l == local,
                _ => false,
            };
            if event {
                starts.push((b, i + 1));
            }
        }
        let terminator = &block.terminator;
        let dropped = match terminator.local_write(local) {
            LocalWrite::Untouched => false,
            LocalWrite::Partial if matches!(terminator, Terminator::Drop { .. }) => true,
            LocalWrite::WholeNamed(_)
            | LocalWrite::WholeOpaque
            | LocalWrite::Partial
            | LocalWrite::Escape
            | LocalWrite::Unlocatable => return None,
        };
        let moved = match terminator {
            Terminator::Call { args, .. } | Terminator::TailCall { args, .. } => {
                any_move(args, local)?
            }
            Terminator::SwitchInt { discr, .. } => any_move([discr], local)?,
            Terminator::Assert { cond, .. } => any_move([cond], local)?,
            Terminator::Goto(_)
            | Terminator::Return
            | Terminator::Drop { .. }
            | Terminator::Opaque { .. }
            | Terminator::Unreachable
            | Terminator::Resume => false,
            // `#[non_exhaustive]`: a terminator this scan does not know, fail closed.
            _ => return None,
        };
        if dropped || moved {
            super::path_defs::for_each_full_graph_terminator_target(terminator, |s| {
                starts.push((s.0, 0));
            });
        }
    }
    let (s_block, s_stmt) = construction?;

    // Walk forward from every event over the full graph (unwind edges included); the
    // construction `S` ends a walk. Every `Discriminant` read of `local` a walk meets
    // is reachable from an event without an intervening `S`.
    let mut unlicensed: FxHashSet<StmtPoint> = FxHashSet::default();
    let mut entered: FxHashSet<usize> = FxHashSet::default();
    while let Some((b, start)) = starts.pop() {
        let Some(block) = blocks.get(b) else {
            continue;
        };
        // A block entered at its top is walked once; a mid-block start (an event
        // inside it) is walked from that point regardless.
        if start == 0 && !entered.insert(b) {
            continue;
        }
        let stop = (b == s_block && s_stmt >= start).then_some(s_stmt);
        let end = stop.unwrap_or(block.stmts.len());
        for j in start..end.min(block.stmts.len()) {
            if let Statement::Assign { rvalue: Rvalue::Discriminant(src), .. } = &block.stmts[j]
                && roots_at(src, local)
            {
                unlicensed.insert((b, j));
            }
        }
        if stop.is_none() {
            super::path_defs::for_each_full_graph_terminator_target(&block.terminator, |s| {
                starts.push((s.0, 0));
            });
        }
    }

    let mut licensed = FxHashSet::default();
    for (b, block) in blocks.iter().enumerate() {
        for (j, stmt) in block.stmts.iter().enumerate() {
            if let Statement::Assign { rvalue: Rvalue::Discriminant(src), .. } = stmt
                && roots_at(src, local)
                && !unlicensed.contains(&(b, j))
            {
                licensed.insert((b, j));
            }
        }
    }
    Some(licensed)
}

/// Trust (2026-09-25, TRUST-09): the RESULT of a primitive-integer `Ord::cmp`, as a
/// global fact on every discriminant temp read from it.
///
/// # What was wrong
///
/// A `#[derive(Ord)]` enum whose variants carry data (regex-syntax 0.8.10's
/// `Utf8Sequence`) lowers `cmp` to
///
/// ```text
/// _3 = discriminant((*_1)); _4 = discriminant((*_2)); _6 = &_3; _7 = &_4;
/// _5 = <isize as Ord>::cmp(copy _6, copy _7) -> bb1
/// bb1: _8 = discriminant(_5); switchInt(move _8) -> [0: bb3, otherwise: bb2]
/// ```
///
/// and bb3's `match (self, other)` ends in `_ => unreachable`, dead exactly because
/// `_8 == 0` (`Equal`) means `_3 == _4`. The extractor rewrites that pinned, compiler-
/// authenticated primitive comparison to `TRUST_TOTAL_CLONE_SENTINEL`
/// (`trust_mir_extract::convert::is_pinned_total_std_primitive_cmp_call`) — a total
/// call with a HAVOCKED result — so `Equal` said nothing about `_3` and `_4`, and the
/// `unreachable` arm was refuted with `_3 = 0, _4 = 1` under `Equal`.
///
/// # Why it is this call and nothing else
///
/// The sentinel is ambiguous in general (`lt`/`le`/`gt`/`ge`/`eq`/`ne` share it, as do
/// derived and container calls), which is why `unwrap_panic::std_partial_eq_callee`
/// refuses to read equality into it. A sentinel call whose DESTINATION is
/// `core::cmp::Ordering` and whose two arguments are shared references to the SAME
/// primitive integer type is `<P as Ord>::cmp` for that primitive `P` and nothing else:
/// the other primitive comparisons return `bool`; `partial_cmp` returns
/// `Option<Ordering>`; a derived or container comparison takes references to its
/// OWN (non-primitive) `Self` type; no other sentinel rewrite returns `Ordering`.
/// core's `Ord for P` is the integer order — `Less` (-1) iff `a < b`, `Equal` (0) iff
/// `a == b`, `Greater` (1) iff `a > b` — which is the fact emitted, as one complete
/// case split over the three.
///
/// # Gates (all fail-closed)
///
///  * the call's destination is a whole local of the std `Ordering` shape
///    ([`is_std_ordering_ty`]) whose ONE value is this call
///    (`local_defs::unique_value_call`);
///  * each argument is a local whose one value is `&X`, `X` a whole local holding one
///    value on every channel (one whole named `Assign`, or a parameter never written)
///    of a primitive integer type below 128 bits, and both `X` have the same type — so
///    `*arg` at the call is `X`'s one value;
///  * each tied temp's one value is `discriminant(dest)`;
///  * the function's control flow is LOOP-FREE
///    (`structural_termination::is_control_flow_loop_free`). The fact is relational
///    and global; with every local on it defined at most once per execution, it is
///    true at every point where the temp holds its value, and before that point the
///    temp is never read. A loop could pair a temp from one iteration with an operand
///    from the next.
pub(crate) fn build_primitive_int_cmp_facts(func: &VerifiableFunction) -> Vec<Formula> {
    // PERF-COMPILER-VCGEN-586: skip the block scan entirely when the body has no
    // bare-dest Call terminator.
    if !super::terminator_presence_for(func).has_bare_dest_call {
        return Vec::new();
    }
    let sentinel = trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL;
    let mut facts = Vec::new();
    // Candidates first, from the terminators alone, so a body with no such call — the
    // common case — pays one pass over its blocks and no seam walk.
    let calls: Vec<(&Terminator, usize, &Operand, &Operand)> = func
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            term @ Terminator::Call { func: callee, args, dest, target: Some(_), .. }
                if callee == sentinel
                    && args.len() == 2
                    && dest.projections.is_empty()
                    && !crate::local_defs::is_parameter(func, dest.local)
                    && crate::local_ty_ref(func, dest.local).is_some_and(is_std_ordering_ty) =>
            {
                Some((term, dest.local, &args[0], &args[1]))
            }
            _ => None,
        })
        .collect();
    if calls.is_empty() || !trust_types::structural_termination::is_control_flow_loop_free(func) {
        return facts;
    }
    // `X` holds one value on every channel: one whole named `Assign` and nothing else,
    // or — a parameter — its entry value and no write of any kind.
    let holds_one_value_everywhere = |x: usize| {
        if crate::local_defs::is_parameter(func, x) {
            crate::local_defs::holds_one_value(func, x)
                && crate::local_defs::every_write_is_whole_named(func, x)
        } else {
            crate::local_defs::unique_value_def(func, x).is_some()
        }
    };
    // The primitive integer local `X` an argument `r` points at, when `r`'s one value is
    // `&X` and `X` holds one value.
    let pointee_int_local = |arg: &Operand| -> Option<(usize, &Ty)> {
        let (Operand::Copy(r) | Operand::Move(r)) = arg else { return None };
        if !r.projections.is_empty() || crate::local_defs::is_parameter(func, r.local) {
            return None;
        }
        let Some(Rvalue::Ref { mutable: false, place: x }) =
            crate::local_defs::unique_value_def(func, r.local)
        else {
            return None;
        };
        if !x.projections.is_empty() || !holds_one_value_everywhere(x.local) {
            return None;
        }
        let ty = crate::local_ty_ref(func, x.local)?;
        let narrow_int = match ty {
            Ty::Int { width, .. } => *width < 128,
            Ty::PtrSizedInt { .. } => true,
            _ => false,
        };
        narrow_int.then_some((x.local, ty))
    };
    for (term, dest, lhs, rhs) in calls {
        // The destination's one value must be THIS call — the terminator the candidate
        // came from, not another call writing the same local.
        if !crate::local_defs::unique_value_call(func, dest).is_some_and(|t| std::ptr::eq(t, term))
        {
            continue;
        }
        let (Some((a, a_ty)), Some((b, b_ty))) = (pointee_int_local(lhs), pointee_int_local(rhs))
        else {
            continue;
        };
        if a_ty != b_ty {
            continue;
        }
        let a = Formula::Var(crate::place_to_var_name(func, &Place::local(a)), Sort::Int);
        let b = Formula::Var(crate::place_to_var_name(func, &Place::local(b)), Sort::Int);
        let dest_place = Place::local(dest);
        for block in &func.body.blocks {
            for stmt in &block.stmts {
                let Statement::Assign { place: t, rvalue: Rvalue::Discriminant(src), .. } = stmt
                else {
                    continue;
                };
                if *src != dest_place
                    || !t.projections.is_empty()
                    || crate::local_defs::is_parameter(func, t.local)
                {
                    continue;
                }
                if !matches!(
                    crate::local_defs::unique_value_def(func, t.local),
                    Some(Rvalue::Discriminant(read)) if *read == dest_place
                ) {
                    continue;
                }
                let tag = Formula::Var(crate::place_to_var_name(func, t), Sort::Int);
                let case = |k: i128, rel: Formula| {
                    Formula::And(vec![
                        Formula::Eq(Box::new(tag.clone()), Box::new(Formula::Int(k))),
                        rel,
                    ])
                };
                facts.push(Formula::Or(vec![
                    case(-1, Formula::Lt(Box::new(a.clone()), Box::new(b.clone()))),
                    case(0, Formula::Eq(Box::new(a.clone()), Box::new(b.clone()))),
                    case(1, Formula::Gt(Box::new(a.clone()), Box::new(b.clone()))),
                ]));
            }
        }
    }
    facts
}

/// `core::cmp::Ordering` as the extractor spells it: an enum of exactly `Less = -1`,
/// `Equal = 0`, `Greater = 1`.
fn is_std_ordering_ty(ty: &Ty) -> bool {
    let Ty::Adt { name, variants, .. } = ty else { return false };
    name == "core::cmp::Ordering"
        && variants.len() == 3
        && variants
            .iter()
            .zip([("Less", -1), ("Equal", 0), ("Greater", 1)])
            .all(|(v, (n, d))| v.name == n && v.discriminant == d && v.fields.is_empty())
}

/// Trust (2026-09-25, TRUST-09): whether a `Discriminant` read of `src` (`*L`,
/// `L: &T`) reads the pointee of a shared-reference PARAMETER that stays frozen for
/// the whole body — the post-barrier half of arm (a) of
/// [`build_discriminant_cse_facts`], and one of the two pre-barrier admissions of it
/// (DISC-CSE-PRE-BARRIER-WRITE-1); its doc carries the soundness argument. All of:
///
///  * `src` canonicalizes — the fold `place_to_var_name` names it by — to exactly
///    `*P`, with `P` a parameter of this function (`*(_9.0)` with
///    `_9 = (copy _1, copy _2)` is `*_1`);
///  * `P` is declared `&T`, shared, and is pinned (`local_defs::pointer_is_pinned`:
///    its entry value only, and no alias of its own storage a callee could reseat it
///    through), so `*P` names the protected bytes at every read;
///  * `T` has no `UnsafeCell` at any inline position ([`ty_is_inline_freeze`]).
fn frozen_shared_param_referent(func: &VerifiableFunction, src: &Place) -> bool {
    let canon = crate::canonical_place(func, src);
    frozen_shared_param_referent_canon(func, &canon)
}

fn frozen_shared_param_referent_canon(func: &VerifiableFunction, canon: &Place) -> bool {
    if !matches!(canon.projections.as_slice(), [trust_types::Projection::Deref]) {
        return false;
    }
    let p = canon.local;
    if !crate::local_defs::is_parameter(func, p) {
        return false;
    }
    let Some(Ty::Ref { mutable: false, inner }) = crate::local_ty_ref(func, p) else {
        return false;
    };
    crate::local_defs::pointer_is_pinned(func, p)
        && ty_is_inline_freeze(&func.body.datatype_defs, inner)
}

/// True iff no `UnsafeCell` lies at any INLINE position of `ty` — the bytes a `&ty`
/// covers — so a protected `&ty` makes all of them immutable: the one structural
/// predicate, [`super::ty_may_hold_unsafe_cell`] (fail-closed on a by-name marker the
/// body's table does not define, a generic parameter, `Unsupported`, `dyn`, a `Vec`,
/// whose `Ty::Seq` drops its allocator parameter, and an ADT with no recorded part; a
/// reference or raw pointer is a frozen address whose pointee is not inline). Trust:
/// 2026-10-15 (INTERIOR-MUT-CHANNEL-1): this walk granted on
/// `!name.contains("UnsafeCell")`, so a `Cell` rendered without its fields passed.
fn ty_is_inline_freeze(defs: &trust_types::DatatypeDefs, ty: &Ty) -> bool {
    !super::ty_may_hold_unsafe_cell(defs, ty)
}

/// True iff every terminator that can run code other than this body is a call of a
/// safe, non-foreign Rust function that makes no atomic write, or a `Drop` (whose
/// glue runs safe `Drop::drop` impls) — the barriers arm (a)'s post-barrier half
/// admits, mirroring `contracts::safe_shared_collection_call_preserves_local`. An
/// `Opaque` terminator or a tail call refuses, and so does any terminator this match
/// does not know.
fn every_barrier_is_a_safe_rust_call(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().all(|block| match &block.terminator {
        Terminator::Call { is_foreign, is_unsafe_sig, atomic, .. } => {
            !*is_foreign && !*is_unsafe_sig && atomic.is_none()
        }
        Terminator::Goto(_)
        | Terminator::SwitchInt { .. }
        | Terminator::Return
        | Terminator::Assert { .. }
        | Terminator::Drop { .. }
        | Terminator::Unreachable
        | Terminator::Resume => true,
        Terminator::TailCall { .. } | Terminator::Opaque { .. } => false,
        // `Terminator` is `#[non_exhaustive]`: a terminator this walk does not know
        // may run code, so it refuses.
        _ => false,
    })
}

/// Per-ADT discriminant range bound (Lever A). For each `d = Discriminant(src)`
/// read whose SOURCE place resolves to a modeled enum, conjoin the membership fact
/// `d ∈ {variant tags}` — the phantom-tag refutation that collapses the spurious
/// `__type_tag` obligation explosion (a read of a 3-variant enum can only produce
/// a discriminant in its variant tag set, so a solver counterexample with a
/// phantom tag `d = 7` is impossible). This is derived at the
/// `Rvalue::Discriminant` read from the modeled datatype itself; unlike the
/// caller-constructible `SwitchInt::exhaustive_enum_unreachable` hint, it does
/// not grant authority to a serialized switch flag.
///
/// SOUNDNESS: the bound is the enum's OWN TYPE INVARIANT — every inhabitant of the
/// enum carries a discriminant drawn EXACTLY from its variants' tags, so the
/// membership disjunction is a TRUE fact about THE VALUE THE READ PRODUCES.
///
/// THAT IS A FACT ABOUT A VALUE, NOT ABOUT A LOCAL, and the two diverge the moment
/// the local receiving it has a SECOND definition. The fact is emitted against a
/// local's var name; `generate::safety` conjoins the global set into `vc.formula`
/// BEFORE `conjoin_preconditions_versioned_recorded` version-renames the whole
/// formula, so it is renamed in lockstep with the body and binds that block's
/// TERMINAL version of the local EXACTLY — a version the discriminant read never
/// produced. A branch merge then makes the membership FALSE of the value actually
/// held, the path condition goes UNSAT, and everything on it is vacuously proved and
/// kernel-certified.
///
/// LIVE FALSE PROVE at 70a7534fd1, on the CAST destination:
///   `let d = if c { e as usize } else { b }; arr[d]`
/// lowers to `bb1: _6 = Discriminant(_1); _5 = move _6 as u64` / `bb2: _5 = copy _3`,
/// so the cast destination `_5` IS the merged local, `d ∈ {0,1}` bound it globally,
/// and the always-out-of-bounds `arr[d]` at `d = 4` verified `1 proved, 0 failed`
/// rc=0 while panicking on 58 of 132 swept inputs. Both destinations — the
/// `Discriminant` dest and the `as`-cast dest — therefore carry
/// `is_single_static_assignment`; `merged_enum_cast_index_still_refutes` is the row.
///
/// The SOURCE-keyed canonical name (`discriminant_formula_var_name`) needs no such
/// gate and gets none: it denotes `src`'s discriminant, and every value `src` can
/// ever hold is an inhabitant of the same enum, so the membership survives any
/// reassignment of `src`.
///
/// GATING THE CAST DESTINATION IS NOT ENOUGH ON ITS OWN. The cast fact
/// `(_5 as ToTy) ∈ {tags}` is a claim about the value `_5` holds, and `_5`'s value
/// is the cast of `_6` — so it is true only if `_6` STILL holds the discriminant
/// where the cast runs. A merged/reseated `_6` (bb1 `_6 = Discriminant(e)`, bb2
/// `_6 = copy b`, bb3 `_5 = move _6 as u64`) makes `_5` arbitrary while `_5` itself
/// is perfectly single-assignment, and the fact false-PROVES the `arr[_5]` bounds
/// row. So the cast arm gates BOTH the cast dest AND the `Discriminant` dest it
/// reads; `merged_disc_dest_cast_index_still_refutes` is the row.
///
/// With every destination on that chain gated the fact deletes only IMPOSSIBLE
/// counterexamples (a phantom tag matching no variant), never a real one
/// (whose witness already carries
/// a valid tag): the OOB-index / div-by-zero canaries are violated even with EVERY
/// discriminant in range, so this fact leaves them refuted. The tag set is the
/// ACTUAL per-variant `VariantDef.discriminant` (or the positional `0..n` for a
/// `Ty::Datatype`), NOT a `0..n-1` interval — a `#[repr]` enum with non-contiguous
/// discriminants (`A = 5, B = 10`) is bounded by `d ∈ {5, 10}`, never the unsound
/// `0 <= d <= 1`, so a valid `d = 10` is never (false-)excluded. Emitted over BOTH
/// the dest's native var name (default lane) and the canonical generated
/// discriminant name (native CHC path), so it attaches whichever lane lowered
/// the read; an unmatched name is inert.
///
/// Trust (UNINHABITED MATCH ARM, false REFUTATION): the tag set is
/// [`inhabited_enum_variant_tag_set`], i.e. the declared tags MINUS every variant
/// whose payload is PROVABLY uninhabited. `Result<u8, Infallible>` is bounded by
/// `d ∈ {0}`, not `{0, 1}`, so the dead `Err` arm's `Unreachable` block stops being
/// accused. rustc's OWN lowering already omits an uninhabited variant's `SwitchInt`
/// target (measured: `switch _2 { 0 => .., 2 => .., otherwise => Unreachable }` for
/// `enum E3 { A(u8), B(Infallible), C(u8) }`), so the declared-but-impossible tag was
/// the only thing keeping that block satisfiable. See that function for the soundness
/// argument; the `tags.is_empty()` guard below is the fail-closed half of it.
pub(super) fn build_discriminant_variant_range_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let mut facts = Vec::new();
    // The statement-version oracle, built on first need (only a REASSIGNABLE
    // discriminant destination asks it — see `discriminant_dest_establish_name`).
    let mut versions: Option<std::rc::Rc<super::StmtVersionCtx>> = None;
    let mut int_casts_by_src_local: Option<FxHashMap<usize, Vec<(&Place, u32, bool)>>> = None;
    for (block_index, block) in func.body.blocks.iter().enumerate() {
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { place: dest, rvalue: Rvalue::Discriminant(src), .. } = stmt
            else {
                continue;
            };
            // Resolve the SOURCE place's type to a modeled enum and read its
            // actual per-variant discriminant tag set. `None` (struct, by-name
            // datatype ref the body's table does not define, unresolvable, or
            // non-ADT) yields no fact — conservative. RESOLVED through the body's
            // datatype table: a recursive enum is a bare by-name marker at every use
            // site, and reading the marker instead of its definition silently dropped
            // the whole fact (see `crate::place_ty_resolved_cow`).
            let Some(src_ty) = crate::place_ty_resolved_cow(func, src) else {
                continue;
            };
            let Some(tags) = inhabited_enum_variant_tag_set(src_ty.as_ref()) else {
                continue;
            };
            // FAIL CLOSED on an empty set. It arises two ways — a `Ty::Adt` whose
            // declared variants are empty (no fact was ever emitted for one) and, since
            // the uninhabited filter, a source enum EVERY variant of which is dead. The
            // membership over an empty set is the unsatisfiable `false`, and these facts
            // are GLOBAL to the function: publishing it would erase every overflow /
            // bounds / div-by-zero obligation in the body from one dead-place read.
            // MEASURED, not argued — delete this `continue` and both `+` rows of
            // `tests/fixtures/uninhabited_all_dead_source_mir.json` go `Failed` ->
            // `Proved`, two real `u8` overflows discharged by a premise about a place
            // the body never reads (`tests/uninhabited_arm_realmir.rs` fires there). The
            // read's infeasibility is a PATH property; a whole-function premise is the
            // wrong carrier for it, so emit nothing.
            if tags.is_empty() {
                continue;
            }
            // Trust (REPR-U128-HIGH-TAG-1, defense in depth): FAIL CLOSED when the
            // `Formula::Int` tags do not denote values this read can put in `dest`.
            // The live case was a `#[repr(u128)]` tag above `i128::MAX`, which the
            // extractor stored as the lossy `val as i128` (`u128::MAX` as `-1`):
            // this fact said `_3 ∈ {0, -1, 5}` about a `u128` read whose
            // `SwitchInt` label renders the TRUE `u128::MAX`, the arm for that
            // variant was UNSAT, and every row in it — `x + 1`, `a[i]`,
            // `unreachable_unchecked()` — was proved under the default policy and
            // certify. The extractor now lowers such an enum to `Unsupported`, so
            // no extracted body reaches here with one; this gate keeps a SERIALIZED
            // or hand-built body (an older dump) from reopening the lie. Every name
            // below — the canonical carrier, the dest, its pinned token and the
            // cast destination — is a claim about the same read, so the whole read
            // is skipped. Same rule as `abstract_interp::discriminant_read_hull`.
            if !discriminant_tags_denote_dest_values(func, dest, &tags) {
                continue;
            }
            // Build `d ∈ {tags}` over the dest var name (default lane) AND the
            // canonical generated discriminant name (native CHC path). Either
            // name may be the one a VC references; the other is inert.
            //
            // The DEST name is gated on single assignment (see the header): on a
            // reassigned dest the fact binds a value the read never produced. The
            // SOURCE-keyed canonical name is not — it names `src`'s discriminant,
            // which is an inhabitant of this enum however often `src` is reseated.
            let discr_name =
                crate::discriminant_formula_var_name(&crate::place_to_var_name(func, src));
            let dest_is_ssa =
                super::callee_summaries::is_single_static_assignment(func, dest.local);
            let mut tag_var_sets: Vec<(String, std::borrow::Cow<'_, [i128]>)> =
                vec![(discr_name, std::borrow::Cow::Borrowed(tags.as_slice()))];
            if dest_is_ssa {
                tag_var_sets.push((
                    crate::place_to_var_name(func, dest),
                    std::borrow::Cow::Borrowed(tags.as_slice()),
                ));
            } else if let Some(pinned) = discriminant_dest_establish_name(
                func,
                versions.get_or_insert_with(|| super::stmt_versions_for(func)),
                block_index,
                stmt_idx,
                dest,
            ) {
                // Trust (RESULT DISCRIMINANT DOMAIN, false REFUTATION): a destination
                // that is NOT single-assignment loses the bare-name fact above, and
                // before this arm it lost the bound ENTIRELY — while the `SwitchInt`
                // that consumes it still reads the value through the version token
                // the read's own statement mints (`_4#s2_0`). Nothing constrained that
                // token, so the `otherwise -> Unreachable` arm of an exhaustive match
                // was refuted with an impossible tag. Measured on orca-daemon
                // (bc52b0880, seal 321aaeda7): `[unreach] FAILED` at
                // `termination_signals.rs:40` with `_5#s2_0 = -1` for a
                // `Result<Signal, Errno>`, whose tags are `{0, 1}`.
                //
                // What disqualifies the destination is usually not the destination at
                // all: ONE `Terminator::Opaque` (an indirect or `-> !` fn-pointer call)
                // or one `Unsupported`/intrinsic statement anywhere in the body is an
                // unlocatable write to EVERY local (`local_defs::LocalWrite::
                // Unlocatable`), so every local fails `is_single_static_assignment`.
                //
                // SOUNDNESS: the fact is pinned to the token that denotes EXACTLY the
                // value this statement wrote — the same enum type invariant as the
                // bare-name arm, stated about the same value. The token denotes that
                // value only while no UNVERSIONED write (a partial or alias store, an
                // unlocatable asm/`Unsupported` write) can intervene, which
                // `discriminant_dest_establish_name` checks by position.
                tag_var_sets.push((pinned, std::borrow::Cow::Borrowed(tags.as_slice())));
            }
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
            //
            // Trust (P0 raw-vs-NORMALIZED discriminant FALSE PROOF — the SECOND
            // consumer of the `guards.rs::normalize_raw_discriminant` lesson, and the
            // WORSE one: this fact is GLOBAL, conjoined by `build_global_invariant_facts`
            // onto EVERY VC of the function). While `VariantDef::discriminant` still
            // STORED the extractor's RAW BIT PATTERN — always non-negative in its `i128`
            // carrier, `-1` under `#[repr(i8)]` arriving as `255` — the old
            // `tags.iter().all(|&t| t >= 0)` gate was VACUOUS for every signed repr and
            // the "negative tags take the loose path" promise two paragraphs above was
            // never actually enforced. Live witness:
            //
            //     #[repr(i8)] enum E { A = 0, B = -1 }        // patterns {0, 255}
            //     fn f(e: E, arr: &[u8; 256]) -> u8 { arr[e as usize] }
            //
            // the raw gate passed, the cast-destination fact `_3 ∈ {0, 255}` was emitted,
            // and the bounds VC `_3 < 256` PROVED — while `E::B as usize` really is
            // `0xFFFF_FFFF_FFFF_FFFF` and the index panics.
            // `normalized_nonneg_tag_set` reinterprets each pattern as its TRUE SIGNED
            // VALUE first (mirroring `guards.rs::normalize_raw_discriminant` and the
            // native bridge's `normalize_disc`), so that enum's tag set is `{0, -1}`, the
            // gate declines, and NO cast-destination fact is emitted — exactly the loose
            // path this site already documents as its intent.
            //
            // PREMISE CORRECTED 2026-08-31 (this paragraph asserted the opposite as a
            // LIVE convention, which is now false and is exactly the convention that
            // would make the `guards.rs` signed->unsigned cast lane unsound). Since
            // `b4fd4c0e43a` repair #1, extraction DECODES the tag at the single boundary
            // (`trust_mir_extract::ty_convert`'s `decode_discr_tag`; an enum with a tag
            // it cannot decode is `Unsupported` since REPR-U128-HIGH-TAG-1), so
            // `VariantDef::discriminant` — and therefore `enum_variant_tag_set`, and
            // therefore the `dest`/`discr` facts above — carries the TRUE SIGNED tag,
            // not the raw pattern. That is the correct fact and nothing here needs to
            // change: `normalize_raw_discriminant` is IDEMPOTENT on an already-decoded
            // value (`normalize(-1, 8, true) == -1`), so `normalized_nonneg_tag_set`
            // gives the same verdict on either spelling. The RULE the old paragraph was
            // reaching for still stands and is what must be preserved: NORMALIZE before
            // any ORDER comparison on a declared discriminant, and never normalize an
            // equality against a tag variable that carries whatever the tag facts carry
            // (same split as `guards.rs`). DO NOT re-raw the tags to match this comment's
            // former claim — `guards.rs`'s `Ite(Ge(c,0), c, c + 2^64)` cast relation
            // would then take its POSITIVE arm on `_4 == 255` and false-PROVE
            // `_d < 256`.
            if dest_is_ssa {
                let casts_by_src = int_casts_by_src_local.get_or_insert_with(|| {
                    let mut map: FxHashMap<usize, Vec<(&Place, u32, bool)>> = FxHashMap::default();
                    for cast_block in &func.body.blocks {
                        for cast_stmt in &cast_block.stmts {
                            // The cast must read a whole local and target an integer
                            // type (so `∈ {tags}` is meaningful). The cast destination
                            // is gated on single assignment for the same reason as the
                            // `Discriminant` dest, and it is the destination the LIVE
                            // false PROVE went through (see the header: `let d = if c {
                            // e as usize } else { b }`).
                            if let Statement::Assign {
                                place: cast_dest,
                                rvalue:
                                    Rvalue::Cast(
                                        Operand::Copy(p) | Operand::Move(p),
                                        Ty::Int { width: to_w, signed: to_s },
                                    ),
                                ..
                            } = cast_stmt
                                && p.projections.is_empty()
                                && cast_dest.projections.is_empty()
                                && super::callee_summaries::is_single_static_assignment(
                                    func,
                                    cast_dest.local,
                                )
                            {
                                map.entry(p.local)
                                    .or_default()
                                    .push((cast_dest, *to_w, *to_s));
                            }
                        }
                    }
                    map
                });
                if let Some(casts) = casts_by_src.get(&dest.local)
                    && let Some(normalized_tags) =
                        normalized_nonneg_tag_set(func, dest, src_ty.as_ref(), &tags)
                {
                    for &(cast_dest, to_w, to_s) in casts {
                        // Fold each NORMALIZED tag (the value the cast actually
                        // reads) through the destination type (mod 2^w + sign
                        // reinterpretation); dedup — a narrowing cast can collapse
                        // distinct tags onto one residue.
                        let mut cast_tags: Vec<i128> = normalized_tags
                            .iter()
                            .map(|&t| truncate_nonneg_tag_as_int(t, to_w, to_s))
                            .collect();
                        cast_tags.sort_unstable();
                        cast_tags.dedup();
                        tag_var_sets.push((
                            crate::place_to_var_name(func, cast_dest),
                            std::borrow::Cow::Owned(cast_tags),
                        ));
                    }
                }
            }
            for (var_name, tag_set) in tag_var_sets {
                let var = Formula::Var(var_name, Sort::Int);
                match tag_set.as_ref() {
                    [] => {}
                    [t] => {
                        facts.push(Formula::Eq(Box::new(var), Box::new(Formula::Int(*t))));
                    }
                    tags => {
                        let cases: Vec<Formula> = tags
                            .iter()
                            .map(|&t| Formula::Eq(Box::new(var.clone()), Box::new(Formula::Int(t))))
                            .collect();
                        facts.push(Formula::Or(cases));
                    }
                }
            }
        }
    }
    facts
}

/// Trust (REPR-U128-HIGH-TAG-1): whether `tags` — a `Discriminant` source's
/// `VariantDef::discriminant` set, stated as `Formula::Int` terms — denotes the
/// values a `dest = Discriminant(src)` read can produce.
///
/// A NON-NEGATIVE tag means the same number under every integer type, so a set of
/// them always qualifies (the historical behaviour, unchanged). A NEGATIVE tag
/// qualifies only when `dest` is a SIGNED integer: under an unsigned `dest` (in
/// practice the `u128` read of a `#[repr(u128)]` enum whose tag above `i128::MAX`
/// was stored as the lossy `val as i128`) the read never produces it, and a
/// membership fact over it is FALSE — it deletes the real tag and makes the arm
/// that tests it vacuous. An unresolvable `dest` with a negative tag declines too.
///
/// Fail-closed: it only ever suppresses a fact. The rule is
/// `abstract_interp::transfer::discriminant_read_hull`'s, which already returns
/// `None` for a negative tag under an unsigned `dest`; this is the same decision
/// for the membership fact and for `assert_refutation`'s discriminant pin.
pub(super) fn discriminant_tags_denote_dest_values(
    func: &VerifiableFunction,
    dest: &Place,
    tags: &[i128],
) -> bool {
    if tags.iter().all(|&tag| tag >= 0) {
        return true;
    }
    matches!(
        crate::place_ty_cow(func, dest).as_deref(),
        Some(Ty::Int { signed: true, .. } | Ty::PtrSizedInt { signed: true })
    )
}

/// The version-pinned name of the value a `dest = Discriminant(src)` statement
/// WRITES — `dest#s{block}_{stmt_idx}` — or `None` when no such name is licensed.
///
/// The statement-version oracle spells the value a place holds just after
/// statement `k` of block `b` as `s{b}_{k}` exactly when `k` is the LAST write of
/// that place before the point that the oracle VERSIONS (`StmtVersionCtx::
/// version_token_at` → `FnWrites::last_writer_before`). Asked at `stmt_idx + 1` for
/// the statement's own whole-local destination, the answer is therefore
/// `s{b}_{stmt_idx}` — the token of THIS write. A later whole `Assign`, a call
/// destination, a join with another definition or a loop havoc gets a different token
/// (`s{b}_{k'}`, a joined `s{b}_0_s{c}_1`, `s{b}_pre`, an `e45_` havoc) and is
/// untouched by a fact keyed on this one.
///
/// THE ORACLE DOES NOT VERSION EVERY WRITE. A field store, a store through a `&mut`
/// alias, and every UNLOCATABLE statement (an `Unsupported`/intrinsic statement) can
/// change the local while later reads keep the token `s{b}_{stmt_idx}`. (An `Opaque`
/// terminator — inline asm with `out(reg)` operands — was one too until 2026-10-08; it
/// now versions every local, H3 OPAQUE-ASM-OUTPUT, and the gate below still refuses
/// it.) Pinning across one of those is a premise about a value the
/// read did not produce: measured 2026-10-01 (review of 0a16a57648), an
/// `Opaque{InlineAsm}` or an `Unsupported` statement between the read and the
/// `SwitchInt` turned a correct refutation of the `otherwise` arm into `Proved`. So the
/// pin is ALSO gated on [`crate::local_defs::stmt_dest_fact_is_version_pinnable_at`]:
/// no partial or alias write of the local anywhere, and no unlocatable write that can
/// run after this read and be observed in this body. A diverging `Opaque` with no
/// successor (the orca shape — `exit` at the seal, a `fn() -> !` pointer on main)
/// passes; one with any successor, or any unlocatable statement, after the read does
/// not.
///
/// FAIL CLOSED: a projected destination (`_5.0 = Discriminant(..)`) is refused —
/// the whole-local spelling is the one this pin is argued for — and so is any answer
/// other than exactly `s{b}_{stmt_idx}` (no token, an entry token, a phantom, a
/// join): a fact under a name that does not denote this write would be a premise
/// about some other value.
///
/// Loop iterations share the token, and that is fine: every execution of the
/// statement writes an inhabitant's tag, so the fact is true of whichever execution
/// the token stands for.
fn discriminant_dest_establish_name(
    func: &VerifiableFunction,
    versions: &super::StmtVersionCtx,
    block_index: usize,
    stmt_idx: usize,
    dest: &Place,
) -> Option<String> {
    if !dest.projections.is_empty() {
        return None;
    }
    if !crate::local_defs::stmt_dest_fact_is_version_pinnable_at(
        func,
        dest.local,
        block_index,
        stmt_idx,
    ) {
        return None;
    }
    let block = func.body.blocks.get(block_index)?.id;
    let name = crate::place_to_var_name(func, dest);
    let token = versions.version_token_at(func, block, stmt_idx + 1, &name)?;
    let (b_str, k_str) = token.strip_prefix('s')?.split_once('_')?;
    ((b_str == "0" || !b_str.starts_with('0'))
        && (k_str == "0" || !k_str.starts_with('0'))
        && b_str.parse::<usize>().ok() == Some(block.0)
        && k_str.parse::<usize>().ok() == Some(stmt_idx))
    .then(|| format!("{name}#{token}"))
}

/// Trust (coroutine executor-protocol premise, the FALSE-REFUTATION fix): the
/// resume-state membership `selector ∈ live_states` of a recognized coroutine
/// RESUME body, published as a WHOLE-BODY fact next to the enum-validity bound
/// above and for exactly the same reason.
///
/// # What went wrong without it
///
/// `4ca0cb0eac` made rustc's `ResumedAfter{Return,Panic,Drop}` sentinel a real
/// refutable `Assertion` row and kept the `Unreachable` row of an
/// `exhaustive_enum_unreachable` switch. Both changes are RIGHT — neither the
/// message spelling nor the serialized exhaustiveness bit is proof authority in
/// a public TrustIR input, so neither may erase a row. What it did not do is
/// supply the premise those rows must be DECIDED under. The rows' only
/// reachability condition is a claim about the resume selector
/// (`sel == RETURNED` on the sentinel arm, `sel ∉ cases` on the `otherwise`
/// arm); on the refutation convention SAT = refuted, so an unconstrained
/// selector REFUTES both and the verifier accused correct code. `sel` is this
/// doc's shorthand for the resume-selector local; the diagnostics print the MIR
/// local name.
///
/// # Why a GLOBAL fact and not a per-path premise
///
/// [`trust_types::coroutine_resume_state_contract`] declines unless the selector
/// is written EXACTLY ONCE in the whole body (counting statement destinations
/// and `Call` dests) and that one write is the entry block's
/// `Discriminant(frame)` read. So the value this fact speaks about is the same
/// value at every program point, which is the definition of a whole-body fact.
/// Conjoining it globally also means it survives the `MAX_PATHS_PER_BLOCK`
/// collapse in `v2_build_path_guard_map`, which a per-path premise does not.
///
/// # Authority
///
/// This adds NO trust beyond the recognizer the bridge, the compiler and
/// `coroutine_sentinel::coroutine_sentinel_refutation_vcs` already share. The
/// premise is discharged NOWHERE here: it is the CALLER's obligation, published
/// as the `contract:coroutine-resume-state` / `assumption:coroutine` row, and
/// `stamp_coroutine_conditional_rows` demotes every `Proved` row of such a body
/// out of `Proved` before it can read as an unconditional proof. Emission is
/// untouched — this conditions rows, it never prunes one.
///
/// # Fail-closed gates
///
/// Every doubt yields NO fact (and therefore today's behavior exactly):
///  * the recognizer declines (not an `async fn` resume body, a `gen`/async-drop
///    shape, a frame-state write before the entry read, a reserved arm that is
///    not a verified panic sentinel, …);
///  * the entry dispatch operand is not the whole-local the recognizer named;
///  * the selector is not integer-sorted (a non-integer selector takes a
///    different `guard_to_formula` spelling and the fact would constrain
///    something other than a state number);
///  * the body carries a write channel the destination counter cannot see —
///    see [`selector_write_channel_is_unaccountable`]. The recognizer's counter
///    only sees a write where a DESTINATION PLACE names the target; without this
///    belt "written once" would not imply "single-valued", and the whole-body
///    fact would speak about a value that changed;
///  * an empty live set (impossible per
///    `coroutine_resume_contract_states_are_valid`, which requires non-empty and
///    containing `UNRESUMED = 0`, but an empty `Or` is `false` and would
///    vacuously prove EVERY row — the mirror-image accident, refused explicitly).
///
/// The fact is spelled through the SAME [`crate::guards::guard_to_formula`] path
/// the entry dispatch's own path guards go through, so its selector symbol
/// unifies with theirs by construction rather than by a name coincidence a sort
/// or token change could silently break into an inert conjunct. It is emitted
/// BARE (unversioned) like every other global fact: the block-VC lane conjoins
/// the global set and then version-renames the whole formula at the consuming
/// block's terminal, so the fact and the row's own reads are renamed together.
pub(super) fn build_coroutine_resume_state_facts(func: &VerifiableFunction) -> Vec<Formula> {
    let Some(contract) = trust_types::coroutine_resume_state_contract(&func.body) else {
        return Vec::new();
    };
    let Some(entry) = func.body.blocks.first() else {
        return Vec::new();
    };
    let Terminator::SwitchInt { discr, .. } = &entry.terminator else {
        return Vec::new();
    };
    // (belt) the dispatch operand must be the whole-local selector the recognizer
    // named; anything else and we do not know what we would be constraining.
    if !matches!(
        discr,
        Operand::Copy(place) | Operand::Move(place)
            if place.projections.is_empty() && place.local == contract.discr_local
    ) {
        return Vec::new();
    }
    // (belt) integer-sorted, like every real resume-state selector (`u32`).
    if !matches!(crate::local_ty_ref(func, contract.discr_local), Some(Ty::Int { .. })) {
        return Vec::new();
    }
    if selector_write_channel_is_unaccountable(func, contract.discr_local) {
        return Vec::new();
    }
    let terms: Vec<Formula> = contract
        .live_states
        .iter()
        .map(|state| {
            guards::guard_to_formula(
                func,
                &GuardCondition::SwitchIntMatch { discr: discr.clone(), value: *state },
            )
        })
        .collect();
    match terms.len() {
        0 => Vec::new(),
        1 => terms,
        _ => vec![Formula::Or(terms)],
    }
}

/// Is there any write channel to `local` that the recognizer's
/// "written exactly once" counter provably cannot see? `true` ⇒ DECLINE.
///
/// That counter enumerates DESTINATION PLACES (`Assign` / `SetDiscriminant` /
/// `Deinit` statements and `Call` dests), so it sees a write only where a place
/// names the target. [`trust_types::WriteEffect::FailClosedOrBackstopped`] is
/// the class the model's own taxonomy declares un-capturable by a place-keyed
/// analysis, so this is the missing half of the single-assignment premise —
/// without it "written once" does not mean "single-valued", and the whole-body
/// fact would be about a value that changed.
///
/// Three channels, each refused:
///  * an ALIAS out of the selector — see
///    [`rvalue_opens_an_alias_channel_to`], which decides this arm over an
///    ANCHORED match on every `Rvalue` variant rather than a short allowlist;
///  * any `FailClosedOrBackstopped` statement or terminator anywhere in the
///    body that carries no destination place, so no counter can attribute it;
///    refuse the whole body rather than reason about what it might touch.
///    `Deinit` and `Drop` are in that class too but ARE place-attributed, so
///    they are excluded here and handled by name;
///  * a `Drop` OF the selector, whose glue receives `&mut place`.
///
/// The residual this does NOT cover is a pointer FORGED from an integer
/// (`_p = k as *mut u32`) aimed at the selector's slot. Nothing in this crate
/// models that — `place_names_overlap`, the version oracle and every other
/// single-assignment-gated fact in this module have exactly the same exposure —
/// so it is a property of the place-keyed model, not of this fact.
fn selector_write_channel_is_unaccountable(func: &VerifiableFunction, local: usize) -> bool {
    use trust_types::WriteEffect;
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue, .. } = stmt
                && rvalue_opens_an_alias_channel_to(rvalue, local)
            {
                return true;
            }
            if matches!(stmt.write_effect(), WriteEffect::FailClosedOrBackstopped)
                && !matches!(stmt, Statement::Deinit { .. })
            {
                return true;
            }
        }
        // A `Call` DESTINATION naming the selector. THIS ARM IS INERT TODAY AND NO TEST
        // CAN KILL IT: `coroutine_resume_state_contract` tallies `Terminator::Call
        // { dest }` itself and requires `writes == 1` while also requiring the entry
        // `Discriminant` read, so a `Call` writing the selector is always a SECOND write
        // and the contract declines before this belt runs. It is named anyway because
        // the doc above scopes this predicate to "any write channel the counter provably
        // cannot see", and a reader checking that scope against the code found `Call`
        // missing and had to go read the recognizer to learn it was covered elsewhere.
        // Naming it makes the belt readable on its own and stops the recognizer's tally
        // from being the single point of failure for this channel. Monotone: it can only
        // withdraw the fact, i.e. turn PROVE into FAIL, never the reverse.
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            return true;
        }
        if let Terminator::Drop { place, .. } = &block.terminator
            && place.local == local
        {
            return true;
        }
        if matches!(block.terminator.write_effect(), WriteEffect::FailClosedOrBackstopped)
            && !matches!(block.terminator, Terminator::Drop { .. })
        {
            return true;
        }
    }
    false
}

/// Does this `Rvalue` hand out a reference to — or otherwise carry unmodeled
/// semantics over — `local`? `true` ⇒ the selector's single-assignment premise
/// is not accountable and [`build_coroutine_resume_state_facts`] must DECLINE.
///
/// # Why this is a match and not an `Rvalue::Ref | AddressOf | CopyForDeref`
/// # allowlist
///
/// The allowlist it replaces let `Rvalue::Unsupported` through, and
/// `Unsupported` is exactly where an alias hides: `trust-mir-extract`'s
/// `convert.rs` mints it for `mir::Rvalue::Reborrow` carrying
/// `Operand::Copy(place)` — the reborrowed place itself, i.e. a handle out of
/// `place` whose aliasing semantics the extractor explicitly declines to model
/// ("fail closed rather than assert it behaves as a plain `&place`"). A belt
/// that fails closed downstream of a producer that failed closed upstream must
/// not then treat the marker as an ordinary value read.
///
/// # The anchor
///
/// `Rvalue` is `#[non_exhaustive]`, so a foreign crate cannot write a match the
/// compiler will reject when a variant is added. The next best thing, and what
/// this is, is a match that NAMES every variant that exists today and routes the
/// wildcard to `true` — DECLINE. A variant added upstream therefore withdraws
/// the fact for every body until someone classifies it here, instead of silently
/// joining the value-only arm. `coverage.rs`'s `Rvalue` inventory is the list
/// this was written against.
fn rvalue_opens_an_alias_channel_to(rvalue: &Rvalue, local: usize) -> bool {
    // A `Place` in an alias-producing position, or an `Operand` in a position
    // whose semantics are unmodeled: either one names `local` or it does not.
    let names = |place: &trust_types::Place| place.local == local;
    // `Operand` is `#[non_exhaustive]` too, and its wildcard fails closed for
    // the same reason the `Rvalue` one does — except that here the wildcard is
    // LIVE, not merely future-proofing: `Operand` also has `Symbolic` (a lifted
    // machine-semantics formula) and the unrepresentable-payload sentinel today,
    // and neither can be said NOT to name the selector.
    let operand_names = |operand: &Operand| match operand {
        Operand::Copy(place) | Operand::Move(place) => names(place),
        Operand::Constant(_) => false,
        _ => true,
    };
    match rvalue {
        // ALIAS PRODUCERS: the only ways a pointer/reference to a local can come
        // into existence, and therefore the precondition of every pointer write.
        Rvalue::Ref { place, .. } | Rvalue::AddressOf(_, place) | Rvalue::CopyForDeref(place) => {
            names(place)
        }
        // UNMODELED SEMANTICS over an operand that may be a place stand-in for an
        // alias (`mir::Rvalue::Reborrow` is lowered exactly this way). The whole
        // point of the marker is that we do not know what it does.
        Rvalue::Unsupported { operands, .. } => operands.iter().any(operand_names),
        // Pointer arithmetic. The base is a pointer VALUE, so naming the selector
        // here would already be the forged-pointer residual — but it costs
        // nothing to refuse, and refusing keeps the "any unmodeled use of the
        // selector withdraws the fact" rule uniform.
        Rvalue::PtrOffset { ptr, count } => operand_names(ptr) || operand_names(count),
        // VALUE-ONLY: these read operands and produce values. Reading the
        // selector's VALUE creates no channel by which it can be written.
        Rvalue::Use(_)
        | Rvalue::BinaryOp(..)
        | Rvalue::CheckedBinaryOp(..)
        | Rvalue::UncheckedBinaryOp(..)
        | Rvalue::UnaryOp(..)
        | Rvalue::Cast(..)
        | Rvalue::Aggregate(..)
        | Rvalue::Discriminant(_)
        | Rvalue::Len(_)
        | Rvalue::Repeat(..) => false,
        // THE ANCHOR. A variant that did not exist when this was written is
        // unclassified, so it is unaccountable. Fail closed.
        _ => true,
    }
}

/// The actual discriminant tag set of a MODELED enum type, in declaration order.
/// `Ty::Adt` carries the real `VariantDef.discriminant` per variant (so a
/// `#[repr]` enum's explicit non-contiguous tags are honored); a `Ty::Datatype`
/// carries no discriminant and its tags are read as `0..n`. That reading is sound
/// ONLY because every `Ty::Datatype` producer emits one solely for an enum whose
/// discriminants ARE positional (`Ty::Datatype`'s DISCRIMINANTS doc,
/// DATATYPE-POSITIONAL-TAGS); before that gate, a crate named `clean_kernel` with a
/// `#[repr(u8)] level::Level { Zero = 7, .. }` got `d ∈ {0, 1}` here — false. `None` for a struct, a by-name
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

/// The shared raw-discriminant normalizer, re-exported from `crate::guards` so the
/// convention lives in ONE place. The two lanes previously carried byte-identical copies
/// under a "MUST stay byte-identical" comment — a divergence hazard for exactly the
/// soundness rule they encode: NORMALIZE before any ORDER comparison on a declared
/// discriminant, and never normalize an equality against a tag variable that itself
/// carries the raw pattern. The native bridge keeps its own `normalize_disc` /
/// `sign_extend_raw_value` (`trust-ir-bridge` `lower.rs`) because it is a separate crate;
/// keep those in sync with this one.
use crate::guards::normalize_raw_discriminant;

/// The `(width, signed)` carrier a `#[repr(iN)]`/`#[repr(uN)]` hint names.
fn enum_repr_hint_width_signed(hint: trust_types::EnumReprHint) -> (u32, bool) {
    use trust_types::EnumReprHint as H;
    match hint {
        H::U8 => (8, false),
        H::U16 => (16, false),
        H::U32 => (32, false),
        H::U64 => (64, false),
        H::I8 => (8, true),
        H::I16 => (16, true),
        H::I32 => (32, true),
        H::I64 => (64, true),
    }
}

/// Trust (P0 raw-vs-NORMALIZED discriminant FALSE PROOF): the enum's declared tag set as
/// TRUE SIGNED VALUES, or `None` when the set may not be treated as non-negative.
///
/// `raw_tags` are the extractor's RAW BIT PATTERNS (`VariantDef::discriminant`), always
/// non-negative in their `i128` carrier, so testing them for `>= 0` directly is VACUOUS.
/// Each pattern is reinterpreted per the discriminant's own repr `(width, signed)` before
/// the gate.
///
/// The repr is read from EVERY signal the model carries, and a tag is admitted only when
/// ALL of them agree on ONE non-negative value:
///   * the MIR discriminant temp's DECLARED type (`disc_dest`, the local the cast reads)
///     — REQUIRED; a non-integer / unresolvable type declines outright. This is the
///     signal `guards.rs` uses.
///   * the enum's `#[repr]` hint, when the extractor captured one;
///   * the layout tag / niche scalar's width+signedness, when a layout is present.
/// Requiring AGREEMENT (not just "the first signal says non-negative") is what closes the
/// widened-carrier variant of the same hole: an `isize` discriminant temp over a
/// `repr(i8)` enum would sign-extend `255` at 64 bits and still look non-negative, but the
/// `I8` repr signal reports `-1`, so the set is declined. Any disagreement, any negative,
/// any missing/undecodable signal ⇒ `None` ⇒ NO cast-destination fact (fail-closed: a
/// missed proof, never a false one).
fn normalized_nonneg_tag_set(
    func: &VerifiableFunction,
    disc_dest: &Place,
    enum_ty: &Ty,
    raw_tags: &[i128],
) -> Option<Vec<i128>> {
    let mut candidates: Vec<(u32, bool)> = Vec::new();
    // The value that is actually cast: the MIR discriminant temp.
    let disc_ty = crate::place_ty_cow(func, disc_dest)?;
    candidates.push((disc_ty.int_width()?, disc_ty.is_signed()));
    if let Ty::Adt { faithful_enum_repr, enum_layout, .. } = enum_ty {
        if let Some(Some(hint)) = faithful_enum_repr {
            candidates.push(enum_repr_hint_width_signed(*hint));
        }
        if let Some(layout) = enum_layout {
            // MERGE (b62 <- origin/main; squash d24c671211): `Untagged` is a variant this branch
            // added to `EnumTagEncodingInfo`; upstream's match predates it. An untagged image
            // carries NO tag lane at all, so there is no tag width/signedness to offer
            // as a normalization candidate. FAIL CLOSED by contributing nothing: the
            // candidate list keeps only the MIR discriminant temp's own width (and any
            // faithful repr hint), and if that cannot normalize every raw tag to one
            // agreed non-negative value the caller already returns `None`. Pushing a
            // fabricated width here would be exactly the P0 enum-discriminant
            // narrowing-cast false proof this function exists to prevent.
            let hint = match &layout.encoding {
                trust_types::EnumTagEncodingInfo::Direct { tag_ty, .. } => Some(*tag_ty),
                trust_types::EnumTagEncodingInfo::Niche { niche_ty, .. } => Some(*niche_ty),
                trust_types::EnumTagEncodingInfo::Untagged => None,
            };
            if let Some(hint) = hint {
                candidates.push(enum_repr_hint_width_signed(hint));
            }
        }
    }
    let mut normalized = Vec::with_capacity(raw_tags.len());
    for &raw in raw_tags {
        let mut agreed: Option<i128> = None;
        for &(width, signed) in &candidates {
            let value = normalize_raw_discriminant(raw, width, signed);
            if value < 0 {
                return None;
            }
            match agreed {
                None => agreed = Some(value),
                Some(seen) if seen == value => {}
                Some(_) => return None,
            }
        }
        normalized.push(agreed?);
    }
    Some(normalized)
}

/// Trust (UNINHABITED MATCH ARM, false REFUTATION): [`enum_variant_tag_set`]
/// narrowed to the variants that can actually OCCUR — the declared tag set minus
/// every variant PROVED uninhabited by [`ty_is_provably_uninhabited`].
///
/// THE DEFECT this closes. `match r { Ok(v) => .., Err(e) => match e {} }` over
/// `Result<u8, Infallible>` lowers to `_2 = Discriminant(r)`, `SwitchInt(_2) { 0
/// => ok_arm, otherwise => bb_unreachable }`. `Infallible` has NO inhabitants, so
/// `Err` cannot be the value's variant and the `Unreachable` block is dead by
/// construction — the code is CORRECT. The declared tag set `{0, 1}` nevertheless
/// satisfies the block's path condition `_2 != 0` at `_2 = 1`, so the `Unreachable`
/// row was REFUTED and the user's build failed. Dropping `Err` from the tag set
/// makes the fact `_2 == 0`, which refutes `_2 != 0` — the right answer, reached
/// by the SAME producer and the same authority as the non-empty case.
///
/// RE-MEASURED per row through the real `generate_vcs` +
/// `Router::deterministic_in_process_ay` + `trust_certify::certify_vc`, at HEAD and
/// with this filter, over a matrix of MIR dumped from source. Row totals are
/// deliberately not quoted — they describe the matrix, not the change, and cannot
/// be rechecked from the tree. The INVARIANTS can be:
///
///  * every row that leaves `Failed` goes to `PROVED` and KERNEL-CERTIFIES;
///  * NOT ONE refutation is lost, and no row `Proved` at HEAD regresses.
///
/// The rows that flip are the `Unreachable` sinks of `Result<u8, Infallible>`,
/// `Result<u8, Void>`, `Result<u8, !>`, `Result<u8, (u8, Infallible)>` and of each
/// adversarial body below. Two shapes are recorded as ALREADY PROVED AT HEAD and
/// so are NOT evidence for this filter: `Result<u8, Wrap(Infallible)>` and
/// `Result<u8, [Infallible; 1]>` matched with `Err(_) => 0`. What stays refuted is
/// the genuine violations: a real overflow, a div-by-zero, BOTH out-of-range reads
/// of `Idx { A(u8), B(Infallible), C(u8), D(u8), E(u8) }` indexed per-arm into
/// `[u8; 3]` (tags 3 and 4 are LIVE) whose dead tag-1 arm proves in the same body,
/// the reachable `unreachable!()` of a live sibling variant (refuted at its live
/// tag `_2 = 2`, witness byte-identical to HEAD), the two real `+` overflows of a
/// body whose scrutinee enum is WHOLLY uninhabited, and a lint row.
/// `[Infallible; 0]` and a union keep their tag — asserted at unit granularity in
/// `uninhabited_variant_tests`, since both were already `Proved` at HEAD here and
/// a row-level matrix cannot distinguish "declined" from "never accused".
///
/// EVERY ONE of those adversarial rows is MUTATION-CHECKED in
/// `tests/uninhabited_arm_realmir.rs`: mutate this function to
/// `.filter(|(v, _)| v.discriminant == 0)` — an over-eager filter that deletes the
/// LIVE tags — and the out-of-range reads, the live sibling's panic and the
/// wholly-uninhabited body's overflows all flip to `Proved`, firing three separate
/// assertions. A "must still refute" caption that no mutant can falsify is not
/// coverage; these were written until one could.
///
/// SOUNDNESS — the load-bearing part. This can only ever REMOVE tags, i.e. STRENGTHEN
/// a globally-published premise, so an error in the uninhabitedness judgement is a
/// FALSE PROOF, strictly worse than the false refutation it fixes. Three separate
/// walls hold it:
///
///  1. `ty_is_provably_uninhabited` is a THEOREM about the declared type, not a bit
///     that states the answer: a type is dropped only when the declaration itself
///     forces the value set empty (zero declared variants; every declared variant
///     carrying an uninhabited field; a product with an uninhabited component). It
///     fails closed — "inhabited" — on EVERY shape whose declaration does not settle
///     the question.
///  2. The tag set is read from the same `VariantDef` list, on the same channel and
///     with the same authority, that [`enum_variant_tag_set`] already publishes as
///     `d ∈ {tags}`. No verdict bit (`exhaustive_enum_unreachable` and friends) is
///     consulted; nothing here can be enabled by a flag in a serialized input.
///  3. If the filter empties the set the caller emits NO fact at all (its existing
///     `tags.is_empty()` guard). Publishing the empty membership would mean the
///     unsatisfiable `false`, and these facts are GLOBAL to the function — a `false`
///     would erase every overflow/bounds/div-by-zero obligation in the body, which is
///     exactly the false-proof channel this must not open. The infeasibility of a
///     discriminant read on a wholly-uninhabited place is a PATH property and does not
///     belong in a whole-function premise; declining it costs a proof, not soundness.
///
/// RESIDUAL — the SCALE cliff, and it is NOT a degenerate model from the solver.
/// The tag fact stops closing the `Unreachable` row once the block it guards is
/// reached by more than `MAX_PATHS_PER_BLOCK` (= 64) distinct paths: at that point
/// `v2_build_path_guard_map` (`generate::safety`, the `paths.clear()` arm) CLEARS
/// the block's guard set and substitutes ONE UNGUARDED path — and the same
/// degenerate map is returned for every block at once when the global BFS budget
/// (`steps > cap`) is exhausted, where the function returns `vec![Vec::new()]` for
/// EVERY block at once. A VC with no path condition asserts only "this block is
/// reachable", which is SAT however tight the published tag set is, so the row is
/// refuted again. That is a MECHANISM in deterministic vcgen code, not formula size
/// defeating the backend, and the `0 <= len` lane in
/// `type_ranges::conjoin_length_nonneg_bounds` hits the SAME wall at the SAME N.
/// Supplying the missing reachability condition is the collapse invariant's job,
/// in `generate::safety`: an `Unreachable` row's violation formula is content-free,
/// so on a degraded block that invariant re-conditions it on the block's in-edge
/// disjunction, or DECLINES it when no summary is available. The outcome on those
/// cells is therefore decided there, not by how tight this tag set is, and nothing
/// here should be tuned around them.
pub(super) fn inhabited_enum_variant_tag_set(ty: &Ty) -> Option<Vec<i128>> {
    // Only `Ty::Adt` carries per-variant FIELD types to judge. A `Ty::Datatype`'s
    // empty-`variants` spelling is a BY-NAME back-reference, never "zero variants"
    // (see `Ty::Datatype`'s own doc), so its structure is deliberately not read
    // here: it keeps the declared positional set unfiltered.
    match ty {
        Ty::Adt { variants, .. } if !variants.is_empty() => Some(
            variants
                .iter()
                .filter(|variant| !variant_is_provably_uninhabited(variant))
                .map(|variant| variant.discriminant)
                .collect(),
        ),
        _ => enum_variant_tag_set(ty),
    }
}

/// A declared variant is uninhabited exactly when one of its fields is: a value of
/// the variant is a PRODUCT of its field values, so a single empty factor empties
/// the product. A FIELDLESS variant (`None`, a unit variant) is the empty product,
/// which has exactly one value — INHABITED — and `any` correctly reports `false`
/// for it.
fn variant_is_provably_uninhabited(variant: &trust_types::VariantDef) -> bool {
    variant.fields.iter().any(|(_, field_ty)| ty_is_provably_uninhabited(field_ty))
}

/// Depth budget for [`ty_is_provably_uninhabited`]. Extraction cuts every recursive
/// ADT to a by-name `Ty::Datatype` marker, so a lowered `Ty` is a shallow finite
/// tree; this only bounds the cost of a pathologically deep (or adversarially
/// nested) serialized type. Exhausting it returns the fail-closed "inhabited".
const UNINHABITED_WALK_DEPTH: u32 = 24;

/// Trust (UNINHABITED MATCH ARM): is EVERY value of `ty` impossible — i.e. is the
/// type's declaration itself proof that no inhabitant exists?
///
/// `true` is an ASSERTION that the value set is empty and is consumed to delete a
/// discriminant tag, so it must be a theorem. `false` means "not proved
/// uninhabited" and is the answer for every shape below that is not listed as
/// `true`, INCLUDING every shape the model cannot resolve. The four `true` rules,
/// and why each is a theorem about the input program:
///
///  * `Ty::Never` — the primitive `!`. Empty by definition.
///  * an ENUM with ZERO declared variants (`enum Void {}`, `core::convert::Infallible`)
///    — a value of an enum is one of its variants, and there are none. The
///    `adt_kind == Some(Enum)` conjunct is what makes the emptiness READABLE: a
///    `Ty::Adt` carrying `variants: []` is ALSO how a STRUCT is spelled (`Ty::adt`),
///    and how every pre-Phase-4 serialized `Ty::Adt` deserializes, so `variants: []`
///    ALONE means nothing. `adt_kind` is stamped only by `trust-mir-extract` from
///    rustc's own `AdtDef` (`ty_convert::lower_enum_adt`), and every hand-built,
///    synthetic, or pre-W19 `Ty::Adt` leaves it `None` — which declines here.
///  * an ENUM all of whose declared variants are uninhabited (`enum E { A(Infallible),
///    B(Infallible) }`) — the value set is the union of the variants' value sets.
///    This rule is sound ONLY because the variant list is COMPLETE, never truncated:
///    `lower_enum_adt` either walks `adt_def.variants()` to the end or abandons the
///    whole type to a fail-closed `Ty::Unsupported` marker (its produced-node-budget
///    bail returns `produced_budget_degraded_leaf()`, its recursion back-edge returns
///    a by-name `Ty::Datatype`) — neither of which is an `Adt` and neither of which
///    reaches this arm. A partially-lowered enum can therefore never masquerade as an
///    all-dead one.
///  * a PRODUCT with an uninhabited component — a struct field, a tuple element, or
///    the element of an array of length >= 1. `[T; 0]` is DELIBERATELY EXCLUDED: it
///    holds exactly one value (the empty array) and IS inhabited however dead `T` is;
///    getting that backwards would bless UB. A fieldless struct is likewise the empty
///    product and stays inhabited. Truncating a product's component list could only
///    LOSE an uninhabited factor and answer "inhabited", so the product rules are
///    insensitive to any field-list degradation upstream.
///
/// EVERYTHING ELSE DECLINES, on purpose:
///  * `Ty::Unsupported` (incl. the pre-monomorphization `TyKind::Param` marker),
///    `Ty::Dynamic`, `Ty::Datatype` — unresolved / opaque / by-name; the declaration
///    is not in hand.
///  * `Ty::Adt { adt_kind: None | Some(Struct/Union with no dead field), .. }` — a
///    `None` kind is the un-migrated spelling and cannot be read as an enum. A UNION
///    declines unconditionally: rustc itself holds unions ALWAYS inhabited, and a
///    union's fields overlap rather than compose, so the product rule is not even the
///    right shape.
///  * `Ty::Ref` / `Ty::RawPtr` / `Ty::Slice` / `Ty::SymArray` — behind a pointer, or a
///    length that is a symbol rather than a number, so `len >= 1` is not decidable
///    here.
///  * `Ty::Closure` / `Ty::Coroutine` — their upvar lists are captures, not a complete
///    value decomposition on this side of the model.
fn ty_is_provably_uninhabited(ty: &Ty) -> bool {
    fn walk(ty: &Ty, depth: u32) -> bool {
        let Some(depth) = depth.checked_sub(1) else {
            return false;
        };
        match ty {
            Ty::Never => true,
            Ty::Adt { variants, adt_kind: Some(trust_types::AdtKind::Enum), .. } => variants
                .iter()
                .all(|variant| variant.fields.iter().any(|(_, field_ty)| walk(field_ty, depth))),
            Ty::Adt { fields, adt_kind: Some(trust_types::AdtKind::Struct), .. } => {
                fields.iter().any(|(_, field_ty)| walk(field_ty, depth))
            }
            Ty::Tuple(elems) => elems.iter().any(|elem| walk(elem, depth)),
            Ty::Array { elem, len } => *len >= 1 && walk(elem, depth),
            _ => false,
        }
    }
    walk(ty, UNINHABITED_WALK_DEPTH)
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
            if !is_single_static_assignment(func, dest.local) {
                continue;
            }
            // Unsigned operand — the index value is a non-negative `usize`.
            if !crate::operand_ty_cow(func, a).is_some_and(|t| t.is_integer() && !t.is_signed()) {
                continue;
            }
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
        Rvalue::Len(place) => super::callee_summaries::param_slice_len_place(func, place, fuel),
        Rvalue::Use(op) => stable_min_arg_formula(func, op, fuel),
        _ => None,
    }
}

/// `_t = CheckedSub(Copy/Move(L), c)` with `c >= 1`? Returns the decrement constant
/// `c` (`_t.0` is the decremented value `L - c`) for a self-decrement of `L`.
pub(super) fn checked_self_decrement_const(
    func: &VerifiableFunction,
    l: usize,
    t: usize,
) -> Option<i128> {
    if crate::local_defs::is_parameter(func, t) {
        return None;
    }
    let Some(Rvalue::CheckedBinaryOp(trust_types::BinOp::Sub, lhs, rhs)) =
        crate::local_defs::unique_value_def(func, t)
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

#[cfg(test)]
mod vec_length_benign_callee_tests {
    use super::vec_length_benign_callee as benign;

    #[test]
    fn std_vec_trait_methods_are_benign() {
        assert!(benign("<alloc::vec::Vec<u32> as core::ops::index::IndexMut<usize>>::index_mut"));
        assert!(benign(
            "<alloc::vec::Vec<u32> as core::ops::index::Index<std::ops::Range<usize>>>::index"
        ));
        assert!(benign("<std::vec::Vec<u32> as std::ops::DerefMut>::deref_mut"));
        assert!(benign("core::ops::index::Index::index"));
        assert!(benign("alloc::vec::Vec::<u32>::len"));
    }

    /// Review round 97: a user trait's associated fn spelled with a std ops `Self`, or
    /// with a std ops path inside its generic arguments, is not std's method.
    #[test]
    fn user_trait_methods_spelled_near_std_ops_are_not_benign() {
        for callee in [
            "<core::ops::range::Range<usize> as a1::Evil>::index",
            "<core::ops::RangeFull as a1::Evil>::deref_mut",
            "<alloc::vec::Vec<u32> as g1::My<<T as core::ops::Deref>::Target>>::index",
            "<alloc::vec::Vec<u32> as g1::Evil>::index",
            "<core::ops::range::Range<usize> as core::ops::index::Index<usize>>::index",
            "<alloc::vec::Vec<u32> as core::ops::index::Index<usize>>::index_mut",
            "<alloc::vec::Vec<u32> as core::ops::deref::Deref>::deref::<u8>",
            "mycrate::ops::Index::index",
        ] {
            assert!(!benign(callee), "{callee}");
        }
    }
}
