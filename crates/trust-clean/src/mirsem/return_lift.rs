// Return-shape recovery: straight-line and convergent return spines, guarded
// join locals, and the dominance queries they rest on. A return value is only
// admissible when a unique definition dominates the return block.

use super::*;

/// Recover the return witness (`SemReturn`) the reflection's return-extraction path
/// consumes: the SSA assignments to `_0`/temps plus the returned operand. Mirrors
/// `extract_return_formula`'s execution-order resolution:
///
///   1. walk the complete entry-to-`Return` spine and select its final reachable
///      bare `_0` writer (assignment or `contract_check_ensures` destination);
///   2. interpret that final definition:
///      * `_0 := Use(op)` with `op` a modeled scalar (param/const/move) → CLOSED
///        operand return (`ret = op`); the value is independent of the prefix.
///      * `_0 := BinaryOp(op,a,b)` (modeled) → SSA-TEMP return: the return traces the
///        assigned temp `_0`, so `ret = Var 0` (the return-place index) and the
///        prefix `stmts` carries `Assign(0, R)` the `exec` fold runs. This is the
///        case `extract_return_formula` resolves by tracing `_0` back through its
///        `Assign`.
///
/// Returns the witness only when the return resolves to a modeled scalar fragment
/// (closed param/const, or an exec-foldable SSA temp); `None` (fail-closed) for a
/// return outside the modeled fragment (non-arithmetic rvalue, call, loop, …).
///
/// The witness is meaningful only for a real entry-to-return execution trace.
/// Before reading statements or a return, require one acyclic linear spine from
/// `BlockId(0)` through `Goto`/successful `Assert` edges to the unique
/// `Return`. The only call admitted on that spine is rustc's inherited
/// `contract_check_ensures` wrapper. Every block must belong to the spine, so
/// an unreachable return/assignment island cannot be selected as the function's
/// observable result.
pub(crate) fn straight_line_return_spine(
    body: &trust_types::VerifiableBody,
) -> Option<Vec<&trust_types::BasicBlock>> {
    use std::collections::HashSet;

    use trust_types::{BlockId, Terminator};

    // The modeled observation has one return point. Every serialized block
    // must still be reachable from the real entry; otherwise a disconnected
    // decoy definition could be hidden outside the selected path.
    let ret = unique_return_block(body)?;
    let entry_reachable = cfg_reachable_from(body, BlockId(0))?;
    if entry_reachable.len() != body.blocks.len() {
        return None;
    }
    let reaches_return = |start: BlockId| -> Option<bool> {
        Some(cfg_reachable_from(body, start)?.contains(&ret.id))
    };

    let mut spine = Vec::new();
    let mut seen = HashSet::new();
    let mut current = BlockId(0);
    loop {
        if !seen.insert(current) {
            return None; // cycle before Return
        }
        let block = body.blocks.iter().find(|block| block.id == current)?;
        spine.push(block);
        match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => {
                current = *target;
            }
            Terminator::SwitchInt { targets, otherwise, .. } => {
                // rustc may place a checked-operation panic branch beside the
                // sole success path. Admit it only when exactly one DISTINCT
                // successor can reach the unique Return; a genuine two-way
                // returning branch belongs to the guarded-return lanes.
                let mut successors: Vec<BlockId> =
                    targets.iter().map(|(_, target)| *target).collect();
                successors.push(*otherwise);
                successors.sort_unstable_by_key(|id| id.0);
                successors.dedup();
                let mut returning = Vec::new();
                for successor in successors {
                    if reaches_return(successor)? {
                        returning.push(successor);
                    }
                }
                let [successor] = returning.as_slice() else { return None };
                current = *successor;
            }
            Terminator::Call {
                func,
                args,
                dest,
                target,
                atomic,
                is_foreign,
                is_unsafe_sig,
                ..
            } if crate::is_contract_check_ensures_callee(func)
                && args.len() == 2
                && crate::assignment_types::operand_matches_type(
                    body,
                    &args[1],
                    &body.return_ty,
                )
                && dest.local == 0
                && dest.projections.is_empty()
                && atomic.is_none()
                && !is_foreign
                && !is_unsafe_sig =>
            {
                current = target.as_ref().copied()?;
            }
            Terminator::Return => {
                return (block.id == ret.id).then_some(spine);
            }
            _ => return None,
        }
    }
}

pub(crate) fn straight_line_return_definition<'a>(
    body: &'a trust_types::VerifiableBody,
    spine: &[&'a trust_types::BasicBlock],
) -> Option<StraightLineReturnDefinition<'a>> {
    use trust_types::{Rvalue, Statement, Terminator};

    let mut definition = None;
    for block in spine {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            match statement {
                Statement::Assign { place, rvalue, .. } => {
                    // A projected write mutates only part of the return place and
                    // cannot be represented by the scalar final-definition model.
                    if place.local == 0 {
                        if !place.projections.is_empty() {
                            return None;
                        }
                        let selected =
                            crate::assignment_types::assigned_local_rvalue(body, statement, 0)?;
                        definition = Some(StraightLineReturnDefinition::Assignment {
                            rvalue: selected,
                            block: block.id,
                            statement: statement_index,
                        });
                    }
                    // Once a mutable/raw-mutable alias of `_0` exists, later writes
                    // through it escape every direct destination scan.  The exact
                    // straight-line return lane therefore declines the whole body.
                    if matches!(rvalue,
                        Rvalue::Ref { mutable: true, place }
                            | Rvalue::AddressOf(true, place)
                            if place.local == 0)
                    {
                        return None;
                    }
                }
                Statement::SetDiscriminant { place, .. }
                | Statement::Deinit { place }
                | Statement::Retag { place }
                    if place.local == 0 =>
                {
                    return None;
                }
                _ => {}
            }
        }
        match &block.terminator {
            Terminator::Call { func, args, dest, .. }
                if crate::is_contract_check_ensures_callee(func)
                    && args.len() == 2
                    && crate::assignment_types::operand_matches_type(
                        body,
                        &args[1],
                        &body.return_ty,
                    )
                    && dest.local == 0
                    && dest.projections.is_empty() =>
            {
                definition = Some(StraightLineReturnDefinition::ContractWrapper {
                    value: &args[1],
                    block: block.id,
                });
            }
            Terminator::Call { dest, .. } if dest.local == 0 => return None,
            Terminator::Drop { place, .. } if place.local == 0 => return None,
            _ => {}
        }
    }
    definition
}

/// Acyclic, fully convergent internal-control fallback for a return expression
/// that already reifies its guarded locals (for example two range checks joined
/// by a final `BitOr`).  Only the unique Return block enters the linear kernel
/// trace; every preceding branch-local value is resolved at that exact final use
/// by `sem_rvalue_of_mir_at_site`.
pub(super) fn convergent_return_block_spine(
    body: &trust_types::VerifiableBody,
) -> Option<Vec<&trust_types::BasicBlock>> {
    use trust_types::{BlockId, Rvalue, Statement, Terminator};

    let ret = unique_return_block(body)?;
    let reachable = cfg_reachable_from(body, BlockId(0))?;
    if reachable.len() != body.blocks.len()
        || !trust_types::structural_termination::is_loop_free(&body.blocks)
        || body.blocks.iter().any(|block| {
            !cfg_reachable_from(body, block.id).is_some_and(|set| set.contains(&ret.id))
        })
        || !local_has_only_guarded_writes(body, 0, 1, 0)
    {
        return None;
    }

    for block in &body.blocks {
        if !matches!(
            block.terminator,
            Terminator::Goto(_)
                | Terminator::SwitchInt { .. }
                | Terminator::Assert { .. }
                | Terminator::Return
        ) {
            return None;
        }
        for statement in &block.stmts {
            match statement {
                Statement::Assign { place, rvalue, .. } => {
                    if !place.projections.is_empty()
                        || (place.local != 0 && place.local <= body.arg_count)
                        || matches!(
                            rvalue,
                            Rvalue::Ref { mutable: true, .. } | Rvalue::AddressOf(true, _)
                        )
                    {
                        return None;
                    }
                    if place.local == 0 && block.id != ret.id {
                        return None;
                    }
                }
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                _ => return None,
            }
        }
    }
    Some(vec![ret])
}

pub(super) fn sem_return_of_mir(
    func: &trust_types::VerifiableFunction,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemReturn> {
    use trust_types::{Operand, Projection, Rvalue};
    let body = &func.body;
    let spine = straight_line_return_spine(body).or_else(|| convergent_return_block_spine(body))?;

    // Collect the preceding SSA assignments we model (Assign(local, modeled rvalue)).
    let mut stmts: Vec<SemStmt> = Vec::new();
    for block in &spine {
        for (statement_index, stmt) in block.stmts.iter().enumerate() {
            if let Some((place, rvalue)) = crate::assignment_types::assigned_rvalue(body, stmt) {
                if place.projections.is_empty()
                    && let Some(rv) = sem_rvalue_of_mir_at_site(
                        body,
                        rvalue,
                        param_index,
                        Some((block.id, Some(statement_index))),
                    )
                    && let Ok(idx) = u64::try_from(place.local)
                {
                    stmts.push(SemStmt { idx, rvalue: rv });
                }
            }
        }
    }

    let (last_to_0, last_to_0_site) = match straight_line_return_definition(body, &spine)? {
        StraightLineReturnDefinition::ContractWrapper { value, .. } => {
            // This lane models only direct parameter/constant wrapper operands;
            // non-parameter temps are declined by `sem_operand_of_mir`.  The
            // carried block site is consumed by the live grounder, whose wider
            // temp-reflection fragment needs exact dominance.
            let ret = sem_operand_of_mir(body, value, param_index)?;
            return Some(SemReturn { stmts, ret });
        }
        StraightLineReturnDefinition::Assignment { rvalue, block, statement } => {
            (rvalue, (block, Some(statement)))
        }
    };

    match last_to_0 {
        // `_0 := Use(op)`: the return value is the operand's — CLOSED operand return.
        Rvalue::Use(op) => {
            // CHECKED-ARITH RESULT RETURN (Trust: the `bounded_add`/`checked_sub`/`inc_gt`
            // shape). The lowering of `a + b` / `a - b` / `x + 1` is a CheckedBinaryOp
            // tuple `_t := CheckedBinaryOp(op, a, b)` followed by an OVERFLOW Assert on
            // `_t.1` and the value-field return `_0 := Use(Move/Copy _t.0)`. That field
            // projection makes `sem_operand_of_mir` decline (it only models bare scalar
            // places). Recognize it explicitly: `_t.0` IS the arithmetic result `op(a, b)`
            // (`resolve_checked_field_rvalue` mirrors `clean_ground::resolve_local_field`'s
            // `CheckedBinaryOp` arm), so this is the SAME SSA-TEMP return the direct
            // `_0 := BinaryOp/CheckedBinaryOp(...)` arm models — model it as
            // `Assign(0, Bin(op,a,b))` and return `Var 0`. The grounded result field 0
            // grounds identically to a bare `BinaryOp` (the `eval`/`ground_int`
            // denotation is `Int.<op> a b`), so the return-adequacy proof is the existing
            // env-threading `exec` fold (Lemma 1C SSA-temp). The OVERFLOW safety VC the
            // checked-op also raises is a SEPARATE axis (`function_fully_faithful_witness`
            // additionally requires it DISCHARGED), so this adequacy step alone never
            // closes an unguarded overflow — `unsafe_add` stays fail-closed there.
            if let Operand::Copy(p) | Operand::Move(p) = op {
                if let [Projection::Field(field)] = p.projections.as_slice() {
                    if let Some(rv) = resolve_checked_field_rvalue(
                        body,
                        p.local,
                        *field,
                        Some(last_to_0_site),
                        param_index,
                    ) {
                        stmts.push(SemStmt { idx: 0, rvalue: rv });
                        return Some(SemReturn { stmts, ret: SemOperand::Var(0) });
                    }
                    return None; // a field projection we do not model ⇒ fail closed
                }
            }
            let ret = sem_operand_of_mir(body, op, param_index)?;
            Some(SemReturn { stmts, ret })
        }
        // `_0 := BinaryOp(...)`: the return TRACES the assigned temp `_0` through the
        // arithmetic — SSA-TEMP return. The prefix `stmts` already contains the
        // modeled `Assign(0, R)`; the returned operand is the temp `Var 0` (the
        // return-place index, matching the `set` index `exec` writes).
        Rvalue::BinaryOp(..) | Rvalue::CheckedBinaryOp(..) => {
            // Confirm the assignment's rvalue is in the modeled fragment (else fail-closed).
            sem_rvalue_of_mir_at_site(body, last_to_0, param_index, Some(last_to_0_site))?;
            Some(SemReturn { stmts, ret: SemOperand::Var(0) })
        }
        // Trust: field-read leaf — `_0 := Cast(op, dest_ty)`, a SOUND WIDENING
        // integer cast (verified against `op`'s declared source type —
        // `resolve_widening_cast_rvalue`). The cast is the IDENTITY on the
        // unbounded `Int` carrier (zero-/sign-extension changes representation,
        // not value), so the return traces `op`'s OWN resolved value — INLINED,
        // one level of temp indirection (the SAME discipline as the
        // CheckedBinaryOp field arm above), e.g. `ArrayVec::len`'s
        // `_2 = (*self).0; _0 = _2 as u64; return`: `_2`'s single assignment is
        // the field-read, inlined directly as `_0`'s modeled value. SSA-TEMP
        // return: `ret = Var 0`.
        //
        // Trust: WALL-CAST-LEAF (2026-07-16) — the prefix loop above ALREADY
        // modeled `_0 := Cast(..)` into `stmts` (via `sem_rvalue_of_mir`'s new
        // Cast arm, which delegates to the SAME `resolve_widening_cast_rvalue`),
        // exactly as the `_0 := BinaryOp` SSA-temp arm relies on the prefix loop.
        // So this arm must NOT push a SECOND `idx: 0` statement (that would
        // DUPLICATE the return SSA write and break the `exec` fold). Confirm the
        // cast is value-preserving (fail-closed `?` otherwise) and reuse the
        // prefix `stmts`, mirroring the `BinaryOp`/`CheckedBinaryOp` arm.
        Rvalue::Cast(op, dest_ty) => {
            // Trust: W-CMP-DISCR — the `i16`/`i32`/`i64` `signum` shape `_0 :=
            // Cast(Discriminant(Cmp(self, 0)), iN)` joins the value-preserving
            // cast return here: `sem_rvalue_of_mir` (above) already modeled this
            // `_0 :=` statement as the three-way sign `ArithBin(..)` in `stmts`,
            // so the SSA-temp return traces `_0` exactly like the widening-cast
            // return does. Fail-closed: neither resolver accepting ⇒ `None`.
            resolve_widening_cast_rvalue(body, op, dest_ty, param_index, Some(last_to_0_site))
                .or_else(|| {
                    resolve_signum_cast_rvalue(body, op, dest_ty, param_index, Some(last_to_0_site))
                })?;
            Some(SemReturn { stmts, ret: SemOperand::Var(0) })
        }
        // Trust: DISCRIMINANT-AS-VALUE (M5 slice B, 2026-07-08) — `_0 :=
        // Discriminant(place)`, an ENUM-TAG READ used DIRECTLY as the return value
        // (`Ordering::as_raw`'s `_2 := &self; _0 := Discriminant((*_2)); return`) —
        // the VALUE-position sibling of the discriminant-GUARD leaf
        // (`switch_leaf`'s `Rvalue::Discriminant` arm, 4958c9fb59, which reads a
        // tag to COMPARE against a target inside a `SwitchInt`): here the tag IS
        // the return value, no comparison at all. A CLOSED operand return, like
        // the `Use(op)` arm above: [`SemOperand::Discriminant`] is an
        // operand-shaped, opaque `idx_elem`-carrier value (`return_is_closed`
        // already classifies it as closed, alongside `Index`/`Len`/`Field`/`Cast`)
        // rather than an SSA-assigned temp, so the prefix `stmts` needs no entry
        // for it — `ret` IS the modeled operand directly, exactly mirroring the
        // `Use(op)` arm's `ret: sem_operand_of_mir(...)`. Reuses
        // [`sem_discriminant_base_of_mir`] (extended this increment to ALSO
        // resolve through a locally-taken `&self`, not just a direct reference
        // receiver) — same fail-closed gates, no new ones. HONEST SCOPE: the
        // returned value is the SAME uninterpreted, total `idx_elem(base, -1)`
        // carrier the guard leaf already uses — it asserts nothing about the
        // tag's concrete bit pattern (not "2-variant", not "0/1 bool-shaped"), so
        // a 3-variant `Ordering` (`Less`/`Equal`/`Greater`) is denoted exactly as
        // honestly as a 2-variant enum would be.
        Rvalue::Discriminant(place) => {
            // Trust: W-CMP-DISCR — the `i8` `signum` shape `_0 :=
            // Discriminant(Cmp(self, 0))`, where the return local `_0` IS the i8
            // sign-carrier (no cast — the Ordering discriminant width equals the
            // return width). Recognize the three-way sign BEFORE the opaque
            // discriminant-as-value carrier: the prefix is exactly this one SSA
            // assignment `_0 := (self > 0) - (self < 0)`, an SSA-temp return.
            // Fail-closed: gated by `resolve_signum_ordering_sign` (Cmp-against-0
            // over the vendored `cmp::Ordering` sign encoding); a non-signum
            // discriminant read (`Ordering::as_raw`, `Either::is_left`) falls
            // through to the opaque carrier below, unchanged.
            if let Some(trust_types::Ty::Int { width, signed: true }) =
                body.locals.first().map(|l| &l.ty)
            {
                if let Some(sign_rv) = resolve_signum_ordering_sign(
                    body,
                    place,
                    *width,
                    true,
                    param_index,
                    Some(last_to_0_site),
                ) {
                    return Some(SemReturn {
                        stmts: vec![SemStmt { idx: 0, rvalue: sign_rv }],
                        ret: SemOperand::Var(0),
                    });
                }
            }
            let base =
                sem_discriminant_base_of_mir(body, place, param_index, Some(last_to_0_site))?;
            Some(SemReturn { stmts, ret: SemOperand::Discriminant(Box::new(base)) })
        }
        // Trust: OPTRES-ACCESSOR NOT-LEAF (2026-07-16) — `_0 := UnaryOp(Not, _t)`,
        // the `is_none`/`is_err` return: the FAITHFUL negation of the Bool-typed
        // tag-compare `_t := Eq(Discriminant((*self)), K)` (`is_some`/`is_ok`).
        // Modeled as the `Eq`↔`Ne`-flipped comparison (`resolve_not_of_bool_cmp`,
        // whose doc proves `Not(Eq a b) ≡ Ne a b ≡ Bool.not (Int.beq a b)`), an
        // SSA-temp return whose LAST `_0` assignment is the flipped `Cmp` — traced
        // through the env-threading `exec` fold exactly like the `_0 := Cmp(...)`
        // `is_some` return. Fail-closed on a non-Bool operand or an inner value
        // outside the flat `Eq`/`Ne` fragment. The `UnaryOp(Neg)` shape and any
        // other unary op decline here (unchanged from the prior `_ => None`).
        Rvalue::UnaryOp(trust_types::UnOp::Not, operand) => {
            let flipped =
                resolve_not_of_bool_cmp(body, operand, param_index, Some(last_to_0_site))?;
            stmts.push(SemStmt { idx: 0, rvalue: flipped });
            Some(SemReturn { stmts, ret: SemOperand::Var(0) })
        }
        // Trust: W-LEN-ISEMPTY (2026-07-17) — `_0 := UnaryOp(PtrMetadata, op)`, the
        // `slice::len`/`str::len` straight-line leaf: the return value IS the fat
        // pointer's metadata (the slice length). Resolve to the opaque-total
        // `SemOperand::Len(Var param)` carrier — a CLOSED operand return, EXACTLY like
        // the `Rvalue::Discriminant` discriminant-as-value arm above (`return_is_closed`
        // already classifies `Len` as closed alongside Discriminant/Index/Field), so
        // the prefix `stmts` needs no entry — `ret` IS the modeled operand directly.
        // `op` names a PARAM slice, possibly behind ONE verifiable same-fat-pointer
        // reinterpret `Cast` (`str::len`); all gates live in
        // `resolve_ptr_metadata_slice_len`. Fail-closed on a non-param / mutable /
        // reassigned base or an unverifiable cast. HONEST TIER:
        // uninterpreted-but-total, faithful to the MIR metadata read.
        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, operand) => {
            let len = resolve_ptr_metadata_slice_len(body, operand, param_index, last_to_0_site)?;
            Some(SemReturn { stmts, ret: len })
        }
        // Trust: W-LEN-ISEMPTY — the direct `_0 := Len(place)` return (the
        // `Rvalue::Len` spelling of the same slice-length leaf, e.g. an un-inlined
        // `slice::len`). Same closed-operand carrier and gates as the `PtrMetadata`
        // arm above (no cast passthrough — `Rvalue::Len` takes a place directly).
        Rvalue::Len(place) => {
            let len = slice_len_of_param_place(body, place, param_index)?;
            Some(SemReturn { stmts, ret: len })
        }
        _ => None,
    }
}

/// Trace a checked-arithmetic result's value field: `_0 := Use(Move/Copy _t.0)` where
/// `_t := CheckedBinaryOp(op, a, b)` ⇒ the returned rvalue is `op(a, b)`. This
/// recovers the THEN/ELSE arm value of a guarded return that flows through the
/// overflow-checked temporaries branch lowering inserts (e.g. `guarded_add`'s
/// `_0 := _5.0` where `_5 := CheckedAdd(a, b)`). Mirrors
/// `clean_ground::resolve_local_field`'s `CheckedBinaryOp` arm. `None` (fail-closed)
/// when the local is not a checked-arith field over modeled operands.
pub(super) fn resolve_checked_field_rvalue(
    body: &trust_types::VerifiableBody,
    local: usize,
    field: usize,
    use_site: Option<(trust_types::BlockId, Option<usize>)>,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemRvalue> {
    use trust_types::Rvalue;
    if field != 0 {
        return None;
    }
    // Trust: HOLE-2 SOUNDNESS — the tuple temp `local` must be assigned EXACTLY ONCE across
    // the whole body. This function searches `body.blocks` in vector order and returns the
    // FIRST assignment to `local`; without a uniqueness check, two branch ARMS whose checked
    // ops commit into the SAME tuple-temp local both resolve to the block-order-first
    // `CheckedBinaryOp` — so the second arm silently gets the first arm's value (e.g. the
    // ELSE arm of `if a>0 {a+1} else {a*5}` resolving to the THEN arm's `CheckedAdd`). The
    // loop path's `resolve_temp_copy` counts assignments and declines a multiply-assigned
    // local; this restores the same discipline. Trust (closure pass, 2026-07-05): upgraded to
    // the SHARED `local_soundly_resolvable` gate — ALSO declines a `local` written by a
    // `Terminator::Call` dest or a mutable alias (the write-set-completeness blind spot this
    // Assign-only scan shares with `collect_value_assignments`/`param_reassigned_by_stmt`).
    // Fail-closed.
    if !crate::prove::local_soundly_resolvable(body, local) {
        return None; // never, multiply-assigned, call-dest-written, or mutably aliased.
    }
    let rvalue = if let Some((use_block, use_statement)) = use_site {
        unique_local_definition_dominating(body, local, use_block, use_statement)?.2
    } else {
        body.blocks.iter().flat_map(|block| &block.stmts).find_map(|statement| {
            crate::assignment_types::assigned_local_rvalue(body, statement, local)
        })?
    };
    let Rvalue::CheckedBinaryOp(op, a, b) = rvalue else { return None };
    // Trust: W6 increment-3 (CAPTURING closures, 2026-07-18) —
    // resolve each operand through [`resolve_cast_source_operand`]
    // (bare leaf FIRST, then a struct-FIELD read, then ONE level of
    // temp indirection to those) instead of the bare
    // [`sem_operand_of_mir`] leaf. This lets `map_cap::{closure#0}`'s
    // `_3 = copy _1.0; _4 = CheckedAdd(copy _2, copy _3)` chase the
    // upvar field read `_1.0` (via the temp `_3`), moving the closure
    // body from SHAPE_GAP to its HONEST SAFETY_GAP (the Add-overflow
    // VC stays undischargeable spec-free). MONOTONE + byte-identical
    // for every pre-existing shape: `resolve_cast_source_operand`
    // tries the bare leaf first, so a param/const/`&self`-field
    // operand resolves EXACTLY as before; only a previously-declining
    // temp-held field read now resolves — the SAME field-read chase
    // the bitwise `Bin` arm already uses, sound (entry-time-value
    // gated) and adding no new discharge power.
    Some(SemRvalue::Bin(
        sem_binop_of_mir(op)?,
        resolve_cast_source_operand(body, a, param_index, use_site)?,
        resolve_cast_source_operand(body, b, param_index, use_site)?,
    ))
}

/// Resolve a guarded arm's assignment to the CONVERGENCE LOCAL `join_local` (`0`
/// for a direct join, or the temp `_t` of a join-via-temp guarded return —
/// `clamp`/`max`/`min`). A `UnaryOp(Neg)`
/// arm (`abs`'s `then` arm `_t := -x`) is now ADMITTED via the `-x ≡ 0 - x` identity
/// (modeled as `Bin Sub (Const 0) op`); any other arm value outside the `SemRvalue`
/// fragment (e.g. an array `Index`) still fail-closes (`None`).
pub(super) fn arm_value_rvalue_for(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemRvalue> {
    use trust_types::{Operand, Projection, Rvalue, Ty, UnOp};
    // The arm's last assignment to the convergence local is the value it returns.
    let (use_statement, rv) =
        arm.stmts.iter().enumerate().rev().find_map(|(statement_index, statement)| {
            crate::assignment_types::assigned_local_rvalue(body, statement, join_local)
                .map(|rvalue| (statement_index, rvalue))
        })?;
    match rv {
        // `_0 := Use(_t.0)`: the checked-arith value field — trace to op(a,b).
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [Projection::Field(_)]) =>
        {
            let Projection::Field(n) = p.projections[0] else { return None };
            resolve_checked_field_rvalue(
                body,
                p.local,
                n,
                Some((arm.id, Some(use_statement))),
                param_index,
            )
        }
        // `_join := -op` (the `abs` THEN arm `_t := -x`). MODEL the unary negation as
        // the binary `0 - op` (`Bin Sub (Const 0) op`): `-op ≡ 0 - op` is an integer
        // identity, and — crucially — `eval_rvalue e (Bin Sub (Const 0) op)` ι-reduces
        // to `Int.sub (Int.ofNat 0) (eval e op)`, the BYTE-EXACT term the LIVE
        // `clean_ground::ground_int` grounds a `Formula::Neg(op)` arm to
        // (`Int.sub (Int.ofNat 0) (g op)`). So the branch refinement (`refinementB`)
        // closes reflexively at this term WITHOUT a new `Rvalue` constructor (no
        // recursor change, no 4th axiom). Sound: the modeled `Bin Sub (Const 0) op`
        // denotes exactly `-op` over the integers. Fail-closed if `op` is not modeled.
        //
        // Trust: ABS VERDICT (int-preds corpus item 12, 2026-07-18 — DOCUMENT, do NOT
        // force). This Neg arm makes `iN::abs` reach the branch SHAPE, so
        // `core::num::<impl iN>::abs` is SAFETY_GAP (shape recognized), NOT SHAPE_GAP —
        // and it STAYS SAFETY_GAP, honestly. Its extracted MIR is
        //   bb0: _2 = Lt(self, 0);  SwitchInt(_2)[0 -> bb3 (identity), else -> bb1]
        //   bb1: _3 = Eq(self, iN::MIN);  Assert(!_3, "OverflowNeg") -> bb2
        //   bb2: _0 = Neg(self); ...     bb3: _0 = self; ...
        // The `self < 0` SwitchInt guard routes EVERY negative — INCLUDING `iN::MIN` —
        // into bb1, whose `OverflowNeg` Assert FIRES exactly when `self == iN::MIN`. So
        // abs's panic path is REACHABLE: `abs(iN::MIN)` genuinely panics (debug) / wraps
        // (release). Lemma 6 CERTIFIES the emitted `NegationOverflow` VC's ADEQUACY
        // (the core `Eq(self, MIN)` grounds def-eq to `neg_overflows_iW`, resolved
        // through the block definition that BINDS the assert's own condition local —
        // `vc_faithful::assert_condition_binding`, which replaced the whole-formula
        // `find_violation_leaf_through_eq` scan on 2026-07-29), but
        // `function_safety_vcs_all_discharged`
        // correctly FAILS: the obligation `self != iN::MIN` is NOT implied by the guard
        // `self < 0` (`MIN < 0`), so the negation-overflow VC is genuinely
        // undischargeable WITHOUT a precondition `self != iN::MIN`. The assert-guarded
        // (divergence-guard, task#23) lane does NOT — and MUST NOT — rescue abs: unlike a
        // guard that EXCLUDES the panic before the returned-value path, here the
        // divergence (panic on MIN) is REACHABLE, so abs is a PARTIAL function and the
        // Neg happy path is conditional. Forcing a discharge would falsely certify abs as
        // total. The honest verdict is SAFETY_GAP; the only sound closure is a caller-
        // level precondition `self != iN::MIN`, not a recognizer change.
        Rvalue::UnaryOp(UnOp::Neg, op) => Some(SemRvalue::Bin(
            SemBinOp::Sub,
            SemOperand::Const(0),
            sem_operand_of_mir(body, op, param_index)?,
        )),
        // `_join := Use(Copy/Move s.Deref.Index(_k))` — the ARRAY-INDEX arm `s[i]` (the
        // THEN arm of a guarded `if i < s.len() { s[i] } else { 0 }` return). The slice
        // place `s` is a parameter; the index `_k` is a parameter (`safe_idx`'s `i`) or a
        // constant-loaded temp (`clamp_idx`'s `3`). MODEL it as `Use(Index slice idx)`:
        // `eval_rvalue e (Use (Index slice idx))` ι-reduces (through `eval`) to
        // `idx_elem (eval e slice) (eval e idx)` — the BYTE-EXACT term the LIVE
        // `clean_ground::ground_int` grounds `Formula::Select(slice, idx)` to. So the
        // branch refinement (`refinementB`) closes reflexively at this `idx_elem` term.
        // The element value is UNINTERPRETED (sound, total): the index arm's safety rests
        // on its BOUNDS VC (`i < s.len()`, discharged from the guard), not the element.
        // Fail-closed if the slice place is not a parameter or the index is unresolvable.
        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            if matches!(p.projections.as_slice(), [Projection::Deref, Projection::Index(_)]) =>
        {
            let Projection::Index(idx_local) = p.projections[1] else { return None };
            match body.locals.get(p.local).map(|local| &local.ty) {
                Some(Ty::Ref { mutable: false, inner }) => match inner.as_ref() {
                    Ty::Slice { elem } | Ty::Array { elem, .. }
                        if matches!(elem.as_ref(), Ty::Int { .. }) => {}
                    _ => return None,
                },
                _ => return None,
            }
            if param_reassigned_by_stmt(body, p.local) || deref_write_exists(body, p.local) {
                return None;
            }
            let slice = SemOperand::Var(param_index(p.local)?);
            let idx =
                resolve_index_operand(body, idx_local, arm.id, Some(use_statement), param_index)?;
            Some(SemRvalue::Use(SemOperand::Index(Box::new(slice), Box::new(idx))))
        }
        // Direct modeled `Use`/`BinaryOp`/`CheckedBinaryOp` (field 0 grounds like BinaryOp).
        _ => sem_rvalue_of_mir_at_site(body, rv, param_index, Some((arm.id, Some(use_statement)))),
    }
}

/// Resolve the INDEX LOCAL of an array-index projection `s[_k]` to a `SemOperand` — a
/// parameter index (`safe_idx`'s `i`, modeled `Var p`) or a constant-loaded temp
/// (`clamp_idx`'s `_k := Use(Const c)`, modeled `Const c`). `None` (fail-closed) for
/// any index local that is neither a parameter nor a single literal `Use(Const)`.
pub(super) fn resolve_index_operand(
    body: &trust_types::VerifiableBody,
    idx_local: usize,
    use_block: trust_types::BlockId,
    use_statement: Option<usize>,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemOperand> {
    use trust_types::{ConstValue, Operand, Rvalue, Ty};
    // A parameter index local is modeled directly as `Var p`.
    if let Some(p) = param_index(idx_local) {
        if param_reassigned_by_stmt(body, idx_local)
            || !matches!(body.locals.get(idx_local).map(|local| &local.ty), Some(Ty::Int { .. }))
        {
            return None;
        }
        return Some(SemOperand::Var(p));
    }
    // Trust: block-order-first SOUNDNESS (recognizer well-formedness campaign, 2026-07-05,
    // closure pass) — the loop below RETURNS on the FIRST `Statement::Assign` to `idx_local`;
    // a MULTIPLY-assigned index temp would resolve to a decoy earlier literal instead of the
    // one actually live at the index use. An index-literal temp is a plain SSA-shaped leaf
    // (not a loop counter), so single-assignment is the right invariant. Fail-closed.
    if !matches!(body.locals.get(idx_local).map(|local| &local.ty), Some(Ty::Int { .. }))
        || !crate::prove::local_soundly_resolvable(body, idx_local)
    {
        return None;
    }
    // Otherwise it must be a temp loaded from an integer literal `_k := Use(Const c)`
    // whose sole complete definition dominates the projection use.  For a same-block
    // definition, dominance also means statement order: a definition after `_0 := s[_k]`
    // cannot supply the index observed by that assignment.
    let (_, _, rvalue) =
        unique_local_definition_dominating(body, idx_local, use_block, use_statement)?;
    match rvalue {
        Rvalue::Use(Operand::Constant(ConstValue::Int(k))) => Some(SemOperand::Const(*k)),
        Rvalue::Use(Operand::Constant(ConstValue::Uint(k, _))) => {
            i128::try_from(*k).ok().map(SemOperand::Const)
        }
        _ => None,
    }
}

/// Trust: BRANCHY call-arm sub-axis — chase a Goto-only chain from `start` to the
/// first NON-Goto terminator's block id (cycle-bounded by the body's block count).
/// If `require_no_write_to` is `Some(local)`, ALSO fails (`None`) the moment any
/// TRAVERSED block's statements write `local` — the per-arm sole-writer discipline
/// re-run for a call arm's continuation (mirrors the whole-function `writes_to`
/// check [`sem_call_return_of_mir`] already applies, scoped to just this arm's
/// path). `None` on a missing block or an unresolved cycle.
pub(super) fn goto_chase(
    body: &trust_types::VerifiableBody,
    start: trust_types::BlockId,
    require_no_write_to: Option<usize>,
) -> Option<trust_types::BlockId> {
    use trust_types::Terminator;
    let mut cur = start;
    for _ in 0..=body.blocks.len() {
        let blk = body.blocks.iter().find(|b| b.id == cur)?;
        if let Some(local) = require_no_write_to {
            if blk.stmts.iter().any(|s| stmt_writes_local(s, local)) {
                return None;
            }
        }
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return Some(cur),
        }
    }
    None // cycle.
}

/// Trust: BRANCHY call-arm sub-axis — recognize a SINGLE call-terminated branch
/// arm: `blk` ends in a `Terminator::Call` whose DEST is the branch's convergence
/// local (`join_local`, bare, no projections — Case A of the single-call sole-
/// writer discipline, [`sem_call_return_of_mir`]'s steps 5/12, RE-RUN here
/// per-arm), with NOTHING ELSE in `blk` writing `join_local`, resolving to a
/// certified callee (steps 6/7) with a matching arity and every actual arg a
/// modeled scalar operand (steps 8/9). No dest-type / whole-function return-spine
/// checks here — those are the CALLER's job via the shared `join_local` recovery
/// and the merged join-landing check in [`sem_nested_branch_of_mir`]. Returns
/// `(SemCallReturn, live_target)` — the caller still verifies `live_target`
/// reaches the tree's shared join via a Goto-only, sole-writer-respecting path
/// ([`goto_chase`]).
pub(super) fn sem_call_arm_of_mir(
    func: &trust_types::VerifiableFunction,
    blk: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<(SemCallReturn, trust_types::BlockId)> {
    use trust_types::Terminator;
    let Terminator::Call {
        func: callee_str,
        args,
        dest,
        target,
        atomic,
        is_foreign,
        is_unsafe_sig,
        ..
    } = &blk.terminator
    else {
        return None;
    };
    if *is_foreign || *is_unsafe_sig || atomic.is_some() {
        return None; // ABI fail-closes.
    }
    let target = (*target)?; // diverging call.
    if !dest.projections.is_empty() || dest.local != join_local {
        return None; // not a direct writer of this branch's convergence local.
    }
    if blk.stmts.iter().any(|s| stmt_writes_local(s, join_local)) {
        return None; // the call must be the SOLE writer of `join_local` in this arm.
    }
    let (resolved, fact, callee_id) = resolve_certified_callee(callees, callee_str)?;
    if resolved == func.def_path || *callee_str == func.def_path {
        return None; // self-recursion fails closed.
    }
    if fact.arg_count != args.len() || args.is_empty() {
        return None; // arity + at-least-one-arg.
    }
    let mut sem_args = Vec::with_capacity(args.len());
    for a in args {
        sem_args.push(sem_operand_of_mir(&func.body, a, param_index)?); // every arg a modeled scalar.
    }
    Some((SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args }, target))
}

/// Trust: discriminant-guard leaf — whether the `SwitchInt` terminator at block
/// `switch_bid` is a genuine EXHAUSTIVE 2-VARIANT enum-discriminant switch: the
/// TyCtxt-vetted [`trust_types::Terminator::SwitchInt::exhaustive_enum_unreachable`]
/// flag is set (authoritative — set only when the discriminant is a genuine
/// single-assignment enum-tag temp whose explicit case values are EXACTLY the
/// enum's full tag set and `otherwise` targets `Unreachable`), AND — belt-and-
/// suspenders, since this shape is new and safety-critical — the `otherwise`
/// block's terminator really IS `Unreachable`. Requiring BOTH means a bug in the
/// upstream flag-setting logic cannot alone mint a false certificate here: this
/// shape can decline (never over-accept) if either check fails.
///
/// Does NOT check `targets.len() == 2` — the caller destructures `targets` to
/// exactly two entries BEFORE calling this, so a >2-variant exhaustive switch
/// (3+ explicit targets) never reaches here at all (it declines earlier, at the
/// `targets.as_slice()` match).
pub(super) fn exhaustive_two_arm_discriminant_switch(
    body: &trust_types::VerifiableBody,
    switch_bid: trust_types::BlockId,
    otherwise: trust_types::BlockId,
) -> bool {
    use trust_types::Terminator;
    let Some(switch_block) = body.blocks.iter().find(|b| b.id == switch_bid) else { return false };
    let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } = &switch_block.terminator else {
        return false;
    };
    if !*exhaustive_enum_unreachable {
        return false;
    }
    let Some(other_block) = body.blocks.iter().find(|b| b.id == otherwise) else { return false };
    matches!(other_block.terminator, Terminator::Unreachable)
}

/// The function's sole `Return` block. Guarded-return reflection models one
/// observable convergence point, so multiple returns (or no return) are outside
/// that fragment even when one happens to appear first in block-table order.
pub(crate) fn unique_return_block(
    body: &trust_types::VerifiableBody,
) -> Option<&trust_types::BasicBlock> {
    use trust_types::Terminator;
    let mut returns =
        body.blocks.iter().filter(|block| matches!(block.terminator, Terminator::Return));
    let ret = returns.next()?;
    returns.next().is_none().then_some(ret)
}

/// Recover the only two guarded-return join forms admitted by the semantic
/// extractors: a value-write-free `Return` block for a direct `_0` join, or one
/// bare `_0 := Use(_t)` copy from a non-parameter temp. Other value statements
/// in the join are deliberately rejected: in particular, `_t := forged; _0 :=
/// Use(_t); Return` must not inherit the arm value that the recognizer modeled.
pub(super) fn guarded_return_join_local(
    body: &trust_types::VerifiableBody,
    ret: &trust_types::BasicBlock,
) -> Option<usize> {
    use trust_types::{Operand, Rvalue, Statement};

    let mut copied_temp = None;
    for statement in &ret.stmts {
        match statement {
            Statement::Assign { place, rvalue, .. } => {
                if copied_temp.is_some() || place.local != 0 || !place.projections.is_empty() {
                    return None;
                }
                let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue else {
                    return None;
                };
                if !source.projections.is_empty()
                    || source.local == 0
                    || (1..=body.arg_count).contains(&source.local)
                    || body.locals.get(source.local).is_none()
                {
                    return None;
                }
                copied_temp = Some(source.local);
            }
            Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::PlaceMention(_)
            | Statement::Retag { .. }
            | Statement::Coverage
            | Statement::ConstEvalCounter
            | Statement::Nop => {}
            _ => return None,
        }
    }
    Some(copied_temp.unwrap_or(0))
}

/// Complete write-set gate for a guarded convergence local. Every value write
/// rooted at `local` must be one of the expected bare assignments or bare call
/// destinations; projected writes, discriminant/deinitialization writes, and a
/// mutable alias all fail closed.
pub(super) fn local_has_only_guarded_writes(
    body: &trust_types::VerifiableBody,
    local: usize,
    expected_assignments: usize,
    expected_calls: usize,
) -> bool {
    use trust_types::{Rvalue, Statement, Terminator};

    let mut assignments = 0usize;
    for statement in body.blocks.iter().flat_map(|block| &block.stmts) {
        match statement {
            Statement::Assign { place, rvalue, .. } => {
                // Inspect the alias source independently of the destination.
                // In particular, a malformed self-destination must not let the
                // earlier destination arm hide a mutable path to `local`.
                if matches!(rvalue,
                    Rvalue::Ref { mutable: true, place }
                        | Rvalue::AddressOf(true, place)
                        if place.local == local)
                {
                    return false;
                }
                if place.local == local {
                    if !place.projections.is_empty() {
                        return false;
                    }
                    assignments += 1;
                }
            }
            Statement::SetDiscriminant { place, .. }
            | Statement::Deinit { place }
            | Statement::Retag { place }
                if place.local == local =>
            {
                return false;
            }
            _ => {}
        }
    }
    let mut calls = 0usize;
    for block in &body.blocks {
        if let Terminator::Call { dest, .. } = &block.terminator
            && dest.local == local
        {
            if !dest.projections.is_empty() {
                return false;
            }
            calls += 1;
        }
        if matches!(&block.terminator, Terminator::Drop { place, .. } if place.local == local) {
            return false;
        }
    }
    assignments == expected_assignments && calls == expected_calls
}

/// Whether every entry-to-`node` path passes through `candidate`. Reachability
/// is computed over the complete terminator successor relation; an unknown
/// terminator or missing target makes the proof fail closed.
// Trust: W2 INC2 — `pub(crate)` so `prove::extract_iter_loop_function` can pin that the
// `into_iter`/it-init blocks DOMINATE the loop header (the "executed once, before the
// loop" clause of the iterator's region rooting).
pub(crate) fn block_dominates(
    body: &trust_types::VerifiableBody,
    candidate: trust_types::BlockId,
    node: trust_types::BlockId,
) -> bool {
    use std::collections::HashSet;

    use trust_types::{BlockId, Terminator};

    let entry = BlockId(0);
    let identities: HashSet<BlockId> = body.blocks.iter().map(|block| block.id).collect();
    if identities.len() != body.blocks.len() {
        return false;
    }
    let Some(reachable) = cfg_reachable_from(body, entry) else { return false };
    if !reachable.contains(&candidate) || !reachable.contains(&node) {
        return false;
    }
    if candidate == entry || candidate == node {
        return true;
    }

    let mut seen = HashSet::new();
    let mut stack = vec![entry];
    while let Some(id) = stack.pop() {
        if id == candidate || !seen.insert(id) {
            continue;
        }
        if id == node {
            return false;
        }
        let Some(block) = body.blocks.iter().find(|block| block.id == id) else {
            return false;
        };
        match &block.terminator {
            Terminator::Goto(target) => stack.push(*target),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                stack.extend(targets.iter().map(|(_, target)| *target));
                stack.push(*otherwise);
            }
            Terminator::Call { target, .. } => stack.extend(target.iter().copied()),
            Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => {
                stack.push(*target);
            }
            Terminator::Opaque { targets, .. } => stack.extend(targets.iter().copied()),
            Terminator::Return | Terminator::Unreachable | Terminator::Resume => {}
            _ => return false,
        }
    }
    true
}

/// The sole complete definition of a bare `SwitchInt` discriminant local,
/// together with proof that its defining block dominates every switch that
/// reads it. This prevents a disconnected or one-branch-only assignment from
/// supplying the semantic condition selected by a whole-body scan.
pub(super) fn dominating_switch_discriminant_rvalue(
    body: &trust_types::VerifiableBody,
    local: usize,
) -> Option<(trust_types::BlockId, usize, &trust_types::Rvalue)> {
    use trust_types::{Operand, Terminator};

    if !crate::prove::local_soundly_resolvable(body, local) {
        return None;
    }
    let mut definition = None;
    for block in &body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            if let Some(rvalue) =
                crate::assignment_types::assigned_local_rvalue(body, statement, local)
            {
                if definition.is_some() {
                    return None;
                }
                definition = Some((block.id, statement_index, rvalue));
            }
        }
    }
    let (definition_block, definition_statement, rvalue) = definition?;
    let mut uses = 0usize;
    for block in &body.blocks {
        if let Terminator::SwitchInt { discr, .. } = &block.terminator
            && matches!(discr,
                Operand::Copy(place) | Operand::Move(place)
                    if place.local == local && place.projections.is_empty())
        {
            uses += 1;
            if !block_dominates(body, definition_block, block.id) {
                return None;
            }
        }
    }
    (uses != 0).then_some((definition_block, definition_statement, rvalue))
}

pub(crate) fn unique_local_definition_dominating(
    body: &trust_types::VerifiableBody,
    local: usize,
    use_block: trust_types::BlockId,
    use_statement: Option<usize>,
) -> Option<(trust_types::BlockId, usize, &trust_types::Rvalue)> {
    if !crate::prove::local_soundly_resolvable(body, local) {
        return None;
    }
    let mut definition = None;
    for block in &body.blocks {
        for (statement_index, statement) in block.stmts.iter().enumerate() {
            if let Some(rvalue) =
                crate::assignment_types::assigned_local_rvalue(body, statement, local)
            {
                if definition.is_some() {
                    return None;
                }
                definition = Some((block.id, statement_index, rvalue));
            }
        }
    }
    let (definition_block, definition_statement, rvalue) = definition?;
    if definition_block == use_block {
        if use_statement.is_some_and(|use_index| definition_statement >= use_index) {
            return None;
        }
    } else if !block_dominates(body, definition_block, use_block) {
        return None;
    }
    Some((definition_block, definition_statement, rvalue))
}

/// Shared control-flow admission for guarded-return recognizers.
///
/// Every modeled arm and decision must be reachable from the real MIR entry
/// (`bb0`), both arms must converge at the sole `Return`, and the deterministic
/// entry prefix must encounter a modeled decision before an arm/return. This
/// prevents block-table scans from turning a disconnected switch/return island
/// into the function's observable result.
pub(crate) fn guarded_cfg_is_entry_rooted(
    body: &trust_types::VerifiableBody,
    join: trust_types::BlockId,
    arms: &[trust_types::BlockId],
    decisions: &[trust_types::BlockId],
) -> bool {
    use std::collections::HashSet;

    use trust_types::{BlockId, Terminator};

    if arms.len() < 2 || decisions.is_empty() {
        return false;
    }
    let Some(ret) = unique_return_block(body) else { return false };
    if join != ret.id {
        return false;
    }
    let Some(reachable) = cfg_reachable_from(body, BlockId(0)) else { return false };
    if !reachable.contains(&ret.id)
        || arms.iter().any(|id| !reachable.contains(id))
        || decisions.iter().any(|id| !reachable.contains(id))
    {
        return false;
    }

    let arm_set: HashSet<BlockId> = arms.iter().copied().collect();
    let decision_set: HashSet<BlockId> = decisions.iter().copied().collect();
    let mut seen = HashSet::new();
    let mut current = BlockId(0);
    loop {
        if !seen.insert(current) {
            return false;
        }
        if decision_set.contains(&current) {
            return true;
        }
        if arm_set.contains(&current) || current == ret.id {
            return false;
        }
        let Some(block) = body.blocks.iter().find(|block| block.id == current) else {
            return false;
        };
        current = match &block.terminator {
            Terminator::Goto(target) | Terminator::Assert { target, .. } => *target,
            _ => return false,
        };
    }
}

/// Recover a NESTED / multi-way guarded-return witness (`SemBranchTree`) for a
/// `if c1 { t1 } else if c2 { t2 } else { e }` return — the multi-way generalization of
/// [`sem_cf_return_of_mir`]. The modeled shape is a TREE of `SwitchInt`s over Bool
/// comparison-temp discrs whose leaf arms each assign the convergence local `_t`
/// (`__ret`/`_0`) a modeled scalar rvalue and converge at a single `Return` join:
///
/// ```text
///   bb_g1: _k1 := BinaryOp(c1, …);  SwitchInt(_k1) { 0 → bb_g2, otherwise → bb_t1 }
///   bb_t1: _t := <t1>;  Goto bb_join
///   bb_g2: _k2 := BinaryOp(c2, …);  SwitchInt(_k2) { 0 → bb_e, otherwise → bb_t2 }
///   bb_t2: _t := <t2>;  Goto bb_join
///   bb_e:  _t := <e>;   Goto bb_join
///   bb_join: _0 := Use(_t);  Return
/// ```
///
/// We recover the convergence local exactly as `sem_cf_return_of_mir` does, then build
/// the tree by a bounded recursive walk FROM the entry block: a block that ends in a
/// `SwitchInt` over a reflectable comparison becomes a `Node(cmp-leaf, recurse(otherwise
/// = TRUE arm), recurse(value-0 = FALSE arm))`; a block that assigns the convergence
/// local becomes a `Leaf(arm rvalue)`. The polarity matches `eval_ite`/`ground_int`'s
/// `Ite` arm (`SwitchInt` value-0 ↦ FALSE arm ↦ the `iteI` else, otherwise ↦ TRUE arm).
///
/// `None` (fail-closed) for: a non-comparison discriminant; a `SwitchInt` with more than
/// one value target; an arm value outside the modeled scalar fragment (a `Neg` arm
/// `SemRvalue` does not model — `abs` defers); a cyclic / unmodeled-terminator path; or
/// a join that is not the single bare `Return` (a loop / call). The non-nested cases
/// (`Leaf`, depth-1 `Node`) are recognized too but are routed back to the existing
/// single-branch path by `nested_branch_refinement_witness`'s `is_nested` gate.
///
/// Trust: BRANCHY call-arm sub-axis — `callees`. `None` reproduces steps (2)/(3)
/// BYTE-FOR-BYTE (the call-arm scan below is entirely skipped, an inert no-op) —
/// every EXISTING caller ([`nested_branch_refinement_witness`],
/// [`sem_nested_branch_shape_of`]) passes `None` and is therefore UNCHANGED.
/// `Some(registry)` ADDITIONALLY scans for
/// call-terminated arms ([`sem_call_arm_of_mir`], per-arm certified-callee
/// resolution) and merges them with any plain assign-arms that share the SAME
/// join (via [`goto_chase`]) — admitting an ALL-CALL arm set (`if c { g(a) } else
/// { h(b) }`) or a MIXED set (`if c { g(a) } else { k }`). Consumed ONLY by
/// [`sem_branch_call_shape_of`] (shape-only, no MirSem certificate).
pub(super) fn sem_nested_branch_of_mir(
    func: &trust_types::VerifiableFunction,
    param_index: &dyn Fn(usize) -> Option<u64>,
    callees: Option<&std::collections::BTreeMap<String, CalleeFact>>,
) -> Option<SemBranchTree> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }

    // (1) The CONVERGENCE LOCAL the leaf arms write — same recovery as the
    //     single-branch path: the `Return` block's `_0 := Use(_t)` (join-via-temp) or a
    //     bare `Return` (direct `_0` join).
    let ret_block = unique_return_block(body)?;
    let join_local = guarded_return_join_local(body, ret_block)?;

    // Nested selects can introduce a chain of convergence temporaries. Close
    // transitively over exact pass-through assignments `_outer := Use(_inner)`,
    // where `_inner` is itself written by at least two branch blocks. A
    // single-definition value temp is not a convergence node.
    let passthrough_source =
        |destination: usize, rvalue: &Rvalue, convergence: &[usize]| -> Option<usize> {
            if !convergence.contains(&destination) {
                return None;
            }
            let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) = rvalue else {
                return None;
            };
            if !source.projections.is_empty()
                || source.local == 0
                || (1..=body.arg_count).contains(&source.local)
            {
                return None;
            }
            let writes = body
                .blocks
                .iter()
                .flat_map(|block| &block.stmts)
                .filter(|statement| {
                    matches!(statement,
                        Statement::Assign { place, .. }
                            if place.local == source.local && place.projections.is_empty())
                })
                .count();
            (writes >= 2).then_some(source.local)
        };
    let mut convergence_locals = vec![join_local];
    loop {
        let mut added = false;
        for statement in body.blocks.iter().flat_map(|block| &block.stmts) {
            let Statement::Assign { place, rvalue, .. } = statement else { continue };
            if !place.projections.is_empty() {
                continue;
            }
            if let Some(source) = passthrough_source(place.local, rvalue, &convergence_locals)
                && !convergence_locals.contains(&source)
            {
                convergence_locals.push(source);
                added = true;
            }
        }
        if !added {
            break;
        }
    }
    let has_nested_convergence = convergence_locals.len() > 1;

    // A real arm's last convergence write is a value, not a transparent merge.
    // Require exactly one convergence write in each such block so an ignored
    // earlier write cannot be mistaken for part of the selected value.
    let real_arm_convergence_local = |block: &trust_types::BasicBlock| -> Option<usize> {
        let writes: Vec<(usize, &Rvalue)> = block
            .stmts
            .iter()
            .filter_map(|statement| match statement {
                Statement::Assign { place, rvalue, .. }
                    if place.projections.is_empty()
                        && convergence_locals.contains(&place.local) =>
                {
                    Some((place.local, rvalue))
                }
                _ => None,
            })
            .collect();
        let [(local, rvalue)] = writes.as_slice() else { return None };
        passthrough_source(*local, rvalue, &convergence_locals).is_none().then_some(*local)
    };

    // (2a) UNCHANGED: the plain-assign leaf arm blocks — those that `Goto` and assign
    //     the convergence local.
    let assigns_join = |b: &trust_types::BasicBlock| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == join_local && place.projections.is_empty())
        })
    };
    let assign_arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Goto(_)) && assigns_join(b))
        .collect();

    // (2b) Trust: BRANCHY call-arm sub-axis — ADDITIVE per-arm call-terminated arm
    //     discovery, entirely gated behind `callees.is_some()`. With `callees: None`
    //     `call_arms` stays empty and every step below reproduces the ORIGINAL
    //     assign-arms-only gating byte-for-byte.
    let mut call_arms: std::collections::HashMap<BlockId, SemCallReturn> =
        std::collections::HashMap::new();
    if let Some(callees) = callees {
        for b in &body.blocks {
            if let Some((call, _target)) =
                sem_call_arm_of_mir(func, b, join_local, param_index, callees)
            {
                call_arms.insert(b.id, call);
            }
        }
    }

    let join_id: BlockId;
    let arm_ids: Vec<BlockId> = if call_arms.is_empty() && has_nested_convergence {
        let real_arms: Vec<&trust_types::BasicBlock> = body
            .blocks
            .iter()
            .filter(|block| {
                matches!(block.terminator, Terminator::Goto(_))
                    && real_arm_convergence_local(block).is_some()
            })
            .collect();
        if real_arms.len() < 2 {
            return None;
        }

        // Every write to any convergence local must be either one real arm
        // value or one exact pass-through merge, and every such block must be a
        // pure Goto on the shared return spine.
        for block in &body.blocks {
            let convergence_writes: Vec<(usize, &Rvalue)> = block
                .stmts
                .iter()
                .filter_map(|statement| match statement {
                    Statement::Assign { place, rvalue, .. }
                        if place.projections.is_empty()
                            && convergence_locals.contains(&place.local) =>
                    {
                        Some((place.local, rvalue))
                    }
                    _ => None,
                })
                .collect();
            if convergence_writes.is_empty() {
                continue;
            }
            if !matches!(block.terminator, Terminator::Goto(_)) || convergence_writes.len() != 1 {
                return None;
            }
            let (local, rvalue) = convergence_writes[0];
            if passthrough_source(local, rvalue, &convergence_locals).is_none()
                && real_arm_convergence_local(block).is_none()
            {
                return None;
            }
        }

        // A leaf's successor path may contain only exact convergence
        // pass-through blocks before the unique Return. In particular it must
        // never enter a second real arm: otherwise the second arm can overwrite
        // the value modeled for the first one while `goto_chase` silently skips
        // both statement lists.
        let real_arm_ids: std::collections::HashSet<BlockId> =
            real_arms.iter().map(|block| block.id).collect();
        let convergence_landing = |start: BlockId, arm_local: usize| -> Option<BlockId> {
            let mut current = start;
            let mut carried_local = arm_local;
            for _ in 0..=body.blocks.len() {
                if real_arm_ids.contains(&current) {
                    return None;
                }
                let block = body.blocks.iter().find(|block| block.id == current)?;
                match &block.terminator {
                    Terminator::Goto(next) => {
                        let mut pass_through = None;
                        for statement in &block.stmts {
                            match statement {
                                Statement::Assign { place, rvalue, .. } => {
                                    let Rvalue::Use(Operand::Copy(source) | Operand::Move(source)) =
                                        rvalue
                                    else {
                                        return None;
                                    };
                                    if pass_through.is_some()
                                        || !place.projections.is_empty()
                                        || !source.projections.is_empty()
                                        || !convergence_locals.contains(&place.local)
                                        || !convergence_locals.contains(&source.local)
                                        || source.local != carried_local
                                        || place.local == source.local
                                    {
                                        return None;
                                    }
                                    pass_through = Some(place.local);
                                }
                                Statement::StorageLive(_)
                                | Statement::StorageDead(_)
                                | Statement::PlaceMention(_)
                                | Statement::Retag { .. }
                                | Statement::Coverage
                                | Statement::ConstEvalCounter
                                | Statement::Nop => {}
                                _ => return None,
                            }
                        }
                        if let Some(destination) = pass_through {
                            carried_local = destination;
                        }
                        current = *next;
                    }
                    Terminator::Return
                        if block.id == ret_block.id && carried_local == join_local =>
                    {
                        return Some(block.id);
                    }
                    _ => return None,
                }
            }
            None
        };

        let mut landings = Vec::with_capacity(real_arms.len());
        for block in &real_arms {
            let Terminator::Goto(target) = block.terminator else { return None };
            landings.push(convergence_landing(target, real_arm_convergence_local(block)?)?);
        }
        join_id = *landings.first()?;
        if !landings.iter().all(|landing| *landing == join_id) {
            return None;
        }
        body.blocks.iter().find(|block| block.id == join_id)?;
        real_arms.iter().map(|block| block.id).collect()
    } else if call_arms.is_empty() {
        // EXACTLY the original discovery/gating — byte-identical.
        if assign_arms.len() < 2 {
            return None; // straight-line / single-assignment — not a guarded return.
        }
        // All arms must Goto the SAME join block.
        let Terminator::Goto(found_join) = assign_arms[0].terminator else { return None };
        if !assign_arms
            .iter()
            .all(|b| matches!(b.terminator, Terminator::Goto(j) if j == found_join))
        {
            return None;
        }
        join_id = found_join;
        body.blocks.iter().find(|b| b.id == join_id)?;
        assign_arms.iter().map(|b| b.id).collect()
    } else {
        // Trust: BRANCHY call-arm sub-axis — a mixed or all-call arm set. Determine
        // the SHARED join by Goto-chasing every candidate arm's immediate successor
        // (an assign-arm's Goto target, a call-arm's Call target) and requiring they
        // ALL land on the SAME block — never guessing which arm belongs to the tree.
        let mut landings: Vec<BlockId> = Vec::new();
        for b in &assign_arms {
            let Terminator::Goto(t) = b.terminator else { return None };
            landings.push(goto_chase(body, t, Some(join_local))?);
        }
        for id in call_arms.keys() {
            let blk = body.blocks.iter().find(|b| b.id == *id)?;
            let Terminator::Call { target: Some(t), .. } = &blk.terminator else { return None };
            landings.push(goto_chase(body, *t, Some(join_local))?);
        }
        if assign_arms.len() + call_arms.len() < 2 {
            return None; // fewer than two arms total — not a guarded return.
        }
        join_id = *landings.first()?;
        if !landings.iter().all(|l| *l == join_id) {
            return None; // the arms do not all converge on the SAME join — decline.
        }
        body.blocks.iter().find(|b| b.id == join_id)?;
        assign_arms.iter().map(|b| b.id).collect()
    };

    let decision_ids: Vec<BlockId> = body
        .blocks
        .iter()
        .filter(|block| matches!(block.terminator, Terminator::SwitchInt { .. }))
        .map(|block| block.id)
        .collect();
    let mut cfg_arm_ids = arm_ids.clone();
    cfg_arm_ids.extend(call_arms.keys().copied());
    if !guarded_cfg_is_entry_rooted(body, join_id, &cfg_arm_ids, &decision_ids) {
        return None;
    }
    if has_nested_convergence {
        for local in &convergence_locals {
            let assignments = body
                .blocks
                .iter()
                .flat_map(|block| &block.stmts)
                .filter(|statement| {
                    matches!(statement,
                        Statement::Assign { place, .. }
                            if place.local == *local && place.projections.is_empty())
                })
                .count();
            if !local_has_only_guarded_writes(body, *local, assignments, 0) {
                return None;
            }
        }
    } else if !local_has_only_guarded_writes(body, join_local, assign_arms.len(), call_arms.len()) {
        return None;
    }
    if join_local != 0 && !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }

    // (3) Start the recursive walk at the actual MIR entry, never the minimum
    // block-table island selected by ordering.
    let entry = BlockId(0);

    // The comparison `SemCond` a switch's discriminant temp reflects to — reused from
    // the single-branch path's `switch_leaf` logic. Two recognized discriminant-temp
    // rvalues: `BinaryOp(cmp, a, b)` (a scalar comparison, UNCHANGED — `tag` is unused,
    // always called with `0` from the "value-0 + otherwise" bool shape below) or, Trust:
    // discriminant-guard leaf, `Discriminant(place)` (an enum-tag read — `Either::
    // is_left`-class bodies): the guard is the EQUALITY test `discriminant == tag`,
    // where `tag` is the SPECIFIC target value supplied by the caller (unlike a bool
    // comparison, a multi-valued discriminant carries no self-contained Bool condition
    // — the equality against `tag` IS the guard).
    let switch_leaf = |discr: &Operand, tag: u128| -> Option<SemCond> {
        let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
        if !dp.projections.is_empty() {
            return None;
        }
        let (definition_block, definition_statement, cmp_rvalue) =
            dominating_switch_discriminant_rvalue(body, dp.local)?;
        match cmp_rvalue {
            Rvalue::BinaryOp(cmp_op, ca, cb) => Some(SemCond {
                op: sem_cmpop_of_mir(cmp_op)?,
                a: sem_guard_operand_of_mir(
                    body,
                    ca,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
                b: sem_guard_operand_of_mir(
                    body,
                    cb,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
            }),
            // Trust: discriminant-guard leaf.
            Rvalue::Discriminant(place) => {
                let base = sem_discriminant_base_of_mir(
                    body,
                    place,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?;
                Some(SemCond {
                    op: SemCmpOp::Eq,
                    a: SemOperand::Discriminant(Box::new(base)),
                    b: SemOperand::Const(i128::try_from(tag).ok()?),
                })
            }
            _ => None,
        }
    };

    // The recursive walk. From `start`, follow the linear Goto/Assert chain to the first
    // SwitchInt or arm block; `fuel` bounds the recursion depth (block count) so a cycle
    // cannot loop forever. Trust: BRANCHY call-arm sub-axis — a `call_arms` hit is
    // checked FIRST (a call-arm block is never ALSO in `arm_ids`, but checking first
    // keeps the two lookups independent and cheap either way) and produces a
    // `CallLeaf`; `call_arms` is empty for every pre-existing (`callees: None`) call,
    // so this check is an inert no-op there.
    fn walk(
        body: &trust_types::VerifiableBody,
        start: trust_types::BlockId,
        arm_ids: &[trust_types::BlockId],
        call_arms: &std::collections::HashMap<trust_types::BlockId, SemCallReturn>,
        convergence_locals: &[usize],
        param_index: &dyn Fn(usize) -> Option<u64>,
        switch_leaf: &dyn Fn(&trust_types::Operand, u128) -> Option<SemCond>,
        fuel: usize,
    ) -> Option<SemBranchTree> {
        use trust_types::{Statement, Terminator};
        if fuel == 0 {
            return None;
        }
        // Follow the linear chain (Goto / success-Assert) to the first decision/arm block.
        let mut cur = start;
        for _ in 0..=body.blocks.len() {
            if let Some(call) = call_arms.get(&cur) {
                return Some(SemBranchTree::CallLeaf(call.clone()));
            }
            if arm_ids.contains(&cur) {
                // A leaf arm writes one member of the complete convergence chain.
                let arm = body.blocks.iter().find(|b| b.id == cur)?;
                let arm_local = arm.stmts.iter().rev().find_map(|statement| match statement {
                    Statement::Assign { place, .. }
                        if place.projections.is_empty()
                            && convergence_locals.contains(&place.local) =>
                    {
                        Some(place.local)
                    }
                    _ => None,
                })?;
                let rv = arm_value_rvalue_for(body, arm, arm_local, param_index)?;
                return Some(SemBranchTree::Leaf(rv));
            }
            let block = body.blocks.iter().find(|b| b.id == cur)?;
            if block.stmts.iter().any(|statement| {
                convergence_locals.iter().any(|local| stmt_writes_local(statement, *local))
            }) {
                return None;
            }
            match &block.terminator {
                Terminator::Goto(t) => cur = *t,
                Terminator::Assert { target, .. } => cur = *target,
                Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                    // A decision block: EITHER exactly one value-0 target (FALSE arm) +
                    // otherwise (TRUE arm) — the bool-comparison shape (UNCHANGED) — OR,
                    // Trust: discriminant-guard leaf, exactly TWO explicit tag targets +
                    // an exhaustive, Unreachable-`otherwise` enum-discriminant switch (the
                    // `Either::is_left`-class shape). Reflect the guard, recurse into both.
                    //
                    // Trust: Item 1 SCOPE NOTE (wave-a) — the single-target arm below carries
                    // the BOOL-COMPARISON polarity (value-0 edge = FALSE/else arm). For a
                    // single-target DISCRIMINANT tag read (`matches!(x, Variant_K)`) that
                    // polarity is INVERTED (value-K edge is the MATCHED/TRUE arm) — the exact
                    // bug the single-branch sibling `sem_cf_return_of_mir` fixed by splitting
                    // on `discr_is_tag_read`. This NESTED walker is NOT reached for a
                    // single-branch single-target discriminant match (that sibling now claims
                    // it, so the non-overlap gate declines here), so no wave-a corpus / test
                    // exercises this path with a discriminant. Extending the same tag-read
                    // split to this nested walker is the tracked follow-up; until then a
                    // single-target discriminant node INSIDE a genuinely-nested tree stays a
                    // known latent-inversion spot (fail-closed for K≠0, which never matches
                    // this `*zero_val == 0` arm).
                    let (leaf, then_target, else_target) = match targets.as_slice() {
                        [(zero_val, false_target)] if *zero_val == 0 => {
                            (switch_leaf(discr, 0)?, *otherwise, *false_target)
                        }
                        [(tag_a, block_a), (_tag_b, block_b)] => {
                            if !exhaustive_two_arm_discriminant_switch(body, block.id, *otherwise) {
                                return None;
                            }
                            (switch_leaf(discr, *tag_a)?, *block_a, *block_b)
                        }
                        _ => return None,
                    };
                    let then_tree = walk(
                        body,
                        then_target,
                        arm_ids,
                        call_arms,
                        convergence_locals,
                        param_index,
                        switch_leaf,
                        fuel - 1,
                    )?;
                    let else_tree = walk(
                        body,
                        else_target,
                        arm_ids,
                        call_arms,
                        convergence_locals,
                        param_index,
                        switch_leaf,
                        fuel - 1,
                    )?;
                    return Some(SemBranchTree::Node(
                        SemCondTree::Leaf(leaf),
                        Box::new(then_tree),
                        Box::new(else_tree),
                    ));
                }
                _ => return None, // unmodeled terminator on the path.
            }
        }
        None // exceeded the block count without reaching an arm/decision — a cycle.
    }

    let tree = walk(
        body,
        entry,
        &arm_ids,
        &call_arms,
        &convergence_locals,
        param_index,
        &switch_leaf,
        body.blocks.len() + 1,
    )?;
    // A genuine guarded return must contain at least one decision node.
    if matches!(tree, SemBranchTree::Leaf(_)) {
        return None;
    }
    Some(tree)
}

/// Recover a CONTROL-FLOW return witness (`SemCfReturn`) for a guarded
/// `if cmp(a,b) { then } else { else }` return. The modeled shape (the cleanest
/// closeable sub-case) is a SINGLE `SwitchInt` over a Bool comparison-temp discr
/// whose two arms each assign `_0 := <modeled rvalue>` and converge at a bare
/// `Return` block:
///
/// ```text
///   bb_g: _k := BinaryOp(cmp, a, b);  SwitchInt(_k) { 0 → bb_else, otherwise → … bb_then }
///   bb_then: _0 := <then rvalue>;  Goto bb_join (possibly via Assert/Goto blocks)
///   bb_else: _0 := <else rvalue>;  Goto bb_join
///   bb_join: (empty)  Return
/// ```
///
/// SwitchInt polarity: the value-`0` target reaches the ELSE arm (discr `cmp` is
/// FALSE), the `otherwise` path reaches the THEN arm (discr is TRUE). The two arm
/// blocks are the predecessors of the bare `Return` block whose last `_0 := …` is a
/// modeled scalar value.
///
/// Returns the witness only when the guard and BOTH arm values are in the modeled
/// fragment. The fragment now includes: a single comparison (`Leaf`), a CONJUNCTIVE
/// guard (a chain of `SwitchInt`s → `And`), a scalar arm value, AND an ARRAY-INDEX arm
/// `s[i]` (modeled `Use(Index slice idx)` over the additive `Operand.Index`, with the
/// guard's `s.len()` modeled `Len slice` over `Operand.Len`). `None` (fail-closed) for:
///   * an arm value still outside the modeled fragment (e.g. a `Neg` arm `SemRvalue`
///     does not model — `abs` defers), or an index over a non-parameter slice;
///   * any non-comparison discriminant, more than two converging arms, or a return
///     block that is not the bare empty `Return` join.
///
/// Now called by `branch_refinement_witness` (Step 6B): it recovers the `SemCfReturn`
/// witness whose `Formula::Ite` reflection the LIVE grounder grounds, so the branch
/// refinement (`refinementB`) connects to the live pipeline for single-branch returns.
pub(super) fn sem_cf_return_of_mir(
    func: &trust_types::VerifiableFunction,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SemCfReturn> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }

    // (1) The CONVERGENCE LOCAL the two arms write. Two guarded shapes:
    //     (a) DIRECT join: the Return block has NO `_0 := …` and the arms write `_0`.
    //     (b) JOIN-VIA-TEMP: the Return block reads `_0 := Use(_t)` from a non-param
    //         convergence temp `_t` (the `let r = if c {…} else {…}; r` lowering —
    //         `clamp`/`max`/`min`/`abs`), and the arms write `_t`. Recover `_t`.
    let ret_block = unique_return_block(body)?;
    let assigns_local = |b: &trust_types::BasicBlock, loc: usize| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == loc && place.projections.is_empty())
        })
    };
    let join_local = guarded_return_join_local(body, ret_block)?;
    let assigns_0 = |b: &trust_types::BasicBlock| assigns_local(b, join_local);

    // (2) The arm blocks: predecessors that `Goto` a COMMON join AND assign the
    //     convergence local. The guarded shape has EXACTLY two (then + else).
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Goto(_)) && assigns_0(b))
        .collect();
    if arms.len() != 2 {
        return None; // not the two-arm `if/else` shape (0/1/many arms — deferred).
    }
    let Terminator::Goto(j0) = arms[0].terminator else { return None };
    let Terminator::Goto(j1) = arms[1].terminator else { return None };
    if j0 != j1 {
        return None; // arms converge on different blocks — not a single join.
    }

    // (3) One OR MORE `SwitchInt`s over comparison temps. ONE switch is the bare
    //     `if cmp {…}` guard; a SHORT-CIRCUIT CHAIN of N switches (each value-0 → the
    //     common else arm, otherwise → the next test, last otherwise → the then arm)
    //     is the CONJUNCTIVE guard `c1 && c2 && …` (the ADDITIVE depth frontier the
    //     `And` Cond constructor models).
    let switches: Vec<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                Some((discr, targets, *otherwise, b.id))
            }
            _ => None,
        })
        .collect();
    if switches.is_empty() {
        return None; // straight-line (no guard).
    }
    let arm_ids: Vec<BlockId> = arms.iter().map(|b| b.id).collect();
    let decision_ids: Vec<BlockId> = switches.iter().map(|(_, _, _, id)| *id).collect();
    if !guarded_cfg_is_entry_rooted(body, j0, &arm_ids, &decision_ids) {
        return None;
    }
    if !local_has_only_guarded_writes(body, join_local, arms.len(), 0) {
        return None;
    }
    if join_local != 0 && !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }

    // The `SemCond` leaf a switch's discriminant temp reflects to — `BinaryOp(cmp, a,
    // b)` (a scalar comparison, UNCHANGED — `tag` unused, always called with `0`) or,
    // Trust: discriminant-guard leaf, `Discriminant(place)` (an enum-tag read): the
    // guard is `discriminant == tag`, `tag` being the caller-supplied target value.
    let switch_leaf = |discr: &Operand, tag: u128| -> Option<SemCond> {
        let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
        if !dp.projections.is_empty() {
            return None;
        }
        let (definition_block, definition_statement, cmp_rvalue) =
            dominating_switch_discriminant_rvalue(body, dp.local)?;
        match cmp_rvalue {
            Rvalue::BinaryOp(cmp_op, ca, cb) => Some(SemCond {
                op: sem_cmpop_of_mir(cmp_op)?,
                a: sem_guard_operand_of_mir(
                    body,
                    ca,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
                b: sem_guard_operand_of_mir(
                    body,
                    cb,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
            }),
            // Trust: discriminant-guard leaf.
            Rvalue::Discriminant(place) => {
                let base = sem_discriminant_base_of_mir(
                    body,
                    place,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?;
                Some(SemCond {
                    op: SemCmpOp::Eq,
                    a: SemOperand::Discriminant(Box::new(base)),
                    b: SemOperand::Const(i128::try_from(tag).ok()?),
                })
            }
            _ => None,
        }
    };

    // Trust: SINGLE-TARGET DISCRIMINANT MATCH polarity (Item 1, wave-a) — whether
    // the SwitchInt discriminant temp is assigned from a `Rvalue::Discriminant` (an
    // ENUM-TAG read, `matches!(x, Variant_K)`) as opposed to a `Rvalue::BinaryOp` (a
    // Bool comparison). The two carry OPPOSITE single-target polarities: for a Bool
    // comparison the value-`0` edge is the comparison-FALSE (else) arm, whereas for a
    // tag read the value-`K` edge is the MATCHED (guard `disc == K` TRUE) arm. Same
    // single-static-assignment discipline `switch_leaf` enforces; a temp that is not a
    // bare projectionless local, is multiply-assigned, or is not a `Discriminant` read
    // answers `false` (defaulting to the pre-existing Bool-comparison polarity —
    // byte-identical to before). `switch_leaf` re-checks single-assignment, so a stray
    // `true` here can never produce a certificate on its own (belt-and-suspenders).
    let discr_is_tag_read = |discr: &Operand| -> bool {
        let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return false };
        if !dp.projections.is_empty() {
            return false;
        }
        let mut assigns = body.blocks.iter().flat_map(|b| &b.stmts).filter_map(|s| match s {
            Statement::Assign { place, rvalue, .. }
                if place.local == dp.local && place.projections.is_empty() =>
            {
                Some(rvalue)
            }
            _ => None,
        });
        matches!(assigns.next(), Some(Rvalue::Discriminant(_))) && assigns.next().is_none()
    };

    let (cond, else_arm_id, then_arm_id): (SemCondTree, BlockId, BlockId) =
        if let [(discr, targets, otherwise, bid)] = switches.as_slice() {
            match targets.as_slice() {
                // ---- single explicit target + `otherwise` ----
                [(k_val, k_target)] if discr_is_tag_read(discr) => {
                    // Trust: SINGLE-TARGET DISCRIMINANT MATCH — `matches!(x, Variant_K)`
                    // on a ≥3-variant enum lowers to ONE explicit tag edge + an
                    // `otherwise` false arm (`Bound::is_excluded`/`is_unbounded` on the
                    // 3-variant `Bound`). The value-`K` edge is the MATCHED arm (guard
                    // `disc == K` TRUE); `otherwise` is the guard-FALSE arm. K is READ
                    // FROM THE MIR switch value and threaded into the leaf's `Const(K)`,
                    // so ANY tag certifies (not just 0) and a wrong-K claim is
                    // KernelRejected (K is load-bearing in the kernel leaf — exactly like
                    // the straight-line `_0 := Eq(Disc, K)` discr-compare lane). This is
                    // the sound polarity: the pre-Item-1 code routed this shape through
                    // the Bool-comparison arm below, which INVERTED it (modeling `disc ==
                    // 0` as `disc != 0`) and only ever fired for K=0.
                    let leaf = switch_leaf(discr, *k_val)?;
                    let then_id = first_arm_on_path(body, *k_target, &arm_ids)?;
                    let else_id = first_arm_on_path(body, *otherwise, &arm_ids)?;
                    (SemCondTree::Leaf(leaf), else_id, then_id)
                }
                // ---- single SwitchInt: the bare `if cmp {…}` guard (UNCHANGED → Leaf) ----
                [(zero_val, else_target)] if *zero_val == 0 => {
                    let leaf = switch_leaf(discr, 0)?;
                    let else_id = first_arm_on_path(body, *else_target, &arm_ids)?;
                    let then_id = first_arm_on_path(body, *otherwise, &arm_ids)?;
                    (SemCondTree::Leaf(leaf), else_id, then_id)
                }
                // ---- Trust: discriminant-guard leaf — the EXHAUSTIVE 2-variant enum
                // match shape (`Either::is_left`-class): TWO explicit tag targets,
                // `otherwise` reaching an Unreachable block, TyCtxt-vetted exhaustive.
                [(tag_a, block_a), (_tag_b, block_b)] => {
                    if !exhaustive_two_arm_discriminant_switch(body, *bid, *otherwise) {
                        return None;
                    }
                    let leaf = switch_leaf(discr, *tag_a)?;
                    let else_id = first_arm_on_path(body, *block_b, &arm_ids)?;
                    let then_id = first_arm_on_path(body, *block_a, &arm_ids)?;
                    (SemCondTree::Leaf(leaf), else_id, then_id)
                }
                _ => return None,
            }
        } else {
            // ---- CONJUNCTIVE chain of ≥2 switches: `c1 && c2 && …` (→ And tree) ------
            // Trust: RANGE+DISJUNCTION guard — when the pure-conjunctive chain
            // declines (a value-0 edge lands on ANOTHER TEST instead of the common
            // else arm — the `is_ascii_control`-class `(range) || (eq)` control-flow
            // disjunction), fall back to the DECISION-DAG recognizer. The conjunctive
            // path runs FIRST unchanged, so every existing conjunctive witness is
            // byte-identical.
            sem_conjunctive_chain(body, &switches, &arm_ids, &switch_leaf).or_else(|| {
                sem_decision_dag_chain(body, &switches, &arm_ids, &switch_leaf, param_index)
            })?
        };

    if else_arm_id == then_arm_id {
        return None; // both exits reach the same arm — not a genuine two-way branch.
    }
    let else_arm = arms.iter().find(|b| b.id == else_arm_id)?;
    let then_arm = arms.iter().find(|b| b.id == then_arm_id)?;

    // (6) The arm values — modeled rvalues (each arm's assignment to the convergence
    //     local). Fail-closed if either is out of fragment (e.g. a `Neg` arm, which
    //     `SemRvalue` does not model — `abs` defers here, soundly).
    let then_rv = arm_value_rvalue_for(body, then_arm, join_local, param_index)?;
    let else_rv = arm_value_rvalue_for(body, else_arm, join_local, param_index)?;

    Some(SemCfReturn { cond, then_rv, else_rv })
}
