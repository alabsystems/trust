// ADT and struct return shapes recognised from a discriminant switch: which
// variant each arm constructs and what payload it carries. The opaque shapes
// cover returns whose payload type is not itself modeled, where only the
// variant structure is claimed.

use super::*;

/// Trust: HONEST FLOOR inc-2 (2026-07-23) — the GATE-ITER-GEN-KEY-DISCIPLINE admission gate.
/// A candidate T-STEP consumption is ADMITTED only when EVERY recognizer-trust binding holds;
/// otherwise it declines fail-closed. See [`TStepInstantiation`] and the `SemIterStep` doc.
///
/// This is the EXECUTABLE form of clauses (i)+(ii): the one-arg decline half
/// (`companion_carries_entry_iter_handle`) and the two-key admission (gen-key binding + recv
/// binding + advance). It has NO production caller — it is regression-protection.
#[must_use]
pub fn admit_t_step_instantiation(inst: &TStepInstantiation) -> TStepAdmission {
    // Clause (i) / F-BRIDGE: the one-arg entry-iter-handle decline half, wired. A T-STEP
    // consumption that also references the one-arg `iter_region`/`iter_has_next` family is
    // non-composable BY MECHANISM (two chained `next()` present the SAME carrier with a
    // DIFFERENT true remaining region), independent of the gen-key binding below.
    if inst.companion_carries_entry_iter_handle {
        return TStepAdmission::Decline(
            "F-BRIDGE: consumption references the one-arg entry-time iterator handle \
             (iter_region/iter_has_next) family — non-composable by mechanism"
                .to_string(),
        );
    }
    // Clause (ii): the generation key MUST be `Var(i_ghost)` — the ghost counter at THIS call
    // position. F-SAMEGEN (a literal `g`) and F-CHAIN-INERT (an unbound `g`) both decline here.
    match inst.gen_key {
        TStepGenKey::GhostCounter(i) if i == inst.ghost_counter => {}
        TStepGenKey::GhostCounter(i) => {
            return TStepAdmission::Decline(format!(
                "MALFORMED-BINDING: g bound to ghost slot {i} != this call's ghost counter {}",
                inst.ghost_counter
            ));
        }
        TStepGenKey::Literal(k) => {
            return TStepAdmission::Decline(format!(
                "F-SAMEGEN: g bound to literal generation {k}, not the ghost counter (two \
                 chained next() both at g=0 would reuse a generation)"
            ));
        }
        TStepGenKey::Unbound => {
            return TStepAdmission::Decline(
                "F-CHAIN-INERT: g is unbound (no ghost-counter loop behind this call) — a \
                 straight-line two-chained-next() caller declines"
                    .to_string(),
            );
        }
    }
    // MANDATORY exactly-+1 ADVANCE across the admitted receiver mutation (T-POST-SOME).
    if inst.advance != 1 {
        return TStepAdmission::Decline(format!(
            "DOUBLE-ADVANCE / MALFORMED: receiver mutation advances by {} != +1 (the ghost \
             counter increments by exactly 1 per admitted step)",
            inst.advance
        ));
    }
    // RECV-BINDING PIN: G3 result == G1/G2 header receiver == the T-STEP mint receiver param.
    if inst.into_iter_result_local != inst.header_receiver_local {
        return TStepAdmission::Decline(format!(
            "RECV-BINDING: into_iter result local {} != header next()-receiver local {}",
            inst.into_iter_result_local, inst.header_receiver_local
        ));
    }
    if inst.into_iter_result_local != inst.step_recv_param {
        return TStepAdmission::Decline(format!(
            "RECV-BINDING: bound recv local {} != the T-STEP mint receiver param {}",
            inst.into_iter_result_local, inst.step_recv_param
        ));
    }
    TStepAdmission::Admit
}

/// Trust: HONEST FLOOR inc-2 (2026-07-23) — the clause-(i) decline half wired at the loop
/// chokepoints: whether a projected [`SemLoopFunction`] smuggles the two-key / entry-time
/// iterator handle (a `SemCondTree::IterHasNext` guard or a `SemOperand::IterRegion` anywhere
/// in the body). This is the `SemLoopFunction`-level sibling of
/// [`crate::clean_ground::sem_adt_return_carries_entry_iter_handle`] (which scans a
/// `SemAdtReturn`), for the type that ACTUALLY flows through `loop_refinement_witness` /
/// `iter_loop_partial_witness`.
///
/// Today EVERY projected loop the recognizers build (slice-index, synthesized-counter,
/// break, nested, and the iter-loop ghost projection) names ONLY ghost/param Int slots, so
/// this is VACUOUSLY FALSE (the chokepoint guards below are byte-green). It is
/// regression-protection: it declines fail-closed if a future increment ever routes the
/// two-key handle through a projected loop — which the F12 grounder fence and the standing
/// composition refusal forbid.
#[must_use]
pub fn sem_loop_function_carries_entry_iter_handle(lf: &SemLoopFunction) -> bool {
    fn cond_has(c: &SemCondTree) -> bool {
        match c {
            SemCondTree::IterHasNext(_) => true,
            SemCondTree::And(a, b) | SemCondTree::Or(a, b) => cond_has(a) || cond_has(b),
            SemCondTree::Leaf(leaf) => op_has(&leaf.a) || op_has(&leaf.b),
        }
    }
    fn op_has(op: &SemOperand) -> bool {
        match op {
            SemOperand::IterRegion(_) => true,
            SemOperand::Move(b)
            | SemOperand::Len(b)
            | SemOperand::Field(b, _)
            | SemOperand::Discriminant(b)
            | SemOperand::Cast(b, _, _)
            | SemOperand::PreOp(b, _) => op_has(b),
            SemOperand::Index(a, b) => op_has(a) || op_has(b),
            SemOperand::Var(_) | SemOperand::Const(_) => false,
        }
    }
    fn rv_has(rv: &SemRvalue) -> bool {
        match rv {
            SemRvalue::Use(o) => op_has(o),
            SemRvalue::Bin(_, a, b) => op_has(a) || op_has(b),
            SemRvalue::Sel(c, a, b) => op_has(&c.a) || op_has(&c.b) || op_has(a) || op_has(b),
            SemRvalue::Cmp(_, a, b)
            | SemRvalue::Or(a, b)
            | SemRvalue::And(a, b)
            | SemRvalue::BitBin(_, a, b)
            | SemRvalue::ArithBin(_, a, b) => rv_has(a) || rv_has(b),
        }
    }
    cond_has(&lf.cond) || lf.body.iter().any(|s| rv_has(&s.rvalue))
}

/// Map rustc MIR's declaration-order aggregate variant INDEX to the enum's actual
/// declared discriminant.  This is deliberately first-class-metadata-only: legacy
/// flattened `Ty::Adt { variants: [] }` values cannot distinguish an index from an
/// explicit `#[repr]` discriminant and therefore decline instead of inventing one.
pub(super) fn aggregate_variant_discriminant(
    destination_ty: &trust_types::Ty,
    aggregate_name: &str,
    variant_index: usize,
) -> Option<i128> {
    let trust_types::Ty::Adt { name, variants, .. } = destination_ty else { return None };
    if name != aggregate_name {
        return None;
    }
    variants.get(variant_index).map(|variant| variant.discriminant)
}

/// Recognize the ADT-RETURN shape: `if cond { <construct variant A> } else { <construct
/// variant B> }`, `A != B`, both variants of the SAME outer enum named by the
/// function's own return type. Reuses steps (1)-(5) of [`sem_cf_return_of_mir`]
/// VERBATIM (the guard/arm/join extraction — the two recognizers are siblings, not a
/// refactor, matching this file's established duplication-over-coupling convention
/// for `sem_cf_return_of_mir`/`sem_nested_branch_of_mir`'s shared `switch_leaf`);
/// diverges ONLY at the arm-value step, calling [`arm_adt_ctor_value_for`] instead of
/// [`arm_value_rvalue_for`]. Fail-closed (`None`) on anything outside the recognized
/// fragment — a >1-field variant payload, a multiply-assigned/aliased temp, an extra
/// write to `_0`, a mismatched outer enum name, or identical then/else variants.
#[must_use]
pub fn sem_adt_return_shape_of(func: &trust_types::VerifiableFunction) -> Option<SemAdtReturn> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1)-(2): the convergence local + the two Goto arm blocks — VERBATIM copy of
    // `sem_cf_return_of_mir`'s steps (1)-(2).
    let ret_block = unique_return_block(body)?;
    let assigns_local = |b: &trust_types::BasicBlock, loc: usize| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == loc && place.projections.is_empty())
        })
    };
    let join_local = guarded_return_join_local(body, ret_block)?;
    if join_local != 0 {
        return None; // this lane models direct enum construction into `_0` only.
    }
    let assigns_0 = |b: &trust_types::BasicBlock| assigns_local(b, join_local);
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Goto(_)) && assigns_0(b))
        .collect();
    if arms.len() != 2 {
        return None;
    }
    let Terminator::Goto(j0) = arms[0].terminator else { return None };
    let Terminator::Goto(j1) = arms[1].terminator else { return None };
    if j0 != j1 {
        return None;
    }

    // Trust: ADT-return well-formedness — `_0` (the RETURN local, distinct from an
    // arbitrary join-via-temp) must be written EXACTLY in these two arm blocks and
    // NOWHERE else in the whole function (adversarial probe (c): an extra write to
    // `_0` after construction must decline). `join_local` may legitimately be a
    // join-via-temp with its own writes elsewhere; the invariant applies to the
    // OUTER return local `0` specifically.
    if !local_has_only_guarded_writes(body, 0, 2, 0) {
        return None;
    }

    // Trust: RECORD-WITNESS inc-2 (ok/err drop-ladder epilogue, 2026-07-22) — the
    // `Result::ok`/`Result::err` bodies converge (both arms `Goto`) at a VALUE-TRANSPARENT
    // conditional-drop ladder (a SECOND `SwitchInt(Discriminant(self))` routing ONLY to
    // `Return` / `Drop(self) → Return` / `Unreachable`) AFTER the `Option` aggregate,
    // rather than directly at the sole `Return` block. Recognize it fail-closed here; when
    // present its `SwitchInt` is EXCLUDED from the guard analysis and entry-rooting is
    // checked THROUGH the ladder. `None` (byte-unchanged) for EVERY non-ladder shape: for
    // those `j0` IS the `Return` block (or a non-ladder block the existing entry-rooting
    // already declines), so the detector returns immediately.
    let drop_ladder = recognize_drop_ladder_epilogue(body, j0);

    // (3): the guard SwitchInt(s) — VERBATIM copy of `sem_cf_return_of_mir`'s step (3),
    // with the recognized drop-ladder's OWN `SwitchInt` filtered out (it is an epilogue,
    // never a guard). The filter is a NO-OP whenever `drop_ladder` is `None`.
    let mut switches: Vec<(&Operand, &Vec<(u128, BlockId)>, BlockId, BlockId)> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                Some((discr, targets, *otherwise, b.id))
            }
            _ => None,
        })
        .collect();
    if let Some(ladder) = &drop_ladder {
        switches.retain(|(_, _, _, id)| *id != ladder.switch_block);
    }
    if switches.is_empty() {
        return None;
    }
    let arm_ids: Vec<BlockId> = arms.iter().map(|b| b.id).collect();
    let decision_ids: Vec<BlockId> = switches.iter().map(|(_, _, _, id)| *id).collect();
    let entry_rooted = if let Some(ladder) = &drop_ladder {
        drop_ladder_cfg_is_entry_rooted(body, ladder.switch_block, &arm_ids, &decision_ids)
    } else {
        guarded_cfg_is_entry_rooted(body, j0, &arm_ids, &decision_ids)
    };
    if !entry_rooted {
        return None;
    }

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
                a: sem_adt_guard_operand_of_mir(
                    body,
                    ca,
                    &param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
                b: sem_adt_guard_operand_of_mir(
                    body,
                    cb,
                    &param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
            }),
            Rvalue::Discriminant(place) => {
                let base = sem_discriminant_base_of_mir(
                    body,
                    place,
                    &param_index,
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

    // Trust: RECORD-WITNESS inc-2 — alongside the guard, the TAG↔DOWNCAST expected self
    // variant for each arm (`Some` ONLY for a two-target discriminant dispatch over a
    // 2-variant `disc_index_safe` self enum; `None` everywhere else, so a downcast-field
    // payload declines outside that shape). Derived straight from THIS branch's
    // (tag_a → then, tag_b → else) mapping so the polarity is unambiguous — never
    // re-derived from `cond` (whose single-target form has the opposite polarity).
    let (cond, else_arm_id, then_arm_id, then_expected_variant, else_expected_variant): (
        SemCondTree,
        BlockId,
        BlockId,
        Option<usize>,
        Option<usize>,
    ) = if let [(discr, targets, otherwise, bid)] = switches.as_slice() {
        match targets.as_slice() {
            [(zero_val, else_target)] if *zero_val == 0 => {
                let leaf = switch_leaf(discr, 0)?;
                let else_id = first_arm_on_path(body, *else_target, &arm_ids)?;
                let then_id = first_arm_on_path(body, *otherwise, &arm_ids)?;
                (SemCondTree::Leaf(leaf), else_id, then_id, None, None)
            }
            [(tag_a, block_a), (tag_b, block_b)] => {
                if !exhaustive_two_arm_discriminant_switch(body, *bid, *otherwise) {
                    return None;
                }
                let leaf = switch_leaf(discr, *tag_a)?;
                let else_id = first_arm_on_path(body, *block_b, &arm_ids)?;
                let then_id = first_arm_on_path(body, *block_a, &arm_ids)?;
                let (then_ev, else_ev) =
                    downcast_expected_variants(body, &leaf, *tag_a, *tag_b, &param_index);
                (SemCondTree::Leaf(leaf), else_id, then_id, then_ev, else_ev)
            }
            _ => return None,
        }
    } else {
        let (cond, else_id, then_id) =
            sem_conjunctive_chain(body, &switches, &arm_ids, &switch_leaf)?;
        (cond, else_id, then_id, None, None)
    };

    if else_arm_id == then_arm_id {
        return None;
    }
    let else_arm = arms.iter().find(|b| b.id == else_arm_id)?;
    let then_arm = arms.iter().find(|b| b.id == then_arm_id)?;

    // Trust: RECORD-WITNESS inc-2 — gate B(i): a recognized drop-ladder must re-read the
    // discriminant of the SAME self local the DISPATCH read. The dispatch self local is
    // the base of a two-target discriminant guard; a ladder present under any other guard
    // shape (a comparison, a non-discriminant dispatch) is malformed and fails closed.
    if let Some(ladder) = &drop_ladder
        && dispatch_self_local(&cond) != Some(ladder.self_local)
    {
        return None;
    }

    // (5.5) Trust: W20 REFERENCE-RETURN guard↔projection coherence — the from_end-aware
    // ConstantIndex bounds gate. Runs HERE (guard `cond` in hand, BEFORE the step-6 arm
    // value construction) because `arm_adt_ctor_value_for` has no guard access — exactly
    // the siting the ratified adversarial-correctness verdict demands. A NO-OP for every
    // non-slice-reference return (existing ADT-return lanes are byte-unaffected); for a
    // `Some(&s[i])` payload it is the SOLE net against an out-of-bounds ConstantIndex
    // forgery (trust-vcgen's `constant_index_projection_vc` is from_end-BLIND, so the
    // `from_end:true` `1 <= o` clause is singly load-bearing) and against a
    // branch-polarity swap / a guard keyed to a different slice handle.
    if !slice_ref_return_guard_coherent(body, then_arm, else_arm, join_local, &param_index, &cond) {
        return None;
    }

    // (6) NEW: the ADT-constructed arm values (the divergence point from
    // `sem_cf_return_of_mir`). The per-arm `expected_variant` carries the TAG↔DOWNCAST
    // provenance for a `Result::ok`/`err`-class downcast-field payload (`None` for every
    // other arm — no downcast admitted).
    let then_ctor =
        arm_adt_ctor_value_for(body, then_arm, join_local, &param_index, then_expected_variant)?;
    let else_ctor =
        arm_adt_ctor_value_for(body, else_arm, join_local, &param_index, else_expected_variant)?;
    if then_ctor.variant == else_ctor.variant {
        return None; // not a genuine two-variant dispatch.
    }

    // The outer enum's name — read from the RETURN TYPE (never assumed), and cross-
    // checked (inside `arm_adt_ctor_value_for`) against each arm's own Aggregate.
    let trust_types::Ty::Adt { name: enum_name, .. } = &body.return_ty else { return None };

    Some(SemAdtReturn {
        cond,
        then_arm: then_ctor,
        else_arm: else_ctor,
        enum_name: enum_name.clone(),
    })
}

/// Recognize an ARM's ADT-constructed return value: the arm block's SOLE assignment
/// to `join_local` (bare, no projections) must be `Rvalue::Aggregate(AggregateKind::Adt
/// {name, variant, active_field: None}, operands)` with `operands.len() <= 1` (a
/// nullary or single-field variant — the `Ok(x)`/`Err(e)`/`Some(x)`/`None` family;
/// a 2+-field variant payload is OUT OF SCOPE for this increment, declined). The
/// single operand, if present, must be a `Move`/`Copy` of a local with NO
/// projections — a bare `Operand::Constant` payload (a literal-valued arm, e.g.
/// `Ok(0)`) is OUT OF SCOPE for this increment and declines here (this only ever
/// admits a `Move`/`Copy` of a PLACE; [`sem_operand_of_mir`]'s own `Constant` arm is
/// unreachable from this call site by construction). Resolved either directly (a
/// parameter — [`sem_operand_of_mir`]) or, for a scratch temp, through its OWN single
/// `Statement::Assign` (gated by
/// [`crate::prove::local_soundly_resolvable`] — the well-formedness discipline that
/// declines a multiply-assigned or call-dest/mutably-aliased temp, closing
/// adversarial probe (b)): a `Use` rvalue resolves to a [`SemAdtPayload::Scalar`],
/// while an integer `Cast` retains its exact destination width/signedness in
/// [`SemAdtPayload::IntCast`]; a ZERO-operand `Aggregate` (a nested
/// fieldless-variant construction) resolves to a [`SemAdtPayload::NullaryNested`].
/// Fail-closed (`None`) on anything else — an `active_field: Some(_)` union-repr
/// aggregate, a 2+-operand aggregate, a projected/multiply-assigned payload local,
/// or a payload rvalue outside the {Cast, Use, nullary Aggregate} fragment.
///
/// Trust: RECORD-WITNESS inc-2 (ok/err, 2026-07-22) — a `Use` payload that reads a
/// DOWNCAST + FIELD off the dispatched self enum (`Use(Move((_self as v#N).f))`, the
/// `Result::ok`/`err` `Some(x)` payload) resolves to a [`SemAdtPayload::DowncastField`]
/// (see [`downcast_field_payload`]) when `expected_downcast_variant == Some(N)` — the
/// TAG↔DOWNCAST provenance the caller established for this arm's path. Every other arm
/// passes `None`, so no downcast payload is ever admitted outside the discriminant
/// dispatch that pins its variant.
pub(super) fn arm_adt_ctor_value_for(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    expected_downcast_variant: Option<usize>,
) -> Option<SemAdtArm> {
    use trust_types::{AggregateKind, Operand, Rvalue};
    let (use_statement, rv) =
        arm.stmts.iter().enumerate().rev().find_map(|(statement_index, statement)| {
            crate::assignment_types::assigned_local_rvalue(body, statement, join_local)
                .map(|rvalue| (statement_index, rvalue))
        })?;
    let Rvalue::Aggregate(
        AggregateKind::Adt { name, variant: variant_index, active_field, .. },
        operands,
    ) = rv
    else {
        return None;
    };
    if active_field.is_some() {
        return None; // union-repr aggregate — out of scope.
    }
    if operands.len() > 1 {
        return None; // 2+-field variant payload — out of scope for this increment.
    }
    let return_local_ty = &body.locals.get(join_local)?.ty;
    if join_local == 0 && return_local_ty != &body.return_ty {
        return None;
    }
    let variant = aggregate_variant_discriminant(return_local_ty, name, *variant_index)?;
    let Some(payload_op) = operands.first() else {
        return Some(SemAdtArm { variant, payload: None });
    };
    let (Operand::Copy(p) | Operand::Move(p)) = payload_op else { return None };
    if !p.projections.is_empty() {
        return None;
    }
    // A direct parameter/constant payload — resolve without any temp-tracing.
    if let Some(direct) = sem_operand_of_mir(body, payload_op, param_index) {
        return Some(SemAdtArm { variant, payload: Some(SemAdtPayload::Scalar(direct)) });
    }
    // A scratch temp: it must be the ARM's OWN local (this arm's sole-writer
    // discipline), soundly resolvable (single-assign, not a call dest, not
    // mutably-aliased — closes adversarial probe (b)).
    if param_index(p.local).is_some() || !crate::prove::local_soundly_resolvable(body, p.local) {
        return None;
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, p.local, arm.id, Some(use_statement))?;
    let definition_site = Some((definition_block, Some(definition_statement)));
    match definition {
        // Preserve the actual integer-cast semantics.  Merely reaching this arm
        // under some guard is not evidence that a narrowing/sign-changing cast is
        // the identity; the destination metadata therefore remains in the witness.
        Rvalue::Cast(op, dest_ty) => {
            let trust_types::Ty::Int { width, signed } = dest_ty else { return None };
            if !matches!(*width, 8 | 16 | 32 | 64 | 128)
                || !matches!(op,
                    Operand::Copy(source) | Operand::Move(source)
                        if source.projections.is_empty()
                            && matches!(body.locals.get(source.local).map(|local| &local.ty),
                                Some(trust_types::Ty::Int { .. })))
            {
                return None;
            }
            let source = resolve_cast_source_operand(body, op, param_index, definition_site)?;
            Some(SemAdtArm {
                variant,
                payload: Some(SemAdtPayload::IntCast { source, width: *width, signed: *signed }),
            })
        }
        Rvalue::Use(op) => {
            // Trust: RECORD-WITNESS inc-2 (ok/err, 2026-07-22) — a DOWNCAST + FIELD read
            // off the dispatched self enum (`Move((_self as v#N).f)`, the
            // `Result::ok`/`err` `Some(payload)`). Admitted ONLY under the TAG↔DOWNCAST
            // provenance link + the VARIANT-DISJOINT flattened `idxElem` key; the scalar
            // path below handles every non-downcast `Use` unchanged.
            if let Some(payload) =
                downcast_field_payload(body, op, param_index, expected_downcast_variant)
            {
                return Some(SemAdtArm { variant, payload: Some(payload) });
            }
            let resolved = resolve_cast_source_operand(body, op, param_index, definition_site)?;
            Some(SemAdtArm { variant, payload: Some(SemAdtPayload::Scalar(resolved)) })
        }
        // A NESTED fieldless-variant construction (`Error::Underflow`-class): a
        // ZERO-operand Aggregate.  Its enum name and declaration-order index are
        // checked against the payload local's declared first-class enum metadata;
        // the reported value is that variant's actual discriminant.
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: nested_name,
                variant: nested_variant,
                active_field: nested_active, .. },
            nested_ops,
        ) if nested_active.is_none() && nested_ops.is_empty() => {
            let nested_variant = aggregate_variant_discriminant(
                &body.locals.get(p.local)?.ty,
                nested_name,
                *nested_variant,
            )?;
            Some(SemAdtArm {
                variant,
                payload: Some(SemAdtPayload::NullaryNested {
                    enum_name: nested_name.clone(),
                    variant: nested_variant,
                }),
            })
        }
        // Trust: W20 REFERENCE-RETURN (idx-elem VALUE tier, 2026-07-21) — the payload
        // temp of `Some(&s[i])` is `_p := Ref { mutable: false, place: base[Deref,
        // Index(k) | ConstantIndex{..}] }` (`core::slice::<[i32]>::first`,
        // `<usize as SliceIndex<[i32]>>::get`). An immutable reference RETURN denotes its
        // referent's ELEMENT VALUE at the idx_elem tier: `Some(&s[0])` certifies as "Some
        // of the element-0 value-slot" — `idxElem(s, 0)` — deref-transparently, consistent
        // with W-REF-FWD's ref/deref cancellation and &self-param transparency. This is
        // NOT an address/aliasing claim. This arm recognizes the projection + the
        // base/raw-exposure/mutability gates and mints the `idxElem` payload; the
        // guard↔projection COHERENCE (from_end-aware bounds) is enforced UPSTREAM in
        // `sem_adt_return_shape_of` (step 5.5), which has the guard this call site lacks.
        Rvalue::Ref { mutable: false, place } => {
            let proj = slice_ref_projection_of_ref_place(
                body,
                place,
                param_index,
                (definition_block, Some(definition_statement)),
            )?;
            // `from_end:true` (`slice::last`) denotes index `sliceLen(s) - offset`, which
            // no current `SemOperand` composes (no Sub / Len-minus-const carrier; `PreOp`
            // is Not/Neg only) — decline HONESTLY here (fail-closed `None`).
            let idx = proj.kind.index_operand()?;
            Some(SemAdtArm {
                variant,
                payload: Some(SemAdtPayload::Scalar(SemOperand::Index(
                    Box::new(SemOperand::Var(proj.base_param)),
                    Box::new(idx),
                ))),
            })
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Trust: RECORD-WITNESS inc-2 (ok/err DowncastField + value-transparent drop-ladder
// epilogue, 2026-07-22) — the two scoped recognizer extensions that flip
// `Result::<T,E>::ok`/`err` (`match self { Ok(x) => Some(x), Err(_) => None }` and its
// mirror) through the EXISTING 2-arm `Bool.rec`/`congrArg` kernel recipe. The kernel
// side is UNCHANGED; these add (1) a DOWNCAST + FIELD payload denoting at a
// VARIANT-DISJOINT flattened `idxElem` key with a TAG↔DOWNCAST provenance pin, and (2)
// fail-closed recognition of the post-`Option`-aggregate conditional-drop ladder.
// ---------------------------------------------------------------------------
/// Trust: RECORD-WITNESS inc-2 — resolve `Move/Copy((_self as v#N).f)` (a DOWNCAST +
/// FIELD read off the dispatched self enum) to a [`SemAdtPayload::DowncastField`] at the
/// VARIANT-DISJOINT flattened `idxElem` key. Fail-closed (`None`) unless ALL hold:
///   * `op` is a `Copy`/`Move` of a place whose projections are EXACTLY
///     `[Downcast(v), Field(f)]`;
///   * the base is a PARAMETER (the by-value `self`), NOT reassigned/aliased
///     ([`param_reassigned_by_stmt`] — which flags statement writes / mutable aliases /
///     call-dest writes but NOT a `Drop`, so a post-Aggregate `Drop(self)` in the ladder
///     leaves this entry-time read value-faithful, closing gate C for the payload root);
///   * the base's type is a `disc_index_safe` enum `Ty::Adt` — a niche layout declines
///     (a flattened-slot read on the wrong variant would be unsound);
///   * TAG↔DOWNCAST provenance (gate D): `v == expected_downcast_variant` — the downcast
///     variant equals the variant the dispatch arm established for this path (a mismatch,
///     or a caller that could not establish one, declines);
///   * the within-variant field `f` exists and its type is a scalar `Ty::Int`, and its
///     FLATTENED name `__v{v}_{field_name}` resolves to a position (≥ 1) in the self
///     `Ty::Adt.fields` (gate A / DOWNCAST-KEY-DISJOINTNESS) — that position is the
///     disjoint key; a legacy / non-flattened dump (missing the `__v..` field) declines.
pub(super) fn downcast_field_payload(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    expected_downcast_variant: Option<usize>,
) -> Option<SemAdtPayload> {
    use trust_types::{Operand, Projection, Ty};
    let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
    let [Projection::Downcast(v), Projection::Field(f)] = p.projections.as_slice() else {
        return None;
    };
    // The base is the by-value `self` PARAMETER, not reassigned/aliased.
    let base_param = param_index(p.local)?;
    if param_reassigned_by_stmt(body, p.local) {
        return None;
    }
    // TAG↔DOWNCAST provenance (gate D).
    if expected_downcast_variant != Some(*v) {
        return None;
    }
    let self_ty = &body.locals.get(p.local)?.ty;
    let Ty::Adt { variants, fields, .. } = self_ty else { return None };
    if variants.is_empty() || !self_ty.disc_index_safe() {
        return None; // not an enum, or a niche layout (unsound off-variant slot read).
    }
    let variant_def = variants.get(*v)?;
    let (field_name, field_ty) = variant_def.fields.get(*f)?;
    if !matches!(field_ty, Ty::Int { .. }) {
        return None; // a non-scalar payload (String / nested ADT) declines.
    }
    // DOWNCAST-KEY-DISJOINTNESS (gate A): the VARIANT-DISJOINT flattened `idxElem` key is
    // the position of `__v{v}_{field}` in the flattened `fields` list — NEVER the
    // within-variant index `f`. Derived from the dump's own first-class field metadata;
    // fail-closed if that flattened name is absent (a legacy / non-flattened dump).
    let flat_name = format!("__v{v}_{field_name}");
    let flat_key = fields.iter().position(|(name, _)| name == &flat_name)?;
    let flat_key = u64::try_from(flat_key).ok()?;
    if flat_key == 0 {
        return None; // the `__tag` slot is never a payload field (belt-and-suspenders).
    }
    Some(SemAdtPayload::DowncastField { base_param, flat_key, downcast_variant: *v })
}

/// Trust: RECORD-WITNESS inc-2 — the TAG↔DOWNCAST expected self variant for each arm of a
/// TWO-TARGET discriminant dispatch, mapped straight from the branch's `(tag_then → then,
/// tag_else → else)` tag assignment through the self enum's first-class variant metadata.
/// `(None, None)` (so a downcast-field payload declines) unless the guard `leaf` is a
/// discriminant-equality read of a bare `self` PARAMETER whose type is a 2-variant
/// `disc_index_safe` enum. The polarity is UNAMBIGUOUS here (the caller passes the tags in
/// then/else order), unlike a re-derivation from the collapsed `cond`.
pub(super) fn downcast_expected_variants(
    body: &trust_types::VerifiableBody,
    leaf: &SemCond,
    tag_then: u128,
    tag_else: u128,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> (Option<usize>, Option<usize>) {
    let none = (None, None);
    if leaf.op != SemCmpOp::Eq {
        return none;
    }
    let SemOperand::Discriminant(base) = &leaf.a else { return none };
    let SemOperand::Var(sp) = base.as_ref() else { return none };
    let Some(self_local) = usize::try_from(*sp).ok().and_then(|s| s.checked_add(1)) else {
        return none;
    };
    if param_index(self_local) != Some(*sp) {
        return none;
    }
    let Some(local) = body.locals.get(self_local) else { return none };
    let trust_types::Ty::Adt { variants, .. } = &local.ty else { return none };
    if variants.len() != 2 || !local.ty.disc_index_safe() {
        return none;
    }
    let (Ok(tag_then), Ok(tag_else)) = (i128::try_from(tag_then), i128::try_from(tag_else)) else {
        return none;
    };
    let then_v = variants.iter().position(|variant| variant.discriminant == tag_then);
    let else_v = variants.iter().position(|variant| variant.discriminant == tag_else);
    (then_v, else_v)
}

/// Trust: RECORD-WITNESS inc-2 — the dispatch self local from a two-target discriminant
/// guard `Discriminant(Var(sp)) == _` (`Some(sp + 1)`); `None` for any other guard. Used
/// to pin gate B(i): the drop-ladder must re-read the SAME self local the dispatch read.
pub(super) fn dispatch_self_local(cond: &SemCondTree) -> Option<usize> {
    let SemCondTree::Leaf(SemCond { op: SemCmpOp::Eq, a: SemOperand::Discriminant(base), .. }) =
        cond
    else {
        return None;
    };
    let SemOperand::Var(sp) = base.as_ref() else { return None };
    usize::try_from(*sp).ok()?.checked_add(1)
}

/// Trust: RECORD-WITNESS inc-2 — recognize a VALUE-TRANSPARENT conditional-drop ladder
/// epilogue at `head` (the arms' common `Goto` target): the `Result::ok`/`err`
/// post-`Option`-aggregate tail
/// ```text
///   head: _t = Discriminant(self);  SwitchInt(_t) { .. -> Return | Drop(self) | Unreachable }
///   drop: Drop(self) -> Return
///   ret:  Return
/// ```
/// Fail-closed (`None`) unless ALL hold (gates B/C):
///   (i)   `head` ends in a `SwitchInt` over a bare temp `_t`, and its ONLY value work is
///         `_t = Discriminant(self)` (a bare read of a modeled-enum self local; storage
///         markers tolerated) — ZERO `_0` writes / any other statement declines (gate
///         B(ii));
///   (ii)  EVERY `SwitchInt` target (incl. `otherwise`) is a statement-free `Return`
///         block (the sole return), a statement-free `Drop { place: self } -> Return`
///         block (gate B(iii): the `Drop` place is EXACTLY the dispatched self local), or
///         a statement-free `Unreachable` — the ladder does NOTHING but conditionally drop
///         `self` and return (gate B(iv): every target converges to the sole `Return`).
/// The caller cross-checks `self_local` EQUAL to the dispatch self local (gate B(i)) and
/// EXCLUDES `head`'s `SwitchInt` from the guard analysis. Returns immediately for every
/// non-ladder shape (a `Return`-terminated join is not a `SwitchInt`).
pub(super) fn recognize_drop_ladder_epilogue(
    body: &trust_types::VerifiableBody,
    head: trust_types::BlockId,
) -> Option<DropLadderEpilogue> {
    use trust_types::{Operand, Rvalue, Statement, Terminator};
    let head_block = body.blocks.iter().find(|b| b.id == head)?;
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &head_block.terminator else {
        return None;
    };
    let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
    if !dp.projections.is_empty() {
        return None;
    }
    // (i) the head does NOTHING but `_t = Discriminant(self)` — no `_0` write, no other
    //     effect (storage markers tolerated).
    let mut discriminant_reads = 0usize;
    for statement in &head_block.stmts {
        match statement {
            Statement::Assign { place, rvalue, .. }
                if place.local == dp.local && place.projections.is_empty() =>
            {
                if !matches!(rvalue, Rvalue::Discriminant(_)) {
                    return None;
                }
                discriminant_reads += 1;
            }
            Statement::StorageLive(_) | Statement::StorageDead(_) | Statement::Nop => {}
            _ => return None,
        }
    }
    if discriminant_reads != 1 {
        return None;
    }
    // Resolve `_t`'s dominating definition `_t = Discriminant(self)` and read the self
    // local (a bare, modeled-enum place).
    let (_, _, rvalue) = dominating_switch_discriminant_rvalue(body, dp.local)?;
    let Rvalue::Discriminant(self_place) = rvalue else { return None };
    if !self_place.projections.is_empty() {
        return None;
    }
    let self_local = self_place.local;
    if crate::assignment_types::modeled_enum_variant_count(&body.locals.get(self_local)?.ty)
        .is_none()
    {
        return None;
    }
    let ret = unique_return_block(body)?;
    // (ii) every target is Return / Drop(self)→Return / Unreachable — nothing else.
    let mut reaches_return = false;
    for target in targets.iter().map(|(_, t)| *t).chain(std::iter::once(*otherwise)) {
        let block = body.blocks.iter().find(|b| b.id == target)?;
        if !block.stmts.is_empty() {
            return None; // a ladder block does no value work.
        }
        match &block.terminator {
            Terminator::Return => {
                if target != ret.id {
                    return None;
                }
                reaches_return = true;
            }
            Terminator::Drop { place, target: drop_target, .. } => {
                if place.local != self_local || !place.projections.is_empty() {
                    return None; // gate B(iii): the Drop place is EXACTLY the self local.
                }
                if *drop_target != ret.id {
                    return None; // gate B(iv): the drop converges to the sole Return.
                }
            }
            Terminator::Unreachable => {}
            _ => return None,
        }
    }
    if !reaches_return {
        return None; // the ladder must actually reach the Return.
    }
    Some(DropLadderEpilogue { switch_block: head, self_local })
}

/// Trust: RECORD-WITNESS inc-2 — the drop-ladder analogue of [`guarded_cfg_is_entry_rooted`]:
/// the arms + decisions + `ladder_head` are reachable from entry, and the deterministic
/// entry `Goto`/`Assert` prefix hits a modeled decision before any arm / the ladder head.
/// The ladder head → sole `Return` convergence is verified SEPARATELY by
/// [`recognize_drop_ladder_epilogue`], so this treats `ladder_head` as the (post-ladder)
/// join terminal instead of requiring `join == ret` (which the epilogue's `Goto` target is
/// NOT — it is the ladder's `SwitchInt` block).
pub(super) fn drop_ladder_cfg_is_entry_rooted(
    body: &trust_types::VerifiableBody,
    ladder_head: trust_types::BlockId,
    arms: &[trust_types::BlockId],
    decisions: &[trust_types::BlockId],
) -> bool {
    use std::collections::HashSet;

    use trust_types::{BlockId, Terminator};

    if arms.len() < 2 || decisions.is_empty() {
        return false;
    }
    let Some(ret) = unique_return_block(body) else { return false };
    let Some(reachable) = cfg_reachable_from(body, BlockId(0)) else { return false };
    if !reachable.contains(&ret.id)
        || !reachable.contains(&ladder_head)
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
        if arm_set.contains(&current) || current == ret.id || current == ladder_head {
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

// ---------------------------------------------------------------------------
// Trust: RECORD-WITNESS (single-variant struct-constructor, increment 1, 2026-07-22)
// — the bare `fn new(a, b) -> S { S { a, b } }` shape (`expr::types::BinderData::new`-
// class): a STRAIGHT-LINE body whose sole `_0` write is a single-variant struct
// Aggregate immediately followed by `Return`. Genuinely NEW: `arm_adt_ctor_value_for`
// (above) caps operands at ≤ 1 and lives inside the two-arm SwitchInt enum family;
// this recognizes the guard-free multi-field CONCRETE struct constructor. Its kernel
// witness (`trustir_adt::check_struct_return_refinement`) is guard-free `Eq.refl`, so
// EVERY soundness gate lives HERE.
// ---------------------------------------------------------------------------
/// A Unit-CARRIER field type: `Ty::Unit`, or the exact canonical `PhantomData` marker,
/// which `reflect::reflect_struct` reflects to the kernel `Unit` carrier
/// (`reflect_struct_product([]) = Trust.Sort.Unit`). Empty ADT shape alone is
/// insufficient because it also represents bare generic parameters and cannot
/// distinguish an empty enum from a unit struct. A field of this type is a marker:
/// its Aggregate operand is a `ConstValue::Unit`, and its `.mk` argument is the closed
/// `Unit.unit`.
// Trust: RECORD-WITNESS increment 3 — widened to `pub(crate)` (hardened body kept) so
// the sibling `clean_ground` folded recognizer reuses the SAME marker-field predicate.
pub(crate) fn is_unit_carrier_ty(ty: &trust_types::Ty) -> bool {
    matches!(ty, trust_types::Ty::Unit) || crate::assignment_types::is_canonical_unit_marker_ty(ty)
}

/// Recognize the RECORD (single-variant struct-constructor) return shape:
/// `fn f(..) -> S { S { f_0, .., f_n } }` lowering to a STRAIGHT-LINE body whose SOLE
/// `_0` write is `_0 = Aggregate(AggregateKind::Adt { <S>, variant 0, active_field:
/// None }, [op_0 .. op_n])` immediately followed by `Return`. `None` (fail-closed) on
/// anything outside the recognized fragment. The gates, ALL mandatory (the kernel
/// witness is guard-free, so soundness is entirely here):
///
/// - **(1) fresh-metadata** — the return type is a struct (`Ty::Adt`, `variants: []`)
///   with real first-class field metadata; a legacy `__tag`/`__v`-flattened dump (the
///   only `BinderData::new` corpus form) declines.
/// - **(2) return-type cross-check** — the Aggregate's ADT name equals the return
///   type's, its variant index is 0, `active_field` is `None`
///   (gate B — `assignment_types` passes `active_field: Some` rows, so it is no
///   defense here), and its operand count equals the declared field count.
/// - **(3) carrier admission** — `reflect_struct` + `register_adt_carriers`, then
///   RE-GET the registry (a gate-failed inductive stays in the env but out of the
///   registry) and require presence, `type_params` empty (concrete-only, gate 7 — a
///   Pi-wrapped generic `.mk` is deferred), and `.mk` arity == operand count.
/// - **(4) sole-writer** — exactly one bare `_0` assign in the WHOLE body, zero
///   projected `_0.f` writes, zero call-dest / drop of `_0`, no mutable alias
///   (`local_has_only_guarded_writes(body, 0, 1, 0)`); nothing references `_0` between
///   the Aggregate and `Return`.
/// - **(C) spine-statement whitelist** — every terminator is `Goto`/`Return` (NO
///   `SwitchInt`/`Call`/`Drop`/`Assert`), every statement is a storage marker or an
///   UNPROJECTED `Assign` (a deref/field/index-base write — e.g. an
///   `AddressOf(false)`→`*mut` cast-chain store, invisible to `param_reassigned_by_stmt`
///   — has a PROJECTED place and declines).
/// - **(A) PARAM-ROOT admission** — each scalar operand routes through the
///   [`sem_operand_of_mir`] chokepoint, which resolves a bare parameter place to an
///   entry `Var` ONLY when it is `Int`/`Bool` and NOT reassigned
///   (`!param_reassigned_by_stmt`: no direct write, no `&mut`/`&raw mut` alias, no
///   call-dest anywhere). A reassigned-param / non-scalar root fails closed.
/// - **UNIT markers** — a Unit-carrier field ([`is_unit_carrier_ty`]) admits ONLY a
///   `ConstValue::Unit` operand (an `Int`/`Bool` constant in a Unit slot, or vice
///   versa, declines).
/// - **(E) pointer decline** — a pointer/ref/nested-struct/slice field is OUT of
///   increment 1 and declines here (raw-ptr / `NonNull` roots are NOT admitted until
///   `sliceStart`/`ptrOffset` land in increment 3, with their own gates).
#[must_use]
pub fn sem_struct_return_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemStructReturn> {
    use trust_types::{AggregateKind, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1) The return type is a CONCRETE struct with FRESH first-class field metadata.
    let Ty::Adt { name: ret_name, fields: ret_fields, variants, .. } = &body.return_ty else {
        return None;
    };
    if !variants.is_empty() {
        return None; // an ENUM return is the `SemAdtReturn` family's business.
    }
    if ret_fields.is_empty() {
        return None; // a FIELDLESS struct — `reflect_struct` declines it (the ZST lane's shape).
    }
    if ret_fields.iter().any(|(fname, _)| fname == "__tag" || fname.starts_with("__v")) {
        return None; // a LEGACY `__tag`/`__v`-flattened dump — decline (fresh-metadata gate).
    }

    // (4) SOLE-WRITER: exactly one bare `_0` assign in the whole body; zero projected
    // `_0.f` writes, zero call-dest / drop of `_0`, no mutable alias.
    if !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }

    // (C) SPINE-STATEMENT WHITELIST — straight-line terminators + storage-or-unprojected-
    // Assign statements only. A deref-base write has a PROJECTED place and declines here.
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return None,
        }
        for stmt in &block.stmts {
            match stmt {
                Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
                | Statement::Nop => {}
                Statement::Assign { place, .. } if place.projections.is_empty() => {}
                _ => return None,
            }
        }
    }

    // The sole `_0 = Aggregate(..)` write lives in the UNIQUE return block, immediately
    // before `Return` (only storage markers may follow), on the entry-reachable spine.
    let ret_block = unique_return_block(body)?;
    let reachable = cfg_reachable_from(body, BlockId(0))?;
    if !reachable.contains(&ret_block.id) {
        return None;
    }
    let agg_idx = ret_block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::Aggregate(..), .. }
            if place.local == 0 && place.projections.is_empty())
    })?;
    // Nothing between the Aggregate and `Return` (only inert storage markers).
    for stmt in &ret_block.stmts[agg_idx + 1..] {
        match stmt {
            Statement::StorageLive(l) | Statement::StorageDead(l) if *l != 0 => {}
            Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => {}
            _ => return None,
        }
    }

    let Statement::Assign { rvalue: Rvalue::Aggregate(kind, operands), .. } =
        &ret_block.stmts[agg_idx]
    else {
        return None;
    };
    let AggregateKind::Adt { name: agg_name, variant, active_field, .. } = kind else {
        return None;
    };
    // (B) active_field == None as a LITERAL gate (union-repr aggregate declines).
    if active_field.is_some() {
        return None;
    }
    // (2) return-type cross-check: single-variant struct (variant 0), name match, arity.
    if *variant != 0 || agg_name != ret_name || operands.len() != ret_fields.len() {
        return None;
    }

    // (3) CARRIER ADMISSION — reflect the concrete single-`.mk` carrier, register it,
    // and RE-GET the registry (never assume registration succeeded: a gate-failed
    // inductive stays in the env but is absent from the registry).
    let carrier = crate::reflect::reflect_struct(&body.return_ty)?;
    if !carrier.type_params.is_empty() || carrier.is_enum() {
        return None; // (7) concrete-only (no Pi-wrapped generic `.mk`); reflect routed to enum.
    }
    if carrier.fields.len() != operands.len() {
        return None;
    }
    {
        let mut env = crate::trustir_anchor::trustir_env().ok()?;
        let registry =
            crate::clean_ground::register_adt_carriers(&mut env, std::slice::from_ref(&carrier));
        let confirmed = registry.get(&carrier.name)?; // re-get: gate-failed carrier is absent.
        if confirmed.fields.len() != operands.len() {
            return None;
        }
    }

    // Per-field values in MIR / constructor order (incl. Unit markers).
    let mut fields = Vec::with_capacity(operands.len());
    for ((_fname, fty), op) in ret_fields.iter().zip(operands.iter()) {
        if is_unit_carrier_ty(fty) {
            // UNIT/PhantomData marker — accepted BY TYPE; the operand must be a `Unit`
            // constant (an `Int`/`Bool`/other constant in a Unit slot declines).
            match op {
                Operand::Constant(ConstValue::Unit) => fields.push(SemStructField::Unit),
                _ => return None,
            }
        } else if matches!(fty, Ty::Int { .. } | Ty::Bool) {
            // A scalar field — route through the PARAM-ROOT chokepoint (gate A). A
            // reassigned parameter, a non-parameter place, or a `Unit` constant in an
            // `Int` slot all fail closed here (`sem_operand_of_mir` returns `None`).
            let scalar = sem_operand_of_mir(body, op, &param_index)?;
            fields.push(SemStructField::Scalar(scalar));
        } else {
            // (E) POINTER / ref / nested-struct / slice field — OUT of increment 1.
            // A raw-ptr / `NonNull` root is NOT admitted in this lane (fail closed)
            // until `sliceStart`/`ptrOffset` land with their gates (increment 3).
            return None;
        }
    }

    Some(SemStructReturn { struct_ty: body.return_ty.clone(), fields })
}

/// Recognize the projection behind an immutable `&s[i]` reference return: the place must
/// be EXACTLY `[Deref, Index(k)]` or `[Deref, ConstantIndex{..}]` on an IMMUTABLE-
/// reference slice/array PARAMETER with `Ty::Int` elements, with the base param not
/// reassigned, not deref-written, and NOT raw-address-exposed. `use_site` is the `Ref`
/// statement's own site (for resolving a dynamic index local's dominating definition).
/// `None` (fail-closed) on any other shape — mirrors the array-index scalar arm's gate
/// set (mirsem.rs:14824-14834) VERBATIM, PLUS the W20 [`raw_exposure_exists`] gate.
pub(super) fn slice_ref_projection_of_ref_place(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
    use_site: (trust_types::BlockId, Option<usize>),
) -> Option<SliceRefProj> {
    use trust_types::{Projection, Ty};
    // EXACTLY a two-element projection — anything else (bare `[Deref]`, a trailing
    // `Field`, `[Deref, Subslice{..}]`, extra projections, or `Index`/`ConstantIndex`
    // without the leading `Deref`) declines.
    let kind = match place.projections.as_slice() {
        [Projection::Deref, Projection::Index(idx_local)] => {
            let idx =
                resolve_index_operand(body, *idx_local, use_site.0, use_site.1, param_index)?;
            SliceRefProjKind::Index(idx)
        }
        [Projection::Deref, Projection::ConstantIndex { offset, min_length, from_end }] => {
            SliceRefProjKind::ConstantIndex {
                offset: *offset,
                min_length: *min_length,
                from_end: *from_end,
            }
        }
        _ => return None,
    };
    // Base gate — VERBATIM from the array-index scalar arm: an IMMUTABLE-reference
    // Slice/Array PARAMETER with `Ty::Int` elements (slices of refs/ADTs decline; a
    // nested-ref payload is future work with its own denotation question).
    match body.locals.get(place.local).map(|local| &local.ty) {
        Some(Ty::Ref { mutable: false, inner }) => match inner.as_ref() {
            Ty::Slice { elem } | Ty::Array { elem, .. }
                if matches!(elem.as_ref(), Ty::Int { .. }) => {}
            _ => return None,
        },
        _ => return None,
    }
    let base_param = param_index(place.local)?;
    if param_reassigned_by_stmt(body, place.local)
        || deref_write_exists(body, place.local)
        || raw_exposure_exists(body, place.local)
    {
        return None;
    }
    Some(SliceRefProj { base_param, kind })
}

/// Trust: W20 RAW-EXPOSURE gate (the aliasing skeptic) — decline the value-tier
/// reference-return denotation if the body could form a RAW POINTER to the base slice's
/// referent and write through it. [`deref_write_exists`] follows only shared-ref→
/// shared-ref copies and flags `&mut`/`&raw mut` (`AddressOf(true)`) deref-writes; a
/// `&raw const` (`AddressOf(false)`) escape is INVISIBLE to it, yet a const raw pointer
/// can be `Cast` to `*mut` and written — invalidating the value-slot denotation
/// (`*(&s[i])` would no longer equal `idxElem(s,i)`). Mirror [`tcc_scan_rvalue`]'s
/// BOTH-mutabilities `AddressOf` discipline: fail closed if ANY `Rvalue::AddressOf(_,
/// place)` — const OR mut — targets the base or any member of its shared-ref alias set
/// (the base is a shared-ref PARAMETER, so a raw pointer can alias its referent only by
/// first addressing the base or one of its shared-ref views — the `AddressOf` is the
/// choke point).
pub(super) fn raw_exposure_exists(body: &trust_types::VerifiableBody, base: usize) -> bool {
    use std::collections::{HashSet, VecDeque};

    use trust_types::{Operand, Rvalue, Statement, Ty};
    // The shared-ref alias set — the SAME whole-local shared-ref Use-copy closure
    // `deref_write_exists` computes.
    let shared_ref_types_match = |source: usize, destination: usize| {
        let (Some(source_ty), Some(destination_ty)) = (
            body.locals.get(source).map(|decl| &decl.ty),
            body.locals.get(destination).map(|decl| &decl.ty),
        ) else {
            return false;
        };
        matches!(source_ty, Ty::Ref { mutable: false, .. })
            && matches!(destination_ty, Ty::Ref { mutable: false, .. })
            && source_ty.eq_ignoring_disc_index_safe(destination_ty)
    };
    let mut aliases = HashSet::from([base]);
    let mut pending = VecDeque::from([base]);
    let mut processed = 0usize;
    while let Some(source) = pending.pop_front() {
        processed += 1;
        if processed > body.locals.len().saturating_add(1) {
            return true; // internally inconsistent alias graph — fail closed.
        }
        for statement in body.blocks.iter().flat_map(|block| &block.stmts) {
            let Statement::Assign {
                place: destination,
                rvalue: Rvalue::Use(Operand::Copy(source_place) | Operand::Move(source_place)),
                ..
            } = statement
            else {
                continue;
            };
            if destination.projections.is_empty()
                && source_place.projections.is_empty()
                && source_place.local == source
                && shared_ref_types_match(source, destination.local)
                && aliases.insert(destination.local)
            {
                pending.push_back(destination.local);
            }
        }
    }
    // ANY raw address-of (const OR mut) of the base or an alias, at ANY projection.
    body.blocks.iter().flat_map(|block| &block.stmts).any(|statement| {
        matches!(statement,
            Statement::Assign { rvalue: Rvalue::AddressOf(_, place), .. }
            if aliases.contains(&place.local))
    })
}

/// Re-extract the [`SliceRefProj`] behind an arm's `Some(&s[i])` construction WITHOUT
/// building the semantic payload: the arm's sole `Aggregate` write to `join_local`, its
/// single bare `Copy`/`Move` payload temp, and that temp's unique dominating definition
/// (which, for a reference return, is the `Ref` rvalue). Used by the guard↔projection
/// COHERENCE gate ([`slice_ref_return_guard_coherent`]), which needs the projection
/// metadata (`offset`/`min_length`/`from_end`, unrepresented in the built `SemAdtArm`)
/// alongside the guard. `None` for any arm that is not a slice-reference construction —
/// so the coherence gate is a no-op for every other ADT-return lane.
pub(super) fn slice_ref_projection_of_arm(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<SliceRefProj> {
    use trust_types::{AggregateKind, Operand, Rvalue};
    let (use_statement, rv) =
        arm.stmts.iter().enumerate().rev().find_map(|(statement_index, statement)| {
            crate::assignment_types::assigned_local_rvalue(body, statement, join_local)
                .map(|rvalue| (statement_index, rvalue))
        })?;
    let Rvalue::Aggregate(AggregateKind::Adt { active_field: None, .. }, operands) = rv else {
        return None;
    };
    let [payload_op] = operands.as_slice() else { return None };
    let (Operand::Copy(p) | Operand::Move(p)) = payload_op else { return None };
    if !p.projections.is_empty()
        || param_index(p.local).is_some()
        || !crate::prove::local_soundly_resolvable(body, p.local)
    {
        return None;
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, p.local, arm.id, Some(use_statement))?;
    let Rvalue::Ref { mutable: false, place } = definition else { return None };
    slice_ref_projection_of_ref_place(
        body,
        place,
        param_index,
        (definition_block, Some(definition_statement)),
    )
}

/// Trust: W20 REFERENCE-RETURN guard↔projection coherence — the from_end-aware
/// ConstantIndex bounds gate + branch-polarity + same-slice-handle checks, run at the
/// SHAPE step (guard `cond` in hand). Returns `true` (admits) iff either NEITHER arm
/// carries a slice-reference construction (a no-op for every pre-existing ADT-return
/// lane), OR the guard-TRUE (`then`) arm carries it, the guard-FALSE (`else`) arm does
/// NOT (branch polarity), AND the guard is coherent with the projection
/// ([`slice_ref_guard_coherent`]). A slice-reference payload on the guard-FALSE edge, or
/// on BOTH edges, declines.
pub(super) fn slice_ref_return_guard_coherent(
    body: &trust_types::VerifiableBody,
    then_arm: &trust_types::BasicBlock,
    else_arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    cond: &SemCondTree,
) -> bool {
    let then_proj = slice_ref_projection_of_arm(body, then_arm, join_local, param_index);
    let else_proj = slice_ref_projection_of_arm(body, else_arm, join_local, param_index);
    match (then_proj, else_proj) {
        // Not a slice-reference return — every pre-existing ADT-return lane is unaffected.
        (None, None) => true,
        // The `Some(&s[i])` payload is on the guard-TRUE edge (correct polarity).
        (Some(proj), None) => slice_ref_guard_coherent(cond, &proj),
        // The reference payload is on the guard-FALSE edge (branch-polarity forgery), or
        // BOTH arms carry one (two-slice / degenerate dispatch) — decline.
        _ => false,
    }
}

/// The load-bearing guard↔projection coherence check for ONE recognized slice-reference
/// projection against the guard `cond`. Enforces the SAME slice handle on the guard's
/// `Len` and the payload's base, the correct comparison operator, and the from_end-aware
/// in-bounds bound. A single-comparison guard only.
pub(super) fn slice_ref_guard_coherent(cond: &SemCondTree, proj: &SliceRefProj) -> bool {
    // Only a single-comparison bounds guard admits this lane — a conjunctive guard
    // declines (the ADT-return witness's `cond_bool` likewise declines an `And`).
    let SemCondTree::Leaf(c) = cond else { return false };
    let base = SemOperand::Var(proj.base_param);
    match &proj.kind {
        // Dynamic index `s[k]`: guard MUST be `Lt(k, Len(s))` — SAME slice handle, SAME
        // index operand (`SliceIndex::get`; the guard IS the bounds obligation).
        SliceRefProjKind::Index(idx) => {
            c.op == SemCmpOp::Lt && &c.a == idx && c.b == SemOperand::Len(Box::new(base))
        }
        // Constant index: guard MUST be `Ge(Len(s), Const K)` — SAME slice handle — with
        // the from_end-aware in-bounds discharge:
        //   from_end:false (index o):     o < m <= K   (=> 0 <= o < K <= len).
        //   from_end:true  (index len-o): 1 <= o <= K AND m <= K   (=> 0 <= len-o < len).
        // ANY other combination declines. This is the SOLE net against an out-of-bounds
        // ConstantIndex forgery: trust-vcgen's `constant_index_projection_vc` ignores
        // `from_end`, so the `1 <= o` clause is singly load-bearing here.
        SliceRefProjKind::ConstantIndex { offset, min_length, from_end } => {
            let (SemOperand::Len(guard_slice), SemOperand::Const(k)) = (&c.a, &c.b) else {
                return false;
            };
            if c.op != SemCmpOp::Ge || guard_slice.as_ref() != &base {
                return false;
            }
            let (Ok(o), Ok(m)) = (i128::try_from(*offset), i128::try_from(*min_length)) else {
                return false;
            };
            if *from_end { 1 <= o && o <= *k && m <= *k } else { o < m && m <= *k }
        }
    }
}

pub(super) fn opaque_entry_param_field(
    body: &trust_types::VerifiableBody,
    arg_count: usize,
    place: &trust_types::Place,
) -> Option<(u64, u64, trust_types::Ty)> {
    use trust_types::{Projection, Ty};

    if !(1..=arg_count).contains(&place.local) || param_reassigned_by_stmt(body, place.local) {
        return None;
    }
    let (fields, field) = match place.projections.as_slice() {
        [Projection::Deref, Projection::Field(field)] => {
            if deref_write_exists(body, place.local) {
                return None;
            }
            let Ty::Ref { inner, .. } = &body.locals.get(place.local)?.ty else {
                return None;
            };
            let Ty::Adt { fields, .. } = inner.as_ref() else { return None };
            (fields, *field)
        }
        [Projection::Field(field)] => {
            let Ty::Adt { fields, .. } = &body.locals.get(place.local)?.ty else {
                return None;
            };
            (fields, *field)
        }
        _ => return None,
    };
    let field_ty = fields.get(field)?.1.clone();
    Some((u64::try_from(place.local.checked_sub(1)?).ok()?, u64::try_from(field).ok()?, field_ty))
}

pub(super) fn opaque_guard_newtype_u64(ty: &trust_types::Ty) -> bool {
    matches!(ty,
        trust_types::Ty::Adt { fields, variants, faithful_enum_repr: None, .. }
            if variants.is_empty()
                && matches!(fields.as_slice(),
                    [(_, trust_types::Ty::Int { width: 64, signed: false })]))
}

/// Recognize the OPAQUE-CHAIN ADT-RETURN shape (section comment above). ALL
/// of the following must hold — anything else fails closed (`None`):
///
///   (0) the return type is the `Option` enum (a `Result`/other-enum return is
///       the existing `sem_adt_return_shape_of`'s business — NOT admitted
///       here: the mission's "non-Option dest" decline);
///   (1) `_0` is written EXACTLY twice, both by arm-block `Statement::Assign`s
///       (never a `Call` dest);
///   (2) exactly ONE `Return` block, with NO statements, and it is the two
///       arms' common join;
///   (3) the ENTRY→SWITCH prefix, each arm path, and the join account for
///       EVERY block of the body (full-visit accounting — an unwind/cleanup/
///       panic block, e.g. `Lowerer::fold_bvar_opt`'s `debug_assert!` arm,
///       declines the whole shape);
///   (4) every visited statement is an `Assign` to a bare, non-param,
///       non-`_0`, SOLE-WRITTEN temp (never a call dest too) whose rvalue is
///       inside the small fragment ([`OpaqueDef`]); every visited terminator
///       is `Goto`/`Call`/the ONE guard `SwitchInt`/the join's `Return`;
///   (5) every `Call` is non-foreign, non-unsafe-sig, non-atomic, has a
///       `Some` target, a fresh sole-written non-param non-`_0` bare dest,
///       and every argument is a `Constant` or a `Copy`/`Move` of a bare
///       resolved local (a bare param arg additionally must not be a
///       `&mut`-typed param — passing `&mut self` onward would let the callee
///       mutate the fields the guard/payload denotations read);
///   (6) the guard `SwitchInt` has exactly one `(0, else)` target; its
///       discriminant is a sole-written temp defined by a `Cmp` over
///       entry-time operands, OR — gate (G) — a `Bool`-typed step whose
///       callee is the `__trust_total_clone` total-derived-trait sentinel
///       applied to exactly two immutable refs of the SAME single-`Int`-field
///       newtype ADT, one ref-of-param and one ref-of-param-field (either
///       order — the `id == self.id` newtype-Eq shape);
///   (7) the two arm blocks construct DISTINCT `Option` variants: each real
///       aggregate's declaration-order index is mapped through the exact return
///       enum metadata to its declared tag; the nullary variant has ZERO operands,
///       the payload variant EXACTLY ONE operand resolving to a chain value.
#[must_use]
pub fn sem_adt_return_opaque_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtReturnOpaque> {
    use trust_types::{
        AggregateKind, BlockId, Operand, Projection, Rvalue, Statement, Terminator, Ty,
    };
    let body = &func.body;
    let arg_count = body.arg_count;
    trust_vcgen::validate_function(func).ok()?;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }

    // (0) Option-return gate.
    let Ty::Adt { name: enum_name, variants: option_variants, .. } = &body.return_ty else {
        return None;
    };
    if (enum_name != "std::option::Option" && enum_name != "core::option::Option")
        || body.locals.first().map(|local| &local.ty) != Some(&body.return_ty)
        || !matches!(option_variants.as_slice(), [none, some]
            if none.name == "None"
                && none.discriminant == 0
                && none.fields.is_empty()
                && some.name == "Some"
                && some.discriminant == 1
                && some.fields.len() == 1)
    {
        return None;
    }

    // (1) `_0` written exactly twice, never via a Call dest.
    if !local_has_only_guarded_writes(body, 0, 2, 0) {
        return None;
    }

    // (2) exactly one empty Return block = the join.
    let ret_ids: Vec<BlockId> = body
        .blocks
        .iter()
        .filter(|b| matches!(b.terminator, Terminator::Return))
        .map(|b| b.id)
        .collect();
    let [join_id] = ret_ids.as_slice() else { return None };
    let join_id = *join_id;
    let join_block = body.blocks.iter().find(|b| b.id == join_id)?;
    if !join_block.stmts.is_empty() {
        return None;
    }
    // The two arm blocks: Goto(join) + a bare `_0` assign.
    let arm_ids: Vec<BlockId> = body
        .blocks
        .iter()
        .filter(|b| {
            matches!(b.terminator, Terminator::Goto(t) if t == join_id)
                && b.stmts.iter().any(|s| {
                    matches!(s, Statement::Assign { place, .. }
                        if place.local == 0 && place.projections.is_empty())
                })
        })
        .map(|b| b.id)
        .collect();
    let [arm_x, arm_y] = arm_ids.as_slice() else { return None };
    let (arm_x, arm_y) = (*arm_x, *arm_y);

    let block_of = |id: BlockId| body.blocks.iter().find(|b| b.id == id);
    // A temp is chain-writable iff bare, non-param, non-`_0`, written exactly
    // once by a Statement AND never a call dest — or vice versa for a call
    // dest (zero statement writes, exactly one call-dest write).
    let call_dest_count = |local: usize| -> usize {
        body.blocks
            .iter()
            .filter(|b| {
                matches!(&b.terminator,
                    Terminator::Call { dest, .. } if dest.local == local)
            })
            .count()
    };
    let is_param = |local: usize| (1..=arg_count).contains(&local);
    let param_op_index = |local: usize| -> Option<u64> {
        is_param(local).then(|| u64::try_from(local - 1).ok()).flatten()
    };
    // Entry-time operand resolution over the ledger: `Var`/`Const`/
    // `Field(Var, fld)`/an already-defined temp.
    let resolve_operand = |defs: &std::collections::BTreeMap<usize, OpaqueDef>,
                           op: &Operand|
     -> Option<SemChainVal> {
        match op {
            Operand::Constant(trust_types::ConstValue::Int(k)) => {
                Some(SemChainVal::Operand(SemOperand::Const(*k)))
            }
            Operand::Constant(trust_types::ConstValue::Uint(k, _)) => {
                Some(SemChainVal::Operand(SemOperand::Const(i128::try_from(*k).ok()?)))
            }
            Operand::Copy(p) | Operand::Move(p) => {
                if p.projections.is_empty() {
                    if let Some(idx) = param_op_index(p.local) {
                        if param_reassigned_by_stmt(body, p.local) {
                            return None;
                        }
                        // Opaque-chain conditions are grounded over the Int
                        // carrier.  A float/reference/ADT parameter must not be
                        // silently reinterpreted as that carrier merely because
                        // it is a bare parameter place.
                        if !matches!(
                            body.locals.get(p.local).map(|local| &local.ty),
                            Some(Ty::Int { .. }) | Some(Ty::Bool)
                        ) {
                            return None;
                        }
                        return Some(SemChainVal::Operand(SemOperand::Var(idx)));
                    }
                    return match defs.get(&p.local)? {
                        OpaqueDef::Op(o) => Some(SemChainVal::Operand(o.clone())),
                        OpaqueDef::Step(i) => Some(SemChainVal::Step(*i)),
                        _ => None,
                    };
                }
                // Entry-time field read of a parameter: `[Deref, Field(f)]`
                // (a `&self`-shaped param) or `[Field(f)]` (a by-value param).
                let fld = match p.projections.as_slice() {
                    [Projection::Deref, Projection::Field(f)] => {
                        let Some(Ty::Ref { inner, .. }) =
                            body.locals.get(p.local).map(|local| &local.ty)
                        else {
                            return None;
                        };
                        let Ty::Adt { fields, .. } = inner.as_ref() else { return None };
                        if !fields
                            .get(*f)
                            .is_some_and(|(_, ty)| matches!(ty, Ty::Int { .. } | Ty::Bool))
                            || deref_write_exists(body, p.local)
                        {
                            return None;
                        }
                        *f
                    }
                    [Projection::Field(f)] => {
                        let Some(Ty::Adt { fields, .. }) =
                            body.locals.get(p.local).map(|local| &local.ty)
                        else {
                            return None;
                        };
                        if !fields
                            .get(*f)
                            .is_some_and(|(_, ty)| matches!(ty, Ty::Int { .. } | Ty::Bool))
                        {
                            return None;
                        }
                        *f
                    }
                    _ => return None,
                };
                let idx = param_op_index(p.local)?;
                if param_reassigned_by_stmt(body, p.local) {
                    return None;
                }
                Some(SemChainVal::Operand(SemOperand::Field(
                    Box::new(SemOperand::Var(idx)),
                    u64::try_from(fld).ok()?,
                )))
            }
            _ => None,
        }
    };
    // A `&mut`-typed param local (e.g. `&mut self`) must never escape into a
    // call argument (the callee could mutate the fields the entry-time
    // denotations read).
    //
    // Trust: GATE-ITER-REGION-NO-CROSS-INSTANTIATION (2026-07-21) — this decline is
    // LOAD-BEARING for the ITER-NEXT VALUE-PATH lane, not incidental. A caller composing
    // over the `<Iter as Iterator>::next` certificate would pass its `&mut Iter` receiver
    // into the `next` call; blocking a `&mut` param from escaping into ANY call argument
    // here is the mechanized fence that prevents a consumer from instantiating two
    // entry-time-indexed `iter_region(recv)` theorems over the SAME receiver across an
    // admitted mutation (two chained `next()` calls present the SAME `recv` carrier with a
    // DIFFERENT true remaining region — a false `elem0 = elem1` composition). Pinned by
    // `iter_next_value_gate_carrier_and_mut_ref_pin` (clean_ground.rs). Do NOT relax to
    // `&self`-only without a post-state/primed surface that re-keys the handle
    // (`iter_region(recv, generation)`).
    let param_is_mut_ref = |local: usize| -> bool {
        matches!(body.locals.get(local).map(|l| &l.ty), Some(Ty::Ref { mutable: true, .. }))
    };

    // Shared walk state.
    let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut defs: std::collections::BTreeMap<usize, OpaqueDef> = std::collections::BTreeMap::new();
    let mut steps: Vec<SemOpaqueStep> = Vec::new();
    // For gate (G): per-step call-argument pointee denotations (populated only
    // when EVERY arg is an immutable `RefOf` — else `None`).
    let mut step_ref_args: Vec<Option<Vec<(usize, OpaqueRefOrigin)>>> = Vec::new();
    // Unlike `step_ref_args`, this bit survives a mixed ref/non-ref argument
    // list. Any origin-bearing alias call that is not the unique guard step
    // must decline because the refinement has no heap/effect transition.
    let mut step_origin_ref_arg: Vec<bool> = Vec::new();
    // A copied shared-reference parameter field is effect-safe for this
    // heap-free refinement only when its consuming call is the arm's final,
    // direct opaque payload step. Keep that provenance separate from gate (G).
    let mut step_field_ref_arg: Vec<bool> = Vec::new();

    // Process one statement into the ledger. `true` = ok, `false` = decline.
    #[allow(clippy::too_many_lines)]
    fn process_stmt(
        body: &trust_types::VerifiableBody,
        defs: &mut std::collections::BTreeMap<usize, OpaqueDef>,
        resolve: &dyn Fn(
            &std::collections::BTreeMap<usize, OpaqueDef>,
            &Operand,
        ) -> Option<SemChainVal>,
        arg_count: usize,
        call_dest_count: &dyn Fn(usize) -> usize,
        allow_field_ref_arg: bool,
        stmt: &Statement,
    ) -> bool {
        let Statement::Assign { place, rvalue, .. } = stmt else { return false };
        if !place.projections.is_empty()
            || place.local == 0
            || (1..=arg_count).contains(&place.local)
        {
            return false;
        }
        // Sole-written discipline: exactly one Statement write, zero call-dest
        // writes, never mutably aliased.
        if !crate::prove::local_soundly_resolvable(body, place.local)
            || call_dest_count(place.local) != 0
        {
            return false;
        }
        if defs.contains_key(&place.local) {
            return false; // unreachable given sole-writer, kept for defense.
        }
        let def = match rvalue {
            Rvalue::Use(op) => match resolve(defs, op) {
                Some(SemChainVal::Operand(o)) => OpaqueDef::Op(o),
                Some(SemChainVal::Step(i)) => OpaqueDef::Step(i),
                None => {
                    let (Operand::Copy(source) | Operand::Move(source)) = op else {
                        return false;
                    };
                    let Some((_, _, source_ty)) = opaque_entry_param_field(body, arg_count, source)
                    else {
                        return false;
                    };
                    let Some(destination_ty) = body.locals.get(place.local).map(|local| &local.ty)
                    else {
                        return false;
                    };
                    if !matches!(source_ty, trust_types::Ty::Ref { mutable: false, .. })
                        || !source_ty.eq_ignoring_disc_index_safe(destination_ty)
                        || !allow_field_ref_arg
                    {
                        return false;
                    }
                    OpaqueDef::FieldRefArg
                }
            },
            Rvalue::Ref { mutable: false, place: rp } => {
                if rp.projections.is_empty() {
                    if let Some(idx) = (1..=arg_count).contains(&rp.local).then(|| rp.local - 1) {
                        // Ref of a bare NON-`&mut`-typed param.
                        if matches!(
                            body.locals.get(rp.local).map(|l| &l.ty),
                            Some(trust_types::Ty::Ref { mutable: true, .. })
                        ) {
                            return false;
                        }
                        let Some(trust_types::Ty::Ref { mutable: false, inner }) =
                            body.locals.get(place.local).map(|local| &local.ty)
                        else {
                            return false;
                        };
                        let Some(source_ty) = body.locals.get(rp.local).map(|local| &local.ty)
                        else {
                            return false;
                        };
                        if param_reassigned_by_stmt(body, rp.local)
                            || !opaque_guard_newtype_u64(source_ty)
                            || !source_ty.eq_ignoring_disc_index_safe(inner)
                        {
                            return false;
                        }
                        let Ok(idx) = u64::try_from(idx) else { return false };
                        OpaqueDef::RefOf(OpaqueRefOrigin::Param(idx))
                    } else {
                        return false;
                    }
                } else {
                    // Ref of an entry-time parameter field. Keep only its
                    // structural origin; the field may be a newtype ADT and
                    // must not be scalarized merely to feed the guard call.
                    let Some((param, field, field_ty)) =
                        opaque_entry_param_field(body, arg_count, rp)
                    else {
                        return false;
                    };
                    let Some(trust_types::Ty::Ref { mutable: false, inner }) =
                        body.locals.get(place.local).map(|local| &local.ty)
                    else {
                        return false;
                    };
                    if !opaque_guard_newtype_u64(&field_ty)
                        || !field_ty.eq_ignoring_disc_index_safe(inner)
                    {
                        return false;
                    }
                    OpaqueDef::RefOf(OpaqueRefOrigin::ParamField { param, field })
                }
            }
            Rvalue::Aggregate(AggregateKind::Adt { active_field: None, .. }, ops) => {
                for op in ops {
                    match resolve(defs, op) {
                        Some(SemChainVal::Operand(_) | SemChainVal::Step(_)) => {}
                        None => return false,
                    }
                }
                OpaqueDef::Ctor
            }
            Rvalue::BinaryOp(bop, a, b) => {
                let op = sem_cmpop_of_mir(bop);
                let (Some(op), Some(SemChainVal::Operand(a)), Some(SemChainVal::Operand(b))) =
                    (op, resolve(defs, a), resolve(defs, b))
                else {
                    return false;
                };
                OpaqueDef::Cmp(op, a, b)
            }
            _ => return false,
        };
        defs.insert(place.local, def);
        true
    }

    // Process one Call terminator into the ledger; returns the target block.
    let process_call = |defs: &mut std::collections::BTreeMap<usize, OpaqueDef>,
                        steps: &mut Vec<SemOpaqueStep>,
                        step_ref_args: &mut Vec<Option<Vec<(usize, OpaqueRefOrigin)>>>,
                        step_origin_ref_arg: &mut Vec<bool>,
                        step_field_ref_arg: &mut Vec<bool>,
                        allow_field_ref_arg: bool,
                        term: &Terminator|
     -> Option<BlockId> {
        let Terminator::Call {
            func: callee,
            args,
            dest,
            target: Some(target),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            ..
        } = term
        else {
            return None;
        };
        if !dest.projections.is_empty() || dest.local == 0 || is_param(dest.local) {
            return None;
        }
        // Fresh sole-written call dest: zero Statement writes, exactly this one
        // call-dest write, never mutably aliased.
        if !crate::prove::local_has_only_one_bare_call_destination(body, dest.local)
            || call_dest_count(dest.local) != 1
            || defs.contains_key(&dest.local)
        {
            return None;
        }
        let mut ref_args: Option<Vec<(usize, OpaqueRefOrigin)>> = Some(Vec::new());
        let mut has_origin_ref_arg = false;
        let mut has_field_ref_arg = false;
        for arg in args {
            match arg {
                Operand::Constant(_) => {
                    ref_args = None;
                }
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    if is_param(p.local) {
                        if param_is_mut_ref(p.local) || param_reassigned_by_stmt(body, p.local) {
                            return None;
                        }
                        ref_args = None;
                    } else {
                        match defs.get(&p.local) {
                            Some(OpaqueDef::RefOf(pointee)) => {
                                has_origin_ref_arg = true;
                                if let Some(v) = ref_args.as_mut() {
                                    v.push((p.local, pointee.clone()));
                                }
                            }
                            Some(OpaqueDef::Op(_) | OpaqueDef::Step(_) | OpaqueDef::Ctor) => {
                                ref_args = None;
                            }
                            Some(OpaqueDef::FieldRefArg) if allow_field_ref_arg => {
                                has_field_ref_arg = true;
                                ref_args = None;
                            }
                            Some(OpaqueDef::Cmp(..)) | None => return None,
                            Some(OpaqueDef::FieldRefArg) => return None,
                        }
                    }
                }
                _ => return None,
            }
        }
        let bool_typed = matches!(body.locals.get(dest.local).map(|l| &l.ty), Some(Ty::Bool));
        steps.push(SemOpaqueStep { callee: callee.clone(), bool_typed });
        step_ref_args.push(ref_args);
        step_origin_ref_arg.push(has_origin_ref_arg);
        step_field_ref_arg.push(has_field_ref_arg);
        defs.insert(dest.local, OpaqueDef::Step(steps.len() - 1));
        Some(*target)
    };

    // ---- prefix walk: entry → the guard SwitchInt ----
    let mut cur = body.blocks.first()?.id;
    let (cond, then_start, else_start) = loop {
        if !visited.insert(cur) {
            return None; // cycle — not this shape.
        }
        let b = block_of(cur)?;
        if b.id == arm_x || b.id == arm_y {
            return None; // reached an arm without a guard switch.
        }
        for stmt in &b.stmts {
            if !process_stmt(
                body,
                &mut defs,
                &resolve_operand,
                arg_count,
                &call_dest_count,
                false,
                stmt,
            ) {
                return None;
            }
        }
        match &b.terminator {
            Terminator::Goto(t) => cur = *t,
            term @ Terminator::Call { .. } => {
                cur = process_call(
                    &mut defs,
                    &mut steps,
                    &mut step_ref_args,
                    &mut step_origin_ref_arg,
                    &mut step_field_ref_arg,
                    false,
                    term,
                )?;
            }
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                let [(zero_val, else_target)] = targets.as_slice() else { return None };
                if *zero_val != 0 {
                    return None;
                }
                let (Operand::Copy(dp) | Operand::Move(dp)) = discr else { return None };
                if !dp.projections.is_empty() {
                    return None;
                }
                let cond = match defs.get(&dp.local)? {
                    OpaqueDef::Cmp(op, a, b) => {
                        SemOpaqueCond::Cmp { op: *op, a: a.clone(), b: b.clone() }
                    }
                    OpaqueDef::Step(i) => {
                        let i = *i;
                        // Gate (G): the ∀-bound Bool guard is admitted ONLY for
                        // the total-derived-trait sentinel over a newtype-u64
                        // ref pair (one param, one param-field, either order).
                        if !steps.get(i)?.bool_typed
                            || steps.get(i)?.callee
                                != trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL
                        {
                            return None;
                        }
                        let ref_args = step_ref_args.get(i)?.as_ref()?;
                        let [(la, pa), (lb, pb)] = ref_args.as_slice() else { return None };
                        let exact_origin_pair = |a: &OpaqueRefOrigin, b: &OpaqueRefOrigin| {
                            matches!(
                                (a, b),
                                (
                                    OpaqueRefOrigin::Param(1),
                                    OpaqueRefOrigin::ParamField { param: 0, field: 0 }
                                )
                            )
                        };
                        if !(exact_origin_pair(pa, pb) || exact_origin_pair(pb, pa)) {
                            return None;
                        }
                        // Newtype-u64 gate: both ref locals share the SAME
                        // immutable-ref-of-single-unsigned-Int-field-ADT type.
                        let newtype_ok = |local: usize| -> Option<&Ty> {
                            let Some(Ty::Ref { mutable: false, inner }) =
                                body.locals.get(local).map(|l| &l.ty)
                            else {
                                return None;
                            };
                            if !opaque_guard_newtype_u64(inner) {
                                return None;
                            }
                            Some(inner.as_ref())
                        };
                        let (ta, tb) = (newtype_ok(*la)?, newtype_ok(*lb)?);
                        if ta != tb {
                            return None;
                        }
                        SemOpaqueCond::StepBool(i)
                    }
                    _ => return None,
                };
                break (cond, *otherwise, *else_target);
            }
            _ => return None,
        }
    };

    // ---- arm walks: switch target → its `_0`-writing arm block ----
    let walk_arm = |start: BlockId,
                    visited: &mut std::collections::HashSet<BlockId>,
                    defs: &mut std::collections::BTreeMap<usize, OpaqueDef>,
                    steps: &mut Vec<SemOpaqueStep>,
                    step_ref_args: &mut Vec<Option<Vec<(usize, OpaqueRefOrigin)>>>,
                    step_origin_ref_arg: &mut Vec<bool>,
                    step_field_ref_arg: &mut Vec<bool>|
     -> Option<SemOpaqueArm> {
        let first_arm_step = steps.len();
        let mut cur = start;
        loop {
            if !visited.insert(cur) {
                return None; // shared/looping arm path — not this shape.
            }
            let b = block_of(cur)?;
            let is_arm_block = b.id == arm_x || b.id == arm_y;
            if !is_arm_block {
                for stmt in &b.stmts {
                    if !process_stmt(
                        body,
                        defs,
                        &resolve_operand,
                        arg_count,
                        &call_dest_count,
                        true,
                        stmt,
                    ) {
                        return None;
                    }
                }
                match &b.terminator {
                    Terminator::Goto(t) => cur = *t,
                    term @ Terminator::Call { .. } => {
                        cur = process_call(
                            defs,
                            steps,
                            step_ref_args,
                            step_origin_ref_arg,
                            step_field_ref_arg,
                            true,
                            term,
                        )?;
                    }
                    _ => return None,
                }
                continue;
            }
            // The arm block: chain statements, then the FINAL `_0` aggregate.
            let (last, prefix) = b.stmts.split_last()?;
            for stmt in prefix {
                if !process_stmt(
                    body,
                    defs,
                    &resolve_operand,
                    arg_count,
                    &call_dest_count,
                    true,
                    stmt,
                ) {
                    return None;
                }
            }
            let Statement::Assign { place, rvalue, .. } = last else { return None };
            if place.local != 0 || !place.projections.is_empty() {
                return None;
            }
            let Rvalue::Aggregate(AggregateKind::Adt { name, variant, active_field: None, .. }, ops) =
                rvalue
            else {
                return None;
            };
            if name != enum_name {
                return None; // cross-check against the return type — never guessed.
            }
            let variant = aggregate_variant_discriminant(&body.return_ty, name, *variant)?;
            let payload = match ops.as_slice() {
                [] => None,
                [op] => match op {
                    Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                        Some(resolve_operand(defs, op)?)
                    }
                    _ => return None,
                },
                _ => return None,
            };
            let arm = SemOpaqueArm { variant, payload };
            let field_ref_steps = (first_arm_step..steps.len())
                .filter(|i| step_field_ref_arg.get(*i).copied().unwrap_or(false))
                .collect::<Vec<_>>();
            if let [field_ref_step] = field_ref_steps.as_slice()
                && (arm.payload != Some(SemChainVal::Step(*field_ref_step))
                    || field_ref_step.checked_add(1) != Some(steps.len()))
            {
                return None;
            }
            if field_ref_steps.len() > 1 {
                return None;
            }
            return Some(arm);
        }
    };
    // Each mutually exclusive arm starts from the same prefix ledger. Never
    // let a temp defined on the first arm become visible while recognizing the
    // second arm merely because the two walks execute sequentially here.
    let mut then_defs = defs.clone();
    let mut else_defs = defs;
    let then_arm = walk_arm(
        then_start,
        &mut visited,
        &mut then_defs,
        &mut steps,
        &mut step_ref_args,
        &mut step_origin_ref_arg,
        &mut step_field_ref_arg,
    )?;
    let else_arm = walk_arm(
        else_start,
        &mut visited,
        &mut else_defs,
        &mut steps,
        &mut step_ref_args,
        &mut step_origin_ref_arg,
        &mut step_field_ref_arg,
    )?;

    // Origin-bearing references may feed only the sentinel step that is the
    // guard itself. A different/mixed/unused call could mutate a later field
    // denoted from the entry environment, which the kernel statement does not
    // model.
    let origin_guard_step = match &cond {
        SemOpaqueCond::StepBool(i) => Some(*i),
        SemOpaqueCond::Cmp { .. } => None,
    };
    if step_origin_ref_arg
        .iter()
        .enumerate()
        .any(|(i, has_origin)| *has_origin && Some(i) != origin_guard_step)
    {
        return None;
    }

    // (7) distinct Option variants; the nullary arm has NO payload, the other
    // exactly one.
    if then_arm.variant == else_arm.variant {
        return None;
    }
    if !matches!(
        (then_arm.payload.is_some(), else_arm.payload.is_some()),
        (true, false) | (false, true)
    ) {
        return None;
    }
    for arm in [&then_arm, &else_arm] {
        // `Option`: `None` = variant 0 (nullary), `Some` = variant 1 (1 field).
        match (arm.variant, arm.payload.is_some()) {
            (0, false) | (1, true) => {}
            _ => return None,
        }
    }

    // (3) full-visit accounting: prefix + arms + the join must cover EVERY
    // block (an unreachable unwind/panic/cleanup block declines the shape).
    visited.insert(join_id);
    if visited.len() != body.blocks.len() {
        return None;
    }

    Some(SemAdtReturnOpaque { steps, cond, then_arm, else_arm, enum_name: enum_name.clone() })
}

/// Recognize only the audited Instantiator `match idx.cmp(&self.depth)` leaf.
/// The result makes no claim about opaque callee values: all three call results
/// are universally bound by the trust-ir witness. Comparison semantics are
/// consumed separately, and only for the one exact overflow VC.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn sem_adt_return_opaque_ord_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemAdtReturnOpaqueOrd> {
    use trust_types::{
        AggregateKind, AssertMessage, BinOp, BlockId, ConstValue, Operand, Place, Projection,
        Rvalue, Statement, Terminator, Ty,
    };

    if func.def_path != INSTANTIATOR_ORD_LEAF_DEF_PATH
        || func.content_hash() != INSTANTIATOR_ORD_LEAF_CONTENT_HASH
    {
        return None;
    }
    let body = &func.body;
    if body.arg_count != 2 || body.blocks.len() != 10 || body.locals.len() != 13 {
        return None;
    }
    let mut ids = body.blocks.iter().map(|block| block.id.0).collect::<Vec<_>>();
    ids.sort_unstable();
    if ids != (0..10).collect::<Vec<_>>() {
        return None;
    }
    let block = |id| body.blocks.iter().find(|candidate| candidate.id == BlockId(id));
    let bare = |place: &Place, local| place.local == local && place.projections.is_empty();
    let u32_ty = |ty: &Ty| matches!(ty, Ty::Int { width: 32, signed: false });

    // Return and compared-operand types. The depth field itself must be a
    // primitive u32, never Cell/UnsafeCell/another interior-mutable carrier.
    let Ty::Adt { name: option_name, variants: option_variants, .. } = &body.return_ty else {
        return None;
    };
    if option_name != "std::option::Option"
        || option_variants.len() != 2
        || option_variants[0].name != "None"
        || option_variants[0].discriminant != 0
        || !option_variants[0].fields.is_empty()
        || option_variants[1].name != "Some"
        || option_variants[1].discriminant != 1
        || option_variants[1].fields.len() != 1
        || !u32_ty(&body.locals.get(2)?.ty)
    {
        return None;
    }
    let Ty::Ref { mutable: true, inner: self_inner } = &body.locals.get(1)?.ty else {
        return None;
    };
    let Ty::Adt { name: self_name, fields: self_fields, .. } = self_inner.as_ref() else {
        return None;
    };
    if self_name != "expr::subst::Instantiator"
        || !matches!(self_fields.get(1), Some((name, ty)) if name == "depth" && u32_ty(ty))
    {
        return None;
    }
    for local in [4usize, 5] {
        if !matches!(
            body.locals.get(local).map(|decl| &decl.ty),
            Some(Ty::Ref { mutable: false, inner }) if u32_ty(inner)
        ) {
            return None;
        }
    }
    let Ty::Adt { name: ordering_name, variants: ordering_variants, .. } = &body.locals.get(3)?.ty
    else {
        return None;
    };
    let expected_ordering = [("Less", 255i128), ("Equal", 0), ("Greater", 1)];
    if ordering_name != "std::cmp::Ordering"
        || ordering_variants.len() != expected_ordering.len()
        || !ordering_variants.iter().zip(expected_ordering).all(|(actual, expected)| {
            actual.name == expected.0
                && actual.discriminant == expected.1
                && actual.fields.is_empty()
        })
    {
        return None;
    }

    // bb0: immutable snapshots of idx/depth, then the exact total-derived
    // sentinel. No &mut/raw/interior-mutable alias is admitted.
    let bb0 = block(0)?;
    let [
        Statement::Assign {
            place: ref_idx_dest,
            rvalue: Rvalue::Ref { mutable: false, place: ref_idx },
            ..
        },
        Statement::Assign {
            place: ref_depth_dest,
            rvalue: Rvalue::Ref { mutable: false, place: ref_depth },
            ..
        },
    ] = bb0.stmts.as_slice()
    else {
        return None;
    };
    if !bare(ref_idx_dest, 4)
        || !bare(ref_idx, 2)
        || !bare(ref_depth_dest, 5)
        || ref_depth.local != 1
        || ref_depth.projections.as_slice() != [Projection::Deref, Projection::Field(1)]
    {
        return None;
    }
    let Terminator::Call {
        func: cmp_callee,
        args: cmp_args,
        dest: cmp_dest,
        target: Some(cmp_target),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        ..
    } = &bb0.terminator
    else {
        return None;
    };
    if cmp_callee != trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL
        || !bare(cmp_dest, 3)
        || *cmp_target != BlockId(1)
        || !matches!(cmp_args.as_slice(), [Operand::Move(a), Operand::Copy(b)] if bare(a, 4) && bare(b, 5))
    {
        return None;
    }

    // bb1/bb2: the sole discriminant and exhaustive three-tag dispatch.
    let bb1 = block(1)?;
    let [Statement::Assign { place: disc_dest, rvalue: Rvalue::Discriminant(disc_source), .. }] =
        bb1.stmts.as_slice()
    else {
        return None;
    };
    let Terminator::SwitchInt {
        discr: Operand::Move(disc_operand),
        targets,
        otherwise,
        exhaustive_enum_unreachable: true,
        ..
    } = &bb1.terminator
    else {
        return None;
    };
    let mut actual_targets = targets.clone();
    actual_targets.sort_by_key(|(tag, _)| *tag);
    if !bare(disc_dest, 6)
        || !bare(disc_source, 3)
        || !bare(disc_operand, 6)
        || actual_targets != vec![(0, BlockId(5)), (1, BlockId(4)), (255, BlockId(3))]
        || *otherwise != BlockId(2)
    {
        return None;
    }
    let bb2 = block(2)?;
    if !bb2.stmts.is_empty() || !matches!(bb2.terminator, Terminator::Unreachable) {
        return None;
    }

    let option_arm = |id: usize, variant: usize, payload: Option<usize>| -> Option<()> {
        let arm = block(id)?;
        let [
            Statement::Assign {
                place,
                rvalue:
                    Rvalue::Aggregate(
                        AggregateKind::Adt { name, variant: actual_variant, active_field: None, .. },
                        operands,
                    ),
                ..
            },
        ] = arm.stmts.as_slice()
        else {
            return None;
        };
        if !bare(place, 0)
            || name != option_name
            || *actual_variant != variant
            || !matches!(arm.terminator, Terminator::Goto(BlockId(9)))
        {
            return None;
        }
        match (payload, operands.as_slice()) {
            (None, []) => Some(()),
            (Some(expected), [Operand::Move(place)]) if bare(place, expected) => Some(()),
            _ => None,
        }
    };
    option_arm(3, 0, None)?;
    option_arm(6, 1, Some(7))?;
    option_arm(8, 1, Some(9))?;

    // Greater arm: exactly CheckedSub(idx, 1u32), exactly its overflow flag,
    // then exactly bvar(checked_result). No statement/call/write can occur
    // between cmp and this assert beyond the enumerated pure definitions.
    let bb4 = block(4)?;
    let [
        Statement::Assign {
            place: checked_dest,
            rvalue:
                Rvalue::CheckedBinaryOp(
                    BinOp::Sub,
                    Operand::Copy(idx),
                    Operand::Constant(ConstValue::Uint(1, 32)),
                ),
            ..
        },
    ] = bb4.stmts.as_slice()
    else {
        return None;
    };
    let Terminator::Assert {
        cond: Operand::Move(flag),
        expected: false,
        msg: AssertMessage::Overflow(BinOp::Sub),
        target: assert_target,
        ..
    } = &bb4.terminator
    else {
        return None;
    };
    if !bare(checked_dest, 11)
        || !bare(idx, 2)
        || flag.local != 11
        || flag.projections.as_slice() != [Projection::Field(1)]
        || *assert_target != BlockId(7)
    {
        return None;
    }
    let bb7 = block(7)?;
    let [
        Statement::Assign {
            place: result_dest,
            rvalue: Rvalue::Use(Operand::Move(result_source)),
            ..
        },
    ] = bb7.stmts.as_slice()
    else {
        return None;
    };
    let Terminator::Call {
        func: bvar_callee,
        args: bvar_args,
        dest: bvar_dest,
        target: Some(bvar_target),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        ..
    } = &bb7.terminator
    else {
        return None;
    };
    if !bare(result_dest, 10)
        || result_source.local != 11
        || result_source.projections.as_slice() != [Projection::Field(0)]
        || bvar_callee != "expr::constructors::<impl expr::Expr>::bvar"
        || !matches!(bvar_args.as_slice(), [Operand::Move(value)] if bare(value, 10))
        || !bare(bvar_dest, 9)
        || *bvar_target != BlockId(8)
    {
        return None;
    }

    // Equal arm: only immutable field snapshots and lift_at; self (`&mut`) is
    // never moved/passed onward, closing the moved-mut-reference alias channel.
    let bb5 = block(5)?;
    let [
        Statement::Assign {
            place: value_dest,
            rvalue: Rvalue::Use(Operand::Copy(value_source)),
            ..
        },
        Statement::Assign {
            place: depth_dest,
            rvalue: Rvalue::Use(Operand::Copy(depth_source)),
            ..
        },
    ] = bb5.stmts.as_slice()
    else {
        return None;
    };
    let Terminator::Call {
        func: lift_callee,
        args: lift_args,
        dest: lift_dest,
        target: Some(lift_target),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        ..
    } = &bb5.terminator
    else {
        return None;
    };
    if !bare(value_dest, 12)
        || value_source.local != 1
        || value_source.projections.as_slice() != [Projection::Deref, Projection::Field(0)]
        || !bare(depth_dest, 8)
        || depth_source.local != 1
        || depth_source.projections.as_slice() != [Projection::Deref, Projection::Field(1)]
        || lift_callee != "expr::subst::<impl expr::Expr>::lift_at"
        || !matches!(
            lift_args.as_slice(),
            [
                Operand::Copy(value),
                Operand::Constant(ConstValue::Uint(0, 32)),
                Operand::Move(depth),
            ] if bare(value, 12) && bare(depth, 8)
        )
        || !bare(lift_dest, 7)
        || *lift_target != BlockId(6)
    {
        return None;
    }
    let join = block(9)?;
    if !join.stmts.is_empty() || !matches!(join.terminator, Terminator::Return) {
        return None;
    }

    Some(SemAdtReturnOpaqueOrd {
        steps: vec![
            SemOpaqueStep { callee: cmp_callee.clone(), bool_typed: false },
            SemOpaqueStep { callee: lift_callee.clone(), bool_typed: false },
            SemOpaqueStep { callee: bvar_callee.clone(), bool_typed: false },
        ],
        cmp_step: 0,
        ord_variants: ordering_variants
            .iter()
            .map(|variant| (variant.name.clone(), variant.discriminant))
            .collect(),
        arms: vec![
            ("Less".to_string(), SemOpaqueArm { variant: 0, payload: None }),
            ("Equal".to_string(), SemOpaqueArm { variant: 1, payload: Some(SemChainVal::Step(1)) }),
            (
                "Greater".to_string(),
                SemOpaqueArm { variant: 1, payload: Some(SemChainVal::Step(2)) },
            ),
        ],
        enum_name: option_name.clone(),
        crossed_asserts: 1,
    })
}

/// Forward reachability from `start` over EVERY terminator successor edge
/// (guarded + unguarded). Used by [`sem_scalar_sentinel_select_shape_of`]'s
/// full-visit accounting: a drop-flag unwind/cleanup block that is unreachable
/// from entry cannot affect the observable return and is therefore ignored, while
/// a reachable extra block DECLINES the whole shape.
///
/// FAIL-CLOSED (`None`): if a reachable block carries a terminator whose
/// successor edges this walk does not model, reachability is UNKNOWN — we cannot
/// prove the cleanup blocks are unreachable, so the whole recognition declines
/// (never a silent CFG hole; `Terminator` is `#[non_exhaustive]`, so a future
/// variant lands here rather than being treated as an unsound sink).
pub(crate) fn cfg_reachable_from(
    body: &trust_types::VerifiableBody,
    start: trust_types::BlockId,
) -> Option<std::collections::HashSet<trust_types::BlockId>> {
    use trust_types::Terminator;
    let mut seen: std::collections::HashSet<trust_types::BlockId> =
        std::collections::HashSet::new();
    let mut stack = vec![start];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let block = body.blocks.iter().find(|b| b.id == id)?;
        match &block.terminator {
            Terminator::Goto(t) => stack.push(*t),
            Terminator::SwitchInt { targets, otherwise, .. } => {
                stack.extend(targets.iter().map(|(_, t)| *t));
                stack.push(*otherwise);
            }
            Terminator::Call { target, .. } => stack.extend(target.iter().copied()),
            Terminator::Assert { target, .. } => stack.push(*target),
            Terminator::Drop { target, .. } => stack.push(*target),
            Terminator::Opaque { targets, .. } => stack.extend(targets.iter().copied()),
            Terminator::Return | Terminator::Unreachable | Terminator::Resume => {}
            // Any unmodeled terminator ⇒ reachability unknown ⇒ fail closed.
            _ => return None,
        }
    }
    Some(seen)
}

/// Recognize the SCALAR SENTINEL-SELECT shape (section comment above). ALL of the
/// following must hold — anything else fails closed (`None`):
///
///   (0) `arg_count == 2`; the return AND both by-value params are the SAME
///       `Ty::Int` (the `min`/`max` scalar-int signature);
///   (1) `_0` is written EXACTLY twice (the two arm assigns), NEVER via a `Call`
///       dest, and neither parameter is reassigned/aliased;
///   (2) the ENTRY block's terminator is the `__trust_total_clone` sentinel `Call`
///       (non-foreign/atomic/unsafe) writing a bare `Bool` temp, over two
///       immutable-ref args; its statements are ONLY storage markers, a
///       `Bool = const bool` drop-flag init, or a `&param` ref (no `_0`/param
///       write, no arithmetic/side effect);
///   (3) the call's target is `SwitchInt(guard) { 0 -> ELSE } otherwise -> THEN`
///       with no value statements;
///   (4) each arm assigns `_0 := Use(Copy/Move <bare param>)` EXACTLY once (the
///       two arms returning the two DISTINCT params), drops a bare
///       Copy-scalar-int param, and converges at the common JOIN;
///   (5) the JOIN is a bare `Return` (no statements);
///   (6) FULL-VISIT ACCOUNTING: the ONLY blocks reachable from entry are exactly
///       these five (every drop-flag unwind/cleanup block is unreachable).
#[must_use]
pub fn sem_scalar_sentinel_select_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemScalarSentinelSelect> {
    use trust_types::{BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    let body = &func.body;

    // (0) EXACTLY two by-value scalar-int params; scalar-int return of the SAME type.
    if body.arg_count != 2 {
        return None;
    }
    let Ty::Int { width, signed } = body.return_ty else { return None };
    let same_int =
        |ty: &Ty| matches!(ty, Ty::Int { width: w, signed: s } if *w == width && *s == signed);
    if !same_int(&body.locals.get(0)?.ty)
        || !same_int(&body.locals.get(1)?.ty)
        || !same_int(&body.locals.get(2)?.ty)
    {
        return None;
    }
    // Copy-scalar-int predicate — the ONLY type whose `Drop` is a trivial (no-op)
    // drop glue we may treat as a no-op. A primitive integer is `Copy` (cannot
    // `impl Drop`), so its drop is a genuine no-op; anything else DECLINES.
    let is_copy_scalar_int = |ty: &Ty| matches!(ty, Ty::Int { .. } | Ty::PtrSizedInt { .. });

    // No UNMODELED statement anywhere (fail-closed, like `sem_call_return_of_mir`).
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return None;
    }

    // (1) `_0` written EXACTLY twice, NEVER via a Call dest; params not reassigned.
    if !local_has_only_guarded_writes(body, 0, 2, 0) {
        return None;
    }
    if param_reassigned_by_stmt(body, 1) || param_reassigned_by_stmt(body, 2) {
        return None;
    }

    let block_of = |id: BlockId| body.blocks.iter().find(|b| b.id == id);
    let bare = |p: &trust_types::Place| p.projections.is_empty();
    // A statement with NO value effect on `_0`/params (storage/coverage markers).
    let is_marker = |s: &Statement| {
        matches!(
            s,
            Statement::StorageLive(_)
                | Statement::StorageDead(_)
                | Statement::Nop
                | Statement::PlaceMention(_)
                | Statement::Coverage
                | Statement::ConstEvalCounter
        )
    };

    // (2) THE ENTRY BLOCK carries the sentinel guard call.
    let entry = block_of(BlockId(0))?;
    for s in &entry.stmts {
        match s {
            _ if is_marker(s) => {}
            // A `Bool = const bool` drop-flag init, or a `&param` ref — to a bare
            // NON-param NON-`_0` temp. Nothing else (no arithmetic/side effect).
            Statement::Assign { place, rvalue, .. }
                if bare(place) && place.local != 0 && !(1..=2).contains(&place.local) =>
            {
                match rvalue {
                    Rvalue::Use(Operand::Constant(ConstValue::Bool(_))) => {}
                    Rvalue::Ref { mutable: false, place: rp }
                        if bare(rp) && (1..=2).contains(&rp.local) => {}
                    _ => return None,
                }
            }
            _ => return None,
        }
    }
    let Terminator::Call {
        func: guard_callee,
        args: guard_args,
        dest: guard_dest,
        target: Some(switch_id),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        ..
    } = &entry.terminator
    else {
        return None;
    };
    // The guard MUST be the TOTAL sentinel — a non-sentinel guard call DECLINES
    // (no extraction-side totality proof ⇒ no call admitted in guard position).
    if *guard_callee != trust_types::total_call_summaries::TRUST_TOTAL_CLONE_SENTINEL {
        return None;
    }
    let guard_local = guard_dest.local;
    if !bare(guard_dest)
        || guard_local == 0
        || (1..=2).contains(&guard_local)
        || !matches!(body.locals.get(guard_local).map(|l| &l.ty), Some(Ty::Bool))
    {
        return None;
    }
    // Exactly two args, each a Copy/Move of a bare immutable-ref temp (the
    // compare-of-refs shape; their values are irrelevant — the result is
    // uninterpreted, so this is shape-faithfulness, not a value claim).
    if guard_args.len() != 2 {
        return None;
    }
    for a in guard_args {
        let (Operand::Copy(p) | Operand::Move(p)) = a else { return None };
        if !bare(p)
            || !matches!(
                body.locals.get(p.local).map(|l| &l.ty),
                Some(Ty::Ref { mutable: false, .. })
            )
        {
            return None;
        }
    }

    // (3) THE SWITCH BLOCK: SwitchInt(guard) { 0 -> ELSE } otherwise -> THEN.
    let switch = block_of(*switch_id)?;
    if !switch.stmts.iter().all(&is_marker) {
        return None;
    }
    let Terminator::SwitchInt { discr, targets, otherwise, .. } = &switch.terminator else {
        return None;
    };
    let (Operand::Copy(d) | Operand::Move(d)) = discr else { return None };
    if !bare(d) || d.local != guard_local || targets.len() != 1 {
        return None;
    }
    let (tag, else_bb) = &targets[0];
    if *tag != 0 {
        return None;
    }
    let else_id = *else_bb;
    let then_id = *otherwise;

    // (4) THE TWO ARMS: each returns a distinct by-value param, drops a bare
    // Copy-scalar-int param, converges at the common JOIN.
    let read_arm = |arm_id: BlockId| -> Option<(u64, BlockId)> {
        let arm = block_of(arm_id)?;
        let mut ret_param: Option<usize> = None;
        for s in &arm.stmts {
            match s {
                _ if is_marker(s) => {}
                // drop-flag write: `Bool = const bool` to a bare non-param non-`_0` temp.
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Bool(_))),
                    ..
                } if bare(place) && place.local != 0 && !(1..=2).contains(&place.local) => {}
                // the arm return: `_0 = Use(Copy/Move <bare param>)`, EXACTLY once.
                Statement::Assign {
                    place,
                    rvalue: Rvalue::Use(Operand::Copy(p) | Operand::Move(p)),
                    ..
                } if place.local == 0 && bare(place) && bare(p) && (1..=2).contains(&p.local) => {
                    if ret_param.is_some() {
                        return None; // a second `_0` write within the arm.
                    }
                    ret_param = Some(p.local);
                }
                _ => return None,
            }
        }
        let ret_local = ret_param?;
        // Drop terminator: discards a bare Copy-scalar-int param, targets the JOIN.
        let Terminator::Drop { place: dp, target: join, .. } = &arm.terminator else {
            return None;
        };
        if !bare(dp)
            || !(1..=2).contains(&dp.local)
            || !is_copy_scalar_int(&body.locals.get(dp.local)?.ty)
        {
            return None;
        }
        Some((u64::try_from(ret_local - 1).ok()?, *join))
    };
    let (then_var, then_join) = read_arm(then_id)?;
    let (else_var, else_join) = read_arm(else_id)?;
    if then_join != else_join {
        return None;
    }
    let join_id = then_join;
    // The two arms return the two DISTINCT parameters (the min/max select shape).
    if then_var == else_var || then_var > 1 || else_var > 1 {
        return None;
    }

    // (5) THE JOIN: a bare `Return` (no statements).
    let join = block_of(join_id)?;
    if !join.stmts.is_empty() || !matches!(join.terminator, Terminator::Return) {
        return None;
    }

    // (6) FULL-VISIT ACCOUNTING: the ONLY blocks reachable from entry are exactly
    // these five distinct blocks (every drop-flag unwind/cleanup block is
    // UNREACHABLE on the happy path, so it cannot affect the return; a reachable
    // extra block DECLINES).
    let expected: std::collections::HashSet<BlockId> =
        [BlockId(0), switch.id, then_id, else_id, join_id].into_iter().collect();
    if expected.len() != 5 {
        return None;
    }
    if cfg_reachable_from(body, BlockId(0))? != expected {
        return None;
    }

    Some(SemScalarSentinelSelect { then_var, else_var, width, signed })
}

pub(super) fn payload_extract_cfg_marker(statement: &trust_types::Statement) -> bool {
    use trust_types::Statement;
    matches!(
        statement,
        Statement::StorageLive(_)
            | Statement::StorageDead(_)
            | Statement::Nop
            | Statement::PlaceMention(_)
            | Statement::Coverage
            | Statement::ConstEvalCounter
    )
}

/// Bind the payload-extraction value equations to the executable CFG rather
/// than merely finding a matching switch somewhere in the block table.
///
/// The accepted suffixes are the two shapes emitted by the committed corpus:
/// `Option::unwrap_or` joins directly at `Return`; `Result::unwrap_or` joins at
/// one exhaustive discriminant switch which either returns immediately (the
/// moved-out payload variant) or drops the still-live `self` variant and then
/// returns.  Any extra reachable block, call, assertion, resume, alternate
/// switch, or side-effecting statement fails closed.
pub(super) fn payload_extract_cfg_is_exact(
    body: &trust_types::VerifiableBody,
    switch_bid: trust_types::BlockId,
    otherwise: trust_types::BlockId,
    payload_block: trust_types::BlockId,
    default_block: trust_types::BlockId,
    self_local: usize,
    default_local: usize,
    extract_variant: usize,
) -> bool {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator};

    // Duplicate block identities make every block-table lookup ambiguous.
    let block_ids: std::collections::HashSet<BlockId> =
        body.blocks.iter().map(|block| block.id).collect();
    if block_ids.len() != body.blocks.len() || switch_bid != BlockId(0) {
        return false;
    }
    let block = |id: BlockId| body.blocks.iter().find(|candidate| candidate.id == id);
    let bare = |place: &trust_types::Place| place.projections.is_empty();

    let Some(unreachable) = block(otherwise) else { return false };
    if !unreachable.stmts.is_empty() || !matches!(unreachable.terminator, Terminator::Unreachable) {
        return false;
    }

    let arm_statements_are_exact = |arm: &trust_types::BasicBlock| {
        let mut return_writes = 0usize;
        for statement in &arm.stmts {
            if payload_extract_cfg_marker(statement) {
                continue;
            }
            match statement {
                Statement::Assign { place, .. } if place.local == 0 && bare(place) => {
                    return_writes += 1;
                }
                _ => return false,
            }
        }
        return_writes == 1
    };

    let Some(payload_arm) = block(payload_block) else { return false };
    let Some(default_arm) = block(default_block) else { return false };
    if !arm_statements_are_exact(payload_arm) || !arm_statements_are_exact(default_arm) {
        return false;
    }

    // The extracted arm consumes the payload and drops the unused scalar
    // default; the default arm proceeds without a drop. Both must converge at
    // the same join. This pins the two recognized assignments to the actual
    // switch successors and excludes a decoy arm table.
    let Terminator::Drop { place: dropped_default, target: payload_join, .. } =
        &payload_arm.terminator
    else {
        return false;
    };
    if dropped_default.local != default_local || !bare(dropped_default) {
        return false;
    }
    let Terminator::Goto(default_join) = &default_arm.terminator else {
        return false;
    };
    if payload_join != default_join {
        return false;
    }
    let join_id = *default_join;
    let Some(join) = block(join_id) else { return false };

    let mut expected = std::collections::HashSet::from([
        switch_bid,
        otherwise,
        payload_block,
        default_block,
        join_id,
    ]);

    if join.stmts.iter().all(payload_extract_cfg_marker)
        && matches!(join.terminator, Terminator::Return)
    {
        // `Option::unwrap_or`: the common join is the return block.
    } else {
        // `Result::unwrap_or`: the join contains exactly one discriminant read
        // of the same `self`, then an exhaustive 0/1 switch. The extracted
        // variant returns directly; the other variant drops `self` first.
        let mut tail_disc: Option<usize> = None;
        for statement in &join.stmts {
            if payload_extract_cfg_marker(statement) {
                continue;
            }
            let Statement::Assign { place, rvalue: Rvalue::Discriminant(source), .. } = statement
            else {
                return false;
            };
            if tail_disc.is_some()
                || !bare(place)
                || place.local == 0
                || (1..=body.arg_count).contains(&place.local)
                || source.local != self_local
                || !bare(source)
            {
                return false;
            }
            tail_disc = Some(place.local);
        }
        let Some(tail_disc) = tail_disc else { return false };
        if body
            .blocks
            .iter()
            .flat_map(|candidate| &candidate.stmts)
            .filter(|statement| {
                matches!(statement, Statement::Assign { place, .. } if place.local == tail_disc && bare(place))
            })
            .count()
            != 1
        {
            return false;
        }
        let Terminator::SwitchInt { discr, targets, otherwise: tail_otherwise, .. } =
            &join.terminator
        else {
            return false;
        };
        let (Operand::Copy(disc_place) | Operand::Move(disc_place)) = discr else {
            return false;
        };
        if disc_place.local != tail_disc
            || !bare(disc_place)
            || *tail_otherwise != otherwise
            || targets.len() != 2
            || !exhaustive_two_arm_discriminant_switch(body, join_id, *tail_otherwise)
        {
            return false;
        }
        let mut by_tag = std::collections::HashMap::new();
        for (tag, target) in targets {
            if *tag > 1
                || by_tag.insert(usize::try_from(*tag).unwrap_or(usize::MAX), *target).is_some()
            {
                return false;
            }
        }
        if by_tag.len() != 2 || extract_variant > 1 {
            return false;
        }
        let Some(&return_id) = by_tag.get(&extract_variant) else { return false };
        let Some(&drop_id) = by_tag.get(&(1 - extract_variant)) else { return false };
        let Some(return_block) = block(return_id) else { return false };
        if !return_block.stmts.is_empty() || !matches!(return_block.terminator, Terminator::Return)
        {
            return false;
        }
        let Some(drop_block) = block(drop_id) else { return false };
        let Terminator::Drop { place: dropped_self, target: after_drop, .. } =
            &drop_block.terminator
        else {
            return false;
        };
        if !drop_block.stmts.is_empty()
            || dropped_self.local != self_local
            || !bare(dropped_self)
            || *after_drop != return_id
        {
            return false;
        }
        expected.insert(return_id);
        expected.insert(drop_id);
    }

    expected.len() >= 4
        && cfg_reachable_from(body, BlockId(0)).is_some_and(|reachable| reachable == expected)
}
