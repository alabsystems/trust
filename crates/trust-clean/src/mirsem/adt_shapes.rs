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
/// Trust: DECLINE LABELLING (2026-08-26) — replay [`sem_adt_return_shape_of`]'s OWN
/// early stages, in its order, using its OWN helpers, and name the first that stops a
/// body.
///
/// This exists because two attempts to size the 2-arm lane's residue failed for the same
/// underlying reason: both measured a MODEL of the recognizer (a shell scan over MIR
/// shapes, then a structural proxy over gates I chose) instead of the recognizer. A
/// `DowncastOpaque` payload lane was then built against the proxy's 410-body estimate and
/// gained exactly zero, because the recognizer declines before the payload resolver is
/// ever called.
///
/// It covers the stages up to the guard/arm split — deliberately NOT the whole function,
/// because the later stages are threaded through `?` on shared helpers and labelling them
/// means editing eighteen exits. Those are reported as one bucket, which is honest about
/// what it does and does not resolve.
#[must_use]
pub fn sem_adt_return_decline_reason(func: &trust_types::VerifiableFunction) -> &'static str {
    use trust_types::{Statement, Terminator};
    if trust_vcgen::validate_function(func).is_err() {
        return "validate_function rejects the body";
    }
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        // Split the four clauses — "a write does not match its place type" was a guess
        // at which one fires, and it stops a third of the class.
        if let Some(k) = crate::assignment_types::first_assignment_mismatch_kind(body) {
            return k;
        }
        return crate::assignment_types::all_assignments_match_reason(body);
    }
    let Some(ret_block) = unique_return_block(body) else {
        return "no unique return block";
    };
    let Some(join_local) = guarded_return_join_local(body, ret_block) else {
        return "no guarded-return join local";
    };
    if join_local != 0 {
        return "the join local is not `_0` (join-via-temp)";
    }
    let assigns_0 = |b: &trust_types::BasicBlock| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. }
                if place.local == 0 && place.projections.is_empty())
        })
    };
    // Trust: the diagnostic MUST use the same arm-convergence rule the recognizer uses.
    // It briefly did not — the recognizer was widened to admit a value-transparent arm
    // `Drop` and this filter was left on `Goto`, so the histogram kept reporting a gate the
    // recognizer no longer applied. That is precisely the recognizer/diagnostic drift the
    // eight `_reasoned` conversions exist to prevent, reintroduced by hand.
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| arm_convergence_target(b).is_some() && assigns_0(b))
        .collect();
    if arms.len() != 2 {
        // Trust: ARM-TERMINATOR SPLIT (2026-08-27) — 650 of the 2,640 uncovered TWO-ARM
        // bodies stop here, second only to entry-rooting. The lane requires an arm to end
        // in `Goto`; naming what the `_0`-writing blocks actually END IN says whether that
        // is an addressable shape restriction (a value-transparent `Drop`) or the
        // interprocedural wall wearing a different label (a `Call`).
        if arms.len() < 2 {
            let writers: Vec<&trust_types::BasicBlock> =
                body.blocks.iter().filter(|b| assigns_0(b)).collect();
            let mut drops = 0usize;
            let mut calls = 0usize;
            let mut other = 0usize;
            for b in &writers {
                match &b.terminator {
                    Terminator::Goto(_) => {}
                    Terminator::Drop { .. } => drops += 1,
                    Terminator::Call { .. } => calls += 1,
                    _ => other += 1,
                }
            }
            if writers.len() < 2 {
                return "fewer than 2 blocks write `_0` at all";
            }
            if calls > 0 {
                return "an arm ends in a CALL (interprocedural)";
            }
            if drops > 0 {
                return "an arm ends in a DROP (value-transparent shape restriction)";
            }
            if other > 0 {
                return "an arm ends in some other terminator";
            }
        }
        return if arms.len() < 2 {
            "fewer than 2 Goto arms write `_0`"
        } else {
            "more than 2 Goto arms write `_0`"
        };
    }
    let (Some(j0), Some(j1)) =
        (arm_convergence_target(arms[0]), arm_convergence_target(arms[1]))
    else {
        return "an arm does not converge (neither Goto nor a value-transparent Drop)";
    };
    if j0 != j1 {
        return "the two arms do not join at the same block";
    }
    if !local_has_only_guarded_writes(body, 0, 2, 0) {
        return "`_0` is written outside the two arms";
    }
    if sem_adt_return_shape_of(func).is_some() {
        return "RECOGNIZED";
    }

    // Replay the next stages, still using the recognizer's own helpers, to split the
    // "later stage" bucket. The 96 bodies it held on `fp4` are the last unresolved class
    // in this report; everything below mirrors the recognizer's order exactly.
    let Some(j0) = arm_convergence_target(arms[0]) else {
        return "an arm does not converge (late)";
    };
    let drop_ladder = recognize_drop_ladder_epilogue(body, j0);
    let mut switches: Vec<trust_types::BlockId> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { .. } => Some(b.id),
            _ => None,
        })
        .collect();
    if let Some(l) = &drop_ladder {
        switches.retain(|id| *id != l.switch_block);
    }
    if switches.is_empty() {
        return "no guard SwitchInt (after excluding a drop-ladder epilogue)";
    }
    let arm_ids: Vec<trust_types::BlockId> = arms.iter().map(|b| b.id).collect();
    let entry_rooted = if let Some(l) = &drop_ladder {
        drop_ladder_cfg_is_entry_rooted(body, l.switch_block, &arm_ids, &switches)
    } else {
        guarded_cfg_is_entry_rooted(body, j0, &arm_ids, &switches)
    };
    if !entry_rooted {
        return "the guarded CFG is not entry-rooted";
    }
    if switches.len() > 1 {
        return "more than one guard SwitchInt (conjunctive chain)";
    }
    if !matches!(body.return_ty, trust_types::Ty::Adt { .. }) {
        return "the return type is not an ADT";
    }
    // Final layer: ask `arm_adt_ctor_value_for` itself, once per arm — with the
    // RECOGNIZER'S OWN `expected_downcast_variant`, not a guessed `None`.
    //
    // This layer previously passed `None` because deriving the real variant meant
    // duplicating the recognizer's dispatch analysis, and gate D then declined EVERY
    // downcast payload BY DESIGN — the diagnostic was measuring its own argument. The
    // fix was not a better guess but [`sem_adt_return_dispatch_of`]: one derivation, both
    // callers. A diagnostic that reproduces a gate is a second implementation of that
    // gate, and the two disagree exactly when it matters.
    let pi = |local: usize| -> Option<u64> {
        if (1..=body.arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let mut sw: Vec<(
        &trust_types::Operand,
        &Vec<(u128, trust_types::BlockId)>,
        trust_types::BlockId,
        trust_types::BlockId,
    )> = body
        .blocks
        .iter()
        .filter_map(|b| match &b.terminator {
            Terminator::SwitchInt { discr, targets, otherwise, .. } => {
                Some((discr, targets, *otherwise, b.id))
            }
            _ => None,
        })
        .collect();
    if let Some(l) = &drop_ladder {
        sw.retain(|(_, _, _, id)| *id != l.switch_block);
    }
    let Some((_cond, else_arm_id, then_arm_id, then_ev, else_ev, _why)) =
        sem_adt_return_dispatch_of(body, &sw, &arm_ids, &pi)
    else {
        return "the DISPATCH derivation declines (guard shape / tag mapping)";
    };
    if else_arm_id == then_arm_id {
        return "both dispatch targets reach the SAME arm";
    }
    let mut any_downcast = false;
    let mut failing_arm_without_downcast = false;
    let mut downcast_unpinned = false;
    let mut payload_reason: Option<&'static str> = None;
    let mut payload_accepted = false;
    let mut first_arm_err: Option<&'static str> = None;
    for arm in &arms {
        let ev = if arm.id == then_arm_id {
            then_ev
        } else if arm.id == else_arm_id {
            else_ev
        } else {
            return "an arm block is neither dispatch target";
        };
        let arm_err = match arm_adt_ctor_value_for_reasoned(body, arm, 0, &pi, ev) {
            Ok(_) => continue,
            Err(why) => why,
        };
        let has_downcast = arm.stmts.iter().any(|st| match st {
            Statement::Assign { rvalue, .. } => match rvalue {
                trust_types::Rvalue::Use(
                    trust_types::Operand::Copy(p) | trust_types::Operand::Move(p),
                )
                | trust_types::Rvalue::Ref { place: p, .. } => p
                    .projections
                    .iter()
                    .any(|pr| matches!(pr, trust_types::Projection::Downcast(_))),
                _ => false,
            },
            _ => false,
        });
        if first_arm_err.is_none() {
            first_arm_err = Some(arm_err);
        }
        if has_downcast {
            any_downcast = true;
            if ev.is_none() {
                downcast_unpinned = true;
            }
            // Replay the payload gate on this arm's own downcast operand, through the
            // SAME function the recognizer calls, with the SAME expected variant.
            for st in &arm.stmts {
                let Statement::Assign { rvalue, .. } = st else { continue };
                match rvalue {
                    trust_types::Rvalue::Use(o) => {
                        let (trust_types::Operand::Copy(pl) | trust_types::Operand::Move(pl)) = o
                        else {
                            continue;
                        };
                        if !pl
                            .projections
                            .iter()
                            .any(|pr| matches!(pr, trust_types::Projection::Downcast(_)))
                        {
                            continue;
                        }
                        match downcast_field_payload_reasoned(body, o, &pi, ev) {
                            Err(why) => payload_reason = Some(why),
                            // The payload gate ACCEPTED this read. Whatever declines the
                            // arm is downstream of the payload entirely — the aggregate
                            // shape, the operand count, the temp resolution. Reporting
                            // this as "the payload resolver declines" pointed at the
                            // wrong layer.
                            Ok(_) => payload_accepted = true,
                        }
                    }
                    // `Some(&payload)` — the `as_ref`/`as_mut` family. The payload is
                    // BORROWED, not read by value, so the whole `downcast_field_payload`
                    // fragment (which resolves a VALUE) never applies. A distinct class,
                    // and it was invisible while this bucket was reported as one number.
                    trust_types::Rvalue::Ref { place: pl, mutable } => {
                        if pl
                            .projections
                            .iter()
                            .any(|pr| matches!(pr, trust_types::Projection::Downcast(_)))
                        {
                            payload_reason = Some(if *mutable {
                                "payload is a &mut BORROW of the downcast field (as_mut-class)"
                            } else {
                                "payload is a & BORROW of the downcast field (as_ref-class)"
                            });
                        }
                    }
                    _ => {}
                }
            }
        } else {
            failing_arm_without_downcast = true;
        }
    }
    if failing_arm_without_downcast {
        return first_arm_err.unwrap_or("ARM VALUE declines, NO downcast payload involved");
    }
    if downcast_unpinned {
        // The payload IS a downcast and the dispatch did NOT pin its variant, so gate D
        // refuses it. Ask WHICH gate — some of these are correct refusals (nothing
        // establishes which variant is live), others name a real capability limit, and
        // reporting them as one number is what hid the split for a whole round.
        if let Some((_, targets, _, _)) = sw.first() {
            match targets.as_slice() {
                // The SINGLE-TARGET form (`switch d { 0 => a } otherwise => b`) never
                // reaches the pin at all: [`sem_adt_return_dispatch_of`] hardcodes
                // `(None, None)` for it. Nothing about the enum is wrong — the pin is
                // simply never consulted.
                [(0, _)] => return "SINGLE-TARGET switch — the pin is never consulted",
                [(_, _)] => return "single-target switch on a NON-ZERO tag",
                [(tag_a, _), (tag_b, _)] => {
                    if let SemCondTree::Leaf(leaf) = &_cond
                        && let Err(why) =
                            downcast_expected_variants_reasoned(body, leaf, *tag_a, *tag_b, &pi)
                    {
                        return why;
                    }
                }
                _ => return "3+ switch targets",
            }
        }
        return "DOWNCAST payload whose variant the dispatch does not pin";
    }
    if any_downcast {
        // The variant IS pinned and the payload still declines. Ask the payload gate
        // ITSELF which of its checks refused — `downcast_field_payload_reasoned` is the
        // same code the recognizer runs, so this cannot drift from it.
        if let Some(reason) = payload_reason {
            return reason;
        }
        // The payload gate accepted a downcast read in this arm, so the refusal is a
        // DIFFERENT gate of the arm value. Report that one — it is the arm function's own
        // answer, not a guess about which layer was reached first.
        let _ = payload_accepted;
        return first_arm_err.unwrap_or("DOWNCAST payload, variant PINNED — no gate identified");
    }
    "both arms resolve — declines in the guard/cond or a later cross-check"
}

/// Trust: RECORD-WITNESS — the ADT-return DISPATCH derivation, extracted so the
/// recognizer and the decline diagnostic run the SAME code rather than two copies.
///
/// WHY THIS EXISTS AS A FUNCTION. The diagnostic used to re-derive the arm/guard
/// analysis beside the recognizer and then call [`arm_adt_ctor_value_for`] with
/// `expected_downcast_variant: None`, because deriving the real one meant duplicating
/// this block. Gate D then declined EVERY downcast payload BY DESIGN, so the diagnostic
/// was measuring its own argument, not the recognizer. Sharing the derivation is the
/// only fix that cannot drift: a diagnostic that reproduces a gate is a second
/// implementation of that gate, and the two disagree exactly when it matters.
///
/// Returns `(cond, else_arm_id, then_arm_id, then_expected_variant, else_expected_variant)`.
/// The per-arm expected variant is `Some` ONLY for a two-target discriminant dispatch that
/// [`downcast_expected_variants`] pins; `None` everywhere else, so a downcast-field payload
/// declines outside the dispatch that establishes its variant.
#[allow(clippy::type_complexity)]
pub(super) fn sem_adt_return_dispatch_of(
    body: &trust_types::VerifiableBody,
    switches: &[(
        &trust_types::Operand,
        &Vec<(u128, trust_types::BlockId)>,
        trust_types::BlockId,
        trust_types::BlockId,
    )],
    arm_ids: &[trust_types::BlockId],
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<(
    SemCondTree,
    trust_types::BlockId,
    trust_types::BlockId,
    Option<usize>,
    Option<usize>,
    // Trust: WHY the expected downcast variants were not derived (2026-08-28), `None`
    // when they were. `downcast_expected_variants` was called through its `.ok()`
    // wrapper and its reason discarded, so every failure collapsed into a single
    // downstream label -- measured, 156 of 357 `<X as Try>::branch` bodies, the largest
    // gate in the enum lane, all reporting "derived NO expected downcast variant" and
    // none saying WHICH of its eight causes fired. Carrying the reason costs one tuple
    // slot and two call sites.
    Option<&'static str>,
)> {
    use trust_types::{BlockId, Operand, Rvalue};
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
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
                b: sem_adt_guard_operand_of_mir(
                    body,
                    cb,
                    param_index,
                    Some((definition_block, Some(definition_statement))),
                )?,
            }),
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

    // Trust: RECORD-WITNESS inc-2 — alongside the guard, the TAG↔DOWNCAST expected self
    // variant for each arm (`Some` ONLY for a two-target discriminant dispatch over a
    // 2-variant `disc_index_safe` self enum; `None` everywhere else, so a downcast-field
    // payload declines outside that shape). Derived straight from THIS branch's
    // (tag_a → then, tag_b → else) mapping so the polarity is unambiguous — never
    // re-derived from `cond` (whose single-target form has the opposite polarity).
    let dispatch: (
        SemCondTree,
        BlockId,
        BlockId,
        Option<usize>,
        Option<usize>,
        Option<&'static str>,
    ) = if let [(discr, targets, otherwise, bid)] = switches {
        match targets.as_slice() {
            [(zero_val, else_target)] if *zero_val == 0 => {
                let leaf = switch_leaf(discr, 0)?;
                let else_id = first_arm_on_path(body, *else_target, arm_ids)?;
                let then_id = first_arm_on_path(body, *otherwise, arm_ids)?;
                (
                    SemCondTree::Leaf(leaf),
                    else_id,
                    then_id,
                    None,
                    None,
                    Some("single-target switch: this branch derives no expected variants"),
                )
            }
            [(tag_a, block_a), (tag_b, block_b)] => {
                if !exhaustive_two_arm_discriminant_switch(body, *bid, *otherwise) {
                    return None;
                }
                let leaf = switch_leaf(discr, *tag_a)?;
                let else_id = first_arm_on_path(body, *block_b, arm_ids)?;
                let then_id = first_arm_on_path(body, *block_a, arm_ids)?;
                let (then_ev, else_ev, why) =
                    match downcast_expected_variants_reasoned(
                        body, &leaf, *tag_a, *tag_b, param_index,
                    ) {
                        Ok((t, e)) => (t, e, None),
                        Err(reason) => (None, None, Some(reason)),
                    };
                (SemCondTree::Leaf(leaf), else_id, then_id, then_ev, else_ev, why)
            }
            _ => return None,
        }
    } else {
        let (cond, else_id, then_id) =
            sem_conjunctive_chain(body, switches, arm_ids, &switch_leaf)?;
        (
            cond,
            else_id,
            then_id,
            None,
            None,
            Some("conjunctive multi-switch chain: this branch derives no expected variants"),
        )
    };
    Some(dispatch)
}

/// Trust: VALUE-TRANSPARENT ARM DROP (2026-08-27) — the block an arm converges at, when
/// the arm reaches it through a `Drop` rather than a bare `Goto`.
///
/// WHY. Measured on a frozen 57,803-body corpus: of the 2,640 uncovered TWO-ARM bodies,
/// **648 stop because an arm ends in a `Drop`** — and exactly **0** because it ends in a
/// `Call`. That makes this a shape restriction in the recognizer, not the interprocedural
/// wall, and it is second only to entry-rooting in that population.
///
/// SOUND because the drop is VALUE-TRANSPARENT for the RETURN LOCAL specifically: the
/// dropped place is gated `place.local != 0`, and `local_has_only_guarded_writes(body, 0,
/// 2, 0)` — which the lane already requires — independently refuses ANY `Drop` of `_0`
/// anywhere in the body. So `_0` at the join is exactly what the arm assigned. The unwind
/// edge does not matter here: it leads away from the return, so it cannot change the value
/// observed at the join.
///
/// Deliberately ONE drop deep. A chain of drops is admissible by the same argument, but
/// each extra step needs its own intermediate-block discipline, and one step is what the
/// measurement says the corpus actually contains.
pub(crate) fn arm_convergence_target_for_test(
    arm: &trust_types::BasicBlock,
) -> Option<trust_types::BlockId> {
    arm_convergence_target(arm)
}

fn arm_convergence_target(arm: &trust_types::BasicBlock) -> Option<trust_types::BlockId> {
    use trust_types::Terminator;
    match &arm.terminator {
        Terminator::Goto(j) => Some(*j),
        Terminator::Drop { place, target, .. } if place.local != 0 => Some(*target),
        _ => None,
    }
}

/// The two-arm ENUM-return recognizer. Thin `.ok()` over
/// [`sem_adt_return_shape_reasoned`] — one implementation, two callers, so the reason a
/// census reports can never describe a different gate from the one that fired.
pub fn sem_adt_return_shape_of(func: &trust_types::VerifiableFunction) -> Option<SemAdtReturn> {
    sem_adt_return_shape_reasoned(func).ok()
}

/// Trust: the single implementation behind [`sem_adt_return_shape_of`], stating WHICH
/// gate refused.
///
/// Built for a measured population: 530 uncovered authored call-free bodies are
/// `<X as core::ops::try_trait::Try>::branch` — the `?` desugaring, emitted once per
/// instantiation — and they are exactly this lane's two-arm enum shape, yet every one
/// reports SHAPE_GAP. With 16 refusal points and no way to say which fires, the only way
/// to act on that was to guess, and guessing produced two dead recognizers earlier in
/// this campaign. Its siblings (`sem_struct_return_shape_reasoned`,
/// `sem_enum_ctor_return_shape_reasoned`) are what made the aggregate gate census
/// possible; this closes the same gap for the enum lane.
pub(crate) fn sem_adt_return_shape_reasoned(
    func: &trust_types::VerifiableFunction,
) -> Result<SemAdtReturn, &'static str> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator};
    if trust_vcgen::validate_function(func).is_err() {
        return Err("the function does not validate");
    }
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return Err("an assignment's operand TYPE does not match its place");
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    let Some(ret_block) = unique_return_block(body) else {
        return Err("no UNIQUE return block");
    };
    let assigns_local = |b: &trust_types::BasicBlock, loc: usize| {
        b.stmts.iter().any(|s| {
            matches!(s, Statement::Assign { place, .. } if place.local == loc && place.projections.is_empty())
        })
    };
    let Some(join_local) = guarded_return_join_local(body, ret_block) else {
        return Err("the return block has no guarded JOIN LOCAL");
    };
    if join_local != 0 {
        return Err("the join local is not `_0` (this lane models direct construction into `_0`)");
    }
    let assigns_0 = |b: &trust_types::BasicBlock| assigns_local(b, join_local);
    let arms: Vec<&trust_types::BasicBlock> = body
        .blocks
        .iter()
        .filter(|b| arm_convergence_target(b).is_some() && assigns_0(b))
        .collect();
    if arms.len() != 2 {
        return Err(match arms.len() {
            0 => "NO converging block assigns `_0`",
            1 => "only ONE converging block assigns `_0`",
            _ => "THREE OR MORE converging blocks assign `_0`",
        });
    }
    let (Some(j0), Some(j1)) =
        (arm_convergence_target(arms[0]), arm_convergence_target(arms[1]))
    else {
        return Err("an arm has no convergence target");
    };
    if j0 != j1 {
        return Err("the two arms converge on DIFFERENT blocks");
    }

    local_has_only_guarded_writes_reasoned(body, 0, 2, 0)?;

    let drop_ladder = recognize_drop_ladder_epilogue(body, j0);

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
        return Err("no SwitchInt decision block (outside the drop ladder)");
    }
    let arm_ids: Vec<BlockId> = arms.iter().map(|b| b.id).collect();
    let decision_ids: Vec<BlockId> = switches.iter().map(|(_, _, _, id)| *id).collect();
    let entry_rooted = if let Some(ladder) = &drop_ladder {
        drop_ladder_cfg_is_entry_rooted(body, ladder.switch_block, &arm_ids, &decision_ids)
    } else {
        guarded_cfg_is_entry_rooted(body, j0, &arm_ids, &decision_ids)
    };
    if !entry_rooted {
        return Err("the guarded CFG is not ENTRY-ROOTED");
    }

    let Some((
        cond,
        else_arm_id,
        then_arm_id,
        then_expected_variant,
        else_expected_variant,
        expected_variant_decline,
    )) = sem_adt_return_dispatch_of(body, &switches, &arm_ids, &param_index)
    else {
        return Err("no recognizable two-variant DISPATCH");
    };
    // Trust: a missing expected variant surfaces DOWNSTREAM, at the arm-value gate, as
    // "the dispatch derived NO expected downcast variant" — which says the derivation
    // failed but not why. Substitute the derivation's OWN reason there, so the label
    // names the gate that fired instead of the place it was noticed.
    let attribute = |e: &'static str| -> &'static str {
        if e == "gate D: the dispatch derived NO expected downcast variant" {
            expected_variant_decline.unwrap_or(e)
        } else {
            e
        }
    };

    if else_arm_id == then_arm_id {
        return Err("the dispatch names the SAME arm twice");
    }
    let (Some(else_arm), Some(then_arm)) = (
        arms.iter().find(|b| b.id == else_arm_id),
        arms.iter().find(|b| b.id == then_arm_id),
    ) else {
        return Err("the dispatch names a block that is not one of the two arms");
    };

    if let Some(ladder) = &drop_ladder
        && dispatch_self_local(&cond) != Some(ladder.self_local)
    {
        return Err("the drop ladder's self local differs from the dispatch's");
    }

    if !slice_ref_return_guard_coherent(body, then_arm, else_arm, join_local, &param_index, &cond) {
        return Err("the slice-ref return guard is not coherent");
    }

    let then_ctor =
        arm_adt_ctor_value_for_reasoned(body, then_arm, join_local, &param_index, then_expected_variant)
            .map_err(attribute)?;
    let else_ctor =
        arm_adt_ctor_value_for_reasoned(body, else_arm, join_local, &param_index, else_expected_variant)
            .map_err(attribute)?;
    if then_ctor.variant == else_ctor.variant {
        return Err("both arms construct the SAME variant — not a genuine two-variant dispatch");
    }

    let trust_types::Ty::Adt { name: enum_name, .. } = &body.return_ty else {
        return Err("the return type is not an ADT");
    };

    Ok(SemAdtReturn {
        cond,
        then_arm: then_ctor,
        else_arm: else_ctor,
        enum_name: enum_name.clone(),
    })
}

pub(super) fn arm_adt_ctor_value_for(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    expected_downcast_variant: Option<usize>,
) -> Option<SemAdtArm> {
    arm_adt_ctor_value_for_reasoned(body, arm, join_local, param_index, expected_downcast_variant)
        .ok()
}

/// [`arm_adt_ctor_value_for`] with the decline REASON — ONE implementation, two callers,
/// the same discipline as [`sem_adt_return_dispatch_of`] and
/// [`downcast_field_payload_reasoned`]. The recognizer takes `.ok()`; the diagnostic reads
/// the `Err`, so a corpus histogram attributes every decline to the gate that actually
/// refused instead of to whichever layer the instrument happened to reach first.
pub(super) fn arm_adt_ctor_value_for_reasoned(
    body: &trust_types::VerifiableBody,
    arm: &trust_types::BasicBlock,
    join_local: usize,
    param_index: &dyn Fn(usize) -> Option<u64>,
    expected_downcast_variant: Option<usize>,
) -> Result<SemAdtArm, &'static str> {
    use trust_types::{AggregateKind, Operand, Rvalue};
    let (use_statement, rv) =
        arm.stmts.iter().enumerate().rev().find_map(|(statement_index, statement)| {
            crate::assignment_types::assigned_local_rvalue(body, statement, join_local)
                .map(|rvalue| (statement_index, rvalue))
        })
        .ok_or("the arm has NO assignment to the join local")?;
    let Rvalue::Aggregate(
        AggregateKind::Adt { name, variant: variant_index, active_field, .. },
        operands,
    ) = rv
    else {
        return Err("the arm's join-local rvalue is not an ADT Aggregate");
    };
    if active_field.is_some() {
        return Err("UNION-repr aggregate (active_field) — out of scope");
    }
    if operands.len() > 1 {
        return Err("2+-FIELD VARIANT payload — out of scope for this increment");
    }
    let return_local_ty = &body.locals.get(join_local).ok_or("no such join local")?.ty;
    if join_local == 0 && return_local_ty != &body.return_ty {
        return Err("the return local's type differs from the declared return type");
    }
    let variant = aggregate_variant_discriminant(return_local_ty, name, *variant_index)
        .ok_or("the aggregate's variant is not in the return type's variant metadata")?;
    let Some(payload_op) = operands.first() else {
        return Ok(SemAdtArm { variant, payload: None });
    };
    let (Operand::Copy(p) | Operand::Move(p)) = payload_op else {
        return Err("the payload operand is a CONSTANT, not a place");
    };
    if !p.projections.is_empty() {
        return Err("the payload operand place is PROJECTED");
    }
    // A direct parameter/constant payload — resolve without any temp-tracing.
    if let Some(direct) = sem_operand_of_mir(body, payload_op, param_index) {
        return Ok(SemAdtArm { variant, payload: Some(SemAdtPayload::Scalar(direct)) });
    }
    // A scratch temp: it must be the ARM's OWN local (this arm's sole-writer
    // discipline), soundly resolvable (single-assign, not a call dest, not
    // mutably-aliased — closes adversarial probe (b)).
    if param_index(p.local).is_some() || !crate::prove::local_soundly_resolvable(body, p.local) {
        return Err("outside the modeled arm-value fragment");
    }
    let (definition_block, definition_statement, definition) =
        unique_local_definition_dominating(body, p.local, arm.id, Some(use_statement))
            .ok_or("the payload TEMP has no unique dominating definition")?;
    let definition_site = Some((definition_block, Some(definition_statement)));
    match definition {
        // Preserve the actual integer-cast semantics.  Merely reaching this arm
        // under some guard is not evidence that a narrowing/sign-changing cast is
        // the identity; the destination metadata therefore remains in the witness.
        Rvalue::Cast(op, dest_ty) => {
            let trust_types::Ty::Int { width, signed } = dest_ty else {
                return Err("CAST payload destination is not an integer type");
            };
            if !matches!(*width, 8 | 16 | 32 | 64 | 128)
                || !matches!(op,
                    Operand::Copy(source) | Operand::Move(source)
                        if source.projections.is_empty()
                            && matches!(body.locals.get(source.local).map(|local| &local.ty),
                                Some(trust_types::Ty::Int { .. })))
            {
                return Err("outside the modeled arm-value fragment");
            }
            let source = resolve_cast_source_operand(body, op, param_index, definition_site)
                .ok_or("the CAST source operand resolves to nothing")?;
            Ok(SemAdtArm {
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
            // Trust: SURFACE THE DOWNCAST REASON (2026-08-28). This used to call the
            // `.ok()` wrapper and, on `None`, fall through to the scalar path whose own
            // failure reported "the USE source operand resolves to nothing" — a label
            // that named the FALLBACK rather than the gate that actually fired. Measured:
            // it covered 172 of 357 `<X as Try>::branch` bodies (48.2%), the single
            // largest bucket in the enum lane, and said nothing about any of them.
            //
            // The reasoned variant is the same implementation, so the reason cannot
            // describe a different gate. It is preferred ONLY when the operand really is
            // a downcast read; for an ordinary scalar `Use` the downcast reason would be
            // the misleading one, and the scalar path keeps its own.
            let downcast_decline =
                match downcast_field_payload_reasoned(body, op, param_index, expected_downcast_variant)
                {
                    Ok(payload) => return Ok(SemAdtArm { variant, payload: Some(payload) }),
                    Err(reason) => reason,
                };
            let operand_is_downcast_read = matches!(
                op,
                Operand::Copy(p) | Operand::Move(p)
                    if p.projections.iter().any(|proj| matches!(proj, trust_types::Projection::Downcast(_)))
            );
            let resolved = resolve_cast_source_operand(body, op, param_index, definition_site)
                .ok_or(if operand_is_downcast_read {
                    downcast_decline
                } else {
                    "the USE source operand resolves to nothing"
                })?;
            Ok(SemAdtArm { variant, payload: Some(SemAdtPayload::Scalar(resolved)) })
        }
        // A NESTED fieldless-variant construction (`Error::Underflow`-class): a
        // ZERO-operand Aggregate.  Its enum name and declaration-order index are
        // checked against the payload local's declared first-class enum metadata;
        // the reported value is that variant's actual discriminant.
        Rvalue::Aggregate(
            AggregateKind::Adt {
                name: nested_name,
                variant: nested_variant,
                active_field: nested_active,
                ..
            },
            nested_ops,
        ) if nested_active.is_none() && nested_ops.is_empty() => {
            let nested_variant = aggregate_variant_discriminant(
                &body.locals.get(p.local).ok_or("no such payload local")?.ty,
                nested_name,
                *nested_variant,
            )
            .ok_or("the NESTED aggregate variant is not in the payload local's metadata")?;
            Ok(SemAdtArm {
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
            )
            .ok_or("the borrowed payload is not a recognized slice projection")?;
            // `from_end:true` (`slice::last`) denotes index `sliceLen(s) - offset`, which
            // no current `SemOperand` composes (no Sub / Len-minus-const carrier; `PreOp`
            // is Not/Neg only) — decline HONESTLY here (fail-closed `None`).
            let idx = proj
                .kind
                .index_operand()
                .ok_or("a from_end ConstantIndex composes no SemOperand")?;
            Ok(SemAdtArm {
                variant,
                payload: Some(SemAdtPayload::Scalar(SemOperand::Index(
                    Box::new(SemOperand::Var(proj.base_param)),
                    Box::new(idx),
                ))),
            })
        }
        // Name the rvalue rather than lumping it: each of these is a different piece of
        // work, and "outside the fragment" as one number hides which one is worth doing.
        Rvalue::BinaryOp(..) | Rvalue::UncheckedBinaryOp(..) => {
            Err("payload TEMP is a BINARY OP (arithmetic on the payload)")
        }
        Rvalue::CheckedBinaryOp(..) => Err("payload TEMP is a CHECKED binary op"),
        Rvalue::UnaryOp(..) => Err("payload TEMP is a UNARY OP"),
        // Trust: NESTED-CTOR ARM PAYLOAD (2026-08-26) — `Some(Inner(x))`. Resolved through
        // the STRUCT lane's own `nested_ctor_field_of`, so the admission gates (unique
        // whole-local definition, no call-dest, no SetDiscriminant, declared-arity match,
        // bounded depth) are shared rather than re-implemented. Refused when any field is
        // an `OpaqueParam`: its denotation needs a binder the ADT-return witness's `(o, e)`
        // layout does not have, and inventing one is exactly what fail-closed forbids.
        Rvalue::Aggregate(..) => match nested_ctor_field_of(body, p, param_index, 0) {
            Some(SemStructField::NestedCtor { ty, variant: inner_variant, fields })
                if nested_fields_all_scalar(&fields) =>
            {
                Ok(SemAdtArm {
                    variant,
                    payload: Some(SemAdtPayload::NestedCtor {
                        ty,
                        variant: inner_variant,
                        fields,
                    }),
                })
            }
            Some(SemStructField::NestedCtor { .. }) => {
                Err("nested ctor payload has a NON-SCALAR field (no stub slot for it)")
            }
            // Ask the RESOLVER which of its gates refused — same code, not a second copy.
            _ => match nested_ctor_field_of_reasoned(body, p, param_index, 0) {
                Err(why) => Err(why),
                Ok(_) => Err("the nested-ctor resolver returned a non-NestedCtor field"),
            },
        },
        Rvalue::Discriminant(..) => Err("payload TEMP is a raw DISCRIMINANT read"),
        Rvalue::Len(..) => Err("payload TEMP is a slice LEN"),
        Rvalue::Repeat(..) => Err("payload TEMP is a REPEAT array"),
        Rvalue::Ref { mutable: true, .. } => Err("payload TEMP is a MUTABLE borrow"),
        Rvalue::AddressOf { .. } => Err("payload TEMP is a raw ADDRESS-OF"),
        Rvalue::CopyForDeref(..) => Err("payload TEMP is a CopyForDeref"),
        Rvalue::PtrOffset { .. } => Err("payload TEMP is a POINTER OFFSET"),
        Rvalue::Unsupported { .. } => Err("payload TEMP rvalue is UNSUPPORTED by the extractor"),
        _ => Err("the payload TEMP's rvalue is outside the modeled fragment"),
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
    downcast_field_payload_reasoned(body, op, param_index, expected_downcast_variant).ok()
}

/// [`downcast_field_payload`] with the decline REASON — ONE implementation, two callers.
///
/// The recognizer takes `.ok()`; the decline diagnostic reads the `Err`. It is written
/// this way for the reason recorded on [`sem_adt_return_dispatch_of`]: a diagnostic that
/// re-implements a gate is a second implementation of that gate, and the two disagree
/// exactly when it matters. Every string below names the gate that refused, so a corpus
/// histogram distinguishes a CORRECT refusal (no value identity, no pinned variant) from
/// a real capability gap.
pub(super) fn downcast_field_payload_reasoned(
    body: &trust_types::VerifiableBody,
    op: &trust_types::Operand,
    param_index: &dyn Fn(usize) -> Option<u64>,
    expected_downcast_variant: Option<usize>,
) -> Result<SemAdtPayload, &'static str> {
    use trust_types::{Operand, Projection, Ty};
    let (Operand::Copy(p) | Operand::Move(p)) = op else {
        return Err("payload operand is a CONSTANT, not a place");
    };
    // Trust: W20 VALUE-TIER `&self` PAYLOAD (2026-08-26) — the `&self` counterpart of the
    // dispatch widening in [`downcast_expected_variants`]. `match self { E::A(x) => ..*x.. }`
    // on a `&self` receiver reads `((*_self) as A).f`, i.e. the SAME downcast+field with one
    // leading `Deref`. An immutable reference denotes its referent's value, so the read is
    // the referent's own field and `Var(base_param)` denotes it exactly — the reasoning
    // `sem_operand_of_mir`'s GAP-DEREF-SELF arm already ratified. Gated below on
    // `mutable: false` AND `!deref_write_exists`; `&mut self` and any write-through decline.
    let (v, f, through_ref) = match p.projections.as_slice() {
        [Projection::Downcast(v), Projection::Field(f)] => (v, f, false),
        [Projection::Deref, Projection::Downcast(v), Projection::Field(f)] => (v, f, true),
        _ => return Err("projection is not [Downcast, Field] (nor one Deref before it)"),
    };
    // The base is the `self` PARAMETER (by value, or behind one immutable `&`), not
    // reassigned/aliased.
    let base_param = param_index(p.local).ok_or("the downcast base is not a PARAMETER")?;
    if param_reassigned_by_stmt(body, p.local) {
        return Err("the base parameter is REASSIGNED before the read");
    }
    // TAG↔DOWNCAST provenance (gate D).
    if expected_downcast_variant != Some(*v) {
        // Trust: SPLIT (2026-08-28). One label covered 156 of 357 `Try::branch` bodies
        // — the largest gate in the enum lane — and conflated two situations needing
        // opposite work. NO expected variant means the dispatch derivation
        // (`downcast_expected_variants`) declined and the fix is there; a DIFFERENT one
        // means it derived a variant and the arm reads the other, which is an
        // arm/tag pairing question in `sem_adt_return_dispatch_of`.
        return Err(if expected_downcast_variant.is_none() {
            "gate D: the dispatch derived NO expected downcast variant"
        } else {
            "gate D: the dispatch pins a DIFFERENT downcast variant than the arm reads"
        });
    }
    let self_ty = &body.locals.get(p.local).ok_or("no such local")?.ty;
    let self_ty = if through_ref {
        match self_ty {
            Ty::Ref { mutable: false, inner }
                if !crate::mirsem::deref_write_exists(body, p.local) =>
            {
                inner.as_ref()
            }
            _ => return Err("`&mut self`, a write-through, or a non-reference base"),
        }
    } else {
        self_ty
    };
    let Ty::Adt { variants, fields, .. } = self_ty else {
        return Err("the downcast base is not an ADT");
    };
    if variants.is_empty() {
        return Err("the base ADT carries NO first-class variant metadata");
    }
    if !self_ty.disc_index_safe() {
        return Err("NICHE layout — an off-variant slot read would be unsound");
    }
    let variant_def = variants.get(*v).ok_or("no such variant in the base ADT")?;
    let (field_name, field_ty) =
        variant_def.fields.get(*f).ok_or("no such field in that variant")?;
    // Trust: NON-SCALAR DOWNCAST PAYLOAD (2026-08-26) — a `Ty::Adt` payload is admitted
    // as `DowncastOpaque`, which denotes at the payload's OWN carrier rather than the
    // `Int`-sorted `idxElem` key. Every other gate above (base is an unaliased
    // parameter, `disc_index_safe` enum, TAG-DOWNCAST provenance) has already run, and
    // the flattened key below is computed identically for both, so
    // DOWNCAST-KEY-DISJOINTNESS is unchanged. A `String`, tuple, reference or otherwise
    // non-reflectable payload still declines.
    let opaque_payload = match field_ty {
        Ty::Int { .. } => false,
        Ty::Adt { .. } => true,
        Ty::Ref { .. } => return Err("payload field is a REFERENCE"),
        Ty::Bool => return Err("payload field is Bool"),
        Ty::Tuple(_) => return Err("payload field is a TUPLE"),
        _ => return Err("payload field is neither Int nor Adt"),
    };
    // DOWNCAST-KEY-DISJOINTNESS (gate A): the VARIANT-DISJOINT flattened `idxElem` key is
    // the position of `__v{v}_{field}` in the flattened `fields` list — NEVER the
    // within-variant index `f`. Derived from the dump's own first-class field metadata;
    // fail-closed if that flattened name is absent (a legacy / non-flattened dump).
    let flat_name = format!("__v{v}_{field_name}");
    let flat_key = fields
        .iter()
        .position(|(name, _)| name == &flat_name)
        .ok_or("the flattened `__v{v}_{field}` slot is ABSENT (legacy/non-flattened dump)")?;
    let flat_key = u64::try_from(flat_key).map_err(|_| "flattened key does not fit u64")?;
    if flat_key == 0 {
        return Err("the flattened key is the `__tag` slot"); // never a payload field.
    }
    if opaque_payload {
        return Ok(SemAdtPayload::DowncastOpaque {
            base_param,
            flat_key,
            downcast_variant: *v,
            payload_ty: field_ty.clone(),
        });
    }
    Ok(SemAdtPayload::DowncastField { base_param, flat_key, downcast_variant: *v })
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
    downcast_expected_variants_reasoned(body, leaf, tag_then, tag_else, param_index)
        .unwrap_or((None, None))
}

/// [`downcast_expected_variants`] with the decline REASON — ONE implementation, two
/// callers, for the reason recorded on [`sem_adt_return_dispatch_of`]. `Err` names the
/// gate that refused to pin a variant, so a corpus histogram can tell a CORRECT refusal
/// (nothing establishes which variant is live) from a real capability gap.
pub(super) fn downcast_expected_variants_reasoned(
    body: &trust_types::VerifiableBody,
    leaf: &SemCond,
    tag_then: u128,
    tag_else: u128,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Result<(Option<usize>, Option<usize>), &'static str> {
    let none = "";
    let _ = none;
    if leaf.op != SemCmpOp::Eq {
        return Err("the guard is not an EQUALITY");
    }
    let SemOperand::Discriminant(base) = &leaf.a else {
        return Err("the guard's LHS is not a Discriminant read");
    };
    let SemOperand::Var(sp) = base.as_ref() else {
        return Err("the discriminant base is not a bare Var");
    };
    let Some(self_local) = usize::try_from(*sp).ok().and_then(|s| s.checked_add(1)) else {
        return Err("the base var index does not map to a local");
    };
    if param_index(self_local) != Some(*sp) {
        return Err("the discriminant base is not the PARAMETER at that index");
    };
    let Some(local) = body.locals.get(self_local) else { return Err("no such local") };
    // Trust: W20 VALUE-TIER `&self` DISPATCH (2026-08-26) — an IMMUTABLE reference denotes
    // its referent's VALUE, so `Discriminant(*self)` IS the referent's own tag. Look
    // through exactly one immutable `&` here, mirroring what
    // [`sem_discriminant_base_of_mir`] — which produced this very `leaf` — already did to
    // resolve the base to `Var(sp)`. WITHOUT THIS THE TWO DISAGREE: the base resolver
    // accepts `*self`, this function then re-read the RAW local type, saw `Ty::Ref`, and
    // returned `(None, None)`, so every `&self` dispatch silently lost its TAG↔DOWNCAST
    // provenance and its payload declined at gate D. `&mut` NEVER looks through — it can
    // be written through between the tag read and the payload read — and neither does a
    // reference with any write reaching through it, the same defense the base resolver
    // applies at the same seam.
    let self_ty = match &local.ty {
        trust_types::Ty::Ref { mutable: false, inner }
            if !crate::mirsem::deref_write_exists(body, self_local) =>
        {
            inner.as_ref()
        }
        other => other,
    };
    let trust_types::Ty::Adt { variants, .. } = self_ty else {
        return Err("the dispatch base is not an ADT");
    };
    if variants.is_empty() {
        return Err("the base ADT carries NO first-class variant metadata");
    }
    if variants.len() != 2 {
        return Err("the base enum has 3+ VARIANTS (the pin is 2-variant only)");
    }
    if !self_ty.disc_index_safe() {
        return Err("NICHE layout — the tag does not index variants");
    }
    // RAW label vs DECODED tag, and that is EXACT here rather than an oversight.
    // `VariantDef::discriminant` is decoded at the extraction boundary; a MIR
    // arm label stays raw. For a NON-NEGATIVE tag the raw pattern and the
    // decoded value are the same integer at every width that can hold it, so
    // this comparison is exact on that sub-domain. A NEGATIVE tag's raw pattern
    // is `>= 2^(w-1)` while its decoded value is `< 0`, so they never match and
    // `position` yields `None` — the recognizer declines (fail closed). It is
    // never a WRONG match: no width makes a negative tag's pattern collide with
    // another variant's non-negative tag. This leaf carries no discriminant-temp
    // type, so decoding the label here would mean guessing a width — declining
    // is the correct alternative.
    let (Ok(tag_then), Ok(tag_else)) = (i128::try_from(tag_then), i128::try_from(tag_else)) else {
        return Err("a switch tag does not fit i128");
    };
    let then_v = variants.iter().position(|variant| variant.discriminant == tag_then);
    let else_v = variants.iter().position(|variant| variant.discriminant == tag_else);
    if then_v.is_none() && else_v.is_none() {
        return Err("NEITHER switch tag matches a declared variant discriminant");
    }
    Ok((then_v, else_v))
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
    if crate::assignment_types::modeled_enum_variant_count(
        &body.datatype_defs,
        &body.locals.get(self_local)?.ty,
    )
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
    sem_struct_return_shape_reasoned(func).ok()
}

/// [`sem_struct_return_shape_of`] with the decline REASON — ONE implementation, two
/// callers, the fifth application of the discipline on [`sem_adt_return_dispatch_of`].
///
/// WHY THIS LANE. Measured on a frozen 56,328-body corpus: 55.5% of bodies return an ADT,
/// 97.5% of those are recognized by no extractor, and the largest intraprocedural class in
/// that mass is 6,523 bodies whose SOLE `_0` write is an `Aggregate` — a plain constructor
/// return that this very function declines. That is ~24x the entire `SemAdtReturn` family.
/// Sizing it by gate is what says which of these twenty gates is worth moving.
pub(crate) fn sem_struct_return_shape_reasoned(
    func: &trust_types::VerifiableFunction,
) -> Result<SemStructReturn, &'static str> {
    use trust_types::{
        AggregateKind, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty,
    };
    trust_vcgen::validate_function(func).map_err(|_| "validate_function rejects the body")?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return Err("an assignment's operand TYPE does not match its place");
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1) The return type is a CONCRETE struct with FRESH first-class field metadata.
    let Ty::Adt { name: ret_name, fields: ret_fields, variants, .. } = &body.return_ty else {
        return Err("the return type is not an ADT");
    };
    if !variants.is_empty() {
        return Err("the return is an ENUM (the SemAdtReturn family's business)");
    }
    if ret_fields.is_empty() {
        return Err("a FIELDLESS struct (ZST) — reflect_struct declines it");
    }
    if ret_fields.iter().any(|(fname, _)| fname == "__tag" || fname.starts_with("__v")) {
        return Err("a LEGACY __tag/__v-flattened dump (fresh-metadata gate)");
    }

    // (4) SOLE-WRITER: exactly one bare `_0` assign in the whole body; zero projected
    // `_0.f` writes, zero call-dest / drop of `_0`, no mutable alias.
    if !local_has_only_guarded_writes(body, 0, 1, 0) {
        return Err("`_0` is not written EXACTLY ONCE bare (projected/call-dest/aliased)");
    }

    // (C) SPINE-STATEMENT WHITELIST — straight-line terminators + storage-or-unprojected-
    // Assign statements only. A deref-base write has a PROJECTED place and declines here.
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => {}
            // Named individually, not lumped: a `Drop` is VALUE-TRANSPARENT (the
            // `SemAdtReturn` lane already models a drop-ladder epilogue), a `SwitchInt`
            // means a real branch, and a `Call` means interprocedural. Those are three
            // different pieces of work and reporting them as one number hides which is
            // worth doing — the mistake this report made four times before naming it.
            Terminator::Drop { .. } => return Err("a DROP terminator on the spine"),
            Terminator::SwitchInt { .. } => return Err("a SWITCHINT terminator on the spine"),
            Terminator::Call { .. } => return Err("a CALL terminator on the spine"),
            Terminator::Unreachable => return Err("an UNREACHABLE terminator on the spine"),
            _ => return Err("some other non-straight-line terminator on the spine"),
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
                _ => return Err("a PROJECTED assignment on the spine (e.g. a deref write)"),
            }
        }
    }

    // The sole `_0 = Aggregate(..)` write lives in the UNIQUE return block, immediately
    // before `Return` (only storage markers may follow), on the entry-reachable spine.
    let ret_block = unique_return_block(body).ok_or("no UNIQUE return block")?;
    let reachable = cfg_reachable_from(body, BlockId(0)).ok_or("the CFG is not walkable")?;
    if !reachable.contains(&ret_block.id) {
        return Err("the return block is not reachable from entry");
    }
    let agg_idx = ret_block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::Aggregate(..), .. }
            if place.local == 0 && place.projections.is_empty())
    })
    .ok_or("the return block has NO Aggregate assignment to `_0`")?;
    // Nothing between the Aggregate and `Return` (only inert storage markers).
    for stmt in &ret_block.stmts[agg_idx + 1..] {
        match stmt {
            Statement::StorageLive(l) | Statement::StorageDead(l) if *l != 0 => {}
            Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => {}
            _ => return Err("a statement other than a storage marker FOLLOWS the aggregate"),
        }
    }

    let Statement::Assign { rvalue: Rvalue::Aggregate(kind, operands), .. } =
        &ret_block.stmts[agg_idx]
    else {
        return Err("the sole `_0` write is not an Aggregate in the return block");
    };
    let AggregateKind::Adt { name: agg_name, variant, active_field, .. } = kind else {
        return Err("the aggregate is not an ADT aggregate (tuple/array/closure)");
    };
    // (B) active_field == None as a LITERAL gate (union-repr aggregate declines).
    if active_field.is_some() {
        return Err("UNION-repr aggregate (active_field)");
    }
    // (2) return-type cross-check: single-variant struct (variant 0), name match, arity.
    if *variant != 0 {
        return Err("a STRUCT return whose aggregate names a non-zero variant");
    }
    if agg_name != ret_name {
        return Err("the aggregate's NAME differs from the return type's name");
    }
    if operands.len() != ret_fields.len() {
        return Err("the aggregate's ARITY differs from the return type's field count");
    }

    // (3) CARRIER ADMISSION — reflect the concrete single-`.mk` carrier, register it,
    // and RE-GET the registry (never assume registration succeeded: a gate-failed
    // inductive stays in the env but is absent from the registry).
    let carrier = crate::reflect::reflect_struct(&body.return_ty)
        .ok_or("the return type does NOT REFLECT to a carrier")?;
    if carrier.is_enum() {
        return Err("reflect routed this type to the ENUM family");
    }
    // Trust: GENERIC-CTOR increment (2026-08-25) — a PI-WRAPPED generic `.mk` is
    // admitted. It used to decline here as "(7) concrete-only". Measured over the
    // real-code dumps: of the 113 bare single-statement ADT constructors, 41 build a
    // usable carrier and died on exactly this line, and ALL 41 carry at least one
    // param-typed FIELD — so the cheap version of this lift (bind the type params,
    // leave the field denotations alone) would have gained zero. The field loop below
    // gives those fields a `GenericParam` binder keyed by SOURCE PARAMETER, and
    // `trustir_adt::build_struct_refinement` binds `Sort 1` type binders outermost.
    if carrier.fields.len() != operands.len() {
        return Err("the CARRIER's field count differs from the aggregate's arity");
    }
    {
        let mut env = crate::trustir_anchor::trustir_env().map_err(|_| "no anchor env")?;
        let registry =
            crate::clean_ground::register_adt_carriers(
                &mut env,
                &crate::clean_ground::carrier_closure_for(&body.return_ty, &carrier),
            );
        // re-get: a gate-failed carrier is absent from the registry.
        let confirmed = registry
            .get(&carrier.name)
            .ok_or("the carrier FAILED TO REGISTER (add_inductive / axiom gate)")?;
        if confirmed.fields.len() != operands.len() {
            return Err("the REGISTERED carrier's field count differs from the arity");
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
                _ => return Err("a UNIT-carrier slot's operand is not the unit constant"),
            }
        } else if matches!(fty, Ty::Int { .. } | Ty::Bool) {
            // A scalar field — route through the PARAM-ROOT chokepoint (gate A). A
            // reassigned parameter, a non-parameter place, or a `Unit` constant in an
            // `Int` slot all fail closed here (`sem_operand_of_mir` returns `None`).
            // Trust: SCALAR TEMP CHASE (2026-08-27) — fall back to
            // [`resolve_cast_source_operand`], which tries the direct read, then a field
            // read, then traces a NON-parameter temp's SOLE static assignment one level
            // deep behind its call-dest / mutable-alias gates.
            //
            // WHY IT IS SOUND HERE. `use_site: None` selects the "sole static assignment
            // anywhere" resolution rather than a dominating one — which is exact in THIS
            // lane because the lane already requires a STRAIGHT-LINE spine (the
            // terminator whitelist above rejects any switch/call/drop), so a body with one
            // static assignment has exactly one dynamic one.
            //
            // WHY IT IS WORTH DOING. Of the 788 bodies that pass every INDEPENDENT gate of
            // this lane and are still unrecognized, 156 stop on this operand, and 138 of
            // those (88%) are a bare temp needing exactly this chase. Unlike the classes
            // that produced eight zero-gain widenings, these bodies have NO other
            // independent blocker waiting behind this one.
            let scalar = resolve_cast_source_operand(body, op, &param_index, None)
                .ok_or("a SCALAR field's operand does not resolve")?;
            fields.push(SemStructField::Scalar(scalar));
        } else if matches!(fty, Ty::Adt { .. })
            || carrier
                .fields
                .get(fields.len())
                .is_some_and(|(_, code)| crate::reflect::carrier_mentions_param(code))
        {
            // Trust: GENERIC-CTOR increment (2026-08-25) — a field whose reflected
            // carrier is (or nests) a BOUND TYPE PARAMETER. Its value cannot be an
            // `Env` lookup (`Env` is `Int`-sorted), so it denotes a ∀-bound binder
            // keyed by the SOURCE PARAMETER — which is what keeps the witness
            // non-tautological (see `SemStructField::OpaqueParam`).
            //
            // Admission is deliberately narrow: a BARE, unprojected, entry-time read
            // of a function parameter. A projected place, a temporary, a constant, or
            // a parameter REASSIGNED before the aggregate all fail closed — the last
            // one because the binder denotes the parameter's ENTRY value, exactly the
            // discipline `sem_operand_of_mir` applies on the scalar arm.
            let (Operand::Copy(place) | Operand::Move(place)) = op else {
                return Err("a field operand is a CONSTANT where a place is required");
            };
            // Trust: PROJECTED SOURCE (2026-08-25) — a bare read, or exactly ONE field
            // projection of a parameter. Anything deeper (a deref, an index, a nested
            // field chain) is refused: its value is not determined by the parameter's
            // entry value alone.
            // A NESTED CONSTRUCTOR first (exact structure), else a bare-or-one-field
            // read of a PARAMETER or a TEMPORARY that provably copies one.
            if let Some(nested) = nested_ctor_field_of(body, place, &param_index, 0) {
                fields.push(nested);
            } else {
                let (param, part) = resolve_temp_field_source(body, place, &param_index)
                    .ok_or("a field operand is not a resolvable PARAMETER PART")?;
                fields.push(SemStructField::OpaqueParam { param, part });
            }
        } else {
            // (E) POINTER / ref / slice / tuple field — OUT of increment 1. A raw-ptr /
            // `NonNull` root is NOT admitted in this lane (fail closed) until
            // `sliceStart`/`ptrOffset` land with their gates (increment 3).
            //
            // Trust: LABEL CORRECTION (2026-08-27) — this message used to say
            // "nested-struct" as well. It is WRONG: a `Ty::Adt` field is handled by the
            // arm ABOVE (nested constructor, else parameter part), so no nested struct
            // ever reaches here. The stale word sent a reader looking for a nested-struct
            // gap that does not exist; naming the ACTUAL types is the point of these
            // labels. Split by kind so the corpus says which of them is worth anything.
            return Err(match fty {
                Ty::Ref { .. } => "field type is a REFERENCE",
                Ty::RawPtr { .. } => "field type is a RAW POINTER",
                Ty::Slice { .. } => "field type is a SLICE",
                Ty::Str => "field type is a STR",
                Ty::Array { .. } => "field type is an ARRAY",
                Ty::Tuple(..) => "field type is a TUPLE",
                Ty::Float { .. } => "field type is a FLOAT",
                Ty::Char => "field type is a CHAR",
                Ty::PtrSizedInt { .. } => "field type is a PTR-SIZED INT",
                _ => "field type is outside the modeled fragment",
            });
        }
    }

    Ok(SemStructReturn { struct_ty: body.return_ty.clone(), fields })
}

/// Trust: NESTED-CTOR increment (2026-08-25) — recognize a field operand that is itself
/// a constructor: a temporary whose UNIQUE whole-local definition is an
/// `Rvalue::Aggregate`.
///
/// Soundness is the same uniqueness argument the other temporary chases use: the local
/// must be written exactly once in the whole body, unprojected, never by a call
/// terminator or `SetDiscriminant`, so its value is the same on every path. Bounded
/// depth, and every level re-applies the same field admission the top level does — a
/// field it cannot admit declines the whole nest rather than approximating it.
fn nested_ctor_field_of(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: u32,
) -> Option<SemStructField> {
    nested_ctor_field_of_reasoned(body, place, param_index, depth).ok()
}

/// [`nested_ctor_field_of`] with the decline REASON — ONE implementation, two callers, the
/// fourth application of the discipline recorded on [`sem_adt_return_dispatch_of`]. Twice
/// in a row a class was sized by the layer the instrument happened to reach and the
/// widening built for it gained ZERO; naming this layer's gates is what stops a third.
pub(super) fn nested_ctor_field_of_reasoned(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
    depth: u32,
) -> Result<SemStructField, &'static str> {
    use trust_types::{AggregateKind, ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    if depth > 3 {
        return Err("nesting DEPTH exceeded");
    }
    if !place.projections.is_empty() {
        return Err("the payload place is PROJECTED");
    }
    // A parameter is not a nested constructor.
    if param_index(place.local).is_some() {
        return Err("the payload local is a PARAMETER, not a constructed temp");
    }
    let mut found: Option<&Rvalue> = None;
    for bb in &body.blocks {
        if let Terminator::Call { dest, .. } = &bb.terminator
            && dest.local == place.local
        {
            return Err("the payload temp is a CALL destination");
        }
        for st in &bb.stmts {
            match st {
                Statement::Assign { place: p, rvalue, .. } if p.local == place.local => {
                    if !p.projections.is_empty() {
                        return Err("the payload temp is written through a PROJECTION");
                    }
                    if found.is_some() {
                        return Err("the payload temp is assigned MORE THAN ONCE");
                    }
                    found = Some(rvalue);
                }
                Statement::SetDiscriminant { place: p, .. } if p.local == place.local => {
                    return Err("the payload temp has a SetDiscriminant write");
                }
                _ => {}
            }
        }
    }
    let Rvalue::Aggregate(kind, operands) = found.ok_or("the payload temp has NO assignment")?
    else {
        return Err("the payload temp's rvalue is not an Aggregate");
    };
    let AggregateKind::Adt { name: agg_name, variant, active_field, .. } = kind else {
        return Err("the payload aggregate is not an ADT aggregate");
    };
    if active_field.is_some() {
        return Err("UNION-repr payload aggregate");
    }
    let inner_ty = body.locals.get(place.local).map(|l| l.ty.clone()).ok_or("no such local")?;
    let (ty_name, flat, variants) = match &inner_ty {
        Ty::Adt { name, fields, variants, .. } => (name.clone(), fields.clone(), variants.clone()),
        _ => return Err("the payload temp's declared type is not an ADT"),
    };
    if &ty_name != agg_name {
        return Err("the aggregate's NAME differs from the temp's declared ADT name");
    }
    let variant_idx = usize::try_from(*variant).map_err(|_| "variant index does not fit usize")?;
    // The declared field list for THIS constructor: a variant's own fields for an enum,
    // the struct's fields otherwise.
    let declared: Vec<(String, Ty)> = if variants.is_empty() {
        if variant_idx != 0 {
            return Err("a STRUCT aggregate names a non-zero variant");
        }
        flat
    } else {
        variants.get(variant_idx).ok_or("no such variant in the temp's metadata")?.fields.clone()
    };
    if declared.len() != operands.len() {
        return Err("the DECLARED field count differs from the aggregate's operand count");
    }
    let mut fields = Vec::with_capacity(operands.len());
    for ((_fname, fty), op) in declared.iter().zip(operands.iter()) {
        if is_unit_carrier_ty(fty) {
            match op {
                Operand::Constant(ConstValue::Unit) => fields.push(SemStructField::Unit),
                _ => return Err("a UNIT-carrier field's operand is not the unit constant"),
            }
        } else if matches!(fty, Ty::Int { .. } | Ty::Bool) {
            fields.push(SemStructField::Scalar(
                sem_operand_of_mir(body, op, param_index)
                    .ok_or("a SCALAR field's operand does not resolve")?,
            ));
        } else if matches!(fty, Ty::Adt { .. }) {
            let (Operand::Copy(p) | Operand::Move(p)) = op else {
                return Err("an ADT field's operand is a CONSTANT, not a place");
            };
            // Another nest, or a parameter part.
            match nested_ctor_field_of(body, p, param_index, depth + 1) {
                Some(f) => fields.push(f),
                None => {
                    let (param, part) = resolve_temp_field_source(body, p, param_index)
                        .ok_or("an ADT field is neither a nested ctor nor a parameter part")?;
                    fields.push(SemStructField::OpaqueParam { param, part });
                }
            }
        } else {
            return Err("a field TYPE is outside {Int, Bool, Unit-carrier, Adt}");
        }
    }
    Ok(SemStructField::NestedCtor {
        ty: inner_ty,
        variant: if variants.is_empty() { None } else { Some(variant_idx) },
        fields,
    })
}

/// Trust: NESTED-CTOR ARM PAYLOAD (2026-08-26) — is every field of this nested
/// constructor a SCALAR?
///
/// The ADT-return lane denotes a nested payload through a STUB carrier
/// (`trustir_adt::nested_ctor_stub_ty`) whose slots are `Int`, so a scalar field has a
/// slot and anything else does not. In particular an [`SemStructField::OpaqueParam`] has
/// no denotation at all here — its reading is a ∀-bound binder whose index depends on the
/// whole binder layout, and this lane's `(o, e)` layout binds no such thing. Declining is
/// the only honest option; inventing a binder is what fail-closed forbids.
///
/// A deeper nest declines too: its stub would need a non-`Int` slot, which is the same
/// wall one level down. That is a scope boundary, not a soundness one — when the stub
/// gains typed slots this check is what relaxes.
fn nested_fields_all_scalar(fields: &[SemStructField]) -> bool {
    !fields.is_empty() && fields.iter().all(|f| matches!(f, SemStructField::Scalar(_)))
}

/// Trust: ACCESSOR SHAPE (2026-08-26) — resolve `(*p)` or `(*p).n` on an
/// IMMUTABLE-reference parameter to the `(param, part)` pair the passthrough witness
/// uses.
///
/// `part` is `0` for the whole referent and `n + 1` for its field `n`, the same encoding
/// [`SemStructField::OpaqueParam`] uses. Refused when the parameter is not an immutable
/// reference, is reassigned, is deref-written anywhere in the body, or the projection is
/// anything other than `[Deref]` / `[Deref, Field]` — a deeper chain is not determined by
/// the parameter's entry value alone.
fn resolve_deref_field_source(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<(u64, u64)> {
    use trust_types::{Projection, Ty};
    let part = match place.projections.as_slice() {
        [Projection::Deref] => 0u64,
        [Projection::Deref, Projection::Field(n)] => u64::try_from(*n).ok()?.checked_add(1)?,
        _ => return None,
    };
    // The base must be an IMMUTABLE reference parameter.
    match body.locals.get(place.local).map(|l| &l.ty) {
        Some(Ty::Ref { mutable: false, .. }) => {}
        _ => return None,
    }
    let param = param_index(place.local)?;
    if param_reassigned_by_stmt(body, place.local) || deref_write_exists(body, place.local) {
        return None;
    }
    Some((param, part))
}

/// Trust: PASSTHROUGH-RETURN increment (2026-08-25) — recognize `_0 = <parameter>`.
///
/// Gates, all shared in spirit with the constructor lanes: straight-line terminators
/// only, no calls, the whitelisted statement set, `_0` written exactly once and never
/// through a projection or a `SetDiscriminant`, the source a bare-or-one-field read of a
/// parameter that is neither reassigned nor deref-written. Fail-closed on each.
/// Trust: CONST-RETURN recognizer (2026-08-28) — a single-block body whose one statement
/// writes `_0` from a fixed string literal and returns.
///
/// The sibling of [`sem_passthrough_return_shape_of`], and deliberately as narrow: one
/// block, one statement, an unprojected `_0`, an immutable `&str`/`&[u8]` return, and a
/// `ConstValue::Str`. Anything else declines.
///
/// The byte cap is not arithmetic caution — the witness builds one `List.cons` per byte,
/// so a megabyte literal would build a megabyte-deep kernel term. A literal past the cap
/// declines rather than being truncated: a truncated literal would be a DIFFERENT claim
/// wearing the same theorem.
pub fn sem_const_return_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemConstReturn> {
    use trust_types::{ConstValue, Operand, Rvalue, Statement, Terminator, Ty};
    /// The kernel term is linear in the literal's length; 4 KiB of bytes is far past any
    /// real `Token::display` and still cheap to check.
    const MAX_LITERAL_BYTES: usize = 4096;

    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    // An immutable reference to a string or byte slice. `&mut` is refused for the same
    // reason the passthrough lane refuses it: a mutable reference return carries a
    // post-state this entry-time reading does not capture.
    match &body.return_ty {
        Ty::Ref { mutable: false, inner } => match inner.as_ref() {
            Ty::Str => {}
            Ty::Slice { elem } if matches!(elem.as_ref(), Ty::Int { .. }) => {}
            _ => return None,
        },
        _ => return None,
    }
    let [block] = body.blocks.as_slice() else { return None };
    if !matches!(block.terminator, Terminator::Return) {
        return None;
    }
    let [Statement::Assign { place, rvalue, .. }] = block.stmts.as_slice() else { return None };
    if place.local != 0 || !place.projections.is_empty() {
        return None;
    }
    let Rvalue::Use(Operand::Constant(ConstValue::Str { bytes })) = rvalue else { return None };
    if bytes.len() > MAX_LITERAL_BYTES {
        return None;
    }
    Some(SemConstReturn { return_ty: body.return_ty.clone(), bytes: bytes.clone() })
}

pub fn sem_passthrough_return_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemPassthroughReturn> {
    use trust_types::{BlockId, Operand, Rvalue, Statement, Terminator, Ty};
    trust_vcgen::validate_function(func).ok()?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    // An ADT return, or an IMMUTABLE REFERENCE to one. The scalar shapes are the
    // straight-line lane's business and already covered there.
    //
    // Trust: REFERENCE PASSTHROUGH (2026-08-26) — `fn f(x: &T) -> &T { x }` returns the
    // same reference, so modelling it as "the referent VALUE of parameter p" is exactly
    // the W20 value-tier reading of an immutable reference return: a value claim, never
    // an address or aliasing claim. `&mut` is REFUSED — a mutable reference return
    // carries a post-state the entry-time reading would not capture. Measured across
    // three corpora: 117 call-free reference returns are this shape.
    // Trust: SCALAR GETTER (2026-08-26) — `Int`/`Bool` returns are admitted too.
    // `fn len(&self) -> usize { self.len }` is `_0 = ((*_1).n)`, which the trust-ir
    // straight-line lane cannot express (its `to_ir_operand` requires an unprojected
    // place) and no other lane looked for. Measured across three corpora: 185 call-free
    // scalar returns read a parameter part this way — 131 of them `Deref.Field` on an
    // immutable-reference parameter.
    //
    // The witness statement is carrier-agnostic, so a scalar carrier needs no new
    // machinery: `o p k : Int` says the same thing about the same parameter part that
    // `o p k : S` says for an ADT. Where the straight-line lane DOES handle a body it is
    // tried in the same disjunction and its finer value relation still wins.
    // Trust: CARRIER WIDENING (2026-08-28) — the witness is carrier-agnostic, as the
    // note above already says: `o p k : [T]` asserts the same thing about the same
    // parameter part that `o p k : S` does. The list was not a soundness boundary, it
    // was the set of carriers that had come up so far, and it silently excluded the
    // single most common one in real code.
    //
    // Measured on a dependency-closed monomorphized corpus (31,087 bodies): identity at
    // an ADT certifies, identity at a SLICE REFERENCE declines, on bodies that are
    // otherwise byte-identical. `&[T]`/`&str` is the only type family appearing in more
    // than one uncovered bucket — 201 slice-returning and part of 171 identity bodies.
    //
    // SOUND BY CONSTRUCTION, and this is the load-bearing reason widening is safe here
    // rather than merely plausible: `check_passthrough_return_refinement` builds the
    // carrier's inductive through the same nested-closure path as every other lane, so
    // a return type whose inductive cannot be built FAILS CLOSED there. Admitting a
    // carrier can therefore only ever produce another kernel attempt that must still
    // close modulo 3; it can never convert a refusal into an unchecked claim.
    //
    // Still REFUSED, because for these the claim itself would be wrong rather than
    // merely unprovable:
    //   * `&mut` — a mutable reference return carries a post-state the entry-time
    //     reading does not capture (unchanged, and the reason is unchanged).
    //   * `RawPtr` — returning the same pointer is an ADDRESS claim, not the W20
    //     value-tier claim this witness makes.
    //   * `Dynamic`/`FnPtr`/`FnDef`/`Closure` — no value-tier reading to assert.
    fn passthrough_carrier_admissible(ty: &Ty) -> bool {
        matches!(
            ty,
            Ty::Adt { .. }
                | Ty::Int { .. }
                | Ty::Bool
                | Ty::Float { .. }
                | Ty::Char
                | Ty::PtrSizedInt { .. }
                | Ty::Tuple(_)
                | Ty::Array { .. }
                | Ty::Slice { .. }
                | Ty::Str
        )
    }
    match &body.return_ty {
        ty if passthrough_carrier_admissible(ty) => {}
        Ty::Ref { mutable: false, inner } if passthrough_carrier_admissible(inner) => {}
        _ => return None,
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    if !local_has_only_guarded_writes(body, 0, 1, 0) {
        return None;
    }
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
    let ret_block = unique_return_block(body)?;
    let reachable = cfg_reachable_from(body, BlockId(0))?;
    if !reachable.contains(&ret_block.id) {
        return None;
    }
    // `_0 = <place>` or, for the ACCESSOR shape, `_0 = &<place>`.
    let idx = ret_block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::Use(..) | Rvalue::Ref { .. }, .. }
            if place.local == 0 && place.projections.is_empty())
    })?;
    for stmt in &ret_block.stmts[idx + 1..] {
        match stmt {
            Statement::StorageLive(l) | Statement::StorageDead(l) if *l != 0 => {}
            Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => {}
            _ => return None,
        }
    }
    // Trust: ACCESSOR SHAPE (2026-08-26) — `fn kind(&self) -> &Kind { &self.kind }`.
    // MIR spells it `_0 = &((*_1).n)`, so the place carries a leading `Deref` of the
    // `&self` parameter. Measured across three corpora: 128 call-free reference returns
    // are this shape, the second-largest after the passthrough itself.
    //
    // Admitted only for an IMMUTABLE borrow of an immutable-reference parameter, which
    // is the same W20 value-tier reading the reference passthrough uses: `&(*p).n`
    // denotes the value of field `n` of `p`'s referent. A `&mut` borrow, or a parameter
    // that is deref-written anywhere, is refused by `resolve_deref_field_source`.
    let place = match &ret_block.stmts[idx] {
        Statement::Assign { rvalue: Rvalue::Use(op), .. } => {
            let (Operand::Copy(p) | Operand::Move(p)) = op else { return None };
            p
        }
        Statement::Assign { rvalue: Rvalue::Ref { mutable: false, place }, .. } => place,
        _ => return None,
    };
    let (param, part) = resolve_deref_field_source(body, place, &param_index)
        .or_else(|| resolve_temp_field_source(body, place, &param_index))?;
    Some(SemPassthroughReturn { return_ty: body.return_ty.clone(), param, part })
}

/// Trust: TEMPORARY FIELD SOURCE (2026-08-25) — resolve a field operand that is a
/// TEMPORARY back to the parameter part it copies, when that is unambiguous.
///
/// Measured on a 12,880-body corpus: of 1153 call-free Aggregate constructors only 328
/// are single-statement. The other 825 compute their fields into temporaries first, and
/// the opaque-field arm required a BARE parameter read, so all of them declined.
///
/// SOUNDNESS RESTS ON UNIQUENESS. The local must be written exactly once in the whole
/// body, by an unprojected whole-local `Rvalue::Use`, and never by a call terminator or
/// a `SetDiscriminant`. Then `_t = <operand>` holds on EVERY path that defines `_t`, so
/// reading the field through it is valid regardless of which path reached the
/// constructor. A local written twice, written through a projection, or assigned by a
/// terminator is refused.
///
/// The chase follows only `Use` and is bounded, so `_a = _b; _b = p.0` resolves while
/// anything COMPUTED (`BinaryOp`, `Cast`, a call result) stops it. A two-level
/// projection chain is refused as out of the fragment.
fn resolve_temp_field_source(
    body: &trust_types::VerifiableBody,
    place: &trust_types::Place,
    param_index: &dyn Fn(usize) -> Option<u64>,
) -> Option<(u64, u64)> {
    use trust_types::{Operand, Projection, Rvalue, Statement, Terminator};

    /// `0` for the whole local, `n + 1` for its field `n`; anything else is out.
    fn part_of(place: &trust_types::Place) -> Option<u64> {
        match place.projections.as_slice() {
            [] => Some(0),
            [Projection::Field(n)] => u64::try_from(*n).ok()?.checked_add(1),
            _ => None,
        }
    }

    let mut cur = place.clone();
    for _ in 0..8 {
        if let Some(param) = param_index(cur.local) {
            if param_reassigned_by_stmt(body, cur.local) || deref_write_exists(body, cur.local) {
                return None;
            }
            return Some((param, part_of(&cur)?));
        }
        let mut found: Option<trust_types::Place> = None;
        for bb in &body.blocks {
            if let Terminator::Call { dest, .. } = &bb.terminator
                && dest.local == cur.local
            {
                return None;
            }
            for st in &bb.stmts {
                match st {
                    Statement::Assign { place: p, rvalue, .. } if p.local == cur.local => {
                        if !p.projections.is_empty() || found.is_some() {
                            return None;
                        }
                        match rvalue {
                            Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => {
                                found = Some(src.clone());
                            }
                            _ => return None,
                        }
                    }
                    Statement::SetDiscriminant { place: p, .. } if p.local == cur.local => {
                        return None;
                    }
                    _ => {}
                }
            }
        }
        let src = found?;
        part_of(&src)?;
        // `_a.0` where `_a = p.1` is two levels of projection — out of the fragment.
        if !cur.projections.is_empty() && !src.projections.is_empty() {
            return None;
        }
        let next_part = if cur.projections.is_empty() { part_of(&src)? } else { part_of(&cur)? };
        let mut next = src;
        next.projections = match next_part {
            0 => Vec::new(),
            n => vec![Projection::Field(usize::try_from(n - 1).ok()?)],
        };
        cur = next;
    }
    None
}

/// Trust: BARE-ENUM-CTOR increment (2026-08-25) — recognize a bare ENUM-constructor
/// return (`Cow::from(s)`, `ControlFlow::Continue(x)`, `Err(e)`): the sole `_0` write is
/// a concrete `Aggregate` of a VARIANT, immediately followed by `Return`.
///
/// A near-verbatim sibling of [`sem_struct_return_shape_of`] — same sole-writer gate,
/// same spine-statement whitelist, same unique-return-block / reachability gates, same
/// `active_field == None` literal gate, same PARAM-ROOT admission for scalar fields, and
/// the same `OpaqueParam` binder for a field with no `Int`-sorted denotation. Three
/// things differ, all of them enum-specific:
///
///   1. `variants` must be NON-empty (a struct return is the sibling lane's business);
///   2. the flat `__tag` / `__v{v}_{f}` field view is EXPECTED here rather than a
///      legacy-dump decline — an enum's `Ty::Adt::fields` IS that union view, and the
///      constructor's real shape comes from `variants[v].fields`;
///   3. arity and field types are cross-checked against the CONSTRUCTED VARIANT, and
///      against the registered carrier's v-th constructor.
pub fn sem_enum_ctor_return_shape_of(
    func: &trust_types::VerifiableFunction,
) -> Option<SemEnumCtorReturn> {
    sem_enum_ctor_return_shape_reasoned(func).ok()
}

/// [`sem_enum_ctor_return_shape_of`] with the decline REASON — ONE implementation, two
/// callers, the sixth application of the discipline on [`sem_adt_return_dispatch_of`].
///
/// WHY THIS LANE. Of the 6,523 single-`Aggregate` constructor bodies no extractor
/// recognizes, **2,183** are declined by the STRUCT lane with "the return is an ENUM" —
/// i.e. they are this function's business and it refuses them too. After the 2,325 that
/// are interprocedural, this is the largest reachable class in the whole ADT mass.
pub(crate) fn sem_enum_ctor_return_shape_reasoned(
    func: &trust_types::VerifiableFunction,
) -> Result<SemEnumCtorReturn, &'static str> {
    use trust_types::{
        AggregateKind, BlockId, ConstValue, Operand, Rvalue, Statement, Terminator, Ty,
    };
    trust_vcgen::validate_function(func).map_err(|_| "validate_function rejects the body")?;
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return Err("an assignment's operand TYPE does not match its place");
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // (1) The return type is a concrete ENUM with first-class variant metadata.
    let Ty::Adt { name: ret_name, variants, .. } = &body.return_ty else {
        return Err("the return type is not an ADT");
    };
    if variants.is_empty() {
        return Err("a STRUCT return (sem_struct_return_shape_of owns it)");
    }

    // (4) SOLE-WRITER: exactly one bare `_0` assign; no projected `_0.f` write, no
    // call-dest / drop of `_0`, no mutable alias.
    if !local_has_only_guarded_writes(body, 0, 1, 0) {
        return Err("`_0` is not written EXACTLY ONCE bare (projected/call-dest/aliased)");
    }

    // (C) SPINE-STATEMENT WHITELIST — straight-line terminators + storage-or-unprojected
    // Assign statements only. A `SetDiscriminant` write declines here, which is what
    // keeps this lane to genuine `Aggregate` construction.
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Goto(_) | Terminator::Return => {}
            Terminator::Drop { .. } => return Err("a DROP terminator on the spine"),
            Terminator::SwitchInt { .. } => return Err("a SWITCHINT terminator on the spine"),
            Terminator::Call { .. } => return Err("a CALL terminator on the spine"),
            Terminator::Unreachable => return Err("an UNREACHABLE terminator on the spine"),
            _ => return Err("some other non-straight-line terminator on the spine"),
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
                _ => return Err("a PROJECTED assignment on the spine (e.g. a deref write)"),
            }
        }
    }

    let ret_block = unique_return_block(body).ok_or("no UNIQUE return block")?;
    let reachable = cfg_reachable_from(body, BlockId(0)).ok_or("the CFG is not walkable")?;
    if !reachable.contains(&ret_block.id) {
        return Err("the return block is not reachable from entry");
    }
    let agg_idx = ret_block.stmts.iter().position(|s| {
        matches!(s, Statement::Assign { place, rvalue: Rvalue::Aggregate(..), .. }
            if place.local == 0 && place.projections.is_empty())
    })
    .ok_or("the return block has NO Aggregate assignment to `_0`")?;
    for stmt in &ret_block.stmts[agg_idx + 1..] {
        match stmt {
            Statement::StorageLive(l) | Statement::StorageDead(l) if *l != 0 => {}
            Statement::Coverage | Statement::ConstEvalCounter | Statement::Nop => {}
            _ => return Err("a statement other than a storage marker FOLLOWS the aggregate"),
        }
    }
    let Statement::Assign { rvalue: Rvalue::Aggregate(kind, operands), .. } =
        &ret_block.stmts[agg_idx]
    else {
        return Err("the sole `_0` write is not an Aggregate in the return block");
    };
    let AggregateKind::Adt { name: agg_name, variant, active_field, .. } = kind else {
        return Err("the aggregate is not an ADT aggregate (tuple/array/closure)");
    };
    // (B) union-repr aggregate declines.
    if active_field.is_some() {
        return Err("UNION-repr aggregate (active_field)");
    }
    if agg_name != ret_name {
        return Err("the aggregate's NAME differs from the return type's name");
    }
    let variant_idx = usize::try_from(*variant).map_err(|_| "variant index does not fit usize")?;
    let variant_def = variants.get(variant_idx).ok_or("no such variant in the return type")?;
    if variant_def.fields.len() != operands.len() {
        return Err("the variant's field count differs from the aggregate's arity");
    }

    // (3) CARRIER ADMISSION — reflect, register, and RE-GET (a gate-failed inductive
    // stays in the env but is absent from the registry), then cross-check THIS variant's
    // constructor arity.
    let carrier = crate::reflect::reflect_struct(&body.return_ty)
        .ok_or("the return type does NOT REFLECT to a carrier")?;
    if !carrier.is_enum() {
        return Err("reflect routed this type AWAY from the enum family");
    }
    {
        let mut env = crate::trustir_anchor::trustir_env().map_err(|_| "no anchor env")?;
        let registry =
            crate::clean_ground::register_adt_carriers(
                &mut env,
                &crate::clean_ground::carrier_closure_for(&body.return_ty, &carrier),
            );
        let confirmed = registry
            .get(&carrier.name)
            .ok_or("the carrier FAILED TO REGISTER (add_inductive / axiom gate)")?;
        let ctor = confirmed
            .constructors
            .get(variant_idx)
            .ok_or("the REGISTERED carrier has no such constructor")?;
        if ctor.fields.len() != operands.len() {
            return Err("the registered constructor's arity differs from the aggregate's");
        }
        // The registered constructor must be THIS variant, by discriminant — a carrier
        // whose constructor order does not track MIR variant order would otherwise
        // silently build the wrong variant.
        if ctor.discriminant != variant_def.discriminant {
            return Err("the registered constructor's DISCRIMINANT differs from the variant's");
        }
    }

    // Per-field values over the CONSTRUCTED VARIANT's fields.
    let mut fields = Vec::with_capacity(operands.len());
    for ((_fname, fty), op) in variant_def.fields.iter().zip(operands.iter()) {
        if is_unit_carrier_ty(fty) {
            match op {
                Operand::Constant(ConstValue::Unit) => fields.push(SemStructField::Unit),
                _ => return Err("a UNIT-carrier slot's operand is not the unit constant"),
            }
        } else if matches!(fty, Ty::Int { .. } | Ty::Bool) {
            // Trust: SCALAR TEMP CHASE (2026-08-27) — same fallback and same soundness
            // argument as the struct lane above; this lane requires the same straight-line
            // spine, so a sole static assignment is the definition.
            let scalar = resolve_cast_source_operand(body, op, &param_index, None)
                .ok_or("a SCALAR field's operand does not resolve")?;
            fields.push(SemStructField::Scalar(scalar));
        } else if matches!(fty, Ty::Adt { .. })
            || carrier
                .constructors
                .get(variant_idx)
                .and_then(|c| c.fields.get(fields.len()))
                .is_some_and(|(_, code)| crate::reflect::carrier_mentions_param(code))
        {
            // No `Int`-sorted denotation — a parameter-keyed opaque binder, exactly as on
            // the struct lane. `Ty::Ref`/`Ty::RawPtr` fall through to the decline below.
            let (Operand::Copy(place) | Operand::Move(place)) = op else {
                return Err("a field operand is a CONSTANT where a place is required");
            };
            // Trust: PROJECTED SOURCE (2026-08-25) — a bare read, or exactly ONE field
            // projection of a parameter. Anything deeper (a deref, an index, a nested
            // field chain) is refused: its value is not determined by the parameter's
            // entry value alone.
            // A NESTED CONSTRUCTOR first (exact structure), else a bare-or-one-field
            // read of a PARAMETER or a TEMPORARY that provably copies one.
            if let Some(nested) = nested_ctor_field_of(body, place, &param_index, 0) {
                fields.push(nested);
            } else {
                let (param, part) = resolve_temp_field_source(body, place, &param_index)
                    .ok_or("a field operand is not a resolvable PARAMETER PART")?;
                fields.push(SemStructField::OpaqueParam { param, part });
            }
        } else {
            return Err("a POINTER / reference / slice field type");
        }
    }

    Ok(SemEnumCtorReturn {
        enum_ty: body.return_ty.clone(),
        variant: variant_idx,
        fields,
    })
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
            let idx = resolve_index_operand(body, *idx_local, use_site.0, use_site.1, param_index)?;
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

/// Trust: TRANSPARENT-UNWRAP call-arg widening (2026-08-19) — the width- and
/// depth-parametric sibling of [`opaque_guard_newtype_u64`]: a variantless
/// SINGLE-FIELD struct chain, **G-STRUCT-KIND stamped at every hop**, terminating
/// at ANY `Int`. Scoped to CALL arguments exactly as the u64 form: the call model
/// needs only a deterministic opaque token for the value (`SemOperand::Field` —
/// no scalar-value claim), so the exact-u64 restriction carried no soundness
/// content — it was the measured population of its day. The live population here
/// is `NonMaxU8::get`'s argument `(*self).0 : NonZero<u8>` = `Adt(Adt(Int8))`,
/// the transparent-chain shape the 2026-08-18 unwrap leg certifies on the callee
/// side. The stamp requirement is why this is a SIBLING rather than a
/// replacement: the legacy u64 consumers' dumps may predate `adt_kind`, and the
/// old predicate's scope must not silently move.
pub(super) fn opaque_guard_newtype_chain(ty: &trust_types::Ty) -> bool {
    let mut cur = ty;
    for _ in 0..8usize {
        match cur {
            trust_types::Ty::Int { .. } => return true,
            trust_types::Ty::Adt {
                fields, variants, faithful_enum_repr: None, adt_kind, ..
            } if variants.is_empty()
                && *adt_kind == Some(trust_types::AdtKind::Struct)
                && fields.len() == 1 =>
            {
                cur = &fields[0].1;
            }
            _ => return false,
        }
    }
    false
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
            callee_identity: None,
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
            let Rvalue::Aggregate(
                AggregateKind::Adt { name, variant, active_field: None, .. },
                ops,
            ) = rvalue
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
    // DECODED tags. `VariantDef::discriminant` crossed the extraction boundary as
    // a raw two's-complement bit pattern until that boundary began decoding it, so
    // this list read `("Less", 255)`; against a body extracted by a decoding
    // compiler that comparison can never hold, and the lane would silently accept
    // nothing. The SwitchInt arm labels below are a DIFFERENT channel and are
    // still the raw `u128` the MIR carries — 255 there is correct and is not a
    // leftover.
    let expected_ordering = [("Less", -1i128), ("Equal", 0), ("Greater", 1)];
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
        callee_identity: None,
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
                        AggregateKind::Adt {
                            name,
                            variant: actual_variant,
                            active_field: None,
                            ..
                        },
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
        callee_identity: None,
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
        callee_identity: None,
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
        callee_identity: None,
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
