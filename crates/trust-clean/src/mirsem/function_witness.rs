// Whole-function witnesses: the aggregate that a function's every modeled
// obligation carries a checked certificate. A function emitting any unmodeled
// safety VC cannot be fully faithful, which is why the unmodeled probe runs
// before the aggregate is minted.

use super::*;

/// THE WHOLE-FUNCTION COMPOSITION HOOK (Goal #4, faithfulness_full tier). For a
/// reflected function, mint a COMPOSED kernel-checked adequacy witness iff EVERY
/// operand (1A), EVERY rvalue (1B), and the return witness (1C) in its reflected
/// contract certifies modulo 3. Fail-closed: any uncertified piece — or a function
/// with no modeled operand/rvalue/return, or a return outside the modeled fragment
/// (loops, calls, non-arithmetic rvalues) — yields `None`, never a false witness.
///
/// The return witness (1C) now covers BOTH modeled return shapes: a closed
/// param/const return AND an SSA-TEMP return that traces the assigned temp `_0`
/// through its `Assign(0, R)` via the env-threading `exec` fold (so `bump(x){x+1}`,
/// whose return reads the assigned temp, now composes — it was previously
/// fail-closed). A return that genuinely cannot be modeled still fail-closes.
///
/// This is the composition of the three lemmas: it does not re-prove a monolithic
/// whole-function theorem over arbitrary control flow (multi-block `exec` over loops
/// is the deferred breadth), but it certifies that every PIECE the reflection grounds
/// — operands, rvalues, and the return (closed or single-block SSA-temp) — is
/// kernel-adequate to MirSem.
#[must_use]
pub fn function_adequacy_witness(
    func: &trust_types::VerifiableFunction,
) -> Option<FunctionAdequacyCertificate> {
    // Trust: call-spine increment — the no-registry entry point. With an EMPTY
    // certified-callee registry the call-return arm can never fire
    // (`sem_call_return_of_mir` returns `None` immediately), so this is
    // byte-identical to the pre-increment behavior.
    function_adequacy_witness_with_callees(func, &std::collections::BTreeMap::new())
}

/// Trust: call-spine increment — [`function_adequacy_witness`] with an
/// ALREADY-CERTIFIED callee registry threaded down (see [`CalleeFact`]). The
/// registry admits ONE additional return shape — the CALL return
/// ([`sem_call_return_of_mir`], adequacy via the kernel-checked per-call
/// `callRefinesContract` instance) — tried only AFTER the straight-line shape
/// declines and BEFORE the guarded-branch shapes. All existing arms are
/// byte-identical; an empty registry reproduces the old function exactly.
#[must_use]
pub fn function_adequacy_witness_with_callees(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<FunctionAdequacyCertificate> {
    trust_vcgen::validate_function(func).ok()?;
    use trust_types::{Operand, Rvalue, Statement};
    let body = &func.body;
    if !crate::assignment_types::all_assignments_match(body) {
        return None;
    }
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };

    // Gather the operands + rvalues the return-extraction path reflects (the same
    // superset `function_faithfulness_certified` collects).
    let mut operands: Vec<&Operand> = Vec::new();
    let mut rvalues: Vec<(&Rvalue, Option<(trust_types::BlockId, Option<usize>)>)> = Vec::new();
    // Trust: field-read leaf — modeled pieces `sem_operand_of_mir`/`sem_rvalue_of_mir`
    // cannot represent directly (a body-aware field-read resolution) get collected
    // here as ALREADY-RESOLVED `SemOperand`s, merged into `op_certs` below.
    let mut extra_sem_operands: Vec<SemOperand> = Vec::new();
    // Trust: M6 rung 6 — ALREADY-RESOLVED `SemRvalue` pieces (the shift-narrowed
    // exact cast's `Bin(Shr, ..)` resolution), merged into `rv_certs` below.
    let mut extra_sem_rvalues: Vec<SemRvalue> = Vec::new();
    for block in &body.blocks {
        for (statement_index, stmt) in block.stmts.iter().enumerate() {
            if matches!(stmt, Statement::Assign { .. }) {
                let (place, rvalue) = crate::assignment_types::assigned_rvalue(body, stmt)?;
                if place.local == 0 && place.projections.is_empty() {
                    let return_use_site = Some((block.id, Some(statement_index)));
                    match rvalue {
                        // `_0 := Use(Move/Copy _t.0)` where `_t := CheckedBinaryOp(op,a,b)`
                        // — the checked-arith RESULT return (`bounded_add`/`checked_sub`/
                        // `inc_gt`). The value field `_t.0` IS the arithmetic `op(a, b)`, so
                        // collect the UNDERLYING `a, b` operands (Lemma 1A) and the checked
                        // rvalue (Lemma 1B) — exactly as the direct `_0 := CheckedBinaryOp`
                        // arm does — so the contract's modeled pieces are captured and the
                        // "at least one modeled piece" gate is satisfied. (`sem_return_of_mir`
                        // models the matching SSA-temp return.)
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                            if matches!(
                                p.projections.as_slice(),
                                [trust_types::Projection::Field(0)]
                            ) =>
                        {
                            if let Some((definition_block, definition_statement, checked)) =
                                local_definition_for_optional_use(body, p.local, return_use_site)
                            {
                                if let Rvalue::CheckedBinaryOp(_, a, b) = checked {
                                    rvalues.push((
                                        checked,
                                        Some((definition_block, Some(definition_statement))),
                                    ));
                                    operands.push(a);
                                    operands.push(b);
                                }
                            }
                        }
                        Rvalue::Use(op) => operands.push(op),
                        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                            rvalues.push((rvalue, return_use_site));
                            operands.push(a);
                            operands.push(b);
                        }
                        // Trust: field-read leaf — `_0 := Cast(op, dest_ty)`, a
                        // verified SOUND WIDENING integer cast (identity on the
                        // unbounded Int carrier). Resolve `op` (INLINING one level
                        // of temp indirection through a struct-FIELD READ, the
                        // SAME discipline as the CheckedBinaryOp-field arm above)
                        // and collect the resolved operand so the composed
                        // certificate's "at least one modeled piece" gate is
                        // satisfied — mirrors `sem_return_of_mir`'s Cast arm.
                        // Trust: M6 rung 6 — the SHIFT-NARROWED EXACT cast
                        // resolves to a COMPUTED rvalue (`Bin(Shr, ..)`, see
                        // `resolve_widening_cast_rvalue`'s width-fact arm), not
                        // a bare operand — collect it as an ALREADY-RESOLVED
                        // Lemma-1B piece instead (minted in the rv_certs loop
                        // below, same fail-closed discipline).
                        // Trust: W-CMP-DISCR — `_0 := Cast(..)` ALSO covers the
                        // `i16`/`i32`/`i64` `signum` chain (widening cast declines,
                        // signum resolves it to the `ArithBin(..)` sign rvalue) —
                        // collected as a Lemma-1B piece exactly like the
                        // shift-narrowed cast.
                        Rvalue::Cast(op, dest_ty) => {
                            match resolve_widening_cast_rvalue(
                                body,
                                op,
                                dest_ty,
                                &param_index,
                                return_use_site,
                            )
                            .or_else(|| {
                                resolve_signum_cast_rvalue(
                                    body,
                                    op,
                                    dest_ty,
                                    &param_index,
                                    return_use_site,
                                )
                            }) {
                                Some(SemRvalue::Use(resolved)) => {
                                    extra_sem_operands.push(resolved);
                                }
                                Some(computed) => extra_sem_rvalues.push(computed),
                                None => {}
                            }
                        }
                        // Trust: DISCRIMINANT-AS-VALUE (M5 slice B) — `_0 :=
                        // Discriminant(place)`. Collect the FULL modeled return
                        // operand (`SemOperand::Discriminant(base)`, not just
                        // `base`) so it gets its own Lemma-1A certificate and sets
                        // the "at least one modeled piece" gate below — mirrors
                        // `sem_return_of_mir`'s matching arm exactly (same
                        // resolver, same fail-closed gates).
                        Rvalue::Discriminant(place) => {
                            // Trust: W-CMP-DISCR — the `i8` `signum` shape `_0 :=
                            // Discriminant(Cmp(self, 0))`: recognize the three-way
                            // sign FIRST (Lemma-1B piece), mirroring
                            // `sem_return_of_mir`'s Discriminant arm.
                            let signum_sign =
                                if let Some(trust_types::Ty::Int { width, signed: true }) =
                                    body.locals.first().map(|l| &l.ty)
                                {
                                    resolve_signum_ordering_sign(
                                        body,
                                        place,
                                        *width,
                                        true,
                                        &param_index,
                                        return_use_site,
                                    )
                                } else {
                                    None
                                };
                            if let Some(sign_rv) = signum_sign {
                                extra_sem_rvalues.push(sign_rv);
                            } else if let Some(base) = sem_discriminant_base_of_mir(
                                body,
                                place,
                                &param_index,
                                return_use_site,
                            ) {
                                extra_sem_operands.push(SemOperand::Discriminant(Box::new(base)));
                            }
                        }
                        // Trust: OPTRES-ACCESSOR NOT-LEAF (2026-07-16) — `_0 :=
                        // UnaryOp(Not, _t)` (the `is_none`/`is_err` return). Collect
                        // the FAITHFUL `Eq`↔`Ne`-flipped tag-compare
                        // (`resolve_not_of_bool_cmp`) as an ALREADY-RESOLVED Lemma-1B
                        // piece — mirrors the `Discriminant` arm's `extra_sem_rvalues`
                        // path — so its adequacy is certified in the `rv_certs` loop
                        // and the "at least one modeled piece" gate is satisfied (the
                        // top-level `_0 := UnaryOp` is not itself a `sem_rvalue_of_mir`
                        // rvalue, so it would otherwise contribute NO modeled piece).
                        // Fail-closed for any operand outside the flat Bool-`Eq`/`Ne`
                        // fragment; `UnaryOp(Neg)` / other unary ops fall through.
                        Rvalue::UnaryOp(trust_types::UnOp::Not, operand) => {
                            if let Some(flipped) = resolve_not_of_bool_cmp(
                                body,
                                operand,
                                &param_index,
                                return_use_site,
                            ) {
                                extra_sem_rvalues.push(flipped);
                            }
                        }
                        // Trust: W-LEN-ISEMPTY (2026-07-17) — `_0 := UnaryOp(PtrMetadata,
                        // op)` / `_0 := Len(place)` (the `slice::len`/`str::len`
                        // straight-line leaf). Collect the FULL modeled return operand
                        // (`SemOperand::Len(Var param)`) so it gets its own Lemma-1A
                        // certificate and sets the "at least one modeled piece" gate below
                        // — mirrors the `Discriminant` arm exactly (same resolver, same
                        // fail-closed gates). The top-level `_0 := UnaryOp/Len` is not
                        // itself a `sem_rvalue_of_mir` rvalue, so it would otherwise
                        // contribute NO modeled piece and the closed Len return would be
                        // spuriously rejected by that gate.
                        Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, operand) => {
                            if let Some(len) = resolve_ptr_metadata_slice_len(
                                body,
                                operand,
                                &param_index,
                                (block.id, Some(statement_index)),
                            ) {
                                extra_sem_operands.push(len);
                            }
                        }
                        Rvalue::Len(place) => {
                            if let Some(len) = slice_len_of_param_place(body, place, &param_index) {
                                extra_sem_operands.push(len);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    // The transparent wrapper contributes only when it is the final reachable
    // `_0` definition on the same validated entry-to-return spine consumed by
    // `sem_return_of_mir`. A global block scan could otherwise count an
    // unreachable or malformed wrapper as modeled evidence.
    if let Some(spine) = straight_line_return_spine(body)
        && let Some(StraightLineReturnDefinition::ContractWrapper { value: op, .. }) =
            straight_line_return_definition(body, &spine)
    {
        operands.push(op);
    }

    // Certify every modeled operand (1A). Fail-closed on any modeled-but-uncertified
    // operand. (The "at least one modeled operand" gate is deferred until AFTER the
    // return witness so a GUARDED join-via-temp body — whose `_0 := Use(_t)` operand is
    // the unmodeled convergence temp, but whose ARM operands ARE modeled — is not
    // spuriously rejected here.)
    let mut op_certs: Vec<AdequacyCertificate> = Vec::new();
    let mut any_operand = false;
    for op in operands {
        if let Some(sem) = sem_operand_of_mir(body, op, &param_index) {
            any_operand = true;
            op_certs.push(operand_adequacy_witness(&sem)?);
        }
    }
    // Trust: field-read leaf — the ALREADY-RESOLVED pieces (e.g. a widening
    // cast's field-read source) collected above.
    for sem in &extra_sem_operands {
        any_operand = true;
        op_certs.push(operand_adequacy_witness(sem)?);
    }

    // Certify every modeled rvalue (1B). Fail-closed on any modeled-but-uncertified rvalue.
    //
    // Trust: GUARDED-LOCAL layer fix — a certified rvalue here IS modeled content in
    // its own right (a kernel-checked Lemma-1B piece), so it must ALSO satisfy the
    // "at least one modeled piece" gate below. Previously only the OPERAND loop above
    // set `any_operand`, which every prior straight-line shape happened to also
    // satisfy (a directly-resolvable immediate operand — e.g. a literal constant —
    // always sat alongside the top rvalue). The `is_ascii_alphanumeric`-class shape
    // breaks that coincidence: `_0 := BitOr(_2, _9)`'s own immediate operands are
    // BOTH non-parameter, non-constant temps (they never resolve via
    // `sem_operand_of_mir`), even though the FULLY INLINED rvalue tree (via
    // `resolve_cmp_side`/`sem_guarded_local_value`) certifies completely. Setting the
    // flag here closes that gap without weakening it: this arm still only fires AFTER
    // `rvalue_adequacy_witness` has ALREADY kernel-proven the piece (the `?` above it
    // fails closed first), so a modeled-but-uncertified rvalue still aborts the whole
    // function exactly as before.
    let mut rv_certs: Vec<RvalueAdequacyCertificate> = Vec::new();
    for (rv, use_site) in rvalues {
        if let Some(sem) = sem_rvalue_of_mir_at_site(body, rv, &param_index, use_site) {
            rv_certs.push(rvalue_adequacy_witness(&sem)?);
            any_operand = true;
        }
    }
    // Trust: M6 rung 6 — the ALREADY-RESOLVED rvalue pieces (shift-narrowed
    // exact cast). Same fail-closed discipline: an uncertified piece aborts.
    for sem in &extra_sem_rvalues {
        rv_certs.push(rvalue_adequacy_witness(sem)?);
        any_operand = true;
    }

    // Certify the return witness (1C). ONLY the STRAIGHT-LINE return (the last
    // `_0 := rvalue` flows to a `Return` block) counts toward whole-function
    // faithfulness — its adequacy is the genuine `ground_int(extract_return_formula) =
    // MirSem.eval` equality (external content).
    //
    // The return witness (1C) — TWO modeled shapes:
    //
    //   * STRAIGHT-LINE (`sem_return_of_mir`): the genuine `ground_int(return) =
    //     MirSem.eval` equality.
    //   * GUARDED single-branch (the `Ite` return) — newly admitted via the BRANCH
    //     REFINEMENT, NOT the definitional cf-return unfolding the FIX-2 honesty note
    //     rejected. `branch_refinement_witness` kernel-proves (modulo 3) that
    //     `denote_substitutedB E c t f` ≡ the LIVE-grounded `Formula::Ite` the grounder
    //     emits for the guarded return — a GENUINE refinement (its statement relates the
    //     reflection's substitution denotation to the operational branch semantics; it is
    //     NOT `eval_ite = eval_ite-def`). So when it proves, the guarded return IS
    //     kernel-adequate to MirSem and we mint a `ControlFlow` return certificate. The
    //     modeled fragment now covers single-branch scalar, conjunctive (`Cond.And`), AND
    //     array-index (`Operand.Index`/`Operand.Len`) guarded returns. A guarded return
    //     whose branch refinement does NOT prove (an arm `SemRvalue` still does not model —
    //     a `Neg` arm `abs`; an index over a non-parameter slice) still DEFERS (fail-closed
    //     `None`), so the FIX-2 honesty for the unmodeled guarded fragment is preserved. We
    //     additionally certify the two arms' operands (1A) so the whole contract's pieces
    //     are captured.
    let ret_cert = if let Some(sem_ret) = sem_return_of_mir(func, &param_index) {
        ReturnCertificate::StraightLine(return_adequacy_witness(&sem_ret)?)
    } else if let Some(call_ret) = sem_call_return_of_mir(func, callees)
        // Trust: PTR-SPINE — a body preceded by a ptr-intrinsic prefix chain
        // (memchr `One::count`'s `as_ptr`/`add` before the certified `count_raw`
        // leaf) tries the single-call recognizer FIRST (byte-identical), falling
        // back to the ptr-spine generalization only when it declines.
        .or_else(|| sem_ptr_spine_call_return_of_mir(func, callees))
        // Trust: W-BITINTRIN — a body-less PURE-TOTAL bit-intrinsic call
        // (`count_ones` = `_0 = ctpop(self); Return`, `trailing_zeros` = cttz)
        // resolves to the SAME opaque `call_result` denotation as a certified
        // callee, WITHOUT the registry (the intrinsic has no MIR body). Tried
        // LAST (byte-identical when it declines) — the certified-callee and
        // ptr-spine paths above are unchanged.
        .or_else(|| sem_intrinsic_call_return_of_mir(func))
    {
        // Trust: call-spine increment — the CALL return (the FOURTH return shape).
        // The straight-line path declined (a Call is a terminator, never a modeled
        // rvalue), and the recognizer admitted the sole-call-to-certified-callee
        // shape (directly, or via the ptr-intrinsic-prefix spine). Certify the
        // call's ACTUAL-ARG operands (Lemma 1A) — they are the contract's modeled
        // pieces, satisfying the "at least one modeled piece" gate — then mint the
        // return certificate from the kernel-checked per-call `callRefinesContract`
        // instance. Fail-closed: an uncertifiable arg or a non-modulo-3 instance ⇒
        // no composed witness.
        for a in &call_ret.args {
            op_certs.push(operand_adequacy_witness(a)?);
            any_operand = true;
        }
        ReturnCertificate::Call(call_return_adequacy_witness(&call_ret)?)
    } else if let Some(call_then_op) = sem_call_then_pureop_of_mir(func, callees) {
        // Trust: CALL-THEN-PUREOP — the FIFTH return shape (closes the "Call-then-
        // Compare" named residue, `fixtures/leaf-call-corpus/PROVENANCE.md`). Both
        // the straight-line AND the direct-call-return paths declined (the call
        // writes a TEMP, not `_0`, and `_0`'s sole write is a pure op consuming that
        // temp — not a bare Use passthrough). Certify the call's actual-arg
        // operands (Lemma 1A) AND the non-call operand (Lemma 1A) — the contract's
        // modeled pieces — then mint the return certificate from the kernel-checked
        // per-call `callThenPureOpInstance`. Fail-closed: an uncertifiable arg/
        // operand or a non-modulo-3 instance (incl. the kernel-side scope gate
        // requiring the non-call operand be a CONSTANT — see
        // `call_then_pureop_instance_verdict`'s doc) ⇒ no composed witness.
        for a in &call_then_op.call.args {
            op_certs.push(operand_adequacy_witness(a)?);
        }
        op_certs.push(operand_adequacy_witness(&call_then_op.other)?);
        any_operand = true;
        ReturnCertificate::CallThenPureOp(call_then_pureop_adequacy_witness(&call_then_op)?)
    } else if let Some(call_op_call) = sem_call_op_call_of_mir(func, callees) {
        // Trust: CALL-OP-CALL — the SIXTH return shape (closes the residue
        // `SemCallThenPureOp`'s own doc names: "BOTH operands being the call
        // result ALSO declines — not this shape", `is_full`/`remaining`/
        // `double_len` in `fixtures/container-corpus`). Both prior call shapes
        // declined (TWO Call terminators, not one). Certify BOTH calls' actual-arg
        // operands (Lemma 1A) — the contract's modeled pieces — then mint the
        // return certificate from the kernel-checked per-call-pair
        // `callOpCallInstance` (two nested transports of the SAME proven
        // `callRefinesContract`). Fail-closed: an uncertifiable arg or a
        // non-modulo-3 instance ⇒ no composed witness.
        for a in call_op_call.call_a.args.iter().chain(call_op_call.call_b.args.iter()) {
            op_certs.push(operand_adequacy_witness(a)?);
        }
        any_operand = true;
        ReturnCertificate::CallOpCall(call_op_call_adequacy_witness(&call_op_call)?)
    } else if let Some(chain) = sem_call_chain_pureop_of_mir(func, callees) {
        // Trust: CALL-RESULT-AWARE COMPOSITION — the SEVENTH return shape
        // (closes the TO_ASCII CHAIN residue, `reports/bit-field-nested-
        // rvalue-to-ascii-chain-2026-07-09.md`: `to_ascii_{lower,upper}case`'s
        // call/cast/checked-mul/tuple-projection/BitOr 4-hop chain). Every
        // prior call shape declined (the call's result flows through a Cast
        // and a checked-arith tuple projection before being consumed — none
        // of `Call`/`CallThenPureOp`/`CallOpCall` admit that). Certify the
        // call's actual-arg operands (Lemma 1A) AND the non-call "other"
        // operand (Lemma 1A) — the contract's modeled pieces — then mint the
        // return certificate from the kernel-checked per-call
        // `callChainPureOpInstance`. Fail-closed: an uncertifiable arg/
        // operand or a non-modulo-3 instance (incl. the kernel-side scope
        // gate requiring the non-call operand be a CONSTANT or PARAMETER —
        // see `call_chain_pureop_instance_verdict`'s doc) ⇒ no composed
        // witness.
        for a in &chain.call.args {
            op_certs.push(operand_adequacy_witness(a)?);
        }
        op_certs.push(operand_adequacy_witness(&chain.other)?);
        any_operand = true;
        ReturnCertificate::CallChainPureOp(call_chain_pureop_adequacy_witness(&chain)?)
    } else if let Some(chain) = sem_two_call_chain_of_mir(func, callees) {
        // Trust: TWO-CALL CHAIN — the EIGHTH return shape (`min_max`'s
        // `a.min(b).max(c)`). Every prior call shape declined (TWO Call
        // terminators, and the outer call writes `_0` DIRECTLY — so
        // `CallOpCall`, which needs a pure op over both results, declines; and
        // the single-call recognizers reject the second call). Certify the
        // INNER call's actual-arg operands AND the OUTER call's modeled
        // (non-intermediate) actual-arg operands (Lemma 1A) — the contract's
        // modeled pieces — then mint the certificate from TWO kernel-checked
        // per-call `callReturnInstance` transports. Fail-closed: an
        // uncertifiable arg or a non-modulo-3 instance ⇒ no composed witness.
        for a in &chain.inner.args {
            op_certs.push(operand_adequacy_witness(a)?);
        }
        for arg in &chain.outer_args {
            if let ChainArg::Modeled(op) = arg {
                op_certs.push(operand_adequacy_witness(op)?);
            }
        }
        any_operand = true;
        ReturnCertificate::TwoCallChain(two_call_chain_adequacy_witness(&chain)?)
    } else if let Some(proj) = sem_call_then_project_of_mir(func, callees) {
        // Trust: CALL-THEN-PROJECT — the NINTH return shape
        // (`overflowing_add(a,b).0`). Every prior call shape declined (the
        // call's dest is a TUPLE temp, not an Int/Bool one, and `_0`'s sole
        // write is a `Field(i)` projection of that temp, not a bare passthrough
        // or pure op). Certify the call's actual-arg operands (Lemma 1A) — the
        // contract's modeled pieces — then mint the certificate from the
        // kernel-checked per-call `callThenProjectInstance` (the SAME transport
        // wrapped by the `idx_elem` field selector). Fail-closed: an
        // uncertifiable arg or a non-modulo-3 instance ⇒ no composed witness.
        for a in &proj.call.args {
            op_certs.push(operand_adequacy_witness(a)?);
        }
        any_operand = true;
        ReturnCertificate::CallThenProject(call_then_project_adequacy_witness(&proj)?)
    } else if let Some(br) = branch_refinement_witness(func) {
        // SINGLE-BRANCH guarded return (one `SwitchInt` / conjunctive chain → `Ite`).
        if !br.is_modulo_3() {
            return None;
        }
        // Certify each arm's rvalue (1A/1B) so the contract's pieces are complete; the
        // branch refinement already kernel-proves the whole guarded return adequate, so
        // this is a defensive completeness check (fail-closed on an uncertified arm).
        // The arm rvalues are the body's modeled content, so they satisfy the
        // "at-least-one-modeled-piece" gate below.
        for arm_rv in [&br.ret.then_rv, &br.ret.else_rv] {
            rv_certs.push(rvalue_adequacy_witness(arm_rv)?);
            any_operand = true;
        }
        ReturnCertificate::ControlFlow(cf_return_adequacy_witness(&br.ret)?)
    } else {
        // NESTED / multi-way guarded return (`if c1 {…} else if c2 {…} else {…}` —
        // `sign`, a 3-arm clamp). The single-branch path declined (≥ 3 arms / nested
        // `Ite`). Its `refinementBNested` kernel-proves (modulo 3) that the nested
        // `iteI`-tree denotation ≡ the LIVE-grounded NESTED `Ite`, so the multi-way
        // return is genuinely kernel-adequate to MirSem. Fail-closed (`None`) for any
        // arm/guard outside the modeled fragment.
        let nb = nested_branch_refinement_witness(func)?;
        if !nb.is_modulo_3() {
            return None;
        }
        // Certify EVERY leaf arm's rvalue (1A/1B) — the contract's modeled pieces.
        for arm_rv in nb.tree.leaf_rvalues() {
            rv_certs.push(rvalue_adequacy_witness(arm_rv)?);
            any_operand = true;
        }
        ReturnCertificate::NestedControlFlow(nb)
    };

    // The "at least one modeled piece" gate (an unmodeled body is not certified): a
    // straight-line operand (1A) above, or a guarded arm rvalue (just set).
    if !any_operand {
        return None;
    }

    Some(FunctionAdequacyCertificate { operands: op_certs, rvalues: rv_certs, ret: ret_cert })
}

/// Whether the function emits AT LEAST ONE safety VC that is NOT in the modeled set
/// (`safety_vc_kind_is_modeled`). Drives the fail-closed gate: even one unmodeled
/// safety VC means the function's reflection is not end-to-end kernel-proven, so it
/// must NOT be counted fully faithful. (`function_safety_vcs_faithful` already
/// fail-closes on an unmodeled VC, but it ALSO returns `None` for the vacuously-safe
/// case; this helper lets the composer distinguish "has an unmodeled VC" from "has
/// no safety VC at all".)
pub(super) fn function_emits_unmodeled_safety_vc(func: &trust_types::VerifiableFunction) -> bool {
    trust_vcgen::generate_vcs(func)
        .iter()
        .any(|vc| is_safety_vc_kind(&vc.kind) && !safety_vc_kind_is_modeled(&vc.kind))
}

/// Public accessor for [`function_emits_unmodeled_safety_vc`] — the synthesized-loop
/// fully-faithful path (`prove::synth_loop_function_fully_faithful`) uses it to enforce
/// that a loop function emits NO unmodeled safety VC before claiming full faithfulness.
#[must_use]
pub fn function_emits_unmodeled_safety_vc_pub(func: &trust_types::VerifiableFunction) -> bool {
    function_emits_unmodeled_safety_vc(func)
}

/// Whether the function emits AT LEAST ONE safety VC (of any kind).
pub(super) fn function_emits_any_safety_vc(func: &trust_types::VerifiableFunction) -> bool {
    trust_vcgen::generate_vcs(func).iter().any(|vc| is_safety_vc_kind(&vc.kind))
}

/// THE COMPLETE PER-FUNCTION VERDICT (Goal #4 culmination). Mint a
/// [`FullFaithfulnessCertificate`] iff this function's ENTIRE reflection is
/// kernel-proven adequate to the MIR operational semantics, modulo exactly the 3
/// foundational axioms. Both axes must close:
///
///   (a) the WHOLE-FUNCTION CONTRACT certifies — [`function_adequacy_witness`] is
///       `Some` and modulo 3 (every operand 1A, rvalue 1B, return 1C); AND
///   (b) EVERY safety VC the emitter raises is a MODELED kind whose adequacy
///       certifies modulo 3 — i.e. NO unmodeled safety VC, and (when modeled safety
///       VCs exist) [`function_safety_vcs_faithful`] is `Some` and modulo 3.
///
/// FAIL-CLOSED (`None`), never a false verdict:
///   * the contract is uncertified, OR
///   * the function emits ANY unmodeled safety VC (signed overflow, float div,
///     shift/cast/negation, loop, call, …), OR
///   * a modeled safety VC's adequacy does not kernel-check modulo 3.
///
/// The VACUOUSLY-SAFE case is fully faithful: a function that raises NO safety VC and
/// whose contract certifies has nothing unsafe to capture, so its reflection is
/// end-to-end adequate (`safety = None`). A function WITH modeled-and-certified
/// safety VCs carries `safety = Some(certs)`.
#[must_use]
pub fn function_fully_faithful_witness(
    func: &trust_types::VerifiableFunction,
) -> Option<FullFaithfulnessCertificate> {
    // Trust: call-spine increment — the no-registry entry point (empty registry ⇒
    // the call-return arm never fires ⇒ byte-identical pre-increment behavior).
    function_fully_faithful_witness_with_callees(func, &std::collections::BTreeMap::new())
}

/// Trust: call-spine increment — [`function_fully_faithful_witness`] with an
/// ALREADY-CERTIFIED callee registry threaded down (see [`CalleeFact`]): the
/// contract axis runs [`function_adequacy_witness_with_callees`], which admits
/// the CALL return shape for a sole call to a registry-certified callee. The
/// safety axis (b) is UNCHANGED — every emitted safety VC must still be a
/// modeled kind that certifies modulo 3 (a safe same-crate call emits no safety
/// VC; an `unsafe` callee raises an unmodeled VC and fails closed here).
///
/// HONEST SCOPE (Trust: call-requires establishment): this witness is the
/// ADEQUACY certificate — the reflection (incl. the call's `call_result`
/// denotation) is kernel-faithful to MIR semantics. It does NOT by itself
/// assert that the callee's `#[requires]` HOLDS at the call site, nor that the
/// caller's safety VCs are DISCHARGED — both are SEPARATE clauses of the
/// COUNTED fully-faithful bar in `prove.rs`
/// (`function_safety_vcs_all_discharged` ∧
/// `function_call_requires_established`), exactly as `unsafe_add`'s adequacy
/// witness mints while its discharge gate fails. A consumer combining this
/// witness into a "fully faithful" claim MUST conjoin both gates.
#[must_use]
pub fn function_fully_faithful_witness_with_callees(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<FullFaithfulnessCertificate> {
    // (a) The WHOLE-FUNCTION CONTRACT must certify modulo 3 (Lemmas 1A+1B+1C).
    //     Fail-closed on any uncertified contract piece or an unmodeled return.
    let contract = function_adequacy_witness_with_callees(func, callees)?;
    if !contract.is_modulo_3() {
        return None; // defensive: a certificate that exists is modulo 3 by construction
    }

    // (b) EVERY safety VC must be modeled. Fail-closed on ANY unmodeled safety VC —
    //     even one means the reflection is not end-to-end kernel-proven.
    if function_emits_unmodeled_safety_vc(func) {
        return None;
    }

    // Now: either the function emits modeled safety VCs (which must ALL certify), or
    // it emits NONE (the vacuously-safe case).
    let safety = if function_emits_any_safety_vc(func) {
        // All emitted safety VCs are modeled (we returned above otherwise), so the
        // safety-VC faithfulness builder must certify them all modulo 3. Fail-closed
        // if it does not (an uncertified modeled adequacy).
        let certs = function_safety_vcs_faithful(func)?;
        if !certs.all_modulo_3() {
            return None;
        }
        Some(certs)
    } else {
        None // VACUOUSLY safe: no safety VC to capture; the contract suffices.
    };

    Some(FullFaithfulnessCertificate { contract, safety })
}
