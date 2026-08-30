// Trust: EFHT-T (2026-08-29) — the TRANSPORT lane's OWN recognizer entry.
//
// WHY A SECOND RECOGNIZER. `prove::transported_call_return_fully_faithful_via_trustir`
// used to take its shape from `sem_call_return_of_mir`, the recognizer every opaque
// call lane shares (14 call sites). Measured on the 1,027-body transport subset, 28 of
// 28 authored uncovered sole-call callers with a certified callee were refused at that
// FIRST exit, and three of the four measured shapes are refused for reasons the
// transport fence makes irrelevant:
//
//   S2  `_t = Copy((*_p).f); g(copy _t) -> _0`                 a field-read ACTUAL
//   S3  `_t = Copy((*_p).f); g(copy _t) -> _r; _0 = Cmp(k, _r)` call-then-COMPARE
//   S4  `_t = Copy(*_p);     g(copy _t) -> _r; _0 = Not(_r)`    call-then-NOT (Bool)
//
// Widening the shared recognizer would move every opaque lane with it. This module is
// therefore a SEPARATE entry that admits S2/S3/S4 INSIDE the EFHT fence and nowhere
// else; `sem_call_return_of_mir`, `sem_call_arg_operand`, `sem_call_then_pureop_of_mir`
// and every kernel term are BYTE-UNCHANGED (the design constraint; the consumer pins
// the shared recognizer's verdicts on the transport fixtures). The reach cost is the
// spine: this walk admits ONLY `Goto`/`Return`/`Unreachable` around exactly one
// returning `Call` — no `SwitchInt` guard, no divergence sink — because the EFHT
// caller allow-list (`prove::body_is_read_only_except_sole_call`) refuses every
// second `Call` anyway and a second spine walk must stay simpler than the fence it
// serves, never wider.
//
// WHAT IS RECOGNIZED. A [`SemTransportedCall`]: the shared [`SemCallReturn`] (so
// `call_site_requires_established` and `sem_call_arg_to_ir_pinned` take it unchanged),
// the call's block and destination local, one [`ActualBase`] per actual — the CHAIN OF
// CUSTODY read off the MIR definition, never off a MirSem resolution — and a
// [`SemTransportTail`]: the Return block's one `_0` statement over the call result.
//
// THE GATES, in order; every refusal is a named `&'static str` (`decline`):
//   P-SPINE    exactly one returning `Call`; every other terminator `Goto`/`Return`/
//              `Unreachable`; a unique `Return` block; the entry-to-Return walk is a
//              simple chain through the call (cycles, dead ends and joins INTO the
//              chain from an off-path block are refused by name).
//   P-CALLEE   resolves uniquely in the registry, is not the function itself, matches
//              the compiler-extracted signature exactly, and CARRIES A `ret_model` —
//              this lane transports a value, so a callee without one has nothing to
//              transport (registry membership alone is NOT read as purity — CLAUDE.md
//              H1; a `ret_model` is minted only after `body_is_read_only(callee)`).
//   P-DEST     `_0` is the dest (tail `None`, nothing else writes `_0`) OR a scalar
//              non-parameter temp `_r` written ONLY by the call, with `_0` written
//              exactly once, in the Return block, as its LAST statement.
//   P-ACTUAL   per actual, first match: (a) `sem_operand_of_mir` (bare scalar param,
//              direct `*p` read, constant); (b) an unprojected shared-reference ENTRY
//              parameter with no write through it (the opaque-handle arm, re-stated
//              locally); (c) a temp whose UNIQUE definition DOMINATING THE CALL BLOCK
//              is literally `Use(Copy((*_p).f))` with `_p` an entry parameter, resolved
//              by `sem_call_arg_field_read_operand` and REQUIRED to agree with the MIR
//              base and field; (d) a temp whose unique dominating definition is
//              `Use(Copy(*_p))` with `_p: &{Int,Bool}` an entry parameter, resolved by
//              `sem_deref_materialization_temp_operand` and required to agree.
//              Anything else — an `OpaqueConst`, a reborrow temp, a projected place, a
//              cast, an aggregate — is refused.
//   P-TEMP     every (c)/(d) temp has exactly one bare assignment and no other rooted
//              write, alias, call destination or drop (`call_family_local_writes_exact`).
//   P-TAIL     `Use(_r)` -> `None`; `Not(_r)` with `_r: Bool` AND the callee's declared
//              return `Bool` -> `NotBool` (desugared by the consumer to `Cmp(Eq, _r, 0)`
//              on the 0/1 carrier, the SAME reading the chain builder and the pureop
//              lane use); `BinaryOp(cmp, a, b)` with exactly one side the bare `_r` and
//              `cmp` in `sem_cmpop_of_mir` -> `Cmp`. An INTEGER `Not` is refused by name
//              (it denotes the opaque `bnot`), and so is EVERY arithmetic tail
//              (`Add`/`Sub`/`Mul`/…): `IrRvalue::Bin` denotes unbounded `Int.add` where
//              release MIR wraps, and the minted callee models come from a builder whose
//              overflow discipline this lane has not re-derived. First landing: `Cmp`
//              and `NotBool` only.
//   P-TAIL-OTHER  the comparison's other operand is a constant, an unprojected
//              `Int`/`Bool` ENTRY parameter, or a temp whose unique definition is a
//              field read `Use(Copy((*_p).f))` of a handle `_p` that is the base of one
//              of THIS call's actuals (any slot) AND whose definition dominates the call
//              block (a PRE-CALL read). The two refusals are ORDERED: the handle-set
//              check fires first (`tail-reads-a-handle-not-transported`), the pre-call
//              check second (`tail-other-not-pre-call`), so a post-call read of an
//              untransported handle reports the first. Both restrictions are stricter
//              than the fence requires and are pinned so relaxing either is a deliberate,
//              separately-argued change.
//
// WHAT THIS MODULE DOES NOT DECIDE. Types. Arm (c) records `FieldOf(p, f)` for ANY
// entry parameter `_p` — `sem_call_arg_field_read_operand`'s Case 1b admits a
// u64-newtype / transparent-chain field as a deterministic opaque token and its Case 2
// admits an `&mut Closure` upvar. The consumer's G-ACTUAL-VALUE
// (`prove::efht_value_actual_ok`) RE-DERIVES the field type as `Int`/`Bool` off the
// base parameter's `&Adt` type / `datatype_defs`, requires the base slot to read as a
// handle, and applies `ret_model_param_fences_hold(.., Handle)` — the
// interior-mutability refusal the MirSem chase does not perform. Arm (d) likewise
// leaves the literal `&{Int,Bool}` match and the Value fences to the consumer. A
// recognizer result is a SHAPE, never a verdict.
//
// NO-UB PREMISE (inherited from EFHT, stated here because the design text never did):
// the H2 argument — that `idxElem(e(p-1), f)` read before the call is the referent's
// ENTRY value — assumes Rust's shared-reference aliasing guarantee: no foreign writer
// to a live `&S` referent. The fence closes every Trust-VISIBLE write channel in the
// caller and callee; it does not close UB. A hand-built or `unsafe`-derived body that
// violates the aliasing rules is outside the claim.

use super::{
    call_family_local_writes_exact, deref_write_exists, param_reassigned_by_stmt,
    resolve_certified_callee, sem_call_arg_field_read_operand, sem_cmpop_of_mir,
    sem_binop_of_mir, sem_deref_materialization_temp_operand, sem_operand_of_mir,
    unique_local_definition_dominating, CalleeFact, SemCallReturn, SemCmpOp, SemOperand,
};

/// The MIR-read chain of custody for one actual (or the tail's other operand): WHAT the
/// operand was read off, by local, before any MirSem resolution. The consumer keys its
/// type re-derivation and its fences on this, never on the resolved `SemOperand`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ActualBase {
    /// An integer/boolean literal.
    Const,
    /// `Copy`/`Move` of the UNPROJECTED entry parameter local `p`.
    Param(usize),
    /// A temp whose unique dominating definition is `Use(Copy((*_p).f))`, `_p` an entry
    /// parameter local.
    FieldOf(usize, u64),
    /// A read through `*_p` — either the direct operand `Copy(*_p)` or a temp whose
    /// unique dominating definition is `Use(Copy(*_p))` — `_p` an entry parameter local.
    DerefOf(usize),
}

impl ActualBase {
    /// The entry parameter local this base reads, if any.
    pub(crate) fn param(&self) -> Option<usize> {
        match self {
            ActualBase::Const => None,
            ActualBase::Param(p) | ActualBase::FieldOf(p, _) | ActualBase::DerefOf(p) => Some(*p),
        }
    }
}

/// The Return block's one statement over the call result. First landing: `None`,
/// `NotBool`, `Cmp` — no arithmetic tail (see the module doc).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SemTransportTail {
    /// `_0 = g(..)` directly, or `_r = g(..); _0 = Use(_r)`.
    None,
    /// `_r = g(..); _0 = Not(_r)` with `_r: Bool` — logical negation on the 0/1 carrier.
    NotBool,
    /// `_r = g(..); _0 = cmp(_r, other)` (`call_is_lhs`) or `cmp(other, _r)`.
    Cmp { op: SemCmpOp, other: (SemOperand, ActualBase), call_is_lhs: bool },
}

/// The recognized transport shape. Produced ONLY by
/// [`sem_transported_call_of_mir_diag`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemTransportedCall {
    /// The shared call record (resolved callee, stable id, modeled actuals).
    pub call: SemCallReturn,
    /// The block whose terminator is the transported call.
    pub call_block: trust_types::BlockId,
    /// The call's destination local (`0`, or the scalar temp `_r`).
    pub dest: usize,
    /// One base per actual, in `call.args` order.
    pub bases: Vec<ActualBase>,
    /// The Return block's statement over the call result.
    pub tail: SemTransportTail,
}

/// Record the FIRST refusing gate, without changing that it refuses (the idiom of
/// `call_lift::decline`, restated here because that one is private to its module).
#[inline]
fn decline<T>(why: &mut Option<&'static str>, reason: &'static str) -> Option<T> {
    if why.is_none() {
        *why = Some(reason);
    }
    None
}

/// [`sem_transported_call_of_mir_diag`] without the reason. Production consumes the
/// `_diag` twin (the consumer surfaces the reason); the pins use this one.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn sem_transported_call_of_mir(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
) -> Option<SemTransportedCall> {
    sem_transported_call_of_mir_diag(func, callees, &mut None)
}

/// The transport lane's recognizer. See the module doc for the gate list; every
/// refusal names the FIRST gate that fired in `why`.
pub(crate) fn sem_transported_call_of_mir_diag(
    func: &trust_types::VerifiableFunction,
    callees: &std::collections::BTreeMap<String, CalleeFact>,
    why: &mut Option<&'static str>,
) -> Option<SemTransportedCall> {
    use trust_types::{BlockId, Operand, Projection, Rvalue, Statement, Terminator, Ty, UnOp};

    if callees.is_empty() {
        return decline(why, "no-certified-callee-in-registry");
    }
    let body = &func.body;
    let arg_count = body.arg_count;
    let param_index = move |local: usize| -> Option<u64> {
        if (1..=arg_count).contains(&local) { u64::try_from(local - 1).ok() } else { None }
    };
    let is_entry_param = |local: usize| (1..=arg_count).contains(&local);
    let local_ty = |local: usize| body.locals.get(local).map(|l| &l.ty);
    let is_scalar = |local: usize| matches!(local_ty(local), Some(Ty::Int { .. }) | Some(Ty::Bool));

    // ── P-SPINE ─────────────────────────────────────────────────────────────
    if body.blocks.iter().flat_map(|b| &b.stmts).any(|s| matches!(s, Statement::Unsupported { .. }))
    {
        return decline(why, "Unsupported-statement-in-body");
    }
    {
        let mut ids = std::collections::HashSet::new();
        if body.blocks.iter().any(|b| !ids.insert(b.id)) {
            return decline(why, "duplicate-block-ids");
        }
    }
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
                let Some(target) = target else {
                    // Narrower than the shared recognizer ON PURPOSE: the EFHT caller
                    // allow-list refuses every second `Call`, sink or not, so admitting
                    // it here would only move the refusal later.
                    return decline(why, "diverging-sink-call-outside-transport-spine");
                };
                if call.is_some() {
                    return decline(why, "second-returning-call");
                }
                call = Some((block.id, callee, args, dest, *target, atomic, *is_foreign, *is_unsafe_sig));
            }
            Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => {}
            _ => return decline(why, "terminator-outside-transport-spine"),
        }
    }
    let Some((call_block, callee_str, args, dest, call_target, atomic, is_foreign, is_unsafe_sig)) =
        call
    else {
        return decline(why, "no-call-terminator-at-all");
    };
    if is_foreign || atomic.is_some() || is_unsafe_sig {
        return decline(why, "abi-foreign-or-atomic-or-unsafe-sig");
    }
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let Some(ret_block) = rets.next() else {
        return decline(why, "no-Return-block");
    };
    if rets.next().is_some() {
        return decline(why, "not-a-unique-Return-block");
    }
    // The returning path is ONE simple chain entry → … → call → target → … → Return.
    // Every admitted terminator has out-degree ≤ 1, so a two-successor join cannot
    // occur; the join this spine CAN have — an off-path block whose successor lies on
    // the chain — is refused explicitly below, as is a cycle and a dead end.
    let successor = |blk: &trust_types::BasicBlock| -> Option<BlockId> {
        match &blk.terminator {
            Terminator::Goto(t) => Some(*t),
            Terminator::Call { target, .. } => *target,
            _ => None,
        }
    };
    let mut path: Vec<BlockId> = Vec::with_capacity(body.blocks.len());
    let mut cur = BlockId(0);
    let mut through_call = false;
    loop {
        if path.contains(&cur) {
            return decline(why, "cycle-on-the-returning-path");
        }
        path.push(cur);
        let Some(blk) = body.blocks.iter().find(|b| b.id == cur) else {
            return decline(why, "returning-path-names-a-missing-block");
        };
        if cur == call_block {
            through_call = true;
        }
        if cur == ret_block.id {
            break;
        }
        match successor(blk) {
            Some(next) => cur = next,
            None => return decline(why, "returning-path-dead-ends"),
        }
    }
    if !through_call {
        return decline(why, "call-not-on-the-returning-path");
    }
    if body
        .blocks
        .iter()
        .any(|b| !path.contains(&b.id) && successor(b).is_some_and(|s| path.contains(&s)))
    {
        return decline(why, "join-into-the-spine-from-off-path");
    }
    let _ = call_target;

    // ── P-CALLEE ────────────────────────────────────────────────────────────
    let Some((resolved, fact, callee_id)) = resolve_certified_callee(callees, callee_str) else {
        return decline(why, "callee-not-resolvable-in-registry");
    };
    if resolved == func.def_path || *callee_str == func.def_path {
        return decline(why, "self-recursion");
    }
    if !crate::mirsem::callee_signature_matches(func, args, dest, fact) {
        return decline(why, "callee-signature-mismatch");
    }
    if fact.ret_model.is_none() {
        return decline(why, "callee-minted-no-ret_model");
    }
    if args.is_empty() {
        return decline(why, "call-has-no-arguments");
    }

    // ── P-DEST ──────────────────────────────────────────────────────────────
    if !dest.projections.is_empty() {
        return decline(why, "dest-has-projections");
    }
    let r = dest.local;
    // `(index in the Return block, rvalue)` of the one `_0` statement when `_r != _0`.
    let ret_assign: Option<(usize, &Rvalue)>;
    if r == 0 {
        if !call_family_local_writes_exact(body, 0, 0, &[call_block]) {
            return decline(why, "dest-is-_0-but-other-writes-to-_0");
        }
        ret_assign = None;
    } else {
        if is_entry_param(r) {
            return decline(why, "call-overwrites-a-parameter");
        }
        if !is_scalar(r) {
            return decline(why, "temp-dest-not-scalar");
        }
        if !call_family_local_writes_exact(body, r, 0, &[call_block]) {
            return decline(why, "temp-dest-write-profile-mismatch");
        }
        if !call_family_local_writes_exact(body, 0, 1, &[]) {
            return decline(why, "_0-write-profile-mismatch");
        }
        let Some(idx) = ret_block
            .stmts
            .iter()
            .position(|s| crate::assignment_types::assigned_local_rvalue(body, s, 0).is_some())
        else {
            return decline(why, "return-block-never-writes-_0");
        };
        if idx + 1 != ret_block.stmts.len() {
            return decline(why, "_0-assign-not-last-in-return-block");
        }
        let Some(rv) = crate::assignment_types::assigned_local_rvalue(body, &ret_block.stmts[idx], 0)
        else {
            return decline(why, "return-block-never-writes-_0");
        };
        ret_assign = Some((idx, rv));
    }

    // ── P-ACTUAL + P-TEMP ───────────────────────────────────────────────────
    let mut sem_args = Vec::with_capacity(args.len());
    let mut bases = Vec::with_capacity(args.len());
    for a in args {
        // (a) the bare scalar / direct-deref / constant fragment, base read off MIR.
        if let Some(sem) = sem_operand_of_mir(body, a, &param_index) {
            let base = match a {
                Operand::Constant(_) => ActualBase::Const,
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    ActualBase::Param(p.local)
                }
                Operand::Copy(p) | Operand::Move(p)
                    if matches!(p.projections.as_slice(), [Projection::Deref]) =>
                {
                    ActualBase::DerefOf(p.local)
                }
                _ => return decline(why, "argument-base-unreadable-off-mir"),
            };
            sem_args.push(sem);
            bases.push(base);
            continue;
        }
        let (Operand::Copy(p) | Operand::Move(p)) = a else {
            return decline(why, "argument-outside-transport-fragment");
        };
        if !p.projections.is_empty() {
            return decline(why, "argument-outside-transport-fragment");
        }
        let t = p.local;
        // (b) an unprojected shared-reference ENTRY parameter — the opaque handle.
        if is_entry_param(t) {
            if !matches!(local_ty(t), Some(Ty::Ref { mutable: false, .. })) {
                return decline(why, "argument-outside-transport-fragment");
            }
            if param_reassigned_by_stmt(body, t) || deref_write_exists(body, t) {
                return decline(why, "handle-actual-fails-the-entry-fences");
            }
            let Some(idx) = param_index(t) else {
                return decline(why, "argument-outside-transport-fragment");
            };
            let var = SemOperand::Var(idx);
            sem_args.push(if matches!(a, Operand::Move(_)) { SemOperand::Move(Box::new(var)) } else { var });
            bases.push(ActualBase::Param(t));
            continue;
        }
        if t == 0 {
            return decline(why, "argument-outside-transport-fragment");
        }
        // (c)/(d) — a temp whose unique definition DOMINATES THE CALL BLOCK (the use
        // block is the CALL block, never the Return block: a definition that dominates
        // the Return but not the call is not a pre-call read).
        let Some((_, _, def)) = unique_local_definition_dominating(body, t, call_block, None) else {
            return decline(why, "actual-temp-has-no-unique-dominating-definition");
        };
        let Rvalue::Use(Operand::Copy(src)) = def else {
            return decline(why, "argument-outside-transport-fragment");
        };
        match src.projections.as_slice() {
            [Projection::Deref, Projection::Field(f)] => {
                if !is_entry_param(src.local) {
                    return decline(why, "field-actual-base-is-not-an-entry-parameter");
                }
                let Ok(f) = u64::try_from(*f) else {
                    return decline(why, "argument-outside-transport-fragment");
                };
                let Some(sem) =
                    sem_call_arg_field_read_operand(body, a, call_block, None, &param_index)
                else {
                    return decline(why, "field-actual-chase-declined");
                };
                let agrees = matches!(&sem,
                    SemOperand::Field(base, ff)
                        if **base == SemOperand::Var(param_index(src.local).unwrap_or(u64::MAX))
                            && *ff == f);
                if !agrees {
                    return decline(why, "field-actual-chase-disagrees-with-mir");
                }
                if !call_family_local_writes_exact(body, t, 1, &[]) {
                    return decline(why, "actual-temp-write-profile-mismatch");
                }
                sem_args.push(sem);
                bases.push(ActualBase::FieldOf(src.local, f));
            }
            [Projection::Deref] => {
                if !is_entry_param(src.local) {
                    return decline(why, "deref-actual-base-is-not-an-entry-parameter");
                }
                match local_ty(src.local) {
                    Some(Ty::Ref { mutable: false, inner })
                        if matches!(inner.as_ref(), Ty::Int { .. } | Ty::Bool) => {}
                    _ => return decline(why, "deref-actual-base-is-not-a-shared-scalar-reference"),
                }
                let Some(sem) = sem_deref_materialization_temp_operand(
                    body,
                    t,
                    &param_index,
                    Some((call_block, None)),
                ) else {
                    return decline(why, "deref-actual-chase-declined");
                };
                let agrees = matches!(&sem,
                    SemOperand::Var(i) if Some(*i) == param_index(src.local));
                if !agrees {
                    return decline(why, "deref-actual-chase-disagrees-with-mir");
                }
                if !call_family_local_writes_exact(body, t, 1, &[]) {
                    return decline(why, "actual-temp-write-profile-mismatch");
                }
                sem_args.push(sem);
                bases.push(ActualBase::DerefOf(src.local));
            }
            _ => return decline(why, "argument-outside-transport-fragment"),
        }
    }

    // ── P-TAIL + P-TAIL-OTHER ───────────────────────────────────────────────
    let tail = match ret_assign {
        None => SemTransportTail::None,
        Some((ret_stmt_idx, rv)) => {
            let is_r = |o: &Operand| {
                matches!(o, Operand::Copy(p) | Operand::Move(p) if p.local == r && p.projections.is_empty())
            };
            match rv {
                Rvalue::Use(o) if is_r(o) => SemTransportTail::None,
                Rvalue::UnaryOp(UnOp::Not, o) => {
                    if !is_r(o) {
                        return decline(why, "return-block-tail-does-not-consume-the-call-result");
                    }
                    match local_ty(r) {
                        Some(Ty::Bool) => {}
                        Some(Ty::Int { .. }) => return decline(why, "integer-not-is-opaque-bnot"),
                        _ => return decline(why, "return-block-tail-outside-fragment"),
                    }
                    if !matches!(local_ty(0), Some(Ty::Bool)) {
                        return decline(why, "not-tail-on-a-non-bool-return");
                    }
                    if !matches!(fact.return_ty, Ty::Bool) {
                        return decline(why, "not-tail-callee-return-not-bool");
                    }
                    SemTransportTail::NotBool
                }
                Rvalue::BinaryOp(op, a, b) => {
                    let call_is_lhs = match (is_r(a), is_r(b)) {
                        (true, false) => true,
                        (false, true) => false,
                        (true, true) => return decline(why, "tail-both-operands-are-the-call-result"),
                        (false, false) => {
                            return decline(why, "return-block-tail-does-not-consume-the-call-result")
                        }
                    };
                    let Some(cmp) = sem_cmpop_of_mir(op) else {
                        if sem_binop_of_mir(op).is_some() {
                            return decline(why, "bin-tail-not-admitted-in-the-first-landing");
                        }
                        return decline(why, "tail-op-outside-fragment");
                    };
                    if !matches!(local_ty(0), Some(Ty::Bool)) {
                        return decline(why, "cmp-tail-on-a-non-bool-return");
                    }
                    let other_op = if call_is_lhs { b } else { a };
                    let other = match other_op {
                        Operand::Constant(_) => {
                            let Some(sem) = sem_operand_of_mir(body, other_op, &param_index) else {
                                return decline(why, "tail-other-outside-fragment");
                            };
                            (sem, ActualBase::Const)
                        }
                        Operand::Copy(q) | Operand::Move(q) => {
                            if !q.projections.is_empty() {
                                return decline(why, "tail-other-outside-fragment");
                            }
                            let q = q.local;
                            if is_entry_param(q) {
                                if !is_scalar(q) {
                                    return decline(why, "tail-other-outside-fragment");
                                }
                                let Some(sem) = sem_operand_of_mir(body, other_op, &param_index)
                                else {
                                    return decline(why, "tail-other-param-fails-the-entry-fences");
                                };
                                (sem, ActualBase::Param(q))
                            } else if q == 0 || q == r {
                                return decline(why, "tail-other-outside-fragment");
                            } else {
                                // A pre-call FIELD READ of a transported handle. The
                                // definition is located at its OWN use first (so the
                                // handle-set check can read the base), then required to
                                // dominate the CALL block — in that order, pinned.
                                let Some((_, _, def)) = unique_local_definition_dominating(
                                    body,
                                    q,
                                    ret_block.id,
                                    Some(ret_stmt_idx),
                                ) else {
                                    return decline(why, "tail-other-temp-has-no-unique-definition");
                                };
                                let Rvalue::Use(Operand::Copy(src)) = def else {
                                    return decline(why, "tail-other-outside-fragment");
                                };
                                let [Projection::Deref, Projection::Field(f)] = src.projections.as_slice()
                                else {
                                    return decline(why, "tail-other-outside-fragment");
                                };
                                if !is_entry_param(src.local) {
                                    return decline(why, "tail-other-outside-fragment");
                                }
                                let Ok(f) = u64::try_from(*f) else {
                                    return decline(why, "tail-other-outside-fragment");
                                };
                                if !bases.iter().any(|b| b.param() == Some(src.local)) {
                                    return decline(why, "tail-reads-a-handle-not-transported");
                                }
                                if unique_local_definition_dominating(body, q, call_block, None)
                                    .is_none()
                                {
                                    return decline(why, "tail-other-not-pre-call");
                                }
                                let Some(sem) = sem_call_arg_field_read_operand(
                                    body,
                                    other_op,
                                    call_block,
                                    None,
                                    &param_index,
                                ) else {
                                    return decline(why, "tail-other-chase-declined");
                                };
                                let agrees = matches!(&sem,
                                    SemOperand::Field(base, ff)
                                        if **base == SemOperand::Var(param_index(src.local).unwrap_or(u64::MAX))
                                            && *ff == f);
                                if !agrees {
                                    return decline(why, "tail-other-chase-disagrees-with-mir");
                                }
                                if !call_family_local_writes_exact(body, q, 1, &[]) {
                                    return decline(why, "tail-other-temp-write-profile-mismatch");
                                }
                                (sem, ActualBase::FieldOf(src.local, f))
                            }
                        }
                        _ => return decline(why, "tail-other-outside-fragment"),
                    };
                    SemTransportTail::Cmp { op: cmp, other, call_is_lhs }
                }
                _ => return decline(why, "return-block-tail-outside-fragment"),
            }
        }
    };

    Some(SemTransportedCall {
        call: SemCallReturn { callee: resolved.to_string(), callee_id, args: sem_args },
        call_block,
        dest: r,
        bases,
        tail,
    })
}
