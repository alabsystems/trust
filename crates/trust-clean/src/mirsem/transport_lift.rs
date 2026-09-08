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
//              `sem_deref_materialization_temp_operand` and required to agree;
//              (e) Trust: EFHT-D (2026-08-30) — a temp whose unique dominating
//              definition is `Use(Copy(*_q))` with `_q: &&_` an entry parameter (a
//              deref-HANDLE actual): `_q` entry-frozen (not reassigned, no deref
//              write), the temp's declared type literally `_q`'s referent type [R2],
//              recorded as `ActualBase::DerefOf(q)` — the CONSUMER decides the slot's
//              reading and applies the Handle fences.
//              (f) `*p` with `p: &Adt` BY VALUE, `& &mut T`, `& *const T`, `&(A, B)`,
//              `&[T; N]` — `deref-actual-base-is-not-a-shared-scalar-reference` (nor a
//              shared reference to a shared reference). Anything else — an
//              `OpaqueConst`, a reborrow temp, a projected place, a cast, an
//              aggregate — is refused.
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// Trust: EFHT-D (2026-08-30) — also `Use(Copy(*_p))` with `_p: &&_` (a deref-HANDLE
    /// actual, P-ACTUAL (e)): the base is the OUTER entry parameter; the consumer decides
    /// the reading of its slot (`prove::caller_transport_slot`). The temp is then a
    /// SECOND handle to the same referent that `deref_write_exists(_p)`'s alias closure
    /// does NOT follow (`&&T != &T` fails `shared_ref_types_match`, lift_mir.rs); the
    /// two-sided read-only ALLOW-LIST carries the temp's write-freedom, and the
    /// consumer's deny-list fence on the temp is belt-and-braces.
    DerefOf(usize),
    /// Trust: EFHT-P (2026-08-30) — `&(_p.f)`: a shared reborrow of field `f` of the
    /// BY-VALUE struct entry parameter `_p` (P-ACTUAL (iii)), or `Copy((*_p).f)` of the
    /// `&Adt` upvar `f` of the shared `&Closure` env `_p` (P-ACTUAL (iv)). The consumer
    /// re-derives the whole custody (`transport_path_handle`) and reads the base's slot
    /// as `PathBase` (`prove::transport_caller_slot`, consumer-only).
    FieldHandle { base: usize, f: u64 },
    /// Trust: EFHT-P (2026-08-30) — a promoted reference constant with a RECOVERED
    /// referent (P-ACTUAL (i)/(ii)): struct scalar fields in declaration order (as
    /// i128), or a fieldless enum variant carrying its DECODED DISCRIMINANT VALUE from
    /// the caller's own `Ty::Adt.variants[variant].discriminant` — NEVER the variant
    /// index (`regex_syntax::hir::Look::Start` is index 0, value 1; `Ordering::Less` is
    /// index 0, value -1 — the refuter-proven false verify this rule exists to stop).
    ConstReferent { fields: Vec<i128>, discr: Option<i128> },
}

impl ActualBase {
    /// The entry parameter local this base reads, if any.
    pub(crate) fn param(&self) -> Option<usize> {
        match self {
            ActualBase::Const | ActualBase::ConstReferent { .. } => None,
            ActualBase::Param(p)
            | ActualBase::FieldOf(p, _)
            | ActualBase::DerefOf(p)
            | ActualBase::FieldHandle { base: p, .. } => Some(*p),
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

/// Trust: EFHT-P (2026-08-30) — one recognized ACTUAL, in terminator order. A
/// `Path`/`Const` actual has NO `SemOperand` at all (the earlier design's
/// `SemOperand::Var(u64::MAX)` sentinel is deliberately absent — the consumer's
/// `sem_call_arg_to_ir_pinned` lowering runs before any base match, so a sentinel
/// would refuse its own actuals), so `sem_call_arg_to_ir_pinned`,
/// `sem_actual_to_formula` and `call_site_requires_established` can never observe one:
/// no `SemOperand` exists for it, and the shared `call.args` record is left EMPTY the
/// moment any `Path`/`Const` actual appears (`transport_only_actuals`, pinned).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TransportActual {
    /// An actual with an ordinary MirSem reading — today's fragment, unchanged.
    Sem(SemOperand),
    /// A depth-2 path handle: field `f` of entry parameter `base` (by-value struct
    /// field reborrow, or shared-`&Closure` upvar). 1-BASED base local; the consumer
    /// applies the 0-based shift when it mints `HandleActual::Path` (pinned).
    Path { base: usize, f: u64 },
    /// A promoted referent constant (struct scalar fields / decoded enum discriminant).
    Const { fields: Vec<i128>, discr: Option<i128> },
}

/// The recognized transport shape. Produced ONLY by
/// [`sem_transported_call_of_mir_diag`] (fail-closed).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SemTransportedCall {
    /// The shared call record (resolved callee, stable id, modeled actuals). Trust:
    /// EFHT-P — `args` is populated ONLY when EVERY actual is [`TransportActual::Sem`];
    /// with any `Path`/`Const` actual it is left EMPTY (`transport_only_actuals`), and
    /// the consumer iterates `actuals` instead.
    pub call: SemCallReturn,
    /// The block whose terminator is the transported call.
    pub call_block: trust_types::BlockId,
    /// The call's destination local (`0`, or the scalar temp `_r`).
    pub dest: usize,
    /// One base per actual, in terminator order (parallel to `actuals`).
    pub bases: Vec<ActualBase>,
    /// Trust: EFHT-P — one [`TransportActual`] per MIR actual, in terminator order.
    pub actuals: Vec<TransportActual>,
    /// Trust: EFHT-P — `true` IFF any actual is `Path`/`Const`; equals
    /// `call.args.is_empty()` by construction (the consumer asserts it).
    pub transport_only_actuals: bool,
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
    // Trust: EFHT-P — one TransportActual per MIR actual; a `Path`/`Const` actual has
    // NO SemOperand at all (no sentinel — see the enum's doc).
    let mut actuals: Vec<TransportActual> = Vec::with_capacity(args.len());
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
            actuals.push(TransportActual::Sem(sem.clone()));
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
            let sem = if matches!(a, Operand::Move(_)) { SemOperand::Move(Box::new(var)) } else { var };
            actuals.push(TransportActual::Sem(sem.clone()));
            sem_args.push(sem);
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
        // ── Trust: EFHT-P (2026-08-30) — P-ACTUAL arms (i)/(ii): a REFERENT CONSTANT
        // actual (`_t = const &Enum::Unit` / `const &Struct(k…)`). The recovery runs
        // through `transport_const_referent` — the SAME derivation the consumer
        // re-runs, so the two cannot drift — and every refusal is a named reason with
        // its fix text on that function's doc. An `OpaqueConst`/scalar constant temp
        // keeps the pre-EFHT-P reason byte-identically (the `Copy` fall-through).
        if matches!(
            def,
            Rvalue::Use(Operand::Constant(
                trust_types::ConstValue::UnitVariantRef { .. }
                    | trust_types::ConstValue::StructScalarFieldsRef { .. }
            ))
        ) {
            match transport_const_referent(body, t, call_block) {
                Ok((fields, discr)) => {
                    if !call_family_local_writes_exact(body, t, 1, &[]) {
                        return decline(why, "actual-temp-write-profile-mismatch");
                    }
                    p_trace(func, "ARM", if discr.is_some() { "i-enum-referent-const" } else { "ii-struct-referent-const" });
                    actuals.push(TransportActual::Const { fields: fields.clone(), discr });
                    bases.push(ActualBase::ConstReferent { fields, discr });
                    continue;
                }
                Err(r) => {
                    p_trace(func, "GATE", r);
                    return decline(why, r);
                }
            }
        }
        // ── Trust: EFHT-P — P-ACTUAL arm (iii): `&(_p.f)`, a shared reborrow of a
        // field of the BY-VALUE STRUCT entry parameter `_p`. `transport_path_handle`
        // carries the whole custody + type derivation (shared with the consumer);
        // an empty or deeper reborrow keeps its pre-EFHT-P reason byte-identically.
        if matches!(def, Rvalue::Ref { mutable: false, .. }) {
            match transport_path_handle(body, t, call_block) {
                Ok((p, f, _handle_ty)) => {
                    if !call_family_local_writes_exact(body, t, 1, &[]) {
                        return decline(why, "actual-temp-write-profile-mismatch");
                    }
                    p_trace(func, "ARM", "iii-by-value-field-reborrow");
                    actuals.push(TransportActual::Path { base: p, f });
                    bases.push(ActualBase::FieldHandle { base: p, f });
                    continue;
                }
                Err(r) => {
                    p_trace(func, "GATE", r);
                    return decline(why, r);
                }
            }
        }
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
                // ── Trust: EFHT-P — P-ACTUAL arm (iv): the shared-`&Closure` upvar
                // HANDLE (`_t = Copy((*_env).f)` with `_env: &Closure` and upvar `f`
                // an `&Adt`). The existing chase declines EVERY shared-`&Closure` base
                // (its Case 2 is `&mut Closure` only), so this arm hijacks nothing the
                // chase admits; a `&mut Closure` env has `mutable: true` and falls
                // through to the chase (residue item 5, unchanged).
                if matches!(local_ty(src.local),
                    Some(Ty::Ref { mutable: false, inner }) if matches!(inner.as_ref(), Ty::Closure { .. }))
                {
                    match transport_path_handle(body, t, call_block) {
                        Ok((p, fu, _handle_ty)) if p == src.local && fu == f => {
                            if !call_family_local_writes_exact(body, t, 1, &[]) {
                                return decline(why, "actual-temp-write-profile-mismatch");
                            }
                            p_trace(func, "ARM", "iv-closure-upvar-handle");
                            actuals.push(TransportActual::Path { base: p, f: fu });
                            bases.push(ActualBase::FieldHandle { base: p, f: fu });
                            continue;
                        }
                        Ok(_) => return decline(why, "field-actual-chase-disagrees-with-mir"),
                        Err(r) => {
                            p_trace(func, "GATE", r);
                            return decline(why, r);
                        }
                    }
                }
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
                actuals.push(TransportActual::Sem(sem.clone()));
                sem_args.push(sem);
                bases.push(ActualBase::FieldOf(src.local, f));
            }
            [Projection::Deref] => {
                if !is_entry_param(src.local) {
                    return decline(why, "deref-actual-base-is-not-an-entry-parameter");
                }
                let q = src.local;
                match local_ty(q) {
                    // (d) — the S4 SCALAR deref temp; this path is byte-unchanged from
                    // EFHT-T's first landing.
                    Some(Ty::Ref { mutable: false, inner })
                        if matches!(inner.as_ref(), Ty::Int { .. } | Ty::Bool) =>
                    {
                        let Some(sem) = sem_deref_materialization_temp_operand(
                            body,
                            t,
                            &param_index,
                            Some((call_block, None)),
                        ) else {
                            return decline(why, "deref-actual-chase-declined");
                        };
                        let agrees = matches!(&sem,
                            SemOperand::Var(i) if Some(*i) == param_index(q));
                        if !agrees {
                            return decline(why, "deref-actual-chase-disagrees-with-mir");
                        }
                        if !call_family_local_writes_exact(body, t, 1, &[]) {
                            return decline(why, "actual-temp-write-profile-mismatch");
                        }
                        actuals.push(TransportActual::Sem(sem.clone()));
                        sem_args.push(sem);
                        bases.push(ActualBase::DerefOf(q));
                    }
                    // (e) — Trust: EFHT-D (2026-08-30) — the deref-HANDLE actual: a temp
                    // `t = Copy(*q)` with `q: &&_` (a shared reference to a shared
                    // reference). This arm decides NOTHING about the inner type beyond
                    // that shape — the consumer reads the slot (`prove::
                    // caller_transport_slot`) and applies the Handle fences, interior
                    // mutability included. It must NOT call
                    // `sem_deref_materialization_temp_operand`, which is Int-only by
                    // design (lift_mir.rs). Fix text (v7/D3) for the two new refusals:
                    // "deref-handle-actual-fails-the-entry-fences" — the outer handle
                    // `q` must be entry-frozen: (a) remove the reassignment of `q`
                    // (bind a fresh local instead); (b) move the write out of this
                    // function; (c) if the write is intended, this call cannot
                    // transport its model — it stays on the opaque-call lane.
                    // "deref-handle-temp-type-disagrees-with-the-referent" — the temp
                    // holding `*q` must have exactly the referent type: (a) let the
                    // compiler type it (drop the cast/annotation); (b) if the type
                    // lowered as `Unsupported`, raise the type-lowering budget.
                    Some(Ty::Ref { mutable: false, inner })
                        if matches!(inner.as_ref(), Ty::Ref { mutable: false, .. }) =>
                    {
                        if param_reassigned_by_stmt(body, q) || deref_write_exists(body, q) {
                            return decline(why, "deref-handle-actual-fails-the-entry-fences");
                        }
                        // [R2] — the temp's DECLARED type must be `q`'s inner type,
                        // literally: a hand-built or budget-degraded dump cannot smuggle
                        // a differently-typed referent under the same handle.
                        if !local_ty(t).is_some_and(|tt| tt.eq_ignoring_disc_index_safe(inner.as_ref())) {
                            return decline(why, "deref-handle-temp-type-disagrees-with-the-referent");
                        }
                        if !call_family_local_writes_exact(body, t, 1, &[]) {
                            return decline(why, "actual-temp-write-profile-mismatch");
                        }
                        let Some(idx) = param_index(q) else {
                            return decline(why, "argument-outside-transport-fragment");
                        };
                        let var = SemOperand::Var(idx);
                        let sem = if matches!(a, Operand::Move(_)) { SemOperand::Move(Box::new(var)) } else { var };
                        actuals.push(TransportActual::Sem(sem.clone()));
                        sem_args.push(sem);
                        bases.push(ActualBase::DerefOf(q));
                    }
                    // (f) — everything else (`*p` with `p: &Adt` BY VALUE, `& &mut T`,
                    // `& *const T`, `&(A, B)`, `&[T; N]`): string byte-identical to the
                    // pre-EFHT-D refusal. Fix (v7/D3): the deref actual's base must be
                    // `&{int,bool}` (value) or `&&{[T],str,Adt}` (handle) — (a) pass a
                    // reference to the value instead of the value (`f(p)`, not `f(*p)`);
                    // (b) for `& &mut T` / `& *const T`, take a shared reference two
                    // levels (`&&T`); (c) an ADT VALUE model is residue item 2/(2b),
                    // not this lane.
                    _ => return decline(why, "deref-actual-base-is-not-a-shared-scalar-reference"),
                }
            }
            _ => return decline(why, "argument-outside-transport-fragment"),
        }
    }

    // ── Trust: EFHT-P — the transport-only actual gates ─────────────────────
    // A `Path`/`Const` actual rides OUTSIDE the SemOperand fragment: the callee's
    // `requires` vocabulary has no term for a field path or a constant referent, so a
    // non-empty (or unknown) precondition refuses by name; and a call whose EVERY
    // actual is a constant referent would substitute to a fully grounder-connected
    // term and be re-checked at a tier the callee never earned — refused (the leaf
    // lane's shape, not a transport).
    let transport_only_actuals = actuals.iter().any(|a| !matches!(a, TransportActual::Sem(_)));
    if transport_only_actuals {
        if !matches!(fact.requires.as_deref(), Some([])) {
            return decline(why, "path-or-const-handle-actual-needs-an-empty-callee-requires");
        }
        // Trust: SOUNDNESS (2026-08-31) — quantify over the HANDLE-SLOT actuals, which
        // is what the spec says ("if every Handle-slot actual is `Const` … refuse") and
        // what the purpose requires. Quantifying over ALL actuals let ONE scalar rider
        // the callee's model need not even read defeat the gate: measured (adversary 2),
        // `eq3(a: &E, b: &E, _k: u8)` with two promoted constants plus a scalar param
        // substituted to a fully ground `Cmp(Eq, Const(0), Const(3))`, became
        // grounder-connected, and was re-checked at the GROUNDED tier (`ProvenModulo3`)
        // for a model minted at the opaque tier — the amplifier for the lossy-constant
        // false verify above.
        //
        // A handle slot is decided by the CALLEE FORMAL, never by the actual's reading.
        // The first spelling of this fix filtered on `!matches!(a, TransportActual::Sem(_))`
        // and was WRONG: arm (b) (an unprojected shared-reference entry parameter — the
        // opaque handle) and arm (e) (the `&&T` deref-handle) both push `Sem(Var(..))`
        // for a genuine handle actual, so the filter deleted real handles, `all()` went
        // vacuously true, and the gate refused `is_record` — the very csv S1 shape this
        // increment was built for (measured: 5 pins red, including the non-negotiable
        // decoded-discriminant pin). `fact.param_tys` is index-parallel to `actuals`
        // with arity already checked, so the formal type is the reliable key; the
        // leading `any` keeps a call with NO handle slot from refusing vacuously.
        let handle_slot = |i: usize| matches!(fact.param_tys.get(i), Some(Ty::Ref { .. }));
        if actuals.iter().enumerate().any(|(i, _)| handle_slot(i))
            && actuals
                .iter()
                .enumerate()
                .filter(|(i, _)| handle_slot(*i))
                .all(|(_, a)| matches!(a, TransportActual::Const { .. }))
        {
            return decline(why, "all-handle-actuals-are-constant-referents");
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
        call: SemCallReturn {
            callee: resolved.to_string(),
            callee_id,
            // Trust: EFHT-P — the shared record carries args ONLY when every actual is
            // `Sem`; with any `Path`/`Const` actual it is EMPTY, so no shared-path
            // consumer (`sem_call_arg_to_ir_pinned`, `sem_actual_to_formula`,
            // `call_site_requires_established`) can ever observe a transport-only
            // actual — pinned (F-S1/F-S2).
            args: if transport_only_actuals { Vec::new() } else { sem_args },
        },
        call_block,
        dest: r,
        bases,
        actuals,
        transport_only_actuals,
        tail,
    })
}

/// Trust: EFHT-P (2026-08-30) — the ONE fence EFHT never needed, because a `&T`
/// handle's referent is never a rooted place but a BY-VALUE aggregate is: the caller
/// read-only allow-list permits a NON-Deref write `_p.f = ..` / `SetDiscriminant(_p)`
/// on an owned local, so a by-value path BASE must additionally show the complete
/// call-family write profile EMPTY — zero bare or projected assignments, no
/// `&mut`/`AddressOf(true)` alias, no `SetDiscriminant`/`Deinit`/`Retag`, no `Drop`,
/// no call destination (`call_family_local_writes` fails closed on each). A
/// `pub(crate)` wrapper so `call_lift.rs` stays byte-unchanged.
pub(crate) fn base_local_is_unwritten(body: &trust_types::VerifiableBody, local: usize) -> bool {
    call_family_local_writes_exact(body, local, 0, &[])
}

/// Trust: EFHT-P — `TRUST_LANE_TRACE=1` prints one `EFHT-P-ARM <arm> <def_path>` per
/// admitting arm and one `EFHT-P-GATE <reason> <def_path>` per NEW gate that fires. A
/// TRACE, never a verdict switch: no env var in this binary changes any verdict.
fn p_trace(func: &trust_types::VerifiableFunction, kind: &str, what: &str) {
    if std::env::var_os("TRUST_LANE_TRACE").is_some() {
        eprintln!("EFHT-P-{kind}\t{what}\t{}", func.def_path);
    }
}

/// Trust: EFHT-P (2026-08-30) — derive the RECOVERED REFERENT of a constant-defined
/// temp `t` from the CALLER'S OWN body: the unique dominating definition must be a
/// `UnitVariantRef`/`StructScalarFieldsRef` constant, the temp's declared `&Adt` type
/// (inline or via `datatype_defs`) must agree with the constant's name and shape, and
/// — the refuter-proven hard rule — an ENUM referent carries the DECODED DISCRIMINANT
/// VALUE `Ty::Adt.variants[variant].discriminant` (decoded once at extraction by
/// `decode_discr_tag`, the same authority `Rvalue::Discriminant` and
/// `decode_switch_label` agree on), NEVER the variant index, and `disc_index_safe` is
/// only the Direct-tag PRECONDITION (it does NOT say tag == index: `Look::Start` is
/// index 0, value 1). Called by the recognizer arm AND re-run verbatim by the consumer,
/// so the two cannot drift. Refusal reasons, each with its fix (v7/D3):
/// * `const-referent-shape-mismatch` — name/kind/variant/field-count disagree with the
///   temp's `&Adt` type. Fix: (a) re-extract the dump with the current extractor;
///   (b) a payload-carrying enum or non-scalar struct constant: compare fields
///   explicitly (`self.0 == K`) so the leaf lane applies.
/// * `const-discr-enum-not-direct-tag` — niche-encoded or unclassified
///   (`disc_index_safe` false; a pre-classification dump deserializes to `false` and
///   refuses — never a stale-dump pass). Fix: (a) an explicit `#[repr(iN/uN)]` with no
///   niche; (b) rewrite as `matches!(self, E::V)` for the SwitchInt lane; (c)
///   re-extract if the dump predates enum classification.
/// * `const-referent-discriminant-unavailable` — the variant list is missing (pre-P4
///   dump), or the decoded discriminant is NEGATIVE and `faithful_enum_repr` does not
///   positively witness a SIGNED repr (`Some(Some(I8|I16|I32|I64))`). A `#[repr(u128)]`
///   tag above `i128::MAX` is stored as a negative `i128` by `decode_discr_tag_or_raw`'s
///   lossy fallback and is indistinguishable from a genuine signed tag in every OTHER
///   field — same `__tag`, same `disc_index_safe`, same stored `-1` — so an absent
///   witness must refuse. `__tag` carries no repr information and is never consulted
///   (it is pushed signed pointer-width for every enum; testing it was a measured false
///   verify). Fix: (a) give the enum an explicit narrow `#[repr(iN)]`; (b) re-extract
///   with an extractor that records the hint; (c) compare fields explicitly
///   (`self.0 == K`) so the leaf lane applies.
/// * `const-referent-leaf-kind-mismatch` — a field's kind/width (Int vs Uint, bit
///   width) differs from the declared field type; nothing is coerced. Fix: re-extract;
///   if it persists this is an extractor bug — file it with the def_path.
/// * `const-referent-leaf-unrepresentable` — a `u128` field above `i128::MAX` has no
///   model-tier literal. Fix: narrow the field type.
pub(crate) fn transport_const_referent(
    body: &trust_types::VerifiableBody,
    t: usize,
    call_block: trust_types::BlockId,
) -> Result<(Vec<i128>, Option<i128>), &'static str> {
    use trust_types::{AdtKind, ConstValue, Operand, Rvalue, Ty};
    let Some((_, _, def)) = unique_local_definition_dominating(body, t, call_block, None) else {
        return Err("actual-temp-has-no-unique-dominating-definition");
    };
    let Rvalue::Use(Operand::Constant(cv)) = def else {
        return Err("const-referent-shape-mismatch");
    };
    let Some(Ty::Ref { mutable: false, inner }) = body.locals.get(t).map(|l| &l.ty) else {
        return Err("const-referent-shape-mismatch");
    };
    let resolved = body.resolved_datatype(inner);
    match cv {
        ConstValue::UnitVariantRef { enum_name, variant } => {
            let Ty::Adt {
                name, variants, disc_index_safe, faithful_enum_repr, ..
            } =
                resolved.as_ref()
            else {
                return Err("const-referent-shape-mismatch");
            };
            if name != enum_name {
                return Err("const-referent-shape-mismatch");
            }
            if !*disc_index_safe {
                return Err("const-discr-enum-not-direct-tag");
            }
            if variants.is_empty() {
                return Err("const-referent-discriminant-unavailable");
            }
            let Some(vd) = variants.get(*variant) else {
                return Err("const-referent-shape-mismatch");
            };
            if !vd.fields.is_empty() {
                return Err("const-referent-shape-mismatch");
            }
            let d = vd.discriminant;
            if d < 0 {
                // A negative decoded discriminant is EITHER a genuine signed tag
                // (`Ordering::Less` = -1) OR the LOSSY `#[repr(u128)]`-above-`i128::MAX`
                // encoding: `decode_discr_tag` cannot represent `u128::MAX` in `i128`,
                // so `decode_discr_tag_or_raw` falls back to `val as i128` = -1, and
                // every `u128 > i128::MAX` has bit 127 set and lands negative.
                //
                // Trust: SOUNDNESS (2026-08-31). This guard used to read the caller's
                // `__tag` pseudo-field, which is VACUOUS: `ty_convert.rs` pushes
                // `("__tag", Int { width: pointer_width, signed: true })` for EVERY
                // enum whatever its repr, so `tag_signed` was a compile-time `true` on
                // every dump the extractor has ever produced and this arm admitted the
                // lossy value. Measured false verify (adversary 2): `#[repr(u128)] enum
                // U128E { Zero = 0, Max = u128::MAX }` certified `is_max(self) ==
                // (discr(self) == -1)` while the runtime discriminant is `2^128 - 1`.
                // `2^128 - 1` has NO `i128` spelling, so REFUSAL is the only sound
                // behaviour and no constant may be substituted.
                //
                // The rule is the build spec's own (§1 B3 (i).4): a negative
                // discriminant needs a signed repr POSITIVELY WITNESSED by
                // `faithful_enum_repr`, never inferred from `__tag`. That witness is
                // exactly `None` for a 128-bit repr (`extractor_enum_repr_hint`:
                // `(Integer::I128, _) => return None`), which is what makes it the
                // discriminating channel. Fail-closed: an absent witness refuses, so a
                // genuinely-signed enum whose hint the extractor did not record is a
                // REACH loss, never a wrong constant.
                let signed_repr_witnessed = matches!(
                    faithful_enum_repr,
                    Some(Some(
                        trust_types::EnumReprHint::I8
                            | trust_types::EnumReprHint::I16
                            | trust_types::EnumReprHint::I32
                            | trust_types::EnumReprHint::I64
                    ))
                );
                if !signed_repr_witnessed {
                    return Err("const-referent-discriminant-unavailable");
                }
            }
            Ok((Vec::new(), Some(d)))
        }
        ConstValue::StructScalarFieldsRef { adt_name, fields } => {
            let Ty::Adt { name, fields: tf, variants, adt_kind, .. } = resolved.as_ref() else {
                return Err("const-referent-shape-mismatch");
            };
            if name != adt_name || !variants.is_empty() || *adt_kind != Some(AdtKind::Struct) {
                return Err("const-referent-shape-mismatch");
            }
            if fields.len() != tf.len() {
                return Err("const-referent-shape-mismatch");
            }
            let fits_signed = |v: i128, w: u32| {
                if w >= 128 {
                    true
                } else {
                    let m = 1i128 << (w - 1);
                    (-m..m).contains(&v)
                }
            };
            let mut vals = Vec::with_capacity(fields.len());
            for (leaf, (_, fty)) in fields.iter().zip(tf) {
                let Ty::Int { width, signed } = fty else {
                    return Err("const-referent-leaf-kind-mismatch");
                };
                let v = match leaf {
                    ConstValue::Int(v) if *signed && fits_signed(*v, *width) => *v,
                    ConstValue::Uint(u, uw) if !*signed && uw == width => {
                        match i128::try_from(*u) {
                            Ok(v) => v,
                            Err(_) => return Err("const-referent-leaf-unrepresentable"),
                        }
                    }
                    _ => return Err("const-referent-leaf-kind-mismatch"),
                };
                vals.push(v);
            }
            Ok((vals, None))
        }
        _ => Err("const-referent-shape-mismatch"),
    }
}

/// Trust: EFHT-P (2026-08-30) — derive the depth-2 PATH HANDLE of a temp `t` from the
/// CALLER'S OWN body: `(base, field, handle_ty)` where `handle_ty` is the `&Adt` the
/// temp holds, RE-DERIVED from the base's field/upvar declaration (never from the
/// temp alone; the temp's declared type must agree). Two admitted shapes:
/// * `&(_p.f)` with `_p` a by-value STRUCT entry parameter whose field `f` is an ADT —
///   additionally requires `base_local_is_unwritten(_p)` (an owned aggregate CAN be
///   written by a non-Deref statement the allow-list permits; a `&T` referent cannot);
/// * `Copy((*_p).f)` with `_p: &Closure` (SHARED) whose upvar `f` is `&Adt`.
/// Every refusal is named, with its fix (v7/D3):
/// * `field-reborrow-base-is-an-enum` / `-is-not-a-struct` — only a by-value STRUCT
///   has a path reading (a union has none; an enum's field depends on its
///   discriminant; a hand-built/unclassified kind fails closed). Fix: (a) match the
///   enum and pass the payload; (b) take `&self` so the Handle lane applies.
/// * `field-reborrow-base-is-a-reference-handle` — `&(*p).f` through a `&Adt` handle
///   is a path over a handle, not admitted in this landing. Fix: pass `p` itself.
/// * `field-reborrow-field-is-scalar` — `&(s.f)` with scalar `s.f` needs a Value
///   reading of a by-value field (a follow-up, not this landing). Fix: pass `s.f` by
///   value.
/// * `field-reborrow-field-type-mismatch` — the field/upvar type is not the ADT handle
///   the temp (or the callee formal) declares. Fix: re-extract; else file.
/// * `field-reborrow-base-is-written` — the by-value base is assigned,
///   projected-assigned, aliased mutably, discriminant-set, deinitialized, retagged,
///   dropped or a call destination. Fix: (a) copy the field to a fresh local BEFORE
///   any write; (b) split the write into a separate function.
/// * `upvar-handle-is-not-a-shared-reference` / `-not-a-shared-adt-reference` — the
///   upvar is `&mut`/raw (item 5's business) or not an `&Adt`. Fix: capture by shared
///   reference.
pub(crate) fn transport_path_handle(
    body: &trust_types::VerifiableBody,
    t: usize,
    call_block: trust_types::BlockId,
) -> Result<(usize, u64, trust_types::Ty), &'static str> {
    use trust_types::{AdtKind, Operand, Projection, Rvalue, Ty};
    let argc = body.arg_count;
    let Some((_, _, def)) = unique_local_definition_dominating(body, t, call_block, None) else {
        return Err("actual-temp-has-no-unique-dominating-definition");
    };
    match def {
        Rvalue::Ref { mutable: false, place } => match place.projections.as_slice() {
            [Projection::Field(f)] => {
                let p = place.local;
                if !(1..=argc).contains(&p) {
                    return Err("argument-outside-transport-fragment");
                }
                let Ok(f_u) = u64::try_from(*f) else {
                    return Err("argument-outside-transport-fragment");
                };
                let Some(bt) = body.locals.get(p).map(|l| &l.ty) else {
                    return Err("field-reborrow-base-is-not-a-struct");
                };
                let resolved = body.resolved_datatype(bt);
                let Ty::Adt { fields: bf, variants, adt_kind, .. } = resolved.as_ref() else {
                    return Err("field-reborrow-base-is-not-a-struct");
                };
                if *adt_kind == Some(AdtKind::Enum) || !variants.is_empty() {
                    return Err("field-reborrow-base-is-an-enum");
                }
                if *adt_kind != Some(AdtKind::Struct) {
                    return Err("field-reborrow-base-is-not-a-struct");
                }
                let Some((_, fty)) = bf.get(*f) else {
                    return Err("field-reborrow-field-type-mismatch");
                };
                match fty {
                    Ty::Int { .. } | Ty::Bool => return Err("field-reborrow-field-is-scalar"),
                    Ty::Adt { .. } => {}
                    _ => return Err("field-reborrow-field-type-mismatch"),
                }
                let handle_ty = Ty::Ref { mutable: false, inner: Box::new(fty.clone()) };
                let agrees = body
                    .locals
                    .get(t)
                    .is_some_and(|l| l.ty.eq_ignoring_disc_index_safe(&handle_ty));
                if !agrees {
                    return Err("field-reborrow-field-type-mismatch");
                }
                if !base_local_is_unwritten(body, p) {
                    return Err("field-reborrow-base-is-written");
                }
                Ok((p, f_u, handle_ty))
            }
            [Projection::Deref, Projection::Field(_)] => {
                Err("field-reborrow-base-is-a-reference-handle")
            }
            _ => Err("argument-outside-transport-fragment"),
        },
        Rvalue::Use(Operand::Copy(src)) => {
            let [Projection::Deref, Projection::Field(f)] = src.projections.as_slice() else {
                return Err("argument-outside-transport-fragment");
            };
            let p = src.local;
            if !(1..=argc).contains(&p) {
                return Err("field-actual-base-is-not-an-entry-parameter");
            }
            let Ok(f_u) = u64::try_from(*f) else {
                return Err("argument-outside-transport-fragment");
            };
            let Some(Ty::Ref { mutable: false, inner }) = body.locals.get(p).map(|l| &l.ty)
            else {
                return Err("upvar-handle-is-not-a-shared-reference");
            };
            let Ty::Closure { upvars, .. } = inner.as_ref() else {
                return Err("argument-outside-transport-fragment");
            };
            let Some(up) = upvars.get(*f) else {
                return Err("upvar-handle-is-not-a-shared-adt-reference");
            };
            match up {
                Ty::Ref { mutable: false, inner: ui } if matches!(ui.as_ref(), Ty::Adt { .. }) => {}
                Ty::Ref { mutable: true, .. } | Ty::RawPtr { .. } => {
                    return Err("upvar-handle-is-not-a-shared-reference")
                }
                _ => return Err("upvar-handle-is-not-a-shared-adt-reference"),
            }
            let agrees =
                body.locals.get(t).is_some_and(|l| l.ty.eq_ignoring_disc_index_safe(up));
            if !agrees {
                return Err("field-reborrow-field-type-mismatch");
            }
            Ok((p, f_u, up.clone()))
        }
        _ => Err("argument-outside-transport-fragment"),
    }
}
