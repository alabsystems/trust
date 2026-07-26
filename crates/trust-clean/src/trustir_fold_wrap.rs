// trust-clean/trustir_fold_wrap.rs — Trust: structural-fold lane, RUNG E.
//
// The G-FAMILY WRAPPERS (docs/design/2026-07-10-structural-fold-lane.md §3.4 +
// §5 Rung E; reports/m6-shape-gap-attack-plan-2026-07-10.md family G): the thin
// folder-launch / delegate methods of clean-kernel `expr/subst.rs` that reach
// the rung-C/D-certified memoized Expr folds. Two recognizers, two transport
// designs — SAY-WHICH-SHIPPED note, per the rung-E mission:
//
//   1. FOLDER-LAUNCH wrappers (`subst_fvar`, `lift_at`, `abstract_fvar_at`,
//      `instantiate_at` — the last unhostaged by main's Instantiator-SCC
//      P-ORD-CMP leaf-assert landing, which this rung composes with — and
//      the hostage kin `instantiate_rev` / `lower_loose_bvars` /
//      `instantiate_level_params_map/_direct`):
//      design-§3.4 OPTION (B), per-wrapper INLINING — STRUCTURALLY FORCED,
//      not a shortcut: the wrapper's only call edge is the GENERIC
//      `Expr::fold_opt_or_clone` (dumped once, polymorphically), whose own
//      callee renders as the generic trait path — the call graph has NO edge
//      from the wrapper to the concrete `<F as ExprFolderOpt>::fold_expr_opt`
//      row, so no registry-ordered CalleeFact can ever transport it (the
//      rung-B/D "the registry has no such edge" precedent, one level up).
//      The recognizer reads the concrete folder off the wrapper's OWN
//      Aggregate (or the fingerprinted `Abstractor::new` ctor), re-recognizes
//      the folder row's SCC from the sibling bodies, and the gate arm
//      composes the callee's REGISTERED FOLD DENOTATION through the
//      kernel-checked `wrapAdequate`/`wrapAdequateD` composition theorem
//      (`trustir_fold_expr` rung-E section — `unwrapOr` over
//      `memoAdequate(D)`, `congrArg`-proven, `axiom_deps` empty).
//
//   2. PURE DELEGATES (`lift`, `lift_from`, `abstract_fvar`, and
//      `instantiate` — FF once its callee `instantiate_at` certifies ahead of
//      it in the callees-first order): design-§3.4 OPTION (A), the GROWTH
//      PATH — these
//      DO have a real call-graph edge to a named sibling (`lift_at`, …), so
//      they ride the callees-first CERTIFIED registry exactly like the Int
//      call lane, through the ADT-VALUED transport twin
//      (`CallE`/`callResultE`/`callReturnInstanceE` — TExpr-sorted, minted
//      over the SAME fold mirror as the callee's own certificate). The
//      recognizer additionally RE-RECOGNIZES the callee's launch shape from
//      the sibling bodies (the callee-caller MATCH conjunct: the registry
//      entry, the dump body, and the fold-mirror the twin is minted over must
//      all name the same callee — a stale/doctored sibling body fails this
//      conjunct even when the registry key still exists).
//
// HONESTY TIER (unchanged from rungs C/D — carried by every verdict here):
// MODEL-ONLY (`trustir_adt.rs` tier), kind-tree property (`ExprMeta` erased),
// premises P-ACYC / P-ADDR / P-STACK / P-CLONE / P-SAT-ADD / P-CTOR-ZST /
// P-OPT-STD as named in `trustir_fold_expr`'s module doc. Rung E adds NO new
// premise: the launch wrapper's `unwrap_or_else(|| self.clone())` fallback arm
// is P-CLONE's existing position (the `fold_opt_or_clone` closure body is
// fingerprinted, and `<Expr as Clone>::clone`'s own dump re-checked); the
// guard clone arm (`lift_at`'s `amount == 0`) is the same position. The
// `FoldMemo::default()` / `HashMap::new()` fresh-empty-memo start is covered
// by P-ADDR's oracle-soundness reading (the memoAdequate hypothesis holds for
// ANY sound memo state; the fresh memo is the trivially-sound start) +
// P-OPT-STD for the std constructors (rendered as the `__trust_total_clone`
// derived-total sentinel by extraction — zero args, dest type pinned to
// `FoldMemo`).
//
// FAIL-CLOSED: every decline NAMED; any statement/terminator/block outside
// the pinned launch/delegate vocabulary declines; unwind noise is tolerated
// ONLY as the exact `Drop(folder) → Resume` / `Resume` epilogue.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use trust_types::{
    AggregateKind, ConstValue, Operand, Rvalue, Statement, Terminator, Ty, VerifiableFunction,
};

use crate::trustir_fold::DumpBodies;
use crate::trustir_fold_expr::{
    CLONE_CLONE, EXPR_CLONE, EXPR_NAME, ExprFoldDecline, FOLDMEMO_TY, SemExprFold, TOTAL_CLONE,
    TRAIT_PREFIX, block, is_local, op_local, real_stmts, sem_expr_fold_shape_of,
};

/// The generic sharing-preserving driver (dumped once, polymorphically) and
/// its clone-fallback closure.
const FOLD_OPT_OR_CLONE: &str = "expr::Expr::fold_opt_or_clone";
const FOLD_OPT_OR_CLONE_CLOSURE: &str = "expr::Expr::fold_opt_or_clone::{closure#0}";
const GEN_FOLD_EXPR_OPT: &str = "expr::visitor::opt::ExprFolderOpt::fold_expr_opt";
const OPTION_UNWRAP_OR_ELSE: &str = "std::option::Option::<T>::unwrap_or_else";

// ===========================================================================
// Named declines
// ===========================================================================

/// Why the rung-E wrapper recognizer declined — every decline NAMED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FoldWrapDecline {
    /// Signature is not `fn(&Expr, ..) -> Expr` (launch) / delegate-compatible.
    SignatureUnsupported(String),
    /// The wrapper body deviates from the pinned launch vocabulary.
    LaunchShape(String),
    /// The optional `param == 0` early-clone guard drifts.
    GuardShape(String),
    /// The folder Aggregate/ctor disagrees with the recognized fold row
    /// (different folder type, broken field map, memo not fresh, depth-init
    /// mismatch) — the caller-callee MISMATCH kill.
    FolderMismatch(String),
    /// The `fold_opt_or_clone` driver / its clone closure / `Expr::clone` /
    /// the folder ctor (`Abstractor::new`) fingerprint drifts.
    DriverDrift(String),
    /// The concrete folder row's own fold recognition declined (forwarded).
    FoldRow(ExprFoldDecline),
    /// The delegate body deviates from the pinned single-call vocabulary.
    DelegateShape(String),
    /// Delegate: the callee is not in the callees-first certified registry.
    CalleeUnresolved(String),
    /// Delegate: registry entry / sibling dump body / signature disagree —
    /// the stale-registry / callee-caller mismatch kill.
    CalleeMismatch(String),
}

impl FoldWrapDecline {
    /// Stable snake_case decline name.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            FoldWrapDecline::SignatureUnsupported(_) => "fold_wrap::signature_unsupported",
            FoldWrapDecline::LaunchShape(_) => "fold_wrap::launch_shape",
            FoldWrapDecline::GuardShape(_) => "fold_wrap::guard_shape",
            FoldWrapDecline::FolderMismatch(_) => "fold_wrap::folder_mismatch",
            FoldWrapDecline::DriverDrift(_) => "fold_wrap::driver_drift",
            FoldWrapDecline::FoldRow(d) => d.name(),
            FoldWrapDecline::DelegateShape(_) => "fold_wrap::delegate_shape",
            FoldWrapDecline::CalleeUnresolved(_) => "fold_wrap::callee_unresolved",
            FoldWrapDecline::CalleeMismatch(_) => "fold_wrap::callee_mismatch",
        }
    }
}

type R<T> = Result<T, FoldWrapDecline>;

fn launch_err(detail: impl Into<String>) -> FoldWrapDecline {
    FoldWrapDecline::LaunchShape(detail.into())
}

// ===========================================================================
// Recognized shapes
// ===========================================================================

/// Where a folder field's initial value comes from in the wrapper.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LaunchFieldSrc {
    /// A wrapper parameter local (`2..=arg_count` — never `self`).
    Param(usize),
    /// A scalar integer literal (e.g. `Lowerer`'s `start: 0`).
    Lit(u128),
    /// The fresh memo (`FoldMemo::default()` sentinel / `HashMap::new()`).
    Memo,
}

/// The recognized folder-launch wrapper.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemFoldLaunch {
    /// The folder type def-path (from the wrapper's own Aggregate / ctor).
    pub folder: String,
    /// The resolved `<F as ExprFolderOpt>::fold_expr_opt` row def-path.
    pub row_path: String,
    /// The folder row's recognized SCC shape (ctors, leaves, depth facts).
    pub fold: SemExprFold,
    /// `Some(param_local)` when the wrapper carries the `param == 0`
    /// early-clone guard (`lift_at`'s `amount == 0` arm; P-CLONE identity).
    pub zero_guard: Option<usize>,
    /// Folder-field sources in field order (the caller→callee value map).
    pub field_srcs: Vec<LaunchFieldSrc>,
    /// Depth family: the initial-depth (d0) source (the wrapper operand
    /// feeding the folder's sole mutable depth field).
    pub d0: Option<LaunchFieldSrc>,
    /// The fingerprinted folder ctor def-path (`Abstractor::new`) when the
    /// folder is built by a ctor call instead of an inline Aggregate.
    pub ctor: Option<String>,
}

/// The recognized ADT-returning pure delegate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemAdtDelegate {
    /// The callee def-path (EXACT registry key).
    pub callee: String,
    /// The callee's index in the sorted certified registry (the twin's
    /// `Nat` callee-id pin).
    pub callee_id: u64,
    /// The modeled actual arguments (`Var` = param index, `Const` = literal).
    pub args: Vec<crate::trustir_anchor::IrOperand>,
}

// ===========================================================================
// Small helpers
// ===========================================================================

fn adt_name(ty: &Ty) -> Option<&str> {
    match ty {
        Ty::Adt { name, .. } | Ty::Datatype { name, .. } => Some(name),
        _ => None,
    }
}

fn is_expr_ref(ty: &Ty) -> bool {
    matches!(ty, Ty::Ref { mutable: false, inner } if adt_name(inner.as_ref()) == Some(EXPR_NAME))
}

/// Shallow, fail-closed type compatibility for folder-field pinning: integer
/// types must match exactly; references must agree on mutability and pointee
/// Adt identity; Adt/Datatype carriers must agree by name. Anything else
/// (including two types this check cannot positively identify) is
/// INCOMPATIBLE — never a silent accept.
fn ty_compat(a: &Ty, b: &Ty) -> bool {
    match (a, b) {
        (Ty::Int { width: w1, signed: s1 }, Ty::Int { width: w2, signed: s2 }) => {
            w1 == w2 && s1 == s2
        }
        (Ty::Bool, Ty::Bool) => true,
        (Ty::Ref { mutable: m1, inner: i1 }, Ty::Ref { mutable: m2, inner: i2 }) => {
            m1 == m2
                && match (adt_name(i1.as_ref()), adt_name(i2.as_ref())) {
                    (Some(n1), Some(n2)) => n1 == n2,
                    _ => ty_compat(i1.as_ref(), i2.as_ref()),
                }
        }
        _ => match (adt_name(a), adt_name(b)) {
            (Some(n1), Some(n2)) => n1 == n2,
            _ => false,
        },
    }
}

fn body_has_unsupported(func: &VerifiableFunction) -> bool {
    func.body.blocks.iter().any(|b| {
        b.stmts.iter().any(|s| matches!(s, Statement::Unsupported { .. }))
            || matches!(b.terminator, Terminator::Opaque { .. })
    })
}

// ===========================================================================
// Driver fingerprints — `fold_opt_or_clone`, its closure, `Folder::new`
// ===========================================================================

fn driver_drift(member: &str, detail: impl Into<String>) -> FoldWrapDecline {
    FoldWrapDecline::DriverDrift(format!("{member}: {}", detail.into()))
}

fn wrap_co_member<'a>(bodies: &'a DumpBodies, path: &str) -> R<&'a VerifiableFunction> {
    bodies
        .get(path)
        .ok_or_else(|| FoldWrapDecline::DriverDrift(format!("{path}: missing sibling dump")))
}

/// Pin the generic `Expr::fold_opt_or_clone` body: exactly
/// `_3 = fold_expr_opt(folder, self); _4 = {clone-closure}(self);
///  _0 = Option::unwrap_or_else(_3, _4); return` — the composition the
/// `wrapAdequate` kernel theorem models (P-OPT-STD + P-CLONE positions).
fn match_fold_opt_or_clone(func: &VerifiableFunction) -> R<()> {
    let m = FOLD_OPT_OR_CLONE;
    let body = &func.body;
    if body.arg_count != 2 || body.blocks.len() != 3 {
        return Err(driver_drift(m, "not the 3-block driver shape"));
    }
    if !matches!(body.locals.get(1).map(|l| &l.ty), Some(t) if is_expr_ref(t)) {
        return Err(driver_drift(m, "param 1 is not &Expr"));
    }
    if adt_name(&body.return_ty) != Some(EXPR_NAME) {
        return Err(driver_drift(m, "return type is not Expr"));
    }
    let b0 = block(body, trust_types::BlockId(0)).ok_or_else(|| driver_drift(m, "no bb0"))?;
    if !real_stmts(b0).is_empty() {
        return Err(driver_drift(m, "unexpected bb0 statements"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t0), .. } = &b0.terminator else {
        return Err(driver_drift(m, "bb0 does not call fold_expr_opt"));
    };
    if callee != GEN_FOLD_EXPR_OPT {
        return Err(driver_drift(m, format!("bb0 calls {callee}")));
    }
    let opt_dest = dest.local;
    if !matches!(args.as_slice(), [f, s] if op_local(f) == Some(2) && op_local(s) == Some(1))
        || !dest.projections.is_empty()
    {
        return Err(driver_drift(m, "fold_expr_opt does not forward (folder, self)"));
    }
    let b1 = block(body, *t0).ok_or_else(|| driver_drift(m, "missing bb1"))?;
    // bb1: the clone-fallback closure aggregate (captures exactly [self]).
    let stmts = real_stmts(b1);
    let [
        Statement::Assign {
            place: cp,
            rvalue: Rvalue::Aggregate(AggregateKind::Closure { name, .. }, caps),
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(driver_drift(m, "bb1 statements are not the closure aggregate"));
    };
    if name != FOLD_OPT_OR_CLONE_CLOSURE {
        return Err(driver_drift(m, format!("closure aggregate names {name}")));
    }
    if !matches!(caps.as_slice(), [c] if op_local(c) == Some(1)) {
        return Err(driver_drift(m, "closure does not capture exactly self"));
    }
    let Terminator::Call { func: callee1, args: args1, dest: dest1, target: Some(t1), .. } =
        &b1.terminator
    else {
        return Err(driver_drift(m, "bb1 does not call unwrap_or_else"));
    };
    if callee1 != OPTION_UNWRAP_OR_ELSE {
        return Err(driver_drift(m, format!("bb1 calls {callee1}")));
    }
    let ok = matches!(args1.as_slice(), [o, f]
        if op_local(o) == Some(opt_dest) && op_local(f) == Some(cp.local))
        && is_local(dest1, 0);
    if !ok {
        return Err(driver_drift(m, "unwrap_or_else does not consume (fold result, closure)"));
    }
    let b2 = block(body, *t1).ok_or_else(|| driver_drift(m, "missing return block"))?;
    if !matches!(b2.terminator, Terminator::Return) || !real_stmts(b2).is_empty() {
        return Err(driver_drift(m, "driver does not return the unwrap result directly"));
    }
    Ok(())
}

/// Pin the driver's clone-fallback closure: `_2 = copy (self capture);
/// _0 = Clone::clone(_2); return` (the P-CLONE identity arm).
fn match_fold_opt_or_clone_closure(func: &VerifiableFunction) -> R<()> {
    let m = FOLD_OPT_OR_CLONE_CLOSURE;
    let body = &func.body;
    if body.arg_count != 1 || body.blocks.len() != 2 {
        return Err(driver_drift(m, "not the 2-block clone-closure shape"));
    }
    let b0 = block(body, trust_types::BlockId(0)).ok_or_else(|| driver_drift(m, "no bb0"))?;
    let stmts = real_stmts(b0);
    let [
        Statement::Assign {
            place: p,
            rvalue: Rvalue::Use(Operand::Copy(src) | Operand::Move(src)),
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(driver_drift(m, "closure bb0 is not the capture read"));
    };
    if src.local != 1 || src.projections != vec![trust_types::Projection::Field(0)] {
        return Err(driver_drift(m, "closure does not read capture .0"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(driver_drift(m, "closure bb0 does not call clone"));
    };
    if callee != CLONE_CLONE && callee != EXPR_CLONE {
        return Err(driver_drift(m, format!("closure calls {callee}")));
    }
    if !matches!(args.as_slice(), [a] if op_local(a) == Some(p.local)) || !is_local(dest, 0) {
        return Err(driver_drift(m, "closure clone does not consume the capture into _0"));
    }
    let b1 = block(body, *t).ok_or_else(|| driver_drift(m, "missing return block"))?;
    if !matches!(b1.terminator, Terminator::Return) || !real_stmts(b1).is_empty() {
        return Err(driver_drift(m, "closure does not return the clone directly"));
    }
    Ok(())
}

/// Pin a folder ctor (`Abstractor::new`): `HashMap::new() → _m;
/// _0 = Folder { arg1, arg2, …, _m }; return`. Returns the folder type name
/// and the field sources (ctor-arg locals mapped through, memo position).
fn match_folder_ctor(func: &VerifiableFunction) -> R<(String, Vec<LaunchFieldSrc>)> {
    let m = func.def_path.as_str();
    let body = &func.body;
    if body.blocks.len() != 2 {
        return Err(driver_drift(m, "ctor is not the 2-block shape"));
    }
    let b0 = block(body, trust_types::BlockId(0)).ok_or_else(|| driver_drift(m, "no bb0"))?;
    if !real_stmts(b0).is_empty() {
        return Err(driver_drift(m, "unexpected ctor bb0 statements"));
    }
    let Terminator::Call { func: callee, args, dest, target: Some(t), .. } = &b0.terminator else {
        return Err(driver_drift(m, "ctor bb0 does not call the map ctor"));
    };
    // `HashMap::<K, V>::new` — the fresh empty memo (P-OPT-STD).
    if !(callee.starts_with("std::collections::HashMap::") && callee.ends_with("::new")) {
        return Err(driver_drift(m, format!("ctor calls {callee}, not HashMap::new")));
    }
    if !args.is_empty() || !dest.projections.is_empty() {
        return Err(driver_drift(m, "map ctor call shape"));
    }
    let memo_local = dest.local;
    let b1 = block(body, *t).ok_or_else(|| driver_drift(m, "missing ctor aggregate block"))?;
    let stmts = real_stmts(b1);
    let [
        Statement::Assign {
            place,
            rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops),
            ..
        },
    ] = stmts.as_slice()
    else {
        return Err(driver_drift(m, "ctor does not build the folder aggregate"));
    };
    if !is_local(place, 0) || !matches!(b1.terminator, Terminator::Return) {
        return Err(driver_drift(m, "ctor aggregate is not returned directly"));
    }
    // The ctor's return type carries the folder's declared field types — pin
    // every aggregate operand against its field (fail-closed).
    let Ty::Adt { name: decl_name, fields: decl_fields, .. } = &body.return_ty else {
        return Err(driver_drift(m, "ctor return type is not the folder Adt"));
    };
    if decl_name != name || decl_fields.len() != ops.len() {
        return Err(driver_drift(m, "ctor aggregate does not match the declared folder type"));
    }
    let mut srcs = Vec::with_capacity(ops.len());
    for (op, (_, fty)) in ops.iter().zip(decl_fields) {
        match op {
            Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                if p.local == memo_local {
                    if adt_name(fty) != Some("std::collections::HashMap")
                        && adt_name(fty) != Some(FOLDMEMO_TY)
                    {
                        return Err(driver_drift(m, "ctor memo field type"));
                    }
                    srcs.push(LaunchFieldSrc::Memo);
                } else if (1..=body.arg_count).contains(&p.local) {
                    let ok = body.locals.get(p.local).is_some_and(|l| ty_compat(&l.ty, fty));
                    if !ok {
                        return Err(driver_drift(m, "ctor arg/field type mismatch"));
                    }
                    srcs.push(LaunchFieldSrc::Param(p.local));
                } else {
                    return Err(driver_drift(m, "ctor aggregate operand is not an arg/memo"));
                }
            }
            Operand::Constant(ConstValue::Uint(v, _)) => {
                if !matches!(fty, Ty::Int { .. }) {
                    return Err(driver_drift(m, "ctor literal/field type mismatch"));
                }
                srcs.push(LaunchFieldSrc::Lit(*v));
            }
            _ => return Err(driver_drift(m, "ctor aggregate operand shape")),
        }
    }
    if srcs.iter().filter(|s| matches!(s, LaunchFieldSrc::Memo)).count() != 1 {
        return Err(driver_drift(m, "ctor does not place the fresh map exactly once"));
    }
    Ok((name.clone(), srcs))
}

// ===========================================================================
// The folder-launch recognizer (option (b) — per-wrapper inlining)
// ===========================================================================

/// Recognize the folder-launch wrapper shape of `func`, fail-closed with
/// NAMED declines: optional `param == 0` early-clone guard, fresh-memo folder
/// construction (inline Aggregate + `FoldMemo::default()` sentinel, or a
/// fingerprinted `Folder::new` ctor), the pinned `fold_opt_or_clone`
/// delegation, `Drop(folder) → Return` epilogue, and the concrete folder
/// row's own SCC recognition from the sibling bodies.
#[allow(clippy::too_many_lines)]
pub fn sem_fold_launch_wrapper_of(
    func: &VerifiableFunction,
    bodies: &DumpBodies,
) -> Result<SemFoldLaunch, FoldWrapDecline> {
    let body = &func.body;
    // Signature: fn(&Expr, ..) -> Expr.
    if adt_name(&body.return_ty) != Some(EXPR_NAME) {
        return Err(FoldWrapDecline::SignatureUnsupported(format!(
            "{} does not return Expr",
            func.def_path
        )));
    }
    if body.arg_count < 1 || !matches!(body.locals.get(1).map(|l| &l.ty), Some(t) if is_expr_ref(t))
    {
        return Err(FoldWrapDecline::SignatureUnsupported(format!(
            "{} param 1 is not &Expr",
            func.def_path
        )));
    }
    if body_has_unsupported(func) {
        return Err(launch_err("unsupported statements/terminators present"));
    }
    // No parameter may be reassigned/aliased anywhere (entry-time reading).
    for p in 1..=body.arg_count {
        if crate::mirsem::param_reassigned_by_stmt(body, p) {
            return Err(launch_err(format!("parameter _{p} is reassigned/aliased")));
        }
    }

    let mut visited: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut cur = trust_types::BlockId(0);
    let mut zero_guard: Option<usize> = None;
    let mut clone_ret_block: Option<trust_types::BlockId> = None;

    // Optional guard prologue: `_g = Eq(copy param, const 0); switch`.
    let b0 = block(body, cur).ok_or_else(|| launch_err("no bb0"))?;
    let b0_stmts = real_stmts(b0);
    if let Terminator::SwitchInt { discr, targets, otherwise, .. } = &b0.terminator {
        let [
            Statement::Assign {
                place: gp,
                rvalue: Rvalue::BinaryOp(trust_types::BinOp::Eq, ga, gb),
                ..
            },
        ] = b0_stmts.as_slice()
        else {
            return Err(FoldWrapDecline::GuardShape("guard block statements".into()));
        };
        let Some(gparam) = op_local(ga) else {
            return Err(FoldWrapDecline::GuardShape("guard lhs is not a bare local".into()));
        };
        if !(2..=body.arg_count).contains(&gparam) {
            return Err(FoldWrapDecline::GuardShape("guard lhs is not a parameter".into()));
        }
        if !matches!(gb, Operand::Constant(ConstValue::Uint(0, _))) {
            return Err(FoldWrapDecline::GuardShape("guard rhs is not the 0 literal".into()));
        }
        if op_local(discr) != Some(gp.local) || !gp.projections.is_empty() {
            return Err(FoldWrapDecline::GuardShape("switch discr is not the guard temp".into()));
        }
        // targets: [(0 → build path)]; otherwise → the clone arm.
        let [(0, build_bb)] = targets.as_slice() else {
            return Err(FoldWrapDecline::GuardShape("guard switch targets".into()));
        };
        // Clone arm: `_0 = Clone::clone(self)` → shared return block.
        let cb = block(body, *otherwise)
            .ok_or_else(|| FoldWrapDecline::GuardShape("missing clone arm".into()))?;
        if !real_stmts(cb).is_empty() {
            return Err(FoldWrapDecline::GuardShape("clone arm statements".into()));
        }
        let Terminator::Call { func: cc, args: cargs, dest: cdest, target: Some(ct), .. } =
            &cb.terminator
        else {
            return Err(FoldWrapDecline::GuardShape("clone arm terminator".into()));
        };
        if cc != CLONE_CLONE && cc != EXPR_CLONE {
            return Err(FoldWrapDecline::GuardShape(format!("clone arm calls {cc}")));
        }
        if !matches!(cargs.as_slice(), [a] if op_local(a) == Some(1)) || !is_local(cdest, 0) {
            return Err(FoldWrapDecline::GuardShape(
                "clone arm does not clone self into _0".into(),
            ));
        }
        visited.insert(b0.id.0);
        visited.insert(cb.id.0);
        zero_guard = Some(gparam);
        clone_ret_block = Some(*ct);
        cur = *build_bb;
    }

    // Build path: memo/ctor acquisition.
    let mut ctor: Option<String> = None;
    let mut ctor_srcs: Option<Vec<LaunchFieldSrc>> = None;
    let mut ctor_arg_map: Vec<Operand> = Vec::new();
    let mut memo_local: Option<usize> = None;
    let mut folder_local_from_ctor: Option<usize> = None;
    let mut folder_name_from_ctor: Option<String> = None;

    let acq = block(body, cur).ok_or_else(|| launch_err("missing memo/ctor block"))?;
    if !real_stmts(acq).is_empty() {
        return Err(launch_err("memo/ctor block has statements"));
    }
    let Terminator::Call { func: acallee, args: aargs, dest: adest, target: Some(at), .. } =
        &acq.terminator
    else {
        return Err(launch_err("memo/ctor block terminator is not a call"));
    };
    if acallee == TOTAL_CLONE {
        // `FoldMemo::default()` — the derived-total sentinel, zero args, dest
        // type pinned to FoldMemo.
        if !aargs.is_empty() || !adest.projections.is_empty() {
            return Err(launch_err("memo default call shape"));
        }
        let memo_ty_ok =
            body.locals.get(adest.local).is_some_and(|l| adt_name(&l.ty) == Some(FOLDMEMO_TY));
        if !memo_ty_ok {
            return Err(launch_err("memo default dest is not FoldMemo"));
        }
        memo_local = Some(adest.local);
    } else if acallee.ends_with("::new") {
        // A folder ctor (`Abstractor::new`) — fingerprint its own dump.
        let ctor_body = wrap_co_member(bodies, acallee)?;
        let (fname, srcs) = match_folder_ctor(ctor_body)?;
        if aargs.len() != ctor_body.body.arg_count {
            return Err(FoldWrapDecline::FolderMismatch("ctor arity mismatch".into()));
        }
        for a in aargs {
            match a {
                Operand::Copy(p) | Operand::Move(p)
                    if p.projections.is_empty() && (2..=body.arg_count).contains(&p.local) => {}
                Operand::Constant(ConstValue::Uint(_, _)) => {}
                _ => {
                    return Err(FoldWrapDecline::FolderMismatch(
                        "ctor actual is not a param/literal".into(),
                    ));
                }
            }
        }
        if !adest.projections.is_empty() {
            return Err(launch_err("ctor dest shape"));
        }
        ctor = Some(acallee.clone());
        ctor_srcs = Some(srcs);
        ctor_arg_map = aargs.clone();
        folder_local_from_ctor = Some(adest.local);
        folder_name_from_ctor = Some(fname);
    } else {
        return Err(launch_err(format!("memo/ctor block calls {acallee}")));
    }
    visited.insert(acq.id.0);
    cur = *at;

    // The launch block: [folder aggregate,] `&mut folder`, fold_opt_or_clone.
    let lb = block(body, cur).ok_or_else(|| launch_err("missing launch block"))?;
    let lstmts = real_stmts(lb);
    let (folder_name, folder_local, agg_ops): (String, usize, Vec<Operand>) = if let Some(fl) =
        folder_local_from_ctor
    {
        // Ctor form: sole statement is the `&mut folder` borrow.
        let [
            Statement::Assign {
                place: rp, rvalue: Rvalue::Ref { mutable: true, place: fsrc }, ..
            },
        ] = lstmts.as_slice()
        else {
            return Err(launch_err("launch block (ctor form) statements"));
        };
        if !is_local(fsrc, fl) {
            return Err(launch_err("&mut is not of the ctor-built folder"));
        }
        let _ = rp;
        (folder_name_from_ctor.clone().unwrap_or_default(), fl, Vec::new())
    } else {
        let [
            Statement::Assign {
                place: fp,
                rvalue: Rvalue::Aggregate(AggregateKind::Adt { name, variant: 0, .. }, ops),
                ..
            },
            Statement::Assign {
                place: _rp,
                rvalue: Rvalue::Ref { mutable: true, place: fsrc },
                ..
            },
        ] = lstmts.as_slice()
        else {
            return Err(launch_err("launch block statements"));
        };
        if !fp.projections.is_empty() || !is_local(fsrc, fp.local) {
            return Err(launch_err("&mut is not of the folder aggregate"));
        }
        (name.clone(), fp.local, ops.clone())
    };
    // The folder local's DECLARED type must name the same folder Adt and
    // carry its field types (the wrong-denotation kill: a doctored aggregate
    // naming a different folder than the declared local type declines here).
    let folder_decl_fields: Vec<(String, Ty)> = match body.locals.get(folder_local).map(|l| &l.ty) {
        Some(Ty::Adt { name: dn, fields, .. }) if dn == &folder_name => fields.clone(),
        _ => {
            return Err(FoldWrapDecline::FolderMismatch(format!(
                "folder local's declared type does not name {folder_name}"
            )));
        }
    };
    // Aggregate form: every operand's type must match its declared field.
    if !agg_ops.is_empty() {
        if agg_ops.len() != folder_decl_fields.len() {
            return Err(FoldWrapDecline::FolderMismatch("folder field arity".into()));
        }
        for (op, (_, fty)) in agg_ops.iter().zip(&folder_decl_fields) {
            let ok = match op {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    body.locals.get(p.local).is_some_and(|l| ty_compat(&l.ty, fty))
                }
                Operand::Constant(ConstValue::Uint(_, _)) => matches!(fty, Ty::Int { .. }),
                _ => false,
            };
            if !ok {
                return Err(FoldWrapDecline::FolderMismatch(
                    "folder field operand/type mismatch".into(),
                ));
            }
        }
    }
    // Ctor form: the wrapper's actuals must match the ctor's declared params.
    if let Some(ctor_path) = &ctor {
        let ctor_body = wrap_co_member(bodies, ctor_path)?;
        for (i, a) in ctor_arg_map.iter().enumerate() {
            let pty = ctor_body
                .body
                .locals
                .get(i + 1)
                .map(|l| &l.ty)
                .ok_or_else(|| FoldWrapDecline::FolderMismatch("ctor param type".into()))?;
            let ok = match a {
                Operand::Copy(p) | Operand::Move(p) if p.projections.is_empty() => {
                    body.locals.get(p.local).is_some_and(|l| ty_compat(&l.ty, pty))
                }
                Operand::Constant(ConstValue::Uint(_, _)) => matches!(pty, Ty::Int { .. }),
                _ => false,
            };
            if !ok {
                return Err(FoldWrapDecline::FolderMismatch(
                    "ctor actual/param type mismatch".into(),
                ));
            }
        }
    }
    // The borrow temp local (for the call's folder argument).
    let borrow_local =
        match lstmts.last() {
            Some(Statement::Assign {
                place, rvalue: Rvalue::Ref { mutable: true, .. }, ..
            }) if place.projections.is_empty() => place.local,
            _ => return Err(launch_err("launch block does not end in the &mut borrow")),
        };
    let Terminator::Call { func: lcallee, args: largs, dest: ldest, target: Some(lt), .. } =
        &lb.terminator
    else {
        return Err(launch_err("launch block terminator is not the driver call"));
    };
    if lcallee != FOLD_OPT_OR_CLONE {
        return Err(launch_err(format!("launch block calls {lcallee}")));
    }
    if !matches!(largs.as_slice(), [s, f]
        if op_local(s) == Some(1) && op_local(f) == Some(borrow_local))
        || !is_local(ldest, 0)
    {
        return Err(launch_err("driver call does not forward (self, &mut folder) into _0"));
    }
    visited.insert(lb.id.0);

    // Epilogue: Drop(folder) → Return (shared with the guard's clone arm).
    let db = block(body, *lt).ok_or_else(|| launch_err("missing drop block"))?;
    let Terminator::Drop { place: dp, target: dt, .. } = &db.terminator else {
        return Err(launch_err("post-call block is not the folder drop"));
    };
    if !is_local(dp, folder_local) || !real_stmts(db).is_empty() {
        return Err(launch_err("drop is not of the folder"));
    }
    visited.insert(db.id.0);
    let rb = block(body, *dt).ok_or_else(|| launch_err("missing return block"))?;
    if !matches!(rb.terminator, Terminator::Return) || !real_stmts(rb).is_empty() {
        return Err(launch_err("epilogue does not return directly"));
    }
    if let Some(crb) = clone_ret_block {
        if crb != rb.id {
            return Err(FoldWrapDecline::GuardShape(
                "clone arm does not share the return block".into(),
            ));
        }
    }
    visited.insert(rb.id.0);

    // Every unvisited block must be exact unwind noise:
    // `Drop(folder) → Resume` / `Resume` / `Unreachable`.
    for b in &body.blocks {
        if visited.contains(&b.id.0) {
            continue;
        }
        if !real_stmts(b).is_empty() {
            return Err(launch_err(format!("stray statements in bb{}", b.id.0)));
        }
        match &b.terminator {
            Terminator::Resume | Terminator::Unreachable => {}
            Terminator::Drop { place, target, .. } if is_local(place, folder_local) => {
                let tb =
                    block(body, *target).ok_or_else(|| launch_err("unwind drop target missing"))?;
                if !matches!(tb.terminator, Terminator::Resume) {
                    return Err(launch_err("unwind drop does not resume"));
                }
            }
            _ => return Err(launch_err(format!("stray terminator in bb{}", b.id.0))),
        }
    }

    // Driver + closure + Expr::clone fingerprints (P-OPT-STD / P-CLONE).
    match_fold_opt_or_clone(wrap_co_member(bodies, FOLD_OPT_OR_CLONE)?)?;
    match_fold_opt_or_clone_closure(wrap_co_member(bodies, FOLD_OPT_OR_CLONE_CLOSURE)?)?;
    crate::trustir_fold_expr::match_expr_clone(wrap_co_member(bodies, EXPR_CLONE)?)
        .map_err(FoldWrapDecline::FoldRow)?;

    // Resolve the concrete folder row and recognize its SCC.
    let row_path = [
        format!("<{folder_name} as {TRAIT_PREFIX}>::fold_expr_opt"),
        format!("<{folder_name}<'_> as {TRAIT_PREFIX}>::fold_expr_opt"),
    ]
    .into_iter()
    .find(|p| bodies.contains_key(p))
    .ok_or_else(|| {
        FoldWrapDecline::FolderMismatch(format!("no fold_expr_opt row for {folder_name}"))
    })?;
    let row = bodies.get(&row_path).expect("just resolved");
    let fold = sem_expr_fold_shape_of(row, bodies).map_err(FoldWrapDecline::FoldRow)?;
    if fold.folder != folder_name {
        return Err(FoldWrapDecline::FolderMismatch(format!(
            "wrapper builds {folder_name} but the row recognizes {}",
            fold.folder
        )));
    }

    // Field map: aggregate form reads the wrapper's own operands; ctor form
    // composes the ctor fingerprint map with the wrapper's actuals.
    let field_srcs: Vec<LaunchFieldSrc> = if let Some(srcs) = ctor_srcs {
        srcs.into_iter()
            .map(|s| match s {
                LaunchFieldSrc::Param(ctor_arg) => {
                    // ctor param `i` ← wrapper actual `ctor_arg_map[i-1]`.
                    match ctor_arg_map.get(ctor_arg - 1) {
                        Some(Operand::Copy(p) | Operand::Move(p)) => {
                            Ok(LaunchFieldSrc::Param(p.local))
                        }
                        Some(Operand::Constant(ConstValue::Uint(v, _))) => {
                            Ok(LaunchFieldSrc::Lit(*v))
                        }
                        _ => Err(FoldWrapDecline::FolderMismatch("ctor actual map broke".into())),
                    }
                }
                other => Ok(other),
            })
            .collect::<R<Vec<_>>>()?
    } else {
        let mut srcs = Vec::with_capacity(agg_ops.len());
        for (i, op) in agg_ops.iter().enumerate() {
            if i == fold.memo_field {
                // The memo field must consume the fresh memo BY MOVE.
                let ok = matches!(op, Operand::Move(p)
                    if p.projections.is_empty() && Some(p.local) == memo_local);
                if !ok {
                    return Err(FoldWrapDecline::FolderMismatch(
                        "memo field is not the fresh FoldMemo::default() move".into(),
                    ));
                }
                srcs.push(LaunchFieldSrc::Memo);
                continue;
            }
            match op {
                Operand::Copy(p) | Operand::Move(p)
                    if p.projections.is_empty() && (2..=body.arg_count).contains(&p.local) =>
                {
                    srcs.push(LaunchFieldSrc::Param(p.local));
                }
                Operand::Constant(ConstValue::Uint(v, _)) => srcs.push(LaunchFieldSrc::Lit(*v)),
                _ => {
                    return Err(FoldWrapDecline::FolderMismatch(
                        "folder field operand is not a param/literal/fresh memo".into(),
                    ));
                }
            }
        }
        srcs
    };
    // The memo position must agree with the recognized row.
    if field_srcs.get(fold.memo_field) != Some(&LaunchFieldSrc::Memo)
        || field_srcs.iter().filter(|s| matches!(s, LaunchFieldSrc::Memo)).count() != 1
    {
        return Err(FoldWrapDecline::FolderMismatch(
            "memo field position disagrees with the recognized row".into(),
        ));
    }
    // Depth family: record d0 (the operand feeding the sole mutable field).
    let d0 = if let Some(d) = &fold.depth {
        match field_srcs.get(d.depth_field) {
            Some(s @ (LaunchFieldSrc::Param(_) | LaunchFieldSrc::Lit(_))) => Some(*s),
            _ => {
                return Err(FoldWrapDecline::FolderMismatch(
                    "depth field source is not a param/literal".into(),
                ));
            }
        }
    } else {
        None
    };

    Ok(SemFoldLaunch { folder: folder_name, row_path, fold, zero_guard, field_srcs, d0, ctor })
}

// ===========================================================================
// The ADT delegate recognizer (option (a) — registry + TExpr transport)
// ===========================================================================

/// Recognize the ADT-returning pure-delegate shape: exactly one call, callee
/// resolved EXACTLY in the certified registry, `_0` written only by the call,
/// every actual a bare parameter copy or a scalar literal, empty linear
/// epilogue. Fail-closed with NAMED declines.
pub fn sem_adt_delegate_of(
    func: &VerifiableFunction,
    callees: &std::collections::BTreeMap<String, crate::mirsem::CalleeFact>,
) -> Result<SemAdtDelegate, FoldWrapDecline> {
    use crate::trustir_anchor::IrOperand;
    let body = &func.body;
    if callees.is_empty() {
        return Err(FoldWrapDecline::CalleeUnresolved("empty certified registry".into()));
    }
    if adt_name(&body.return_ty) != Some(EXPR_NAME) {
        return Err(FoldWrapDecline::SignatureUnsupported(format!(
            "{} does not return Expr",
            func.def_path
        )));
    }
    if body_has_unsupported(func) {
        return Err(FoldWrapDecline::DelegateShape("unsupported statements present".into()));
    }
    // No statements anywhere; exactly one Call; other terminators Goto/Return.
    let mut call = None;
    for b in &body.blocks {
        if !real_stmts(b).is_empty() {
            return Err(FoldWrapDecline::DelegateShape(format!("statements in bb{}", b.id.0)));
        }
        match &b.terminator {
            Terminator::Call { func: c, args, dest, target, atomic, is_foreign, .. } => {
                if call.is_some() {
                    return Err(FoldWrapDecline::DelegateShape("second call".into()));
                }
                if *is_foreign || atomic.is_some() {
                    return Err(FoldWrapDecline::DelegateShape("foreign/atomic callee".into()));
                }
                call = Some((c, args, dest, *target));
            }
            Terminator::Goto(_) | Terminator::Return => {}
            _ => return Err(FoldWrapDecline::DelegateShape("stray terminator".into())),
        }
    }
    let Some((callee, args, dest, target)) = call else {
        return Err(FoldWrapDecline::DelegateShape("no call".into()));
    };
    if !is_local(dest, 0) {
        return Err(FoldWrapDecline::DelegateShape("call dest is not bare _0".into()));
    }
    let Some(target) = target else {
        return Err(FoldWrapDecline::DelegateShape("diverging call".into()));
    };
    // Linear Goto-only path from the call to the unique Return.
    let mut rets = body.blocks.iter().filter(|b| matches!(b.terminator, Terminator::Return));
    let ret_block =
        rets.next().ok_or_else(|| FoldWrapDecline::DelegateShape("no return block".into()))?;
    if rets.next().is_some() {
        return Err(FoldWrapDecline::DelegateShape("multiple return blocks".into()));
    }
    let mut cur = target;
    let mut steps = 0usize;
    while cur != ret_block.id {
        let blk = block(body, cur)
            .ok_or_else(|| FoldWrapDecline::DelegateShape("broken return spine".into()))?;
        match &blk.terminator {
            Terminator::Goto(t) => cur = *t,
            _ => return Err(FoldWrapDecline::DelegateShape("non-linear return spine".into())),
        }
        steps += 1;
        if steps > body.blocks.len() {
            return Err(FoldWrapDecline::DelegateShape("cyclic return spine".into()));
        }
    }
    if callee == &func.def_path {
        return Err(FoldWrapDecline::DelegateShape("self delegation".into()));
    }
    // Resolve EXACTLY in the certified registry (no suffix guessing).
    let Some((key, fact)) = callees.get_key_value(callee.as_str()) else {
        return Err(FoldWrapDecline::CalleeUnresolved(callee.clone()));
    };
    let callee_id = callees
        .keys()
        .position(|k| k == key)
        .and_then(|i| u64::try_from(i).ok())
        .ok_or_else(|| FoldWrapDecline::CalleeUnresolved("registry index".into()))?;
    if fact.arg_count != args.len() {
        return Err(FoldWrapDecline::CalleeMismatch(format!(
            "arity: call passes {}, registry declares {}",
            args.len(),
            fact.arg_count
        )));
    }
    // The callee's precondition must be KNOWN EMPTY (these wrappers declare
    // none); a declared/unparsed requires fails closed.
    match &fact.requires {
        Some(reqs) if reqs.is_empty() => {}
        _ => {
            return Err(FoldWrapDecline::CalleeMismatch(
                "callee declares/carries an unestablished requires".into(),
            ));
        }
    }
    if args.is_empty() {
        return Err(FoldWrapDecline::DelegateShape("no actuals".into()));
    }
    // Every actual: bare param copy (entry-time; reassignment-gated) or a
    // scalar integer literal.
    let mut ir_args = Vec::with_capacity(args.len());
    for a in args {
        match a {
            Operand::Copy(p) | Operand::Move(p)
                if p.projections.is_empty() && (1..=body.arg_count).contains(&p.local) =>
            {
                if crate::mirsem::param_reassigned_by_stmt(body, p.local) {
                    return Err(FoldWrapDecline::DelegateShape(format!(
                        "parameter _{} reassigned before the delegate call",
                        p.local
                    )));
                }
                ir_args.push(IrOperand::Var(u64::try_from(p.local - 1).unwrap_or(u64::MAX)));
            }
            Operand::Constant(ConstValue::Uint(v, _)) => {
                let Ok(c) = i128::try_from(*v) else {
                    return Err(FoldWrapDecline::DelegateShape("literal overflow".into()));
                };
                ir_args.push(IrOperand::Const(c));
            }
            Operand::Constant(ConstValue::Int(v)) => ir_args.push(IrOperand::Const(*v)),
            _ => {
                return Err(FoldWrapDecline::DelegateShape(
                    "actual is not a bare param/scalar literal".into(),
                ));
            }
        }
    }
    Ok(SemAdtDelegate { callee: key.clone(), callee_id, args: ir_args })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The decline names are stable identifiers (census/report keys).
    #[test]
    fn decline_names_are_stable() {
        assert_eq!(
            FoldWrapDecline::SignatureUnsupported(String::new()).name(),
            "fold_wrap::signature_unsupported"
        );
        assert_eq!(FoldWrapDecline::LaunchShape(String::new()).name(), "fold_wrap::launch_shape");
        assert_eq!(FoldWrapDecline::GuardShape(String::new()).name(), "fold_wrap::guard_shape");
        assert_eq!(
            FoldWrapDecline::FolderMismatch(String::new()).name(),
            "fold_wrap::folder_mismatch"
        );
        assert_eq!(FoldWrapDecline::DriverDrift(String::new()).name(), "fold_wrap::driver_drift");
        assert_eq!(
            FoldWrapDecline::DelegateShape(String::new()).name(),
            "fold_wrap::delegate_shape"
        );
        assert_eq!(
            FoldWrapDecline::CalleeUnresolved(String::new()).name(),
            "fold_wrap::callee_unresolved"
        );
        assert_eq!(
            FoldWrapDecline::CalleeMismatch(String::new()).name(),
            "fold_wrap::callee_mismatch"
        );
        // The forwarded fold decline keeps ITS name (no re-wrapping).
        assert_eq!(
            FoldWrapDecline::FoldRow(ExprFoldDecline::MissingCoMember(String::new())).name(),
            "missing_co_member"
        );
    }
}
