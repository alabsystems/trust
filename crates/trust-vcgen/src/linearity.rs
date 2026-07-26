// trust-vcgen/linearity.rs: ownership linearity (`must-consume`) verification.
//
// The trust-vc (ownership) lane. Verifies an owned by-value parameter is MOVED
// OUT (consumed) on every path to a `Return`, rather than silently dropped — a
// linearity / no-leak property that Rust's AFFINE type system does NOT enforce
// (an owned value may simply be dropped). Useful for resource/handle types that
// must be explicitly handed off (committed, returned to a pool, closed) rather
// than implicitly destroyed.
//
// The verdict is a sound forward reachability over the MIR move dataflow. A consume is a
// genuine move of the parameter out of its slot AND that does not merely relocate the
// resource into a local the function then drops: `param_leaks` catches a path that never
// moves the parameter, and `param_resource_dropped` catches a move into a locally-DROPPED
// tuple/array/binding (a silent drop the slot-liveness view alone would mis-credit as
// `Consumed` — found by the adversarial false-proof hunt). An unmodeled move position can
// at worst yield a (sound) false `Leaked`, never a false `Consumed`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    BasicBlock, BlockId, Operand, Rvalue, Statement, Terminator, VerifiableBody, VerifiableFunction,
};

/// Outcome of the `#[trust::must_consume]` linearity check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MustConsume {
    /// The owned parameter is moved out on every path to `Return` (consumed).
    Consumed,
    /// A path to `Return` never moves the parameter — it is dropped (a leak).
    /// Carries the parameter's local index.
    Leaked { param: usize },
    /// Not analyzable as a single owned-parameter function (sound: no verdict).
    NotApplicable,
}

/// Whether `op` is a whole-value consume of `local` — a `Move(local)` OR a
/// `Copy(local)` with no projection. For a NON-Copy owned type (the only kind
/// `#[trust::must_consume]` is meaningful on) the optimized MIR represents the
/// consuming LAST USE of a value as `Copy` (Copy and Move are equivalent at a
/// last use), so both must count; a *field* read `Copy(local.field)` carries a
/// projection and is correctly NOT a whole consume.
fn op_consumes(op: &Operand, local: usize) -> bool {
    matches!(
        op,
        Operand::Move(p) | Operand::Copy(p) if p.local == local && p.projections.is_empty()
    )
}

/// Whether any operand syntactically present in `rvalue` consumes `local`.
///
/// `Ref` / `AddressOf` / `Discriminant` / `Len` / `CopyForDeref` read a `Place`
/// by reference — they do NOT take it by value. Any consume position not modeled
/// here is conservatively treated as "not a consume", which can only report a
/// sound false `Leaked`, never a false `Consumed`.
fn rvalue_consumes(rvalue: &Rvalue, local: usize) -> bool {
    match rvalue {
        Rvalue::Use(op) | Rvalue::Cast(op, _) | Rvalue::Repeat(op, _) | Rvalue::UnaryOp(_, op) => {
            op_consumes(op, local)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            op_consumes(a, local) || op_consumes(b, local)
        }
        Rvalue::Aggregate(_, ops) => ops.iter().any(|o| op_consumes(o, local)),
        _ => false,
    }
}

/// Whether `block` consumes `local` (in any statement or its terminator).
///
/// CONSERVATIVE for soundness: if the block REASSIGNS `local`'s slot
/// (`Assign { place: local }`, e.g. a `mut` parameter), any consume of `local`
/// here is ambiguous — it might move the NEW value while the incoming parameter
/// was already overwritten (dropped). We then do NOT count it, so the parameter
/// stays live and a leak is soundly reported rather than a false `Consumed`
/// hiding the overwrite-drop.
fn block_moves(block: &BasicBlock, local: usize) -> bool {
    let reassigns = block.stmts.iter().any(|stmt| {
        matches!(stmt, Statement::Assign { place, .. }
            if place.local == local && place.projections.is_empty())
    });
    if reassigns {
        return false;
    }
    let stmt_move = block.stmts.iter().any(
        |stmt| matches!(stmt, Statement::Assign { rvalue, .. } if rvalue_consumes(rvalue, local)),
    );
    stmt_move
        || match &block.terminator {
            Terminator::Call { args, .. } => args.iter().any(|a| op_consumes(a, local)),
            Terminator::SwitchInt { discr, .. } => op_consumes(discr, local),
            _ => false,
        }
}

/// Successor block ids of a terminator (mirrors the CFG edges the verifier uses).
fn successors(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Goto(t) => vec![*t],
        Terminator::SwitchInt { targets, otherwise, .. } => {
            let mut s: Vec<BlockId> = targets.iter().map(|(_, t)| *t).collect();
            s.push(*otherwise);
            s
        }
        Terminator::Call { target: Some(t), .. } => vec![*t],
        Terminator::Assert { target, .. } | Terminator::Drop { target, .. } => vec![*target],
        Terminator::Opaque { targets, .. } => targets.clone(),
        _ => vec![],
    }
}

/// Predecessor map over the CFG.
fn predecessors(body: &VerifiableBody) -> FxHashMap<BlockId, Vec<BlockId>> {
    let mut preds: FxHashMap<BlockId, Vec<BlockId>> = FxHashMap::default();
    for block in &body.blocks {
        for succ in successors(&block.terminator) {
            preds.entry(succ).or_default().push(block.id);
        }
    }
    preds
}

/// Whether `local` (an owned-by-value parameter) is DROPPED on some path — there
/// is an entry→`Return` path that never consumes it.
///
/// SOUNDNESS — never a false "not leaked". Forward "parameter still un-moved at
/// block entry" reachability: live_in[entry]=true; live_in[B] = ⋁ preds P
/// (live_in[P] ∧ ¬consumes[P]) to a monotone fixpoint; any `Return` reached with
/// the parameter still live and unconsumed is a leak path. Missing a real consume
/// only ADDS live blocks → MORE (sound) leak reports, never removing one.
fn param_leaks(body: &VerifiableBody, local: usize) -> bool {
    let entry = body.blocks[0].id;
    let moves: FxHashMap<BlockId, bool> =
        body.blocks.iter().map(|b| (b.id, block_moves(b, local))).collect();
    let preds = predecessors(body);

    let mut live_in: FxHashMap<BlockId, bool> =
        body.blocks.iter().map(|b| (b.id, b.id == entry)).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for block in &body.blocks {
            if block.id == entry {
                continue;
            }
            let new = preds
                .get(&block.id)
                .into_iter()
                .flatten()
                .any(|p| *live_in.get(p).unwrap_or(&false) && !*moves.get(p).unwrap_or(&false));
            if new && !live_in[&block.id] {
                live_in.insert(block.id, true);
                changed = true;
            }
        }
    }

    body.blocks.iter().any(|block| {
        matches!(block.terminator, Terminator::Return) && live_in[&block.id] && !moves[&block.id]
    })
}

/// Whether `param`'s resource flows (through whole-local moves) into a local that is then
/// DROPPED — a SILENT DROP of the owned value even though its original slot was "moved
/// out". Moving the parameter into a local tuple/array/struct/binding that the function
/// then drops at scope end runs the resource's destructor INSIDE the function; that is NOT
/// a handoff, yet the slot-liveness check (`param_leaks`) counts the move-out as a consume
/// and wrongly reports `Consumed`. (Found by the adversarial false-proof hunt:
/// `fn f(t: Token) { let pair = (t, 0); }` PROVED must-consume while `t`'s `Drop` runs.)
///
/// Forward over-approximate taint: the param, plus any local a tainted value is whole-moved
/// into (Use/Aggregate/Cast/…, via `rvalue_consumes`). A `Drop { place }` of a tainted
/// local means the resource's destructor runs in-function. SOUNDNESS: the taint is
/// whole-local (ignores field structure and re-moves), so it can only report MORE drops →
/// more (sound) `Leaked`, never hide one; a genuine handoff (returning the value, or moving
/// it into a call argument) leaves no `Drop` of the tainted local.
fn param_resource_dropped(body: &VerifiableBody, param: usize) -> bool {
    let mut taint: FxHashSet<usize> = FxHashSet::default();
    taint.insert(param);
    let mut changed = true;
    while changed {
        changed = false;
        for block in &body.blocks {
            for stmt in &block.stmts {
                if let Statement::Assign { place, rvalue, .. } = stmt
                    && place.projections.is_empty()
                    && !taint.contains(&place.local)
                    && taint.iter().any(|&t| rvalue_consumes(rvalue, t))
                {
                    taint.insert(place.local);
                    changed = true;
                }
            }
        }
    }
    body.blocks.iter().any(
        |b| matches!(&b.terminator, Terminator::Drop { place, .. } if taint.contains(&place.local)),
    )
}

/// Whether the parameter `local` is an OWNED value whose linearity is meaningful
/// — a by-value ADT (struct/enum). Scalar (Copy) and reference/pointer parameters
/// are NOT subject to `must_consume`: a scalar is freely copied, a reference is
/// borrowed not owned. Checking only owned ADTs avoids flagging an unused `u32`.
fn param_is_owned(func: &VerifiableFunction, local: usize) -> bool {
    func.body
        .locals
        .iter()
        .find(|d| d.index == local)
        .is_some_and(|d| matches!(d.ty, trust_types::Ty::Adt { .. }))
}

/// Verify `#[trust::must_consume]`: every owned by-value (ADT) parameter is moved
/// out (consumed) on every path to `Return`. Reports the FIRST leaked parameter.
/// `NotApplicable` (sound: no verdict) when the function has no owned ADT
/// parameter to check.
#[must_use]
pub fn check_must_consume(func: &VerifiableFunction) -> MustConsume {
    let body = &func.body;
    if body.blocks.is_empty() {
        return MustConsume::NotApplicable;
    }
    let owned: Vec<usize> = (1..=body.arg_count).filter(|&p| param_is_owned(func, p)).collect();
    if owned.is_empty() {
        return MustConsume::NotApplicable;
    }
    for param in owned {
        // Leaked if EITHER the param is never moved out on some path to Return
        // (`param_leaks`), OR its resource is moved into a local that the function then
        // DROPS (`param_resource_dropped`) — a silent drop that the slot-liveness check
        // alone misses.
        if param_leaks(body, param) || param_resource_dropped(body, param) {
            return MustConsume::Leaked { param };
        }
    }
    MustConsume::Consumed
}

#[cfg(test)]
mod tests {
    use trust_types::*;

    use super::*;

    fn func_with(blocks: Vec<BasicBlock>, arg_count: usize) -> VerifiableFunction {
        VerifiableFunction {
            name: "f".into(),
            def_path: "f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals: vec![
                    LocalDecl { index: 0, ty: Ty::Unit, name: None },
                    // An owned ADT parameter (the kind `must_consume` applies to).
                    LocalDecl {
                        index: 1,
                        ty: Ty::Adt { adt_kind: None, layout: None, 
                            variants: Vec::new(),
                            name: "Token".into(),
                            fields: vec![],
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, },
                        name: Some("r".into()),
                    },
                    LocalDecl {
                        index: 2,
                        ty: Ty::Adt { adt_kind: None, layout: None, 
                            variants: Vec::new(),
                            name: "Token".into(),
                            fields: vec![],
                            disc_index_safe: false,
                            faithful_enum_repr: None, enum_layout: None, },
                        name: None,
                    },
                ],
                blocks,
                arg_count,
                return_ty: Ty::Unit,
            },
            contracts: vec![],
            preconditions: vec![],
            postconditions: vec![],
            spec: Default::default(),
        }
    }

    fn move_param_call() -> Statement {
        // a call statement isn't a Statement; use an assign that moves the param.
        Statement::Assign {
            place: Place::local(2),
            rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
            span: SourceSpan::default(),
        }
    }

    #[test]
    fn consumed_when_param_moved_before_return() {
        // bb0: _2 = move _1; return
        let func = func_with(
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![move_param_call()],
                terminator: Terminator::Return,
            }],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Consumed);
    }

    #[test]
    fn leaked_when_param_not_moved() {
        // bb0: return  (param never moved -> dropped)
        let func = func_with(
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Leaked { param: 1 });
    }

    #[test]
    fn leaked_when_one_branch_drops_param() {
        // bb0: switch -> bb1 (moves _1), bb2 (does not move _1); both return.
        let func = func_with(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Constant(ConstValue::Bool(true)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![move_param_call()],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![], // leak: returns without moving _1
                    terminator: Terminator::Return,
                },
            ],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Leaked { param: 1 });
    }

    #[test]
    fn consumed_when_both_branches_move_param() {
        let func = func_with(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Constant(ConstValue::Bool(true)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![move_param_call()],
                    terminator: Terminator::Return,
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![move_param_call()],
                    terminator: Terminator::Return,
                },
            ],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Consumed);
    }

    #[test]
    fn consumed_when_moved_into_call_arg() {
        // bb0: call f(move _1) -> bb1; bb1: return
        let func = func_with(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "drop".into(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Consumed);
    }

    #[test]
    fn not_applicable_without_owned_param() {
        // A function whose only parameter is a scalar (Copy) is not subject to
        // must-consume — it declines (no owned ADT parameter to check).
        let mut func = func_with(
            vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: Terminator::Return }],
            1,
        );
        func.body.locals[1].ty = Ty::Int { width: 32, signed: false };
        assert_eq!(check_must_consume(&func), MustConsume::NotApplicable);
    }

    #[test]
    fn multi_param_reports_a_leaked_owned_param() {
        // Two owned ADT params: bb0 consumes _1 (move into _2's slot via a Use)
        // then returns — _2 is never consumed, so it leaks.
        let func = func_with(
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![move_param_call()], // moves _1
                terminator: Terminator::Return,
            }],
            2,
        );
        // _1 is consumed, _2 is not -> Leaked { param: 2 }.
        assert_eq!(check_must_consume(&func), MustConsume::Leaked { param: 2 });
    }

    #[test]
    fn multi_param_both_consumed_is_consumed() {
        // bb0: call sink2(move _1, move _2) -> bb1 (consumes BOTH, no reassign);
        // bb1: return.
        let func = func_with(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "sink2".into(),
                        args: vec![Operand::Move(Place::local(1)), Operand::Move(Place::local(2))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            2,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Consumed);
    }

    #[test]
    fn reassigned_param_then_consumed_is_leaked() {
        // T-SOUNDNESS: `_1 = move _2; sink(move _1)` overwrites the incoming _1
        // (dropping it) then consumes the NEW value. The incoming _1 leaked, so
        // we must NOT report Consumed for _1.
        let func = func_with(
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1), // reassigns the param _1
                        rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        func: "sink".into(),
                        args: vec![Operand::Move(Place::local(1))], // the NEW _1
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            1,
        );
        assert_eq!(check_must_consume(&func), MustConsume::Leaked { param: 1 });
    }
}
