// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The FORWARDING body shape (joint Rust+Lean cited lane, 2026-09-15): a Rust
//! function whose whole body is ONE call to another function with (some of)
//! its own parameters as the arguments, and nothing else —
//!
//! ```text
//! pub fn pb_max_r(lhs: u64, rhs: u64) -> u64 { pb_max(lhs, rhs) }
//! ```
//!
//! extracted as `bb0: _0 = <callee>(copy _1, copy _2) -> bb1; bb1: return`.
//!
//! This is an AFFIRMATIVE ALLOW-LIST, not a deny-list (CLAUDE.md, "a
//! RETURN-PATH walk that steps past a block must ALLOW-LIST what it steps
//! over"): every block, statement, terminator and operand the body may contain
//! is named below, and anything else refuses the whole body. The recognizer
//! establishes ONLY the shape. What the callee denotes is not its business —
//! the consumer (`admit_function_into`'s forwarding arm) resolves the callee's
//! def-path against the facet table's `KernelChecked` island admission, which
//! only the compiler's Clean-origin registry can have written.

use trust_types::{BlockId, Operand, Place, Rvalue, Statement, Terminator, VerifiableFunction};

/// One recognized forwarding call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IslandForwardingCall {
    /// The callee exactly as the extractor spelled it — the callee's def-path
    /// (`crate::pb_max`), which is the facet-table key the compiler records
    /// Clean-origin identity rows under.
    pub(crate) callee: String,
    /// For each CALLEE argument position, the 0-based SOURCE parameter that
    /// position receives. `f(rhs, lhs)` on `(lhs, rhs)` is `[1, 0]`. A parameter
    /// may appear more than once or not at all; the order is the call's actual
    /// argument order, never the signature's.
    pub(crate) arg_params: Vec<usize>,
}

/// Recognize the forwarding shape, or `None` for anything else.
///
/// Admitted body, and nothing more:
///  * exactly two blocks — the CALL block and the RETURN block;
///  * the call block's statements are only storage markers and at most one
///    plain copy/move of a parameter into a fresh temporary per temporary
///    (`_3 = copy _1`), which the argument reader resolves back to the
///    parameter; the call block's terminator is a non-atomic, non-foreign,
///    safe-signature `Call` whose destination is the unprojected return place
///    `_0` and whose continuation is the return block;
///  * every call argument is a copy/move of an unprojected parameter local or
///    of one such temporary — a constant, a projected place, or anything
///    computed refuses the body (a literal argument is a different shape with
///    its own carrier questions; this lane forwards, it does not build);
///  * the return block has no statements other than storage markers and its
///    terminator is `Return`.
///
/// A `TailCall`, a cleanup edge that lands in a third block, an `Assert`, a
/// `SwitchInt`, a projection anywhere, or a second write to `_0` all fall
/// outside the list and refuse.
pub(crate) fn recognize_island_forwarding_body(
    func: &VerifiableFunction,
) -> Option<IslandForwardingCall> {
    let body = &func.body;
    if body.blocks.len() != 2 || body.arg_count == 0 {
        return None;
    }
    let arg_count = body.arg_count;
    let is_param = |local: usize| (1..=arg_count).contains(&local);
    let unprojected =
        |place: &Place| -> Option<usize> { place.projections.is_empty().then_some(place.local) };
    // Find the one block whose terminator is the forwarding call; the other
    // must be the return block.
    let mut call_block: Option<&trust_types::BasicBlock> = None;
    let mut return_block: Option<&trust_types::BasicBlock> = None;
    for block in &body.blocks {
        match &block.terminator {
            Terminator::Call { .. } if call_block.is_none() => call_block = Some(block),
            Terminator::Return if return_block.is_none() => return_block = Some(block),
            _ => return None,
        }
    }
    let (call_block, return_block) = (call_block?, return_block?);
    // The return block may carry only storage markers.
    if !return_block.stmts.iter().all(|st| is_storage_marker(st)) {
        return None;
    }
    // Copy/move temporaries in the call block: `temp = copy/move param`, each
    // temporary written exactly once, never a parameter or the return place.
    let mut temp_of: Vec<(usize, usize)> = Vec::new(); // (temp local, source param idx)
    for st in &call_block.stmts {
        if is_storage_marker(st) {
            continue;
        }
        let Statement::Assign { place, rvalue, .. } = st else {
            return None;
        };
        let temp = unprojected(place)?;
        if temp == 0 || is_param(temp) || temp_of.iter().any(|(t, _)| *t == temp) {
            return None;
        }
        let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
            return None;
        };
        let src = unprojected(src)?;
        if !is_param(src) {
            return None;
        }
        temp_of.push((temp, src - 1));
    }
    let Terminator::Call {
        func: callee,
        args,
        dest,
        target,
        atomic,
        is_foreign,
        is_unsafe_sig,
        ..
    } = &call_block.terminator
    else {
        return None;
    };
    if atomic.is_some() || *is_foreign || *is_unsafe_sig || callee.is_empty() {
        return None;
    }
    if unprojected(dest)? != 0 {
        return None;
    }
    let BlockId(target) = (*target)?;
    if target != return_block.id.0 {
        return None;
    }
    let mut arg_params = Vec::with_capacity(args.len());
    for arg in args {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        let local = unprojected(place)?;
        if is_param(local) {
            arg_params.push(local - 1);
        } else if let Some((_, param)) = temp_of.iter().find(|(t, _)| *t == local) {
            arg_params.push(*param);
        } else {
            return None;
        }
    }
    Some(IslandForwardingCall { callee: callee.clone(), arg_params })
}

fn is_storage_marker(st: &Statement) -> bool {
    matches!(st, Statement::StorageLive(_) | Statement::StorageDead(_))
}

#[cfg(test)]
mod tests {
    use trust_types::{
        BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
        Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
    };

    use super::{IslandForwardingCall, recognize_island_forwarding_body};

    fn call(args: Vec<Operand>, dest: Place, target: Option<BlockId>) -> Terminator {
        Terminator::Call {
            func: "crate::callee".to_string(),
            args,
            dest,
            target,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: Default::default(),
            callee_identity: None,
            callee_key: None,
        }
    }

    fn func(arg_count: usize, blocks: Vec<BasicBlock>) -> VerifiableFunction {
        let mut locals = vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }];
        for i in 1..=arg_count + 2 {
            locals.push(LocalDecl { index: i, ty: Ty::u64(), name: None });
        }
        VerifiableFunction {
            name: "f".into(),
            def_path: "crate::f".into(),
            span: SourceSpan::default(),
            body: VerifiableBody {
                locals,
                blocks,
                arg_count,
                return_ty: Ty::u64(),
                datatype_defs: Default::default(),
            },
            contracts: Vec::new(),
            preconditions: Vec::new(),
            postconditions: Vec::new(),
            spec: Default::default(),
            tuple_layouts: Default::default(),
        }
    }

    fn ret_block(id: usize) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts: vec![], terminator: Terminator::Return }
    }

    fn copy(local: usize) -> Operand {
        Operand::Copy(Place::local(local))
    }

    #[test]
    fn recognizes_direct_and_temp_copied_forwarding_in_the_calls_argument_order() {
        // `_0 = callee(copy _2, copy _1)` — swapped arguments.
        let direct = func(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(vec![copy(2), copy(1)], Place::local(0), Some(BlockId(1))),
                },
                ret_block(1),
            ],
        );
        assert_eq!(
            recognize_island_forwarding_body(&direct),
            Some(IslandForwardingCall { callee: "crate::callee".into(), arg_params: vec![1, 0] })
        );
        // `_3 = copy _1; _4 = move _2; _0 = callee(move _3, move _4)` with storage markers.
        let via_temps = func(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::StorageLive(3),
                        Statement::Assign {
                            place: Place::local(3),
                            rvalue: Rvalue::Use(copy(1)),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Move(Place::local(2))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: call(
                        vec![Operand::Move(Place::local(3)), Operand::Move(Place::local(4))],
                        Place::local(0),
                        Some(BlockId(1)),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::StorageDead(3)],
                    terminator: Terminator::Return,
                },
            ],
        );
        assert_eq!(
            recognize_island_forwarding_body(&via_temps),
            Some(IslandForwardingCall { callee: "crate::callee".into(), arg_params: vec![0, 1] })
        );
        // Block order does not matter: return block first.
        let reordered = func(
            1,
            vec![
                ret_block(0),
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(vec![copy(1)], Place::local(0), Some(BlockId(0))),
                },
            ],
        );
        assert_eq!(
            recognize_island_forwarding_body(&reordered),
            Some(IslandForwardingCall { callee: "crate::callee".into(), arg_params: vec![0] })
        );
    }

    #[test]
    fn refuses_everything_outside_the_allow_list() {
        let one_call = |term: Terminator| {
            func(
                2,
                vec![BasicBlock { id: BlockId(0), stmts: vec![], terminator: term }, ret_block(1)],
            )
        };
        // A constant argument.
        assert!(
            recognize_island_forwarding_body(&one_call(call(
                vec![copy(1), Operand::Constant(ConstValue::Uint(1, 64))],
                Place::local(0),
                Some(BlockId(1))
            )))
            .is_none()
        );
        // A projected argument.
        assert!(
            recognize_island_forwarding_body(&one_call(call(
                vec![
                    Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] }),
                    copy(2)
                ],
                Place::local(0),
                Some(BlockId(1))
            )))
            .is_none()
        );
        // Destination is not `_0`.
        assert!(
            recognize_island_forwarding_body(&one_call(call(
                vec![copy(1), copy(2)],
                Place::local(3),
                Some(BlockId(1))
            )))
            .is_none()
        );
        // No continuation.
        assert!(
            recognize_island_forwarding_body(&one_call(call(
                vec![copy(1), copy(2)],
                Place::local(0),
                None
            )))
            .is_none()
        );
        // Continuation is not the return block.
        assert!(
            recognize_island_forwarding_body(&one_call(call(
                vec![copy(1), copy(2)],
                Place::local(0),
                Some(BlockId(0))
            )))
            .is_none()
        );
        // Atomic / foreign / unsafe-signature callee.
        for flip in 0..3 {
            let Terminator::Call {
                func: f,
                args,
                dest,
                target,
                span,
                unwind,
                callee_identity,
                callee_key,
                ..
            } = call(vec![copy(1), copy(2)], Place::local(0), Some(BlockId(1)))
            else {
                unreachable!()
            };
            let term = Terminator::Call {
                func: f,
                args,
                dest,
                target,
                span,
                atomic: (flip == 0).then_some(trust_types::AtomicOperation {
                    place: Place::local(1),
                    dest: None,
                    op_kind: trust_types::AtomicOpKind::Load,
                    ordering: trust_types::AtomicOrdering::SeqCst,
                    failure_ordering: None,
                    span: SourceSpan::default(),
                }),
                is_foreign: flip == 1,
                is_unsafe_sig: flip == 2,
                unwind,
                callee_identity,
                callee_key,
            };
            assert!(recognize_island_forwarding_body(&one_call(term)).is_none(), "flip {flip}");
        }
        // A third block.
        let three = func(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(vec![copy(1), copy(2)], Place::local(0), Some(BlockId(1))),
                },
                ret_block(1),
                ret_block(2),
            ],
        );
        assert!(recognize_island_forwarding_body(&three).is_none());
        // A computed statement in the call block, a temp written twice, a temp
        // sourced from a non-parameter, and a write to `_0` before the call.
        let with_stmt = |stmts: Vec<Statement>| {
            func(
                2,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts,
                        terminator: call(vec![copy(1), copy(2)], Place::local(0), Some(BlockId(1))),
                    },
                    ret_block(1),
                ],
            )
        };
        let assign = |place: usize, rv: Rvalue| Statement::Assign {
            place: Place::local(place),
            rvalue: rv,
            span: SourceSpan::default(),
        };
        assert!(
            recognize_island_forwarding_body(&with_stmt(vec![assign(
                3,
                Rvalue::BinaryOp(trust_types::BinOp::Add, copy(1), copy(2))
            )]))
            .is_none()
        );
        assert!(
            recognize_island_forwarding_body(&with_stmt(vec![
                assign(3, Rvalue::Use(copy(1))),
                assign(3, Rvalue::Use(copy(2))),
            ]))
            .is_none()
        );
        assert!(
            recognize_island_forwarding_body(&with_stmt(vec![assign(3, Rvalue::Use(copy(4)))]))
                .is_none()
        );
        assert!(
            recognize_island_forwarding_body(&with_stmt(vec![assign(0, Rvalue::Use(copy(1)))]))
                .is_none()
        );
        // A statement in the return block that is not a storage marker.
        let dirty_return = func(
            2,
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(vec![copy(1), copy(2)], Place::local(0), Some(BlockId(1))),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![assign(0, Rvalue::Use(copy(1)))],
                    terminator: Terminator::Return,
                },
            ],
        );
        assert!(recognize_island_forwarding_body(&dirty_return).is_none());
        // A nullary function has nothing to forward.
        assert!(
            recognize_island_forwarding_body(&func(
                0,
                vec![
                    BasicBlock {
                        id: BlockId(0),
                        stmts: vec![],
                        terminator: call(vec![], Place::local(0), Some(BlockId(1))),
                    },
                    ret_block(1),
                ]
            ))
            .is_none()
        );
    }
}
