// Trust: M4 v0 — the trace planner (design §4.2). An untrusted second
// interpreter of the trust-ir semantics: it mirrors `Eval.lean`'s
// `stepNWithContext` at VISIT granularity (one block-visit per step, exactly
// the granularity `bindBlockParams`/`bindInstrResultDests` operate at —
// `first-party/trust-ir/lean/trust_ir-semantics/TrustIr/Semantics/Eval.lean:52,94,140,310`),
// computing the per-visit `(pc, args, state, nextValueId)` trace that
// `emit.rs` renders into Lean.
//
// NOT TRUSTED (design §2, requirement 3 — "Trust story"): this planner can
// be wrong. A wrong trace/state produces a per-visit Lean statement that
// does not typecheck (`rfl` fails to close the goal) — pinned, not silently
// accepted (`gate.rs`). Nothing here is ever taken on faith by the gate;
// every statement this module computes is independently kernel-rechecked.
//
// I_MAX = 1 (envelope E4) gives the planner one large simplification: an
// instruction's operands can only be BLOCK PARAMS (there is no earlier
// same-block instruction to reference), and a terminator/branch-arg
// reference is either a param or THIS block's one instruction's own dest.
// So there is never a chain of pending values to thread — at most one.
//
// PLANNER-SEMANTICS DRIFT (design risk 6): any change to `Eval.lean`'s bump
// law, dest binding, or frame handling silently invalidates this file until
// the next gate run pins every generated arm. That failure is loud and safe
// (never silent), but it makes trust-ir semantics changes and this file a
// coupled edit surface.

use std::collections::BTreeMap;

use super::envelope::{self, EnvelopeError};
use super::spec::{
    ArgSpec, BinOpLit, CfgFamilySpec, ComposeLevel, InstSpec, TermSpec, TyLit, ValueLit,
};

/// A value the planner can name in Lean without forcing any `semIntBinOp`
/// reduction: either a ground literal or a symbolic identifier bound at the
/// theorem head.
#[derive(Debug, Clone, Copy)]
pub enum Known {
    Ground(ValueLit),
    Sym(&'static str),
}

impl Known {
    /// Render as a Lean `TrustIr.Value.*` literal at the given type.
    pub fn as_value_lean(self, ty: TyLit) -> String {
        match self {
            Known::Ground(v) => v.lean(),
            Known::Sym(ident) => match ty {
                TyLit::Bool => format!("TrustIr.Value.bool {ident}"),
                _ => {
                    let w = ty.width().unwrap_or(64);
                    format!("TrustIr.Value.int {w} {ident}")
                }
            },
        }
    }

    /// Render the bare scalar (no `Value.*` wrapper) — used inside
    /// arithmetic expressions such as `Int.add v_l v_r`. Negative literals
    /// are parenthesized for the same reason as [`ValueLit::lean`].
    pub fn as_scalar_lean(self) -> String {
        match self {
            Known::Ground(ValueLit::Int { value, .. }) if value < 0 => format!("({value})"),
            Known::Ground(ValueLit::Int { value, .. }) => value.to_string(),
            Known::Ground(ValueLit::Bool(b)) => b.to_string(),
            Known::Sym(ident) => ident.to_string(),
        }
    }
}

/// This block's one instruction (if any), resolved against its params.
/// `folded = Some(k)` means both operands were ground and the planner
/// constant-folded the result — the visit stays a plain `rfl` (T1/T2).
/// `folded = None` means at least one operand is symbolic — the visit needs
/// the chain+connect split (T3/T4).
#[derive(Debug, Clone, Copy)]
pub struct ResolvedInst {
    pub op: BinOpLit,
    pub width: u32,
    pub lhs: Known,
    pub rhs: Known,
    /// The AUTHOR-PINNED `bodyResultDests` id (`BlockSpec::dests`) — fixed
    /// per block-body-position, stable across every revisit of this block.
    pub dest: u32,
    /// The PLANNER-COMPUTED fresh id `Sem.bindFresh` allocates THIS visit
    /// (the global `nextValueId` counter, which never resets between
    /// visits — see the double-set law below). Equal to `dest` on a
    /// block's first-ever visit when the spec author pins `dest` to that
    /// natural value (v0's two registered families do this); may differ on
    /// a later revisit of the SAME block (mirrors DATALOOP's `mk 5/6` vs
    /// pinned `mk 3/4`) — the planner still emits BOTH `.set`s always (W4).
    pub fresh_id: u32,
    pub folded: Option<Known>,
}

/// A value flowing into a `Return`/`Br` — either directly known (carrying
/// the type it must render at — a param's declared `TyLit`, or a width
/// synthesized from the instruction that produced it), or a reference to
/// this SAME visit's own pending instruction result (only meaningful when
/// `folded.is_none()`).
#[derive(Debug, Clone, Copy)]
pub enum RetVal {
    Known(Known, TyLit),
    InstResult,
}

/// What a visit ends in.
#[derive(Debug)]
pub enum VisitOutcome {
    Return(Vec<RetVal>),
    Br { target_pc: usize, args: Vec<RetVal> },
}

/// Whether a visit is a plain `rfl` (T1/T2) or needs the chain+connect split
/// (T3/T4), crossed with terminal/non-terminal. v0's two registered families
/// exercise `GroundRflTerminal` and `SymbolicCoreTerminal` (the hand-written
/// stepblock arm's exact shape — the mechanical-regeneration target).
/// `GroundRflNonTerminal`/`SymbolicCoreNonTerminal` (multi-visit `Br`
/// chains) are implemented and unit-tested at the planner level but not yet
/// exercised by a registered, gate-run family — see the landing report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VisitShape {
    GroundRflTerminal,
    GroundRflNonTerminal,
    SymbolicCoreTerminal,
    SymbolicCoreNonTerminal,
}

/// One planned block-visit.
#[derive(Debug)]
pub struct Visit {
    /// 1-based visit index (`k` in the design's notation).
    pub k: usize,
    /// The block this visit executes.
    pub pc: usize,
    /// Args passed into this visit's block params (parallel to
    /// `blocks[pc].params`).
    pub args: Vec<Known>,
    /// `true` for k = 1 (pre-state is `TrustIr.MachineState.empty`);
    /// `false` for k > 1 (pre-state is the previous visit's named
    /// post-state).
    pub pre_state_is_empty: bool,
    pub inst: Option<ResolvedInst>,
    pub outcome: VisitOutcome,
    pub shape: VisitShape,
    /// This visit's POST-state `nextValueId` (`bindBlockParams`'s bump law,
    /// then — if an instruction ran — `bindFresh`'s `+1` then
    /// `bindInstrResultDests`'s `max(_, dest.index+1)` bump).
    pub next_value_id: u32,
}

/// The full compiled plan for one family: every visit, in order, plus the
/// symbolic identifiers bound at every per-visit theorem's head (the
/// family's `entry_args` that are `ArgSpec::Symbolic`).
#[derive(Debug)]
pub struct FamilyPlan {
    pub spec: &'static CfgFamilySpec,
    pub symbolic_idents: Vec<(&'static str, TyLit)>,
    pub visits: Vec<Visit>,
    pub compose: ComposeLevel,
}

fn arg_to_known(a: ArgSpec) -> Known {
    match a {
        ArgSpec::Ground(v) => Known::Ground(v),
        ArgSpec::Symbolic { ident, .. } => Known::Sym(ident),
    }
}

/// Compile a [`CfgFamilySpec`] into a [`FamilyPlan`], or refuse per the
/// static envelope (E1-E9, `envelope.rs`). This is the ONE entry point
/// `gate.rs` calls; a registered family's refusal here is a hard
/// `BridgeGateError` (never a silently smaller family).
pub fn plan_family(spec: &'static CfgFamilySpec) -> Result<FamilyPlan, EnvelopeError> {
    let compose = envelope::check_claims(spec.name, spec.claims)?;

    if spec.entry >= spec.blocks.len() {
        return Err(EnvelopeError::UndefinedEntry {
            family: spec.name,
            entry: spec.entry,
            len: spec.blocks.len(),
        });
    }
    for (i, b) in spec.blocks.iter().enumerate() {
        envelope::check_block_shape(spec.name, i, b)?;
    }

    let symbolic_idents: Vec<(&'static str, TyLit)> = spec
        .entry_args
        .iter()
        .filter_map(|a| match a {
            ArgSpec::Symbolic { ident, ty } => Some((*ident, *ty)),
            ArgSpec::Ground(_) => None,
        })
        .collect();

    let mut visits: Vec<Visit> = Vec::new();
    let mut pc = spec.entry;
    let mut args: Vec<Known> = spec.entry_args.iter().copied().map(arg_to_known).collect();
    let mut k = 1usize;
    // `nextValueId` is a GLOBAL counter that never resets between visits —
    // even a revisited block allocates fresh ids from wherever the trace
    // left off (`bindBlockParams`'s bump law starts from the CURRENT
    // state's `nextValueId`, Eval.lean:60-62).
    let mut next_value_id: u32 = 0;

    loop {
        envelope::check_visit_budget(spec.name, k)?;
        let block = &spec.blocks[pc];
        if args.len() != block.params.len() {
            return Err(EnvelopeError::ParamArityMismatch {
                family: spec.name,
                block: pc,
                given: args.len(),
                params: block.params.len(),
            });
        }

        let mut param_vals: BTreeMap<u32, Known> = BTreeMap::new();
        for ((vid, _ty), a) in block.params.iter().zip(args.iter()) {
            param_vals.insert(*vid, *a);
        }
        // bindBlockParams's bump law: max over params of (index+1), folded
        // from the CURRENT nextValueId (never from 0).
        let post_params_nvid =
            block.params.iter().fold(next_value_id, |acc, (vid, _)| acc.max(*vid + 1));

        // Resolve the block's one instruction, if any (E4: at most one).
        let mut post_inst_nvid = post_params_nvid;
        let inst: Option<ResolvedInst> = match (block.insts.first(), block.dests.first()) {
            (Some(InstSpec::BinOp { op, ty, lhs, rhs }), Some(dest)) => {
                let lhs_k = *param_vals.get(lhs).ok_or(EnvelopeError::UndefinedValueId {
                    family: spec.name,
                    block: pc,
                    value_id: *lhs,
                })?;
                let rhs_k = *param_vals.get(rhs).ok_or(EnvelopeError::UndefinedValueId {
                    family: spec.name,
                    block: pc,
                    value_id: *rhs,
                })?;
                let width = ty.width().unwrap_or(64);
                let folded = match (lhs_k, rhs_k) {
                    (
                        Known::Ground(ValueLit::Int { value: l, .. }),
                        Known::Ground(ValueLit::Int { value: r, .. }),
                    ) => Some(Known::Ground(ValueLit::Int { width, value: op.fold(l, r) })),
                    _ => None,
                };
                // Sem.bindFresh: fresh id = current nextValueId, then +1.
                let fresh_id = post_params_nvid;
                // bindInstrResultDests -> bindResultDests: max(_, dest+1).
                post_inst_nvid = (post_params_nvid + 1).max(dest + 1);
                Some(ResolvedInst {
                    op: *op,
                    width,
                    lhs: lhs_k,
                    rhs: rhs_k,
                    dest: *dest,
                    fresh_id,
                    folded,
                })
            }
            (None, None) => None,
            _ => unreachable!("check_block_shape already asserted insts.len() == dests.len()"),
        };
        next_value_id = post_inst_nvid;
        let pending = inst.is_some_and(|i| i.folded.is_none());

        let resolve = |id: u32| -> Result<RetVal, EnvelopeError> {
            if let Some(i) = inst {
                if i.dest == id {
                    return Ok(match i.folded {
                        Some(k) => RetVal::Known(k, TyLit::from_width(i.width)),
                        None => RetVal::InstResult,
                    });
                }
            }
            let ty = block.params.iter().find(|(vid, _)| *vid == id).map(|(_, ty)| *ty).ok_or(
                EnvelopeError::UndefinedValueId { family: spec.name, block: pc, value_id: id },
            )?;
            param_vals.get(&id).map(|k| RetVal::Known(*k, ty)).ok_or(
                EnvelopeError::UndefinedValueId { family: spec.name, block: pc, value_id: id },
            )
        };

        match block.term {
            TermSpec::Return(ids) => {
                let ret = ids.iter().map(|id| resolve(*id)).collect::<Result<Vec<_>, _>>()?;
                visits.push(Visit {
                    k,
                    pc,
                    args: args.clone(),
                    pre_state_is_empty: k == 1,
                    inst,
                    outcome: VisitOutcome::Return(ret),
                    shape: if pending {
                        VisitShape::SymbolicCoreTerminal
                    } else {
                        VisitShape::GroundRflTerminal
                    },
                    next_value_id,
                });
                break;
            }
            TermSpec::Br { target, args: arg_ids } => {
                if target >= spec.blocks.len() {
                    return Err(EnvelopeError::UndefinedBlockTarget {
                        family: spec.name,
                        block: pc,
                        target,
                        len: spec.blocks.len(),
                    });
                }
                let next = arg_ids.iter().map(|id| resolve(*id)).collect::<Result<Vec<_>, _>>()?;
                let shape = if pending {
                    VisitShape::SymbolicCoreNonTerminal
                } else {
                    VisitShape::GroundRflNonTerminal
                };
                visits.push(Visit {
                    k,
                    pc,
                    args: args.clone(),
                    pre_state_is_empty: k == 1,
                    inst,
                    outcome: VisitOutcome::Br { target_pc: target, args: next.clone() },
                    shape,
                    next_value_id,
                });
                // Next visit's incoming args: `RetVal::InstResult` resolves
                // to the bound `result`/`Int.op l r` ident, which is only
                // meaningful inside THIS visit's own chain/connect Lean —
                // by the time we cross to the next visit it must already be
                // a `Known` (v0 does not thread an unresolved pending value
                // across a block boundary as a fresh symbolic name; the
                // connect theorem always resolves it to `op.value_fn(l, r)`
                // first). Represent it here as a fresh symbolic scalar named
                // after the op, so downstream visits still type-check
                // structurally even though v0 never registers a family that
                // exercises this path end-to-end.
                args = next
                    .into_iter()
                    .map(|r| match r {
                        RetVal::Known(k, _) => k,
                        RetVal::InstResult => Known::Sym("result"),
                    })
                    .collect();
                pc = target;
                k += 1;
            }
        }
    }

    Ok(FamilyPlan { spec, symbolic_idents, visits, compose })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg_family::spec::{
        ArgSpec, BinOpLit, BlockSpec, CfgFamilySpec, ClaimSpec, InstSpec, ModeSlice, TyLit,
        ValueLit,
    };
    use crate::cfg_family::{GEN_BLOCK_ADD, GEN_BLOCK_ADD_SYM};

    #[test]
    fn ground_family_folds_to_the_expected_literal_trace() {
        let plan = plan_family(&GEN_BLOCK_ADD).expect("gen_block_add must plan");
        assert_eq!(plan.visits.len(), 1);
        let v = &plan.visits[0];
        assert_eq!(v.shape, VisitShape::GroundRflTerminal);
        assert_eq!(v.next_value_id, 3, "2 params bump to 2, BinOp bumps to 3");
        let inst = v.inst.expect("gen_block_add has one BinOp");
        assert_eq!(inst.fresh_id, 2, "fresh id = nextValueId right after params (2)");
        assert_eq!(inst.dest, 2, "spec pins the dest to coincide with the natural fresh id");
        match inst.folded {
            Some(Known::Ground(ValueLit::Int { width: 8, value: 7 })) => {}
            other => panic!("expected folded Add(3,4) = 7 at width 8, got {other:?}"),
        }
    }

    #[test]
    fn symbolic_family_leaves_the_binop_pending() {
        let plan = plan_family(&GEN_BLOCK_ADD_SYM).expect("gen_block_add_sym must plan");
        assert_eq!(plan.visits.len(), 1);
        let v = &plan.visits[0];
        assert_eq!(v.shape, VisitShape::SymbolicCoreTerminal);
        assert_eq!(plan.symbolic_idents, vec![("v_l", TyLit::I8), ("v_r", TyLit::I8)]);
        let inst = v.inst.expect("gen_block_add_sym has one BinOp");
        assert!(inst.folded.is_none(), "a symbolic operand must NOT constant-fold");
        assert_eq!(inst.op, BinOpLit::Add);
        assert_eq!(inst.dest, 2);
        assert_eq!(inst.fresh_id, 2);
        assert_eq!(v.next_value_id, 3);
    }

    /// E3: a 7-block unconditional `Br` chain (7 visits) exceeds
    /// `K_MAX = 6` and must refuse — never silently truncate the trace at
    /// visit 6.
    #[test]
    fn seven_block_br_chain_exceeds_visit_budget() {
        const B: BlockSpec =
            BlockSpec { params: &[], insts: &[], dests: &[], term: TermSpec::Return(&[]) };
        const CHAIN: [BlockSpec; 7] = [
            BlockSpec { term: TermSpec::Br { target: 1, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 2, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 3, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 4, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 5, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 6, args: &[] }, ..B },
            B,
        ];
        const SPEC: CfgFamilySpec = CfgFamilySpec {
            name: "plan_test_7chain",
            blocks: &CHAIN,
            entry: 0,
            entry_args: &[],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        let err = plan_family(&SPEC).expect_err("7 visits must exceed K_MAX = 6 (E3)");
        assert!(matches!(
            err,
            EnvelopeError::VisitBudgetExceeded { family: "plan_test_7chain", needed: 7 }
        ));
    }

    /// A 6-block chain (exactly `K_MAX` visits) must plan successfully —
    /// the budget is inclusive, not off-by-one.
    #[test]
    fn six_block_br_chain_is_within_budget() {
        const B: BlockSpec =
            BlockSpec { params: &[], insts: &[], dests: &[], term: TermSpec::Return(&[]) };
        const CHAIN: [BlockSpec; 6] = [
            BlockSpec { term: TermSpec::Br { target: 1, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 2, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 3, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 4, args: &[] }, ..B },
            BlockSpec { term: TermSpec::Br { target: 5, args: &[] }, ..B },
            B,
        ];
        const SPEC: CfgFamilySpec = CfgFamilySpec {
            name: "plan_test_6chain",
            blocks: &CHAIN,
            entry: 0,
            entry_args: &[],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        let plan = plan_family(&SPEC).expect("6 visits == K_MAX must be accepted");
        assert_eq!(plan.visits.len(), 6);
    }

    #[test]
    fn undefined_value_id_refuses() {
        const SPEC: CfgFamilySpec = CfgFamilySpec {
            name: "plan_test_undef",
            blocks: &[BlockSpec {
                params: &[(0, TyLit::I8)],
                insts: &[],
                dests: &[],
                // References ValueId 9, which is not a param and there is
                // no instruction to produce it.
                term: TermSpec::Return(&[9]),
            }],
            entry: 0,
            entry_args: &[ArgSpec::Ground(ValueLit::Int { width: 8, value: 1 })],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        let err = plan_family(&SPEC).expect_err("returning an undefined SSA value must refuse");
        assert!(matches!(err, EnvelopeError::UndefinedValueId { value_id: 9, .. }));
    }

    #[test]
    fn param_arity_mismatch_refuses() {
        const SPEC: CfgFamilySpec = CfgFamilySpec {
            name: "plan_test_arity",
            blocks: &[BlockSpec {
                params: &[(0, TyLit::I8), (1, TyLit::I8)],
                insts: &[InstSpec::BinOp { op: BinOpLit::Add, ty: TyLit::I8, lhs: 0, rhs: 1 }],
                dests: &[2],
                term: TermSpec::Return(&[2]),
            }],
            entry: 0,
            // Only ONE arg for a two-param entry block.
            entry_args: &[ArgSpec::Ground(ValueLit::Int { width: 8, value: 1 })],
            claims: &[ClaimSpec::BoundedRun { compose: ComposeLevel::C0 }],
            mode: ModeSlice::AllModes,
        };
        let err = plan_family(&SPEC).expect_err("arg/param arity mismatch must refuse");
        assert!(matches!(err, EnvelopeError::ParamArityMismatch { given: 1, params: 2, .. }));
    }
}
