// Tests for the recursion-SCC (mutual recursion) termination lane.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

use super::super::{RECURSION_DECREASES_UNSUPPORTED_KIND, check_termination};
use crate::{RecursionSccCall, RecursionSccContext, RecursionSccMeasure, VcgenContext};

const CALLER: &str = "test::rec_cs";

/// `fn rec_cs(n: u32) { if n == 0 { return } CALLEE(n - 1) }` in unoptimized
/// MIR shape: a checked decrement whose `Assert` guards the call block (bb3).
/// With `callee == CALLER` it is direct self recursion; with any other callee it
/// is one edge of a mutual recursion the direct-self lanes cannot see.
fn caller_calling(callee: &str, args_before_measure: Vec<Operand>) -> VerifiableFunction {
    let mut args = args_before_measure;
    args.push(Operand::Move(Place::local(4)));
    VerifiableFunction {
        name: "rec_cs".to_string(),
        def_path: CALLER.to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(0, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(1)],
                        }),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Sub),
                        target: BlockId(3),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::Use(Operand::Move(Place {
                            local: 3,
                            projections: vec![Projection::Field(0)],
                        })),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key(callee),
                        is_foreign: false,
                        func: callee.to_string(),
                        args,
                        dest: Place::local(0),
                        target: Some(BlockId(4)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn with_decreases_n(mut func: VerifiableFunction) -> VerifiableFunction {
    func.contracts.push(Contract {
        kind: ContractKind::Decreases,
        span: SourceSpan::default(),
        body: "n".to_string(),
    });
    func
}

fn n_measure() -> RecursionSccMeasure {
    RecursionSccMeasure::Param { position: 0, name: "n".to_string() }
}

/// The compiler's facts for a member whose bb3 calls `callee`.
fn scc_calling(
    callee: &str,
    own: RecursionSccMeasure,
    callee_measure: RecursionSccMeasure,
) -> RecursionSccContext {
    let mut scc = RecursionSccContext { own_measure: own, ..RecursionSccContext::default() };
    scc.calls.insert(
        3,
        RecursionSccCall { callee: callee.to_string(), is_self: callee == CALLER, callee_measure },
    );
    scc
}

fn termination_vcs(
    func: &VerifiableFunction,
    scc: Option<RecursionSccContext>,
) -> Vec<VerificationCondition> {
    let context = VcgenContext::for_function(func.def_path.clone()).with_recursion_scc(scc);
    let _scope = crate::enter_vcgen_context(&context);
    let mut vcs = Vec::new();
    check_termination(func, &mut vcs);
    vcs
}

fn recursion_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "recursion"))
        .collect()
}

fn recursion_markers(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == RECURSION_DECREASES_UNSUPPORTED_KIND)
        })
        .collect()
}

/// THE HAZARD, pinned from both sides. Without the compiler's SCC facts the
/// call into the other member of `a <-> b` mints no `[termination]` row at all
/// (that is how the pair used to verify and abort). With them, the call is
/// charged, and with no authored measure its row can never be proved.
#[test]
fn a_mutual_call_without_a_measure_is_charged_with_an_unprovable_row() {
    let func = caller_calling("test::other", vec![]);

    let without = termination_vcs(&func, None);
    assert!(recursion_rows(&without).is_empty(), "pre-fix shape: no row at all: {without:#?}");

    let scc = scc_calling("test::other", RecursionSccMeasure::Absent, RecursionSccMeasure::Absent);
    let vcs = termination_vcs(&func, Some(scc));
    let rows = recursion_rows(&vcs);
    assert_eq!(rows.len(), 1, "exactly the one SCC call is charged: {vcs:#?}");
    assert_eq!(
        rows[0].formula,
        Formula::Bool(true),
        "no measure: the violation is always satisfiable"
    );
    assert!(rows[0].contract_metadata.is_none(), "an unmeasured row discharges no authored clause");
    assert!(recursion_markers(&vcs).is_empty());
}

/// THE MEASURE RULE. A call into another member whose measure sits at the same
/// argument position yields EXACTLY the row a direct self call yields — the
/// callee's measure at the call's arguments against the caller's at entry, with
/// the same checked-chain binding, path guards and source-clause binding.
#[test]
fn a_measured_mutual_call_yields_the_self_call_row_with_the_callees_measure() {
    let self_rec = with_decreases_n(caller_calling(CALLER, vec![]));
    let self_rows = termination_vcs(&self_rec, None);
    let self_rows = recursion_rows(&self_rows);
    assert_eq!(self_rows.len(), 1, "control: the self lane binds the checked decrement");
    assert!(self_rows[0].contract_metadata.is_some());

    let mutual = with_decreases_n(caller_calling("test::other", vec![]));
    let scc = scc_calling(
        "test::other",
        n_measure(),
        RecursionSccMeasure::Param { position: 0, name: "m".to_string() },
    );
    let vcs = termination_vcs(&mutual, Some(scc));
    let rows = recursion_rows(&vcs);
    assert!(recursion_markers(&vcs).is_empty(), "{vcs:#?}");
    assert_eq!(rows.len(), 1);
    // `VerificationCondition` has no `PartialEq`; its `Debug` rendering covers
    // every field (kind, function, location, formula, contract metadata).
    assert_eq!(
        format!("{:?}", rows[0]),
        format!("{:?}", self_rows[0]),
        "the SCC row is the self row with the callee's measure"
    );
}

/// The callee's measure is read at the CALLEE's parameter position, not the
/// caller's: `other(7, n - 1)` with `decreases` on `other`'s second parameter
/// binds `n - 1` (the self row), while a measure on its first parameter binds
/// the constant `7`, which does not decrease.
#[test]
fn the_callee_measure_is_read_at_the_callees_argument_position() {
    let func = with_decreases_n(caller_calling(
        "test::other",
        vec![Operand::Constant(ConstValue::Uint(7, 32))],
    ));
    let self_rec = with_decreases_n(caller_calling(CALLER, vec![]));
    let self_rows = termination_vcs(&self_rec, None);
    let self_row = recursion_rows(&self_rows)[0].clone();

    let at_1 = termination_vcs(
        &func,
        Some(scc_calling(
            "test::other",
            n_measure(),
            RecursionSccMeasure::Param { position: 1, name: "j".to_string() },
        )),
    );
    let at_1 = recursion_rows(&at_1);
    assert_eq!(at_1.len(), 1);
    assert_eq!(at_1[0].formula, self_row.formula, "position 1 is the decremented argument");

    let at_0 = termination_vcs(
        &func,
        Some(scc_calling(
            "test::other",
            n_measure(),
            RecursionSccMeasure::Param { position: 0, name: "k".to_string() },
        )),
    );
    let at_0 = recursion_rows(&at_0);
    assert_eq!(at_0.len(), 1);
    assert_ne!(at_0[0].formula, self_row.formula, "position 0 is the constant 7");
}

/// Measures that are not comparable are refused: an authored caller measure
/// against a callee with none, or with an unsupported one.
#[test]
fn a_callee_without_a_comparable_measure_is_refused() {
    let func = with_decreases_n(caller_calling("test::other", vec![]));
    for callee_measure in
        [RecursionSccMeasure::Absent, RecursionSccMeasure::Unsupported("two clauses".to_string())]
    {
        let vcs =
            termination_vcs(&func, Some(scc_calling("test::other", n_measure(), callee_measure)));
        assert_eq!(recursion_markers(&vcs).len(), 1, "{vcs:#?}");
        assert!(recursion_rows(&vcs).is_empty(), "no partial proof surface: {vcs:#?}");
    }
}

/// One measure per member: if the value the other members compare against is
/// not this function's own clause, nothing it proves relates to its callers.
#[test]
fn a_member_whose_own_measure_disagrees_with_the_compiler_is_refused() {
    let func = with_decreases_n(caller_calling("test::other", vec![]));
    for own in [
        RecursionSccMeasure::Absent,
        RecursionSccMeasure::Param { position: 0, name: "x".to_string() },
        RecursionSccMeasure::Param { position: 1, name: "n".to_string() },
    ] {
        let vcs = termination_vcs(&func, Some(scc_calling("test::other", own, n_measure())));
        assert_eq!(recursion_markers(&vcs).len(), 1, "{vcs:#?}");
        assert!(recursion_rows(&vcs).is_empty());
    }
}

/// A reassigned measure parameter does not denote its entry value at the call.
#[test]
fn a_reassigned_measure_parameter_is_refused() {
    let mut func = with_decreases_n(caller_calling("test::other", vec![]));
    func.body.blocks[1].stmts.push(Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(9, 32))),
        span: SourceSpan::default(),
    });
    let vcs = termination_vcs(&func, Some(scc_calling("test::other", n_measure(), n_measure())));
    assert_eq!(recursion_markers(&vcs).len(), 1, "{vcs:#?}");
    assert!(recursion_rows(&vcs).is_empty());
}

/// Every recursive edge must be charged. An SCC successor no direct call
/// realizes (a closure handed to a higher-order callee), and a filed block that
/// is not a call in this body, are each an unmeasurable edge.
#[test]
fn unrealized_and_unextracted_scc_edges_are_charged() {
    let func = with_decreases_n(caller_calling("test::other", vec![]));

    let mut scc = scc_calling("test::other", n_measure(), n_measure());
    scc.unrealized_edges.push("test::rec_cs::{closure#0}".to_string());
    let vcs = termination_vcs(&func, Some(scc));
    let unprovable =
        recursion_rows(&vcs).into_iter().filter(|vc| vc.formula == Formula::Bool(true)).count();
    assert_eq!(unprovable, 1, "{vcs:#?}");

    let mut scc = scc_calling("test::other", n_measure(), n_measure());
    scc.calls.insert(
        1,
        RecursionSccCall {
            callee: "test::ghost".to_string(),
            is_self: false,
            callee_measure: n_measure(),
        },
    );
    let vcs = termination_vcs(&func, Some(scc));
    let unprovable =
        recursion_rows(&vcs).into_iter().filter(|vc| vc.formula == Formula::Bool(true)).count();
    assert_eq!(unprovable, 1, "bb1 is a Return, not the filed call: {vcs:#?}");
}

/// A call the compiler did NOT file as an SCC call is not assumed to be outside
/// the cycle: with an authored measure it is the same uncertainty the direct
/// self lane reports for any non-self call.
#[test]
fn an_unfiled_call_in_a_measured_member_is_an_uncertainty() {
    let func = with_decreases_n(caller_calling("test::other", vec![]));
    let scc = RecursionSccContext { own_measure: n_measure(), ..RecursionSccContext::default() };
    let vcs = termination_vcs(&func, Some(scc));
    assert_eq!(recursion_markers(&vcs).len(), 1, "{vcs:#?}");
    assert!(recursion_rows(&vcs).is_empty());
}

/// Facts installed for ANOTHER function are never read (owner check).
#[test]
fn scc_facts_owned_by_another_function_change_nothing() {
    let func = caller_calling("test::other", vec![]);
    let context = VcgenContext::for_function("test::someone_else").with_recursion_scc(Some(
        scc_calling("test::other", RecursionSccMeasure::Absent, RecursionSccMeasure::Absent),
    ));
    let _scope = crate::enter_vcgen_context(&context);
    let mut vcs = Vec::new();
    check_termination(&func, &mut vcs);
    assert!(recursion_rows(&vcs).is_empty(), "{vcs:#?}");
}

/// The bundle constructor's regeneration scope carries the facts to the
/// source-bound regeneration, and installs nothing when there are none.
#[test]
fn the_regeneration_scope_carries_the_facts() {
    let func = with_decreases_n(caller_calling("test::other", vec![]));
    let scc = scc_calling("test::other", n_measure(), n_measure());
    let (raw, _) = crate::with_recursion_scc_context(CALLER, Some(scc), || {
        crate::regenerate_recursion_decreases_production_variants(&func)
    })
    .expect("regeneration");
    assert_eq!(raw.len(), 1, "the mutual-call row is regenerated with its source binding");
    let (raw, _) = crate::with_recursion_scc_context(CALLER, None, || {
        crate::regenerate_recursion_decreases_production_variants(&func)
    })
    .expect("regeneration");
    assert!(raw.is_empty(), "no facts: the direct-self lane's marker, no source-bound row");
}

/// The compiler reads a member's measure with vcgen's own reader: loop-local
/// clauses are excluded and the lowering marker is stripped.
#[test]
fn function_level_recursion_measures_matches_the_termination_reader() {
    let contracts = vec![
        Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: format!("{}n", crate::contracts::LOWERED_CONTRACT_PREFIX),
        },
        Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "n > 0".to_string(),
        },
    ];
    assert_eq!(crate::function_level_recursion_measures(&contracts), vec!["n".to_string()]);
}
