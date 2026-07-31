#![cfg(feature = "ay-backend")]

use trust_router::{InProcessAyBackend, VerificationBackend};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, Contract, ContractKind, Formula, LocalDecl, Operand,
    Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VcKind, VerifiableBody,
    VerifiableFunction, VerificationResult,
};

fn shift_loop(op: BinOp, count: i128) -> VerifiableFunction {
    // fn shift_loop(mut i: u8) {
    //     decreases i;
    //     while i > 0 {
    //         i = i OP count;
    //     }
    // }
    VerifiableFunction {
        name: "shift_loop".into(),
        def_path: "test::shift_loop".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::u8(), name: Some("i".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("cond".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Gt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(0)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            op,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Int(count)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
        },
        contracts: vec![Contract {
            kind: ContractKind::Decreases,
            span: SourceSpan::default(),
            body: "bb1: i".into(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn e5(func: &VerifiableFunction) -> trust_types::VerificationCondition {
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .find(|vc| {
            matches!(
                &vc.kind,
                VcKind::NonTermination { context, .. } if context == "loop-decreases"
            )
        })
        .expect("the exact Machine{8} loop must emit its E5 obligation")
}

#[test]
fn shift_by_width_is_identity_and_cannot_prove_e5_descent() {
    let vc = e5(&shift_loop(BinOp::Shl, 8));
    let mut saw_masked_shift = false;
    vc.formula.visit(&mut |formula| {
        saw_masked_shift |= matches!(
            formula,
            Formula::BvShl(_, amount, 8)
                if matches!(
                    amount.as_ref(),
                    Formula::BvAnd(raw, mask, 8)
                        if matches!(raw.as_ref(), Formula::BitVec { value: 8, width: 8 })
                            && matches!(
                                mask.as_ref(),
                                Formula::BitVec { value: 7, width: 8 }
                            )
                )
        );
    });
    assert!(saw_masked_shift, "E5 must carry Rust's `8 & 7 == 0` count: {vc:#?}");

    let result = InProcessAyBackend::new().verify(&vc);
    match &result {
        VerificationResult::Failed { counterexample: Some(counterexample), .. } => assert!(
            !counterexample.assignments.is_empty(),
            "AY's SAT result must retain a concrete infinite-loop witness"
        ),
        _ => panic!(
            "`i: u8 = i << 8` is an identity and can run forever for every i > 0; \
             the strict AY lane must return Failed with a SAT witness, got {result:?}",
        ),
    }
}

#[test]
fn unsigned_shift_right_by_one_has_a_strict_checked_e5_proof() {
    let vc = e5(&shift_loop(BinOp::Shr, 1));
    let result = InProcessAyBackend::new().verify(&vc);
    match &result {
        VerificationResult::Proved { strength, .. } => assert_eq!(
            strength,
            &trust_types::ProofStrength::smt_unsat_strict_checked(),
            "E5 proof authority must come from AY's strict proof checker",
        ),
        _ => panic!(
            "for every positive u8, `i >> 1 < i`; AY must return its \
             strict-proof-checked UNSAT verdict, got {result:?}\nformula: {:?}",
            vc.formula,
        ),
    }
}
