//! A true postcondition does not erase eager execution or supply safety premises.
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{Block, BlockId, Constant, FuncId, Inst, InstrNode, Ty, ValueId};
use trust_verifier_api::{TrustSpecBinaryOp, TrustSpecExpr, TrustSpecPredicate, TrustSpecSort};
use trust_wp_lib::trust_ir_body::{
    replay_trust_ir_body_request_validated, verify_trust_ir_body_request_validated,
};

use super::*;

#[derive(Clone, Copy)]
enum Shape {
    Discarded,
    Unselected,
    CalleeAssertion,
}

fn node(inst: Inst, result: u32) -> InstrNode {
    InstrNode::new(inst).with_result(ValueId::new(result))
}

fn set_question(
    public: &mut TrustContractBundle,
    module: &mut trust_ir::Module,
    predicate: TrustSpecPredicate,
    bindings: Vec<(String, trust_ir::proof::ClauseBinding)>,
) {
    public.contracts[0].predicate = predicate.clone().into_contract_predicate().unwrap();
    let mut formula = trust_wp::trust_wp_native_formula_from_trust_spec(&predicate).unwrap();
    formula.bindings = bindings;
    public.contracts[0].metadata[0].value = serde_json::to_string(&formula.bindings).unwrap();
    module.proof_obligations[0].formula = Some(formula);
    let digest =
        public.canonical_obligation_semantic_digest_sha256(&public.obligations[0]).unwrap();
    module.proof_obligations[0].source.as_mut().unwrap().public.as_mut().unwrap().semantic_digest =
        trust_ir::ProofDigest::sha256(std::array::from_fn(|i| {
            u8::from_str_radix(&digest[2 * i..2 * i + 2], 16).unwrap()
        }));
}

fn question(shape: Shape, safe: bool) -> (TrustContractBundle, NativeVerificationBundle) {
    let (mut public, original) = fixture(false);
    let mut module = original.module;
    set_question(
        &mut public,
        &mut module,
        TrustSpecPredicate::new(TrustSpecExpr::bool_literal(true), vec![]),
        vec![],
    );
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
    block.body = vec![
        node(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }, 1),
        node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(safe || matches!(shape, Shape::CalleeAssertion))),
            },
            2,
        ),
        node(Inst::Const { ty: Ty::Bool, value: Constant::Bool(safe) }, 4),
    ];
    if matches!(shape, Shape::CalleeAssertion) {
        let mut assertion = InstrNode::new(Inst::Assert {
            cond: ValueId::new(4),
            kind: trust_ir::AssertKind::DivByZero,
            site: None,
        });
        assertion.proofs.push(trust_ir::ProofAnnotation::DivNonZero);
        block.body.push(assertion);
    }
    let mut division = node(
        Inst::BinOp {
            op: trust_ir::BinOp::UDiv,
            ty: Ty::U64,
            lhs: ValueId::new(1),
            rhs: ValueId::new(2),
        },
        3,
    );
    division.proofs.push(trust_ir::ProofAnnotation::DivNonZero);
    block.body.push(division);
    let returned = if matches!(shape, Shape::Unselected) {
        block.body.push(node(
            Inst::Select {
                ty: Ty::U64,
                cond: ValueId::new(0),
                then_val: ValueId::new(1),
                else_val: ValueId::new(3),
            },
            5,
        ));
        block.body.push(node(
            Inst::ICmp {
                op: trust_ir::ICmpOp::Eq,
                ty: Ty::U64,
                lhs: ValueId::new(5),
                rhs: ValueId::new(1),
            },
            6,
        ));
        6
    } else {
        4
    };
    block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(returned)] }));
    if matches!(shape, Shape::CalleeAssertion) {
        let mut callee = trust_ir::Function::new(
            FuncId::new(1),
            "labeled_assertion",
            module.functions[0].ty,
            BlockId::new(0),
        )
        .with_producer(trust_ir::Producer::TrustIr);
        callee.blocks.push(block);
        module.try_add_function(callee).unwrap();
        let mut caller = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::Bool);
        caller.body = vec![
            node(Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] }, 1),
            InstrNode::new(Inst::Return { values: vec![ValueId::new(1)] }),
        ];
        module.functions[0].blocks = vec![caller];
    } else {
        module.functions[0].blocks = vec![block];
    }
    let native =
        native_verification_bundle_from_module(module, native_trust_ir_digest(1), FuncId::new(0))
            .unwrap();
    native.validate().unwrap();
    (public, native)
}

fn check_wp(public: &TrustContractBundle, native: &NativeVerificationBundle, safe: bool) {
    let original = native.clone();
    let module_bytes = trust_ir::binary::serialize_module(&native.module).unwrap();
    let admitted = trust_ir::ValidatedNativeBundle::new(native).unwrap();
    let id = native
        .requests
        .iter()
        .find_map(|r| match r {
            NativeVerificationRequest::TrustWp(r) => Some(r.id),
            _ => None,
        })
        .unwrap();
    let actual = verify_trust_ir_body_request_validated(&admitted, id).unwrap();
    assert_eq!(
        actual.result().status,
        if safe {
            trust_wp_lib::VerifyBundleStatus::Verified
        } else {
            trust_wp_lib::VerifyBundleStatus::Failed
        },
        "{actual:#?}"
    );
    assert_eq!(
        replay_trust_ir_body_request_validated(
            &admitted,
            id,
            actual.result(),
            Some(actual.witness()),
        )
        .is_ok(),
        safe
    );
    assert_eq!(actual.witness().native_bundle_digest, native.stable_digest());
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            public,
            &public.obligations,
            native,
            &VerifierExecutionContext::new("eager-definedness"),
        );
    assert_eq!(live.result().summary.proved, usize::from(safe), "{:#?}", live.result());
    assert_eq!(live.checked_native_wp_proofs().len(), usize::from(safe));
    if safe {
        let obligation = &public.obligations[0];
        let fact = &live.checked_native_wp_proofs()[&obligation.obligation_id];
        assert!(fact.matches(public, native, obligation, &live.result().evidence[0]));
    }
    if !safe {
        let normal = FullVerificationEngine::with_required_native_engines_timeout_ms(5_000)
            .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
                public,
                &public.obligations,
                native,
                &VerifierExecutionContext::new("eager-definedness-real-primary"),
            );
        assert_eq!(normal.result().summary.proved, 0, "{:#?}", normal.result());
        assert!(normal.checked_native_wp_proofs().is_empty());
    }
    assert_eq!(*native, original);
    assert_eq!(trust_ir::binary::serialize_module(&native.module).unwrap(), module_bytes);
}

fn eager_control(shape: Shape) {
    for safe in [true, false] {
        let (public, native) = question(shape, safe);
        for condition in [false, true] {
            let execution = Interpreter::with_module(&native.module)
                .execute_func(FuncId::new(0), [InterpretValue::bool(condition)]);
            if safe {
                let outcome = execution.unwrap();
                assert_eq!(outcome.host_calls, 0);
                assert_eq!(outcome.returns, vec![InterpretValue::bool(true)]);
            } else {
                let error = execution.unwrap_err();
                assert_eq!(
                    error.code,
                    if matches!(shape, Shape::CalleeAssertion) {
                        InterpretErrorCode::Panic
                    } else {
                        InterpretErrorCode::UndefinedBehavior
                    },
                    "{error:?}"
                );
            }
        }
        check_wp(&public, &native, safe);
    }
}

#[test]
fn discarded_eager_zero_quotient_is_owed_under_a_true_postcondition() {
    eager_control(Shape::Discarded);
}

#[test]
fn unselected_ssa_quotient_is_eager_even_under_a_true_postcondition() {
    eager_control(Shape::Unselected);
}

#[test]
fn local_callee_division_label_does_not_prove_its_false_assertion() {
    eager_control(Shape::CalleeAssertion);
}

#[test]
fn wrapping_u64_add_cannot_prove_the_unbounded_integer_postcondition() {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    use trust_verifier_api::{TrustSpecVariable, TrustSpecVariableOrigin};
    let (mut public, original) = fixture(false);
    let mut module = original.module;
    module.func_types[0].params = vec![Ty::U64];
    module.func_types[0].returns = vec![Ty::U64];
    let predicate = TrustSpecPredicate::new(
        TrustSpecExpr::binary(
            TrustSpecBinaryOp::Gt,
            TrustSpecExpr::result(TrustSpecSort::Int),
            TrustSpecExpr::variable("x", TrustSpecSort::Int),
        ),
        vec![TrustSpecVariable {
            name: "x".into(),
            sort: TrustSpecSort::Int,
            origin: TrustSpecVariableOrigin::Local { index: 1 },
        }],
    );
    set_question(
        &mut public,
        &mut module,
        predicate,
        vec![
            (
                "x".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::Param { index: 0 },
                },
            ),
            (
                "result".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::ResultSlot { index: 0 },
                },
            ),
        ],
    );
    let mut block = Block::new(BlockId::new(0)).with_param(ValueId::new(0), Ty::U64);
    block.body = vec![
        node(Inst::Const { ty: Ty::U64, value: Constant::Int(1) }, 1),
        node(
            Inst::BinOp {
                op: trust_ir::BinOp::Add,
                ty: Ty::U64,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            },
            2,
        ),
        InstrNode::new(Inst::Return { values: vec![ValueId::new(2)] }),
    ];
    module.functions[0].blocks = vec![block];
    let native =
        native_verification_bundle_from_module(module, native_trust_ir_digest(1), FuncId::new(0))
            .unwrap();
    let execution = Interpreter::with_module(&native.module)
        .execute_func(FuncId::new(0), [InterpretValue::int(Ty::U64, i128::from(u64::MAX)).unwrap()])
        .unwrap();
    assert_eq!(execution.host_calls, 0);
    assert_eq!(execution.returns, vec![InterpretValue::int(Ty::U64, 0).unwrap()]);
    let admitted = trust_ir::ValidatedNativeBundle::new(&native).unwrap();
    let id = native
        .requests
        .iter()
        .find_map(|r| match r {
            NativeVerificationRequest::TrustWp(r) => Some(r.id),
            _ => None,
        })
        .unwrap();
    let error = verify_trust_ir_body_request_validated(&admitted, id).unwrap_err().to_string();
    assert!(error.contains("instruction outside scalar WP fragment"), "{error}");
    let live = engine(EvidenceStatus::Unknown)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("wrapping-u64-add"),
        );
    assert_eq!(live.result().summary.proved, 0, "{:#?}", live.result());
    assert!(live.checked_native_wp_proofs().is_empty());
    let normal = FullVerificationEngine::with_required_native_engines_timeout_ms(5_000)
        .verify_obligations_with_native_trust_ir_bundle_and_fresh_receipts(
            &public,
            &public.obligations,
            &native,
            &VerifierExecutionContext::new("wrapping-u64-add-real-primary"),
        );
    assert_eq!(normal.result().summary.proved, 0, "{:#?}", normal.result());
    assert!(normal.checked_native_wp_proofs().is_empty());
}
