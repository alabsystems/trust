// trust-types integration tests: serde roundtrip and model construction
//
// Exercises the public API of trust-types across all major type families:
// Formula, VerificationCondition, Ty, StateMachine, LivenessProperty,
// CrateVerificationResult, and ProofReport types.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn midpoint_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "get_midpoint".to_string(),
        def_path: "midpoint::get_midpoint".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::usize(), name: None },
                LocalDecl { index: 5, ty: Ty::usize(), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(5),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(2, 64)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(5))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

// ---------------------------------------------------------------------------
// VerifiableFunction roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verifiable_function_serde_roundtrip() {
    let func = midpoint_function();
    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.name, func.name);
    assert_eq!(round.def_path, func.def_path);
    assert_eq!(round.body.locals.len(), func.body.locals.len());
    assert_eq!(round.body.blocks.len(), func.body.blocks.len());
    assert_eq!(round.body.arg_count, func.body.arg_count);
}

#[test]
fn callable_item_serde_roundtrip_uses_stable_kind_tags() {
    let closure_hash = CallableDefPathHash::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let value = ConstValue::CallableItem {
        def_path: "fixture::make::{closure#0}".to_string(),
        kind: CallableKind::Closure,
        def_path_hash: closure_hash,
    };
    let json = serde_json::to_string(&value).expect("serialize callable item");
    assert_eq!(
        json,
        r#"{"CallableItem":{"def_path":"fixture::make::{closure#0}","kind":"closure","def_path_hash":{"stable_crate_id":"0123456789abcdef","local_hash":"fedcba9876543210"}}}"#
    );
    let round: ConstValue = serde_json::from_str(&json).expect("deserialize callable item");
    assert!(matches!(
        round,
        ConstValue::CallableItem {
            def_path,
            kind: CallableKind::Closure,
            def_path_hash,
        } if def_path == "fixture::make::{closure#0}" && def_path_hash == closure_hash
    ));

    let function = ConstValue::CallableItem {
        def_path: "fixture::make".to_string(),
        kind: CallableKind::FnDef,
        def_path_hash: CallableDefPathHash::new(1, 2),
    };
    let function_json = serde_json::to_string(&function).expect("serialize function item");
    assert!(function_json.contains(r#""kind":"fn_def""#));
}

#[test]
fn callable_item_symbols_are_injective_over_every_identity_component() {
    let hash_a = CallableDefPathHash::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let hash_b = CallableDefPathHash::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3211);

    let same_path_a =
        ConstValue::callable_smt_var_name("fixture::same", CallableKind::FnDef, hash_a);
    let same_path_b =
        ConstValue::callable_smt_var_name("fixture::same", CallableKind::FnDef, hash_b);
    assert_ne!(
        same_path_a, same_path_b,
        "same textual path from distinct definition hashes must not alias"
    );

    let forged_a = ConstValue::callable_smt_var_name("fixture::a", CallableKind::FnDef, hash_a);
    let forged_b = ConstValue::callable_smt_var_name("fixture::b", CallableKind::FnDef, hash_a);
    assert_ne!(
        forged_a, forged_b,
        "different textual paths with the same externally forged hash must not alias"
    );

    let closure = ConstValue::callable_smt_var_name("fixture::same", CallableKind::Closure, hash_a);
    assert_ne!(same_path_a, closure, "callable kind is part of the stable identity");
    assert_eq!(
        same_path_a,
        ConstValue::callable_smt_var_name("fixture::same", CallableKind::FnDef, hash_a),
        "the same callable identity must be deterministic"
    );
    assert!(
        same_path_a.starts_with("__trust_callable_fn_def_0123456789abcdef_fedcba9876543210_"),
        "both hash components must use fixed-width lowercase hexadecimal: {same_path_a}"
    );
}

#[test]
fn callable_def_path_hash_serde_rejects_noncanonical_hex() {
    let malformed = [
        // Too short.
        r#"{"CallableItem":{"def_path":"fixture::f","kind":"fn_def","def_path_hash":{"stable_crate_id":"123456789abcdef","local_hash":"0123456789abcdef"}}}"#,
        // Uppercase is deliberately noncanonical.
        r#"{"CallableItem":{"def_path":"fixture::f","kind":"fn_def","def_path_hash":{"stable_crate_id":"0123456789abcdeF","local_hash":"0123456789abcdef"}}}"#,
        // Non-hexadecimal byte.
        r#"{"CallableItem":{"def_path":"fixture::f","kind":"fn_def","def_path_hash":{"stable_crate_id":"0123456789abcdeg","local_hash":"0123456789abcdef"}}}"#,
        // The local component is independently validated.
        r#"{"CallableItem":{"def_path":"fixture::f","kind":"fn_def","def_path_hash":{"stable_crate_id":"0123456789abcdef","local_hash":"0123456789abcdeF"}}}"#,
    ];

    for json in malformed {
        let error = serde_json::from_str::<ConstValue>(json)
            .expect_err("noncanonical callable definition hashes must be rejected");
        assert!(
            error.to_string().contains("exactly 16 lowercase hexadecimal digits"),
            "unexpected serde error for {json}: {error}"
        );
    }
}

#[test]
fn historical_unit_constant_json_remains_compatible() {
    let value: ConstValue = serde_json::from_str(r#""Unit""#)
        .expect("the historical unit encoding must remain readable");
    assert!(matches!(value, ConstValue::Unit));
}

#[test]
fn test_verifiable_function_with_contracts_roundtrip() {
    let mut func = midpoint_function();
    func.contracts = vec![
        Contract {
            kind: ContractKind::Requires,
            span: SourceSpan::default(),
            body: "a <= b".to_string(),
        },
        Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: "result >= a && result <= b".to_string(),
        },
    ];
    func.preconditions = vec![Formula::Le(
        Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
        Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
    )];
    func.postconditions = vec![Formula::And(vec![
        Formula::Ge(
            Box::new(Formula::Var("result".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("a".into(), Sort::BitVec(64))),
        ),
        Formula::Le(
            Box::new(Formula::Var("result".into(), Sort::BitVec(64))),
            Box::new(Formula::Var("b".into(), Sort::BitVec(64))),
        ),
    ])];

    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.contracts.len(), 2);
    assert_eq!(round.preconditions.len(), 1);
    assert_eq!(round.postconditions.len(), 1);
    assert!(matches!(round.contracts[0].kind, ContractKind::Requires));
    assert!(matches!(round.contracts[1].kind, ContractKind::Ensures));
}

// ---------------------------------------------------------------------------
// Formula roundtrip — covers all major variants
// ---------------------------------------------------------------------------

#[test]
fn test_formula_literals_roundtrip() {
    let formulas = vec![
        Formula::Bool(true),
        Formula::Bool(false),
        Formula::Int(42),
        Formula::Int(-1),
        Formula::BitVec { value: 255, width: 8 },
    ];
    for formula in &formulas {
        let json = serde_json::to_string(formula).expect("serialize");
        let round: Formula = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, formula);
    }
}

#[test]
fn test_formula_connectives_roundtrip() {
    let formula = Formula::Implies(
        Box::new(Formula::And(vec![
            Formula::Var("p".into(), Sort::Bool),
            Formula::Var("q".into(), Sort::Bool),
        ])),
        Box::new(Formula::Or(vec![
            Formula::Not(Box::new(Formula::Var("r".into(), Sort::Bool))),
            Formula::Var("s".into(), Sort::Bool),
        ])),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_bitvector_ops_roundtrip() {
    let a = Box::new(Formula::Var("x".into(), Sort::BitVec(32)));
    let b = Box::new(Formula::Var("y".into(), Sort::BitVec(32)));
    let formula = Formula::And(vec![
        Formula::BvAdd(a.clone(), b.clone(), 32),
        Formula::BvSub(a.clone(), b.clone(), 32),
        Formula::BvMul(a.clone(), b.clone(), 32),
        Formula::BvUDiv(a.clone(), b.clone(), 32),
        Formula::BvAnd(a.clone(), b.clone(), 32),
        Formula::BvOr(a.clone(), b.clone(), 32),
        Formula::BvXor(a.clone(), b.clone(), 32),
        Formula::BvShl(a.clone(), b.clone(), 32),
        Formula::BvULt(a.clone(), b.clone(), 32),
        Formula::BvSLe(a.clone(), b.clone(), 32),
    ]);
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_quantifiers_roundtrip() {
    let formula = Formula::Forall(
        vec![("i".into(), Sort::Int), ("j".into(), Sort::BitVec(64))],
        Box::new(Formula::Implies(
            Box::new(Formula::Lt(
                Box::new(Formula::Var("i".into(), Sort::Int)),
                Box::new(Formula::Var("j".into(), Sort::BitVec(64))),
            )),
            Box::new(Formula::Exists(
                vec![("k".into(), Sort::Int)],
                Box::new(Formula::And(vec![
                    Formula::Lt(
                        Box::new(Formula::Var("i".into(), Sort::Int)),
                        Box::new(Formula::Var("k".into(), Sort::Int)),
                    ),
                    Formula::Lt(
                        Box::new(Formula::Var("k".into(), Sort::Int)),
                        Box::new(Formula::Var("j".into(), Sort::BitVec(64))),
                    ),
                ])),
            )),
        )),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

#[test]
fn test_formula_array_ops_roundtrip() {
    let arr = Formula::Var("arr".into(), Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int)));
    let idx = Formula::Int(5);
    let val = Formula::Int(42);
    let formula = Formula::Eq(
        Box::new(Formula::Select(Box::new(arr.clone()), Box::new(idx.clone()))),
        Box::new(Formula::Select(
            Box::new(Formula::Store(Box::new(arr), Box::new(idx), Box::new(val))),
            Box::new(Formula::Int(5)),
        )),
    );
    let json = serde_json::to_string(&formula).expect("serialize");
    let round: Formula = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round, formula);
}

// ---------------------------------------------------------------------------
// Ty roundtrip — all variants
// ---------------------------------------------------------------------------

#[test]
fn test_ty_all_variants_roundtrip() {
    let types = vec![
        Ty::Bool,
        Ty::Int { width: 8, signed: true },
        Ty::Int { width: 64, signed: true },
        Ty::Int { width: 32, signed: false },
        Ty::Float { width: 64 },
        Ty::Unit,
        Ty::Never,
        Ty::Ref { mutable: false, inner: Box::new(Ty::Bool) },
        Ty::Ref { mutable: true, inner: Box::new(Ty::i32()) },
        Ty::Slice { elem: Box::new(Ty::u32()) },
        Ty::Array { elem: Box::new(Ty::Bool), len: 10 },
        Ty::Tuple(vec![Ty::i32(), Ty::Bool, Ty::usize()]),
        Ty::Adt { adt_kind: None, layout: None, 
            variants: Vec::new(),
            name: "MyStruct".into(),
            fields: vec![("x".into(), Ty::i32()), ("y".into(), Ty::Bool)],
            disc_index_safe: false,
            // Trust (B3-1 field completion): this construction site was missed by
            // 11598e13fe, leaving `cargo test -p trust-types` uncompilable (E0063)
            // since B3-1 — masked because the suite was not run. `None` = the
            // historical flattened-struct semantics.
            faithful_enum_repr: None, enum_layout: None, },
    ];
    for ty in &types {
        let json = serde_json::to_string(ty).expect("serialize");
        let round: Ty = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(&round, ty);
    }
}

#[test]
fn test_ty_helpers_comprehensive() {
    // Integer checks
    assert!(Ty::i32().is_integer());
    assert!(Ty::i32().is_signed());
    assert_eq!(Ty::i32().int_width(), Some(32));

    assert!(Ty::u32().is_integer());
    assert!(!Ty::u32().is_signed());
    assert_eq!(Ty::u32().int_width(), Some(32));

    assert!(Ty::usize().is_integer());
    assert!(!Ty::usize().is_signed());
    assert_eq!(Ty::usize().int_width(), Some(64));

    assert!(Ty::isize().is_integer());
    assert!(Ty::isize().is_signed());
    assert_eq!(Ty::isize().int_width(), Some(64));

    // Non-integer checks
    assert!(!Ty::Bool.is_integer());
    assert!(!Ty::Bool.is_signed());
    assert_eq!(Ty::Bool.int_width(), None);
    assert!(!Ty::Unit.is_integer());
    assert!(!(Ty::Float { width: 64 }).is_integer());
}

// ---------------------------------------------------------------------------
// Sort::from_ty
// ---------------------------------------------------------------------------

#[test]
fn test_sort_from_ty_comprehensive() {
    assert_eq!(Sort::from_ty(&Ty::Bool), Sort::Bool);
    assert_eq!(Sort::from_ty(&Ty::i32()), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::u32()), Sort::BitVec(32));
    assert_eq!(Sort::from_ty(&Ty::usize()), Sort::BitVec(64));
    assert_eq!(Sort::from_ty(&Ty::isize()), Sort::BitVec(64));
    assert_eq!(Sort::from_ty(&Ty::Float { width: 64 }), Sort::BitVec(64));
    // Fallback for non-primitive types
    assert_eq!(Sort::from_ty(&Ty::Unit), Sort::Int);
    assert_eq!(Sort::from_ty(&Ty::Tuple(vec![])), Sort::Int);
}

// ---------------------------------------------------------------------------
// VerificationCondition + VcKind roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verification_condition_all_kinds_roundtrip() {
    let vc_kinds: Vec<VcKind> = vec![
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::ShiftOverflow { op: BinOp::Shl, operand_ty: Ty::u32(), shift_ty: Ty::u32() },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: "x > 0".into() },
        VcKind::Precondition { callee: "foo::bar".into() },
        VcKind::Postcondition,
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Unreachable,
        VcKind::DeadState { state: "idle".into() },
        VcKind::Deadlock,
        VcKind::Temporal { machine: None, property: "eventually done".into() },
        VcKind::BinaryCopySinkLengthViolation {
            callee: "memcpy".into(),
            desc: "copy sink length may exceed destination capacity".into(),
        },
        VcKind::FfiBoundaryViolation {
            callee: "malloc".into(),
            desc: "return contract may be null".into(),
        },
        VcKind::UseAfterFree,
        VcKind::DoubleFree,
        VcKind::AliasingViolation { mutable: true },
        VcKind::LifetimeViolation,
        VcKind::SendViolation,
        VcKind::SyncViolation,
        VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
        VcKind::LoopInvariantInitiation { invariant: "i <= n".into(), header_block: 1 },
        VcKind::LoopInvariantConsecution { invariant: "i <= n".into(), header_block: 1 },
        VcKind::LoopInvariantSufficiency { invariant: "i <= n".into(), header_block: 1 },
        VcKind::TypeRefinementViolation { variable: "n".into(), predicate: "n >= 0".into() },
        VcKind::FrameConditionViolation { variable: "state".into(), function: "update".into() },
    ];

    for kind in vc_kinds {
        let formula = Formula::Eq(
            Box::new(Formula::BvAdd(
                Box::new(Formula::Var("x".into(), Sort::BitVec(32))),
                Box::new(Formula::BitVec { value: 1, width: 32 }),
                32,
            )),
            Box::new(Formula::Var("y".into(), Sort::BitVec(32))),
        );
        let vc = VerificationCondition {
            kind: kind.clone(),
            function: "test_fn".into(),
            location: SourceSpan {
                file: "test.rs".into(),
                line_start: 10,
                col_start: 4,
                line_end: 10,
                col_end: 20,
            },
            formula: formula.clone(),
            contract_metadata: None,
        };
        let json = serde_json::to_string(&vc).expect("serialize");
        let round: VerificationCondition = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.function, "test_fn");
        assert_eq!(round.kind.description(), kind.description());
        assert_eq!(round.formula, formula);
        // Verify description is non-empty for all kinds
        assert!(!kind.description().is_empty(), "description for {:?}", kind);
    }
}

// ---------------------------------------------------------------------------
// VerificationResult roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_verification_result_all_variants_roundtrip() {
    let results = vec![
        VerificationResult::Proved {
            solver: "ay".into(),
            time_ms: 5,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
        VerificationResult::Proved {
            solver: "clean".into(),
            time_ms: 100,
            strength: ProofStrength::constructive(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
        VerificationResult::Proved {
            solver: "trust-mc".into(),
            time_ms: 50,
            strength: ProofStrength::bounded(100),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        },
        VerificationResult::Failed {
            solver: "ay".into(),
            time_ms: 7,
            counterexample: Some(Counterexample::new(vec![
                ("a".into(), CounterexampleValue::Uint(u64::MAX as u128)),
                ("b".into(), CounterexampleValue::Uint(1)),
            ])),
        },
        VerificationResult::Failed { solver: "ay".into(), time_ms: 3, counterexample: None },
        VerificationResult::Unknown {
            solver: "ay".into(),
            time_ms: 200,
            reason: "quantifier instantiation limit".into(),
        },
        VerificationResult::Timeout { solver: "ay".into(), timeout_ms: 5000 },
    ];

    for result in &results {
        let json = serde_json::to_string(result).expect("serialize");
        let round: VerificationResult = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.solver_name(), result.solver_name());
        assert_eq!(round.time_ms(), result.time_ms());
        assert_eq!(round.is_proved(), result.is_proved());
        assert_eq!(round.is_failed(), result.is_failed());
    }
}

// ---------------------------------------------------------------------------
// StateMachine roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_state_machine_roundtrip() {
    let sm = StateMachine {
        enum_name: "ConnectionState".into(),
        state_local: 1,
        states: vec![
            StateInfo { name: "Idle".into(), discriminant: 0 },
            StateInfo { name: "Connecting".into(), discriminant: 1 },
            StateInfo { name: "Connected".into(), discriminant: 2 },
            StateInfo { name: "Disconnecting".into(), discriminant: 3 },
        ],
        transitions: vec![
            Transition { from: 0, to: 1, source_block: BlockId(0), target_block: BlockId(1) },
            Transition { from: 1, to: 2, source_block: BlockId(1), target_block: BlockId(2) },
            Transition { from: 2, to: 3, source_block: BlockId(2), target_block: BlockId(3) },
            Transition { from: 3, to: 0, source_block: BlockId(3), target_block: BlockId(0) },
        ],
        initial_state: Some(0),
    };

    let json = serde_json::to_string(&sm).expect("serialize");
    let round: StateMachine = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.state_count(), 4);
    assert_eq!(round.transition_count(), 4);
    assert_eq!(round.state_name(0), Some("Idle"));
    assert_eq!(round.state_name(2), Some("Connected"));
    assert_eq!(round.state_name(99), None);
    assert_eq!(round.initial_state, Some(0));
}

// ---------------------------------------------------------------------------
// LivenessProperty + FairnessConstraint roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_liveness_property_all_operators_roundtrip() {
    let properties = vec![
        LivenessProperty {
            name: "termination".into(),
            operator: TemporalOperator::Eventually,
            predicate: "done".into(),
            consequent: None,
            fairness: vec![],
        },
        LivenessProperty {
            name: "safety".into(),
            operator: TemporalOperator::Always,
            predicate: "no_error".into(),
            consequent: None,
            fairness: vec![],
        },
        LivenessProperty {
            name: "progress".into(),
            operator: TemporalOperator::AlwaysEventually,
            predicate: "served".into(),
            consequent: None,
            fairness: vec![FairnessConstraint::Weak {
                action: "schedule".into(),
                vars: vec!["tasks".into()],
            }],
        },
        LivenessProperty {
            name: "response".into(),
            operator: TemporalOperator::LeadsTo,
            predicate: "request".into(),
            consequent: Some("response".into()),
            fairness: vec![FairnessConstraint::Strong {
                action: "dispatch".into(),
                vars: vec!["queue".into(), "workers".into()],
            }],
        },
    ];

    for prop in &properties {
        let json = serde_json::to_string(prop).expect("serialize");
        let round: LivenessProperty = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(round.name, prop.name);
        assert_eq!(round.operator, prop.operator);
        assert_eq!(round.fairness.len(), prop.fairness.len());
        // Verify description and TLA generation are consistent
        assert!(!prop.description().is_empty());
        assert!(!prop.to_tla().is_empty());
    }
}

// ---------------------------------------------------------------------------
// CrateVerificationResult roundtrip + aggregation
// ---------------------------------------------------------------------------

#[test]
fn test_crate_verification_result_aggregation_roundtrip() {
    let mut crate_result = CrateVerificationResult::new("my_crate");

    let func1 = FunctionVerificationResult {
        function_path: "my_crate::safe_div".into(),
        function_name: "safe_div".into(),
        results: vec![(
            VerificationCondition {
                kind: VcKind::DivisionByZero,
                function: "safe_div".into(),
                location: SourceSpan::default(),
                formula: Formula::Bool(false),
                contract_metadata: None,
            },
            VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 5,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
        )],
        from_notes: 1,
        with_assumptions: 0,
    };

    let func2 = FunctionVerificationResult {
        function_path: "my_crate::midpoint".into(),
        function_name: "midpoint".into(),
        results: vec![
            (
                VerificationCondition {
                    kind: VcKind::ArithmeticOverflow {
                        op: BinOp::Add,
                        operand_tys: (Ty::usize(), Ty::usize()),
                    },
                    function: "midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(true),
                    contract_metadata: None,
                },
                VerificationResult::Failed {
                    solver: "ay".into(),
                    time_ms: 8,
                    counterexample: None,
                },
            ),
            (
                VerificationCondition {
                    kind: VcKind::DivisionByZero,
                    function: "midpoint".into(),
                    location: SourceSpan::default(),
                    formula: Formula::Bool(false),
                    contract_metadata: None,
                },
                VerificationResult::Proved {
                    solver: "ay".into(),
                    time_ms: 3,
                    strength: ProofStrength::smt_unsat(),
                    proof_certificate: None,
                    solver_warnings: None,
                    native_proof_envelope: None,
                },
            ),
        ],
        from_notes: 0,
        with_assumptions: 1,
    };

    crate_result.add_function(func1);
    crate_result.add_function(func2);

    // Verify aggregation
    assert_eq!(crate_result.function_count(), 2);
    assert_eq!(crate_result.total_obligations(), 3);
    assert_eq!(crate_result.total_from_notes, 1);
    assert_eq!(crate_result.total_with_assumptions, 1);

    // Serde roundtrip
    let json = serde_json::to_string(&crate_result).expect("serialize");
    let round: CrateVerificationResult = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "my_crate");
    assert_eq!(round.function_count(), 2);
    assert_eq!(round.total_obligations(), 3);
    assert_eq!(round.all_results().len(), 3);
}

#[test]
fn test_binary_decompilation_blocker_json_keeps_proof_grade_gates_separate() {
    let origin = BinaryOrigin {
        binary_path: Some("fixtures/aarch64/tiny".to_string()),
        function_entry: Some(0x400000),
        instruction_address: 0x400008,
        instruction_size: Some(4),
        encoding: Some(0xd518_0000),
        instruction_bytes: vec![0x00, 0x00, 0x18, 0xd5],
        source: None,
    };
    let symbolic_formula = Formula::BvAdd(
        Box::new(Formula::Var("x0".to_string(), Sort::BitVec(64))),
        Box::new(Formula::BitVec { value: 1, width: 64 }),
        64,
    );
    let vc_formula = Formula::Eq(
        Box::new(symbolic_formula.clone()),
        Box::new(Formula::Var("x1".to_string(), Sort::BitVec(64))),
    );
    let checked_assertion = VcKind::Assertion { message: "aarch64 path predicate".to_string() };

    let mut verification = BinaryVerificationSummary {
        solver_dispatch: vec![
            SolverDispatchRecord {
                id: "unsupported-machine-effect".to_string(),
                function: Some("entry".to_string()),
                origin: Some(origin.clone()),
                vc_kind: Some(VcKind::UnsupportedMir {
                    kind: "aarch64_system_register".to_string(),
                    detail: "MSR side effect is not modeled".to_string(),
                }),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsupported,
                replay: ReplayStatus::NotAttempted,
                certificate: ProofCertificateStatus::Unavailable {
                    reason: Some("unsupported machine semantics".to_string()),
                },
                diagnostics: vec!["unsupported machine effect remains in the ledger".to_string()],
                ..Default::default()
            },
            SolverDispatchRecord {
                id: "proved-but-not-replayed".to_string(),
                function: Some("entry".to_string()),
                origin: Some(origin.clone()),
                vc_kind: Some(checked_assertion.clone()),
                vc: Some(SerializableVc {
                    kind: checked_assertion,
                    function: "entry".into(),
                    location: origin.span(),
                    formula: vc_formula.clone(),
                    contract_metadata: None,
                }),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsat,
                replay: ReplayStatus::NotAttempted,
                certificate: ProofCertificateStatus::Checked {
                    checker: "trust-proof-cert".to_string(),
                    format: "checked-binary-certificate-v1".to_string(),
                    sha256: Some(
                        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                            .to_string(),
                    ),
                },
                diagnostics: vec!["solver result still requires machine replay".to_string()],
                ..Default::default()
            },
            SolverDispatchRecord {
                id: "replayed-but-unchecked-cert".to_string(),
                function: Some("entry".to_string()),
                origin: Some(origin.clone()),
                vc_kind: Some(VcKind::Assertion {
                    message: "checked certificate required".to_string(),
                }),
                solver: "ay".to_string(),
                status: SolverDispatchStatus::Unsat,
                replay: ReplayStatus::Replayed,
                certificate: ProofCertificateStatus::Present {
                    format: "lfsc".to_string(),
                    sha256: Some(
                        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                            .to_string(),
                    ),
                    artifact_path: Some("proofs/entry.lfsc".to_string()),
                },
                diagnostics: vec![
                    "certificate exists but was not independently checked".to_string(),
                ],
                ..Default::default()
            },
        ],
        unsupported_ledger: UnsupportedLedger {
            records: vec![UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("aarch64".to_string()),
                origin: Some(origin.clone()),
                opcode: Some("msr".to_string()),
                operand: Some("s3_0_c1_c0_0".to_string()),
                feature: "unsupported_system_register_write".to_string(),
            }],
        },
        proof_certificate: ProofCertificateStatus::Unavailable {
            reason: Some("not every binary VC has a checked certificate".to_string()),
        },
        ..Default::default()
    };
    verification.refresh_from_solver_dispatch();

    let blocker = |stage: &str, feature: &str, reason: &str| TargetValidationBlocker {
        target: DecompileTarget::TrustIr,
        function: Some("entry".to_string()),
        code: feature.to_string(),
        stage: stage.to_string(),
        feature: feature.to_string(),
        reason: reason.to_string(),
        origin: Some(origin.clone()),
        diagnostics: vec![reason.to_string()],
    };
    let output = DecompiledOutput {
        target: DecompileTarget::TrustIr,
        validation: ReconstructionValidationStatus::Failed,
        target_validation_blockers: vec![
            blocker(
                "lift",
                "unsupported_machine_semantics",
                "unsupported AArch64 system register write",
            ),
            blocker("replay", "missing_replay", "solver result has not been replayed"),
            blocker(
                "certificate",
                "missing_checked_certificate",
                "certificate is present but not independently checked",
            ),
            blocker(
                "canonical_trust_ir",
                "symbolic_formula_loss",
                "symbolic formula must remain available as a structured Formula",
            ),
        ],
        preserved_symbolic_formulas: vec![PreservedSymbolicFormula {
            target: DecompileTarget::TrustIr,
            function: Some("entry".to_string()),
            block: Some(0),
            statement_index: Some(0),
            location: "bb0[0].rvalue".to_string(),
            formula: symbolic_formula.clone(),
        }],
        diagnostics: vec!["proof-grade gates are represented as separate blockers".to_string()],
        ..Default::default()
    };
    let artifact = DecompilationArtifact {
        binary: BinaryArtifactMetadata {
            path: Some("fixtures/aarch64/tiny".to_string()),
            format: BinaryArtifactFormat::Elf,
            image_kind: BinaryImageKind::Executable,
            architecture: "aarch64".to_string(),
            entry_point: Some(0x400000),
            ..Default::default()
        },
        target: DecompileTarget::TrustIr,
        functions: vec![DecompiledFunction {
            name: "entry".to_string(),
            entry: 0x400000,
            origin: Some(origin.clone()),
            output: Some(output.clone()),
            unsupported: verification.unsupported_ledger.clone(),
            verification: verification.clone(),
            trust_level: TrustLevel::Partial,
            ..Default::default()
        }],
        unsupported: verification.unsupported_ledger.clone(),
        verification,
        reconstruction: ReconstructionSummary {
            target: DecompileTarget::TrustIr,
            outputs: vec![output],
            validation: ReconstructionValidationStatus::Failed,
            trust_level: TrustLevel::Rejected,
            ..Default::default()
        },
        trust_level: TrustLevel::Partial,
        ..Default::default()
    };

    let json = serde_json::to_string(&artifact).expect("serialize binary blocker artifact");
    assert!(json.contains("unsupported_machine_semantics"));
    assert!(json.contains("missing_replay"));
    assert!(json.contains("missing_checked_certificate"));
    assert!(json.contains("symbolic_formula_loss"));
    assert!(json.contains("preserved_symbolic_formulas"));
    assert!(!json.contains("Undef"));

    let round: DecompilationArtifact =
        serde_json::from_str(&json).expect("deserialize binary blocker artifact");
    assert_eq!(round.verification.status, BinaryVerificationStatus::Mixed);
    assert_eq!(round.verification.unsupported_ledger.records.len(), 1);
    assert_eq!(
        round.verification.unsupported_ledger.records[0].feature,
        "unsupported_system_register_write"
    );
    assert_eq!(round.verification.solver_dispatch[0].status, SolverDispatchStatus::Unsupported);
    assert_eq!(round.verification.solver_dispatch[1].replay, ReplayStatus::NotAttempted);
    assert!(round.verification.solver_dispatch[1].certificate.is_checked());
    assert!(matches!(
        round.verification.solver_dispatch[2].certificate,
        ProofCertificateStatus::Present { .. }
    ));
    assert!(!round.verification.solver_dispatch[2].certificate.is_checked());
    assert_eq!(
        round.verification.solver_dispatch[1].vc.as_ref().expect("serializable VC").formula,
        vc_formula
    );

    let round_output = &round.reconstruction.outputs[0];
    let blocker_features: Vec<&str> = round_output
        .target_validation_blockers
        .iter()
        .map(|blocker| blocker.feature.as_str())
        .collect();
    assert!(blocker_features.contains(&"unsupported_machine_semantics"));
    assert!(blocker_features.contains(&"missing_replay"));
    assert!(blocker_features.contains(&"missing_checked_certificate"));
    assert!(blocker_features.contains(&"symbolic_formula_loss"));
    assert_eq!(round_output.preserved_symbolic_formulas[0].formula, symbolic_formula);
    assert_ne!(round.trust_level, TrustLevel::ProofGrade);
}

#[test]
fn solver_dispatch_roundtrips_binary_artifact_digest_identity() {
    let root_digest = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    let selected_digest = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
    let identity = BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(root_digest)),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0x1000,
            file_size: 0x80,
            sha256: selected_digest.to_string(),
        }),
    };
    assert!(identity.digest_identity_allows_replay());

    let dispatch = SolverDispatchRecord {
        id: "binary-vc-0".to_string(),
        function: Some("entry".to_string()),
        solver: "ay".to_string(),
        status: SolverDispatchStatus::Unsat,
        replay: ReplayStatus::Replayed,
        binary_artifact_digest_identity: Some(identity.clone()),
        ..Default::default()
    };

    let json = serde_json::to_value(&dispatch).expect("serialize solver dispatch");
    assert_eq!(
        json["binary_artifact_digest_identity"]["root_artifact_digest"]["value"],
        serde_json::json!(root_digest)
    );
    assert_eq!(
        json["binary_artifact_digest_identity"]["selected_image"]["sha256"],
        serde_json::json!(selected_digest)
    );

    let round: SolverDispatchRecord =
        serde_json::from_value(json).expect("deserialize solver dispatch");
    assert_eq!(round.replay_artifact_digest_identity(), Some(&identity));
    assert!(round.replay_digest_identity_allows_proof_grade());
}

#[test]
fn solver_dispatch_digest_identity_preserves_legacy_json_defaults() {
    let legacy_json = r#"{"id":"legacy-dispatch","solver":"ay"}"#;
    let dispatch: SolverDispatchRecord =
        serde_json::from_str(legacy_json).expect("deserialize legacy solver dispatch");
    assert!(dispatch.binary_artifact_digest_identity.is_none());
    assert_eq!(
        dispatch.replay_digest_identity_blockers(),
        vec!["missing dispatch binary artifact digest identity".to_string()]
    );

    let json = serde_json::to_value(&dispatch).expect("serialize defaulted solver dispatch");
    assert!(json.get("binary_artifact_digest_identity").is_none());
}

#[test]
fn binary_artifact_digest_identity_can_be_copied_from_metadata() {
    let metadata = BinaryArtifactMetadata {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(
            "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
        )),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0,
            file_size: 16,
            sha256: "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string(),
        }),
        ..Default::default()
    };

    let identity =
        BinaryArtifactDigestIdentity::from_metadata(&metadata).expect("metadata carries identity");
    assert!(identity.digest_identity_allows_replay());
    assert_eq!(
        identity.root_artifact_digest.as_ref().map(|digest| digest.value.as_str()),
        Some("cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc")
    );
    assert!(
        BinaryArtifactDigestIdentity::from_metadata(&BinaryArtifactMetadata::default()).is_none()
    );
}

#[test]
fn proof_certificate_status_exposes_typed_production_checker_evidence_marker() {
    let evidence = ProofCertificateProductionCheckerEvidenceRef::new(
        "ay-lrat-binary-check",
        "0.1.0",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    )
    .expect("typed production checker evidence ref should build");
    let status = ProofCertificateStatus::Checked {
        checker: evidence.legacy_checker_status(),
        format: "lrat".to_string(),
        sha256: Some(
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
        ),
    };

    assert!(status.is_checked());
    assert!(status.is_production_checked());
    assert_eq!(status.production_checker_evidence(), Some(evidence));
}

#[test]
fn proof_certificate_status_marker_parse_fails_closed() {
    let missing = ProofCertificateStatus::Checked {
        checker: "ay-lrat-binary-check".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
        ),
    };
    assert_eq!(
        missing.production_checker_evidence_status(),
        ProofCertificateProductionCheckerEvidenceStatus::Missing
    );
    assert!(!missing.is_production_checked());

    let malformed = ProofCertificateStatus::Checked {
        checker: "ay-lrat-binary-check@0.1.0;production_checker_evidence_sha256=NOTHEX".to_string(),
        format: "lrat".to_string(),
        sha256: Some(
            "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
        ),
    };
    assert!(matches!(
        malformed.production_checker_evidence_status(),
        ProofCertificateProductionCheckerEvidenceStatus::Malformed { .. }
    ));
    assert_eq!(malformed.production_checker_evidence(), None);
    assert!(!malformed.is_production_checked());
}

#[test]
fn target_validation_blocker_code_roundtrips_and_legacy_artifacts_default_it() {
    let blocker = TargetValidationBlocker {
        code: "trust-cg-backend-unavailable".to_string(),
        feature: "backend availability".to_string(),
        reason: "configured trust-cg backend is unavailable".to_string(),
        ..Default::default()
    };

    let json = serde_json::to_value(&blocker).expect("serialize target validation blocker");
    assert_eq!(json["code"], "trust-cg-backend-unavailable");
    let round: TargetValidationBlocker =
        serde_json::from_value(json).expect("deserialize target validation blocker");
    assert_eq!(round, blocker);

    let legacy: TargetValidationBlocker = serde_json::from_str(
        r#"{"feature":"legacy-feature","reason":"artifact predates typed blocker codes"}"#,
    )
    .expect("deserialize legacy target validation blocker");
    assert!(legacy.code.is_empty());
    assert_eq!(legacy.feature, "legacy-feature");
}

#[test]
fn proof_gate_models_roundtrip_without_dropping_replay_cert_target_or_backprop_fields() {
    let origin = BinaryOrigin {
        binary_path: Some("fixtures/aarch64/exclusive".to_string()),
        function_entry: Some(0x400000),
        instruction_address: 0x400014,
        instruction_size: Some(4),
        encoding: Some(0xc800_fc22),
        instruction_bytes: vec![0x22, 0xfc, 0x00, 0xc8],
        source: Some(SourceSpan::binary_address(0x400014)),
    };
    let digest_identity = BinaryArtifactDigestIdentity {
        root_artifact_digest: Some(BinaryArtifactDigest::sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        )),
        selected_image: Some(BinarySelectedImageIdentity {
            file_offset: 0x1000,
            file_size: 0x80,
            sha256: "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
        }),
    };
    let production_checker = ProofCertificateProductionCheckerEvidenceRef::new(
        "trust-proof-cert",
        "0.2.0",
        "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
    )
    .expect("canonical production checker evidence");
    let certificate = ProofCertificateStatus::Checked {
        checker: production_checker.legacy_checker_status(),
        format: "lrat".to_string(),
        sha256: Some(
            "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".to_string(),
        ),
    };
    let atomic_operation = AtomicOperation {
        place: Place::local(1),
        dest: Some(Place::local(2)),
        op_kind: AtomicOpKind::CompareExchangeWeak,
        ordering: AtomicOrdering::AcqRel,
        failure_ordering: Some(AtomicOrdering::Acquire),
        span: SourceSpan::binary_address(0x400014),
    };
    let atomic_fact = Aarch64AtomicSemanticFact {
        origin: Some(origin.clone()),
        opcode: "Stlxr".to_string(),
        operand: Some("W2, X0, [X1]".to_string()),
        access: MemoryAccessKind::Write,
        ordering: MemoryOrderingSemantics::Release,
        exclusive_monitor: Aarch64ExclusiveMonitorSemantics::StoreConditional,
        reports_status: true,
        missing_witnesses: vec![
            "exclusive-monitor reservation state".to_string(),
            "store-conditional status result".to_string(),
        ],
        consumed_by_proof_model: false,
    };
    let dispatch = SolverDispatchRecord {
        id: "aarch64-exclusive-replay-boundary".to_string(),
        function: Some("entry".to_string()),
        origin: Some(origin.clone()),
        solver: "ay".to_string(),
        backend: Some("replay-boundary".to_string()),
        status: SolverDispatchStatus::Unsat,
        replay: ReplayStatus::Replayed,
        certificate: certificate.clone(),
        binary_artifact_digest_identity: Some(digest_identity.clone()),
        diagnostics: vec!["exact replay identity bound to selected image digest".to_string()],
        ..Default::default()
    };
    let target_blocker = TargetValidationBlocker {
        target: DecompileTarget::Wasm,
        function: Some("entry".to_string()),
        code: "missing-formula-to-target-op-binding".to_string(),
        stage: "target-proof-consumer".to_string(),
        feature: "missing_formula_to_target_op_binding".to_string(),
        reason: "target proof consumer requires structural formula-to-WAT binding".to_string(),
        origin: Some(origin.clone()),
        diagnostics: vec![
            "checked certificate identity is necessary but not sufficient".to_string(),
            "exact replay identity is necessary but not sufficient".to_string(),
        ],
    };
    let source_provenance = BinarySourceProvenanceSummary {
        status: "exact".to_string(),
        exact_mapping_count: 0,
        ambiguous_mapping_count: 0,
        diagnostics: vec![
            "exact debug/source provenance has no accepted address mappings".to_string(),
        ],
        source_backpropagation_allowed: true,
    };
    let source_diagnostics = source_provenance.typed_diagnostics();
    assert_eq!(
        source_diagnostics[0].kind,
        BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected
    );

    let json = serde_json::to_value(&(
        atomic_operation,
        atomic_fact,
        dispatch,
        target_blocker,
        source_provenance,
        source_diagnostics,
    ))
    .expect("serialize proof gate model tuple");
    let encoded = json.to_string();
    for field in [
        "failure_ordering",
        "exclusive_monitor",
        "reports_status",
        "missing_witnesses",
        "binary_artifact_digest_identity",
        "selected_image",
        "certificate",
        "replay",
        "target-proof-consumer",
        "source_backpropagation_allowed",
        "binary_address_diagnostics_allowed",
    ] {
        assert!(encoded.contains(field), "serialized proof gate models dropped `{field}`");
    }

    let (
        round_atomic_operation,
        round_atomic_fact,
        round_dispatch,
        round_target_blocker,
        round_source_provenance,
        round_source_diagnostics,
    ): (
        AtomicOperation,
        Aarch64AtomicSemanticFact,
        SolverDispatchRecord,
        TargetValidationBlocker,
        BinarySourceProvenanceSummary,
        Vec<BinarySourceProvenanceDiagnostic>,
    ) = serde_json::from_value(json).expect("deserialize proof gate model tuple");

    assert_eq!(round_atomic_operation.op_kind, AtomicOpKind::CompareExchangeWeak);
    assert_eq!(round_atomic_operation.failure_ordering, Some(AtomicOrdering::Acquire));
    assert_eq!(
        round_atomic_fact.exclusive_monitor,
        Aarch64ExclusiveMonitorSemantics::StoreConditional
    );
    assert!(round_atomic_fact.reports_status);
    assert_eq!(round_atomic_fact.missing_witnesses.len(), 2);
    assert!(!round_atomic_fact.proof_grade_gate_accepted());
    assert_eq!(round_dispatch.replay, ReplayStatus::Replayed);
    assert_eq!(round_dispatch.replay_artifact_digest_identity(), Some(&digest_identity));
    assert!(round_dispatch.replay_digest_identity_allows_proof_grade());
    assert_eq!(round_dispatch.certificate, certificate);
    assert_eq!(round_dispatch.certificate.production_checker_evidence(), Some(production_checker));
    assert_eq!(round_target_blocker.target, DecompileTarget::Wasm);
    assert_eq!(round_target_blocker.code, "missing-formula-to-target-op-binding");
    assert_eq!(round_target_blocker.stage, "target-proof-consumer");
    assert_eq!(round_target_blocker.origin, Some(origin));
    assert!(round_source_provenance.source_backpropagation_allowed);
    assert!(!round_source_provenance.effective_source_backpropagation_allowed());
    assert_eq!(
        round_source_diagnostics[0].kind,
        BinarySourceProvenanceDiagnosticKind::SourceBackpropagationRejected
    );
    assert!(!round_source_diagnostics[0].source_backpropagation_allowed);
    assert!(round_source_diagnostics[0].binary_address_diagnostics_allowed);
}

#[test]
fn test_binary_origin_json_roundtrip_preserves_exact_instruction_provenance_for_aarch64_and_x86_64()
{
    let aarch64_origin = BinaryOrigin {
        binary_path: Some("fixtures/aarch64/tiny".to_string()),
        function_entry: Some(0x400000),
        instruction_address: 0x400004,
        instruction_size: Some(4),
        encoding: Some(0xd280_0020),
        instruction_bytes: vec![0x20, 0x00, 0x80, 0xd2],
        source: Some(SourceSpan::binary_address(0x400004)),
    };
    let x86_64_origin = BinaryOrigin {
        binary_path: Some("fixtures/x86_64/tiny".to_string()),
        function_entry: Some(0x401000),
        instruction_address: 0x401001,
        instruction_size: Some(1),
        encoding: Some(0x55),
        instruction_bytes: vec![0x55],
        source: Some(SourceSpan::binary_address(0x401001)),
    };
    let ledger = UnsupportedLedger {
        records: vec![
            UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("aarch64".to_string()),
                origin: Some(aarch64_origin.clone()),
                opcode: Some("movz".to_string()),
                operand: Some("x0, #1".to_string()),
                feature: "fixture provenance".to_string(),
            },
            UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("x86_64".to_string()),
                origin: Some(x86_64_origin.clone()),
                opcode: Some("push".to_string()),
                operand: Some("rbp".to_string()),
                feature: "fixture provenance".to_string(),
            },
        ],
    };

    let json = serde_json::to_value(&ledger).expect("serialize unsupported ledger");
    let records = json["records"].as_array().expect("records array");
    assert_eq!(records[0]["architecture"], serde_json::json!("aarch64"));
    assert_eq!(records[0]["origin"]["function_entry"], serde_json::json!(0x400000));
    assert_eq!(records[0]["origin"]["instruction_size"], serde_json::json!(4));
    assert_eq!(
        records[0]["origin"]["instruction_bytes"],
        serde_json::json!([0x20, 0x00, 0x80, 0xd2])
    );
    assert_eq!(records[1]["architecture"], serde_json::json!("x86_64"));
    assert_eq!(records[1]["origin"]["function_entry"], serde_json::json!(0x401000));
    assert_eq!(records[1]["origin"]["instruction_size"], serde_json::json!(1));
    assert_eq!(records[1]["origin"]["instruction_bytes"], serde_json::json!([0x55]));

    let round: UnsupportedLedger = serde_json::from_value(json).expect("roundtrip ledger");
    assert_eq!(round.records[0].origin.as_ref(), Some(&aarch64_origin));
    assert_eq!(round.records[1].origin.as_ref(), Some(&x86_64_origin));
}

#[test]
fn unsupported_ledger_family_counts_are_stable_for_aarch64_and_replay_audits() {
    fn origin(address: u64, bytes: Vec<u8>) -> BinaryOrigin {
        BinaryOrigin {
            binary_path: Some("fixtures/aarch64/tiny".to_string()),
            function_entry: Some(0x400000),
            instruction_address: address,
            instruction_size: Some(bytes.len() as u8),
            encoding: None,
            instruction_bytes: bytes,
            source: Some(SourceSpan::binary_address(address)),
        }
    }

    let ledger = UnsupportedLedger {
        records: vec![
            UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("aarch64".to_string()),
                origin: Some(origin(0x400000, vec![0x9f, 0x3b, 0x03, 0xd5])),
                opcode: Some("dmb".to_string()),
                operand: Some("ish".to_string()),
                feature: "modeled only as an ordering boundary".to_string(),
            },
            UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("AArch64".to_string()),
                origin: Some(origin(0x400004, vec![0x01, 0x00, 0x00, 0xd4])),
                opcode: Some("svc".to_string()),
                operand: Some("#0".to_string()),
                feature: "exception boundary requires privileged trap semantics".to_string(),
            },
            UnsupportedRecord {
                stage: "lift".to_string(),
                architecture: Some("arm64".to_string()),
                origin: Some(origin(0x400008, vec![0x00, 0x02, 0x1f, 0xd6])),
                opcode: Some("ret".to_string()),
                operand: Some("x16".to_string()),
                feature: "non-link register return is a control-flow boundary".to_string(),
            },
            UnsupportedRecord {
                stage: "replay".to_string(),
                architecture: Some("aarch64".to_string()),
                origin: Some(origin(0x40000c, vec![0x1f, 0x20, 0x03, 0xd5])),
                opcode: Some("nop".to_string()),
                operand: None,
                feature: "no original instruction bytes mapped for exact machine replay"
                    .to_string(),
            },
            UnsupportedRecord {
                stage: "machine-replay".to_string(),
                architecture: Some("AArch64".to_string()),
                origin: Some(origin(0x400010, vec![0x00, 0x00, 0x00, 0x94])),
                opcode: Some("bl".to_string()),
                operand: Some("#0x400020".to_string()),
                feature: "unsupported control flow: direct call needs replay witness".to_string(),
            },
        ],
    };

    assert_eq!(ledger.records[0].family_tag(), UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY);
    assert_eq!(ledger.records[1].family_tag(), UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY);
    assert_eq!(ledger.records[2].family_tag(), UNSUPPORTED_FAMILY_AARCH64_CONTROL_FLOW_BOUNDARY);
    assert_eq!(
        ledger.records[3].family_tag(),
        UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY
    );
    assert_eq!(ledger.records[4].family_tag(), UNSUPPORTED_FAMILY_BINARY_REPLAY_CONTROL_FLOW);

    let counts = ledger.family_counts();
    assert_eq!(counts.get(UNSUPPORTED_FAMILY_AARCH64_MEMORY_ORDER_BOUNDARY), Some(&1));
    assert_eq!(counts.get(UNSUPPORTED_FAMILY_AARCH64_EXCEPTION_BOUNDARY), Some(&1));
    assert_eq!(counts.get(UNSUPPORTED_FAMILY_AARCH64_CONTROL_FLOW_BOUNDARY), Some(&1));
    assert_eq!(counts.get(UNSUPPORTED_FAMILY_BINARY_REPLAY_INSTRUCTION_IDENTITY), Some(&1));
    assert_eq!(counts.get(UNSUPPORTED_FAMILY_BINARY_REPLAY_CONTROL_FLOW), Some(&1));
    assert_eq!(ledger.family_count(UNSUPPORTED_FAMILY_UNCLASSIFIED), 0);

    let rows = ledger.family_count_rows();
    assert_eq!(rows.len(), 5);
    assert!(rows.windows(2).all(|pair| pair[0].family < pair[1].family));
}

// ---------------------------------------------------------------------------
// RuntimeDisposition classification
// ---------------------------------------------------------------------------

#[test]
fn test_runtime_disposition_classification_matrix() {
    // Test that the full classification matrix works end-to-end
    let overflow_vc =
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) };
    let postcondition_vc = VcKind::Postcondition;

    // Proved + Auto = Proved
    assert_eq!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Proved {
                solver: "ay".into(),
                time_ms: 1,
                strength: ProofStrength::smt_unsat(),
                proof_certificate: None,
                solver_warnings: None,
                native_proof_envelope: None,
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::Proved,
    );

    // Unknown + Auto + has_runtime_fallback = RuntimeChecked
    assert!(matches!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Unknown {
                solver: "ay".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::RuntimeChecked { .. },
    ));

    // Unknown + Auto + no_runtime_fallback = Unknown
    assert!(matches!(
        classify_runtime_disposition(
            &postcondition_vc,
            &VerificationResult::Unknown {
                solver: "ay".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::Auto,
            true,
        ),
        RuntimeDisposition::Unknown { .. },
    ));

    // Unknown + ForceStatic = CompileError
    assert!(matches!(
        classify_runtime_disposition(
            &overflow_vc,
            &VerificationResult::Unknown {
                solver: "ay".into(),
                time_ms: 1,
                reason: "reason".into(),
            },
            RuntimeCheckPolicy::ForceStatic,
            true,
        ),
        RuntimeDisposition::CompileError { .. },
    ));
}

// ---------------------------------------------------------------------------
// content_hash stability
// ---------------------------------------------------------------------------

#[test]
fn test_content_hash_stable_across_serialization() {
    let func = midpoint_function();
    let hash_before = func.content_hash();

    // Serialize and deserialize
    let json = serde_json::to_string(&func).expect("serialize");
    let round: VerifiableFunction = serde_json::from_str(&json).expect("deserialize");
    let hash_after = round.content_hash();

    assert_eq!(hash_before, hash_after, "content hash must survive serde roundtrip");
}

// ---------------------------------------------------------------------------
// ProofReport roundtrip (legacy format)
// ---------------------------------------------------------------------------

#[test]
fn test_proof_report_legacy_roundtrip() {
    let report = ProofReport {
        crate_name: "my_crate".into(),
        functions: vec![FunctionReport {
            function: "my_crate::foo".into(),
            proved: vec![ProvedProperty {
                description: "division by zero".into(),
                solver: "ay".into(),
                time_ms: 5,
                strength: ProofStrength::smt_unsat(),
                evidence: Some(ProofStrength::smt_unsat().into()),
            }],
            failed: vec![FailedProperty {
                description: "overflow".into(),
                solver: "ay".into(),
                counterexample: Some(Counterexample::new(vec![(
                    "x".into(),
                    CounterexampleValue::Int(i64::MAX as i128),
                )])),
            }],
            unknown: vec![],
        }],
        total_proved: 1,
        total_failed: 1,
        total_unknown: 0,
    };

    let json = serde_json::to_string(&report).expect("serialize");
    let round: ProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "my_crate");
    assert_eq!(round.functions.len(), 1);
    assert_eq!(round.total_proved, 0);
    assert_eq!(round.total_failed, 1);
    assert_eq!(round.total_unknown, 1);
    assert_eq!(round.functions[0].proved.len(), 0);
    assert_eq!(round.functions[0].failed.len(), 1);
    assert_eq!(round.functions[0].unknown.len(), 1);
}

// ---------------------------------------------------------------------------
// JsonProofReport roundtrip
// ---------------------------------------------------------------------------

#[test]
fn test_json_proof_report_deserialization_sanitizes_claimed_authority_and_summaries() {
    let report = JsonProofReport {
        metadata: ReportMetadata {
            schema_version: "0.1.0".into(),
            trust_version: "0.1.0".into(),
            timestamp: "2026-03-29T00:00:00Z".into(),
            total_time_ms: 42,
            timeout_ms: Some(5_000),
            function_budget_ms: Some(120_000),
        },
        crate_name: "test_crate".into(),
        summary: CrateSummary {
            functions_analyzed: 2,
            functions_verified: 1,
            functions_runtime_checked: 0,
            functions_with_violations: 1,
            functions_inconclusive: 0,
            total_obligations: 3,
            total_proved: 2,
            total_runtime_checked: 0,
            total_failed: 1,
            total_unknown: 1,
            total_timed_out: 1,
            total_design_requirements: 0,
            total_unattributed_failed: 0,
            total_unattributed_unknown: 0,
            total_unattributed_proved: 0,
            proof_grade_engine_statuses: Vec::new(),
            verdict: CrateVerdict::HasViolations,
        },
        functions: vec![FunctionProofReport {
            function: "test_crate::ok_fn".into(),
            summary: FunctionSummary {
                total_obligations: 1,
                proved: 1,
                runtime_checked: 0,
                failed: 0,
                unknown: 1,
                timed_out: 1,
                design_requirements: 0,
                unattributed_failed: 0,
                unattributed_unknown: 0,
                unattributed_proved: 0,
                total_time_ms: 5,
                max_proof_level: Some(ProofLevel::L0Safety),
                verdict: FunctionVerdict::Verified,
            },
            obligations: vec![ObligationReport {
                obligation_id: None,
                description: "division by zero".into(),
                kind: "division_by_zero".into(),
                proof_level: ProofLevel::L0Safety,
                location: None,
                outcome: ObligationOutcome::Proved { strength: ProofStrength::smt_unsat() },
                solver: "ay".into(),
                time_ms: 5,
                evidence: None,
                proof_evidence: None,
                transport_evidence: None,
            }],
        }],
        hardened: None,
        assumptions: Vec::new(),
        verification_gate: None,
        cargo_proof_inventory: None,
    };

    let json = serde_json::to_string_pretty(&report).expect("serialize");
    assert!(json.contains("\"total_timed_out\": 1"));
    assert!(json.contains("\"timed_out\": 1"));
    assert!(json.contains("\"timeout_ms\": 5000"));
    assert!(json.contains("\"function_budget_ms\": 120000"));
    let round: JsonProofReport = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.crate_name, "test_crate");
    assert_eq!(round.summary.verdict, CrateVerdict::Inconclusive);
    assert_eq!(round.summary.total_proved, 0);
    assert_eq!(round.summary.total_unknown, 1);
    assert_eq!(round.summary.total_timed_out, 0);
    assert_eq!(round.functions.len(), 1);
    assert_eq!(round.functions[0].summary.timed_out, 0);
    assert_eq!(round.functions[0].summary.verdict, FunctionVerdict::Inconclusive);
    assert!(matches!(round.functions[0].obligations[0].outcome, ObligationOutcome::Unknown { .. }));
    assert_eq!(round.metadata.timeout_ms, Some(5_000));
    assert_eq!(round.metadata.function_budget_ms, Some(120_000));

    // Backward compatibility: reports written before the additive metadata
    // fields deserialize with no invented policy values.
    let mut legacy: serde_json::Value = serde_json::from_str(&json).expect("JSON value");
    legacy["metadata"].as_object_mut().expect("metadata object").remove("function_budget_ms");
    legacy["metadata"].as_object_mut().expect("metadata object").remove("timeout_ms");
    let legacy_round: JsonProofReport =
        serde_json::from_value(legacy).expect("legacy report should deserialize");
    assert_eq!(legacy_round.metadata.timeout_ms, None);
    assert_eq!(legacy_round.metadata.function_budget_ms, None);
}

// ---------------------------------------------------------------------------
// VcKind proof_level consistency
// ---------------------------------------------------------------------------

#[test]
fn test_vc_kind_proof_level_consistency() {
    // L0 Safety kinds
    let l0_kinds = vec![
        VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (Ty::i32(), Ty::i32()) },
        VcKind::DivisionByZero,
        VcKind::RemainderByZero,
        VcKind::IndexOutOfBounds,
        VcKind::SliceBoundsCheck,
        VcKind::Assertion { message: "test".into() },
        VcKind::CastOverflow { from_ty: Ty::i32(), to_ty: Ty::u32() },
        VcKind::NegationOverflow { ty: Ty::i32() },
        VcKind::Unreachable,
    ];
    for kind in &l0_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L0Safety, "expected L0 for {:?}", kind);
    }

    // L1 Functional kinds
    let l1_kinds = vec![
        VcKind::Precondition { callee: "f".into() },
        VcKind::Postcondition,
        VcKind::NonTermination { context: "loop".into(), measure: "n".into() },
    ];
    for kind in &l1_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L1Functional, "expected L1 for {:?}", kind);
    }

    // L2 Domain kinds
    let l2_kinds = vec![
        VcKind::Deadlock,
        VcKind::DeadState { state: "s".into() },
        VcKind::Temporal { machine: None, property: "p".into() },
    ];
    for kind in &l2_kinds {
        assert_eq!(kind.proof_level(), ProofLevel::L2Domain, "expected L2 for {:?}", kind);
    }
}

// ---------------------------------------------------------------------------
// W2 inc-0: Rvalue::PtrOffset serialization + additive compat
// ---------------------------------------------------------------------------

/// The modeled MIR `BinOp::Offset` — `Rvalue::PtrOffset { ptr, count }` — must
/// round-trip through serde as its own distinguishable, named-field variant.
/// Mirrors the real `Iter::next` cursor post-increment: `Offset(_14, 1u64)`.
#[test]
fn ptr_offset_rvalue_serde_roundtrip_preserves_variant() {
    let rvalue = Rvalue::PtrOffset {
        ptr: Operand::Copy(Place::local(14)),
        count: Operand::Constant(ConstValue::Uint(1, 64)),
    };
    let json = serde_json::to_string(&rvalue).expect("serialize PtrOffset");
    // Externally-tagged, additive variant: keyed by its own name, with named fields.
    assert!(json.contains("\"PtrOffset\""), "serialized under its own tag: {json}");
    assert!(json.contains("\"ptr\"") && json.contains("\"count\""), "named fields: {json}");

    let round: Rvalue = serde_json::from_str(&json).expect("deserialize PtrOffset");
    match &round {
        Rvalue::PtrOffset { ptr, count } => {
            assert!(matches!(ptr, Operand::Copy(p) if p.local == 14), "ptr operand preserved");
            assert!(
                matches!(count, Operand::Constant(ConstValue::Uint(1, 64))),
                "count operand preserved"
            );
        }
        other => panic!("PtrOffset must round-trip to PtrOffset, got {other:?}"),
    }
    // Round-trip stability: re-serializing the decoded value reproduces the wire form.
    assert_eq!(serde_json::to_string(&round).unwrap(), json);
}

/// Adding the `PtrOffset` variant is ADDITIVE: an OLD dump that erased
/// `BinOp::Offset` to an `Unsupported` marker (the pre-W2-inc-0 spelling) must
/// still parse as `Unsupported` — never silently reinterpreted as `PtrOffset` —
/// so committed corpora keep both their content and their fail-closed verdict.
#[test]
fn old_unsupported_binop_offset_marker_still_deserializes() {
    let old = r#"{"Unsupported":{"kind":"BinOp::Offset","detail":"operation requires explicit MIR semantics before proof","operands":[{"Copy":{"local":14,"projections":[]}},{"Constant":{"Uint":[1,64]}}]}}"#;
    let rvalue: Rvalue =
        serde_json::from_str(old).expect("old Unsupported BinOp::Offset marker must still parse");
    match rvalue {
        Rvalue::Unsupported { kind, operands, .. } => {
            assert_eq!(kind, "BinOp::Offset", "old marker stays Unsupported, not PtrOffset");
            assert_eq!(operands.len(), 2, "operands preserved");
        }
        other => panic!("old marker must stay Unsupported, got {other:?}"),
    }
}
