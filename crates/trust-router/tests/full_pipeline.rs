// trust-router/tests/full_pipeline.rs: Full end-to-end pipeline integration tests
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_report::build_json_report;
use trust_router::{BackendRole, Router, VerificationBackend};
use trust_types::*;
use trust_vcgen::generate_vcs;

fn division_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "divide".to_string(),
        def_path: "pipeline::divide".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 10,
            col_start: 1,
            line_end: 12,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("y".into()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::local(3))),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn bounded_checked_mul_function() -> VerifiableFunction {
    let ty = Ty::u32();
    VerifiableFunction {
        name: "bounded_checked_mul".to_string(),
        def_path: "pipeline::bounded_checked_mul".to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 20,
            col_start: 1,
            line_end: 24,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: ty.clone(), name: None },
                LocalDecl { index: 1, ty: ty.clone(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: ty.clone(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![ty.clone(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Mul,
                            Operand::Copy(Place::local(1)),
                            Operand::Copy(Place::local(2)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Mul),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(0),
                        rvalue: Rvalue::Use(Operand::Copy(Place::field(3, 0))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: ty,
        },
        contracts: vec![],
        preconditions: vec![
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::var("a", Sort::Int))),
                Formula::Le(Box::new(Formula::var("a", Sort::Int)), Box::new(Formula::Int(1000))),
            ]),
            Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(Formula::var("b", Sort::Int))),
                Formula::Le(Box::new(Formula::var("b", Sort::Int)), Box::new(Formula::Int(1000))),
            ]),
        ],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn formula_contains_var(formula: &Formula, expected_name: &str) -> bool {
    match formula {
        Formula::Var(name, _) => name == expected_name,
        Formula::SymVar(symbol, _) => symbol.as_str() == expected_name,
        _ => formula.children().into_iter().any(|child| formula_contains_var(child, expected_name)),
    }
}

fn recursive_countdown_function() -> VerifiableFunction {
    VerifiableFunction {
        name: "countdown".to_string(),
        def_path: "pipeline::countdown".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u32(), name: None },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        is_unsafe_sig: false,
                        is_foreign: false,
                        // E5 recursion rows require the compiler-owned exact
                        // definition identity; a bare same-name callee is not
                        // sufficient authority to classify a self-call.
                        func: "pipeline::countdown".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(0),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn proved_by(solver: &str, strength: ProofStrength) -> VerificationResult {
    VerificationResult::Proved {
        solver: solver.into(),
        time_ms: 1,
        strength,
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn division_vc() -> VerificationCondition {
    generate_vcs(&division_function())
        .into_iter()
        .find(|vc| matches!(vc.kind, VcKind::DivisionByZero))
        .expect("division function should produce a division-by-zero VC")
}

fn handles_l0(vc: &VerificationCondition) -> bool {
    matches!(vc.kind.proof_level(), ProofLevel::L0Safety)
}

fn handles_postcondition(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::Postcondition)
}

fn handles_precondition(vc: &VerificationCondition) -> bool {
    matches!(vc.kind, VcKind::Precondition { .. })
}

fn handles_temporal(vc: &VerificationCondition) -> bool {
    matches!(
        vc.kind,
        VcKind::DeadState { .. }
            | VcKind::Deadlock
            | VcKind::Temporal { .. }
            | VcKind::Liveness { .. }
            | VcKind::Fairness { .. }
            | VcKind::RefinementViolation { .. }
            | VcKind::ProtocolViolation { .. }
    )
}

struct SpecialtyBackend {
    name: &'static str,
    role: BackendRole,
    can_handle_fn: fn(&VerificationCondition) -> bool,
    result: VerificationResult,
}

impl SpecialtyBackend {
    fn new(
        name: &'static str,
        role: BackendRole,
        can_handle_fn: fn(&VerificationCondition) -> bool,
        result: VerificationResult,
    ) -> Self {
        Self { name, role, can_handle_fn, result }
    }
}

impl VerificationBackend for SpecialtyBackend {
    fn name(&self) -> &str {
        self.name
    }

    fn role(&self) -> BackendRole {
        self.role
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        (self.can_handle_fn)(vc)
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        self.result.clone()
    }
}

#[test]
fn test_full_pipeline_recursion_e5_requires_exact_callee_identity() {
    let mut function = recursive_countdown_function();
    let exact_vcs = generate_vcs(&function);
    assert!(
        exact_vcs
            .iter()
            .any(|vc| matches!(&vc.kind, VcKind::NonTermination { context, .. } if context == "recursion")),
        "the exact definition path must emit the proof-gated E5 recursion row: {exact_vcs:#?}",
    );

    let Terminator::Call { func: callee, .. } = &mut function.body.blocks[0].terminator else {
        panic!("countdown fixture must start with a call");
    };
    *callee = "countdown".to_string();

    let vcs = generate_vcs(&function);
    assert!(
        vcs.iter().all(|vc| !matches!(vc.kind, VcKind::NonTermination { .. })),
        "a bare same-name callee must not authorize a proof-gated E5 recursion row: {vcs:#?}",
    );
}

#[test]
fn test_full_pipeline_interval_proves_vcgen_bounded_unsigned_mul() {
    let vcs = generate_vcs(&bounded_checked_mul_function());
    let mul_overflow_vcs = vcs
        .iter()
        .filter(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
        .collect::<Vec<_>>();
    assert_eq!(mul_overflow_vcs.len(), 1, "expected exactly one checked Mul overflow VC");

    assert!(
        formula_contains_var(&mul_overflow_vcs[0].formula, "__trust_ovf_bv_lhs_a")
            && formula_contains_var(&mul_overflow_vcs[0].formula, "__trust_ovf_bv_rhs_b"),
        "vcgen checked unsigned Mul VC must expose fresh BV operand names for interval routing: {:?}",
        mul_overflow_vcs[0].formula
    );

    let router = Router::with_backends(vec![
        Box::new(trust_router::interval_backend::IntervalBackend),
        Box::new(trust_router::constant_folder::ConstantFolderBackend),
    ]);
    let results = router.verify_all(&vcs);

    assert_eq!(results.len(), vcs.len());
    assert!(
        results.iter().all(|(_, result)| result.is_proved()),
        "bounded checked unsigned Mul fixture should be fully proved by the router: {results:?}"
    );
    assert!(
        results.iter().any(|(vc, result)| {
            matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. })
                && result.solver_name() == "interval"
        }),
        "Mul overflow VC should route through the interval backend: {results:?}"
    );

    let report = build_json_report("bounded_mul_pipeline", &results);
    assert_eq!(report.summary.total_failed, 0);
    // The router result above proves interval routing, but a freely
    // constructible status has no request-bound publication authority.
    assert_eq!(report.summary.total_proved, 0);
    assert_eq!(report.summary.total_unknown, results.len());
}

/// Trust: the falsification control the goal demands — `bounded_checked_mul`
/// with its `0 <= a,b <= 1000` precondition DROPPED (the "drop a precondition"
/// mutation). The overflow obligation must now FAIL: an unconstrained u32 `a*b`
/// can overflow (e.g. a=b=65536 ⇒ 2^32). A verifier that still "proves" this is
/// vacuous.
fn unbounded_checked_mul_function() -> VerifiableFunction {
    let mut func = bounded_checked_mul_function();
    func.name = "unbounded_checked_mul".to_string();
    func.def_path = "pipeline::unbounded_checked_mul".to_string();
    // The mutation: remove the input bounds that made the multiplication safe.
    func.preconditions.clear();
    func
}

/// The goal's falsification self-test, at IR level through the REAL backends:
/// proving a real overflow obligation is only meaningful if a buggy variant
/// FAILS. Dropping the `a,b <= 1000` precondition must flip the verdict from
/// proved to refuted. If it does not flip, the original "proof" was vacuous —
/// which is exactly the failure mode this whole effort exists to prevent.
#[test]
fn mutation_control_dropping_precondition_flips_overflow_proof() {
    fn mul_overflow_result(func: &VerifiableFunction) -> VerificationResult {
        let vcs = generate_vcs(func);
        let router = Router::with_backends(vec![
            Box::new(trust_router::interval_backend::IntervalBackend),
            Box::new(trust_router::constant_folder::ConstantFolderBackend),
        ]);
        let results = router.verify_all(&vcs);
        results
            .into_iter()
            .find(|(vc, _)| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .map(|(_, result)| result)
            .expect("a checked Mul overflow VC must be generated")
    }

    let bounded = mul_overflow_result(&bounded_checked_mul_function());
    let unbounded = mul_overflow_result(&unbounded_checked_mul_function());

    // The real obligation proves non-vacuously when the bound holds...
    assert!(bounded.is_proved(), "bounded a*b (a,b <= 1000) must prove safe: {bounded:?}");

    // ...and the mutant must NOT remain proved. This is the load-bearing
    // anti-vacuity assertion: the verifier never certifies what is not true.
    assert!(
        !unbounded.is_proved(),
        "MUTANT NOT FALSIFIED: dropping the precondition left a*b still 'proved' — \
         the proof was vacuous. Got: {unbounded:?}"
    );
    // With interval+folder the mutant lands on Unknown (interval cannot bound an
    // unconstrained product). Under fail-closed semantics an unknown real
    // obligation is a compile error, so the verdict still flips. The strong form
    // — an actual refuting counterexample — is exercised by
    // `mutation_control_ay_refutes_unbounded_overflow` below (ay-backend).
}

/// The strongest form of the falsification control: the real `ay` SMT solver
/// must REFUTE the mutant with a concrete counterexample, not merely fail to
/// prove it. Gated on the `ay-backend` feature because it drives the in-process
/// solver. Run with: `cargo test -p trust-router --features ay-backend`.
#[cfg(feature = "ay-backend")]
#[test]
fn mutation_control_ay_refutes_unbounded_overflow() {
    fn mul_overflow_result(func: &VerifiableFunction) -> VerificationResult {
        let vcs = generate_vcs(func);
        let router = Router::with_backends(vec![
            Box::new(trust_router::interval_backend::IntervalBackend),
            Box::new(trust_router::InProcessAyBackend::new()),
            Box::new(trust_router::constant_folder::ConstantFolderBackend),
        ]);
        router
            .verify_all(&vcs)
            .into_iter()
            .find(|(vc, _)| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Mul, .. }))
            .map(|(_, result)| result)
            .expect("a checked Mul overflow VC must be generated")
    }

    let bounded = mul_overflow_result(&bounded_checked_mul_function());
    let unbounded = mul_overflow_result(&unbounded_checked_mul_function());

    assert!(bounded.is_proved(), "bounded a*b (a,b <= 1000) must prove safe: {bounded:?}");
    assert!(
        unbounded.is_failed(),
        "MUTANT NOT REFUTED: ay must produce a counterexample for unbounded a*b \
         (the proof was vacuous if it does not): {unbounded:?}"
    );
}

/// Anti-vacuity control for a SECOND obligation kind (division-by-zero),
/// through the real `ay` SMT solver. `divide(x, y) = x / y` with no guard on `y`
/// has a reachable division-by-zero (`y = 0`); the verifier must REFUTE it, not
/// vacuously certify it safe. This is the falsification-sensitivity property on
/// a different kind than arithmetic overflow.
#[cfg(feature = "ay-backend")]
#[test]
fn ay_refutes_unguarded_division_by_zero() {
    let vcs = generate_vcs(&division_function());
    let router = Router::with_backends(vec![
        Box::new(trust_router::InProcessAyBackend::new()),
        Box::new(trust_router::constant_folder::ConstantFolderBackend),
    ]);
    let div_result = router
        .verify_all(&vcs)
        .into_iter()
        .find(|(vc, _)| matches!(vc.kind, VcKind::DivisionByZero))
        .map(|(_, result)| result)
        .expect("a division-by-zero VC must be generated");

    assert!(
        div_result.is_failed(),
        "VACUITY BUG: unguarded x/y must be refuted (y=0 is reachable), not proved or unknown: \
         {div_result:?}"
    );
}

#[test]
fn test_full_pipeline_multi_backend_routing_by_proof_level() {
    let safety_vc = division_vc();
    let post_vc = VerificationCondition {
        kind: VcKind::Postcondition,
        function: "functional_post".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let pre_vc = VerificationCondition {
        kind: VcKind::Precondition { callee: "callee".into() },
        function: "functional_pre".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let domain_vc = VerificationCondition {
        kind: VcKind::Deadlock,
        function: "domain".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };
    let fallback_vc = VerificationCondition {
        kind: VcKind::ResilienceViolation {
            service: "storage".into(),
            failure_mode: "timeout".into(),
            reason: "transient".into(),
        },
        function: "resilience".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
    };

    let router = Router::with_backends(vec![
        Box::new(SpecialtyBackend::new(
            "constant-folder",
            BackendRole::General,
            |_| true,
            proved_by("constant-folder", ProofStrength::smt_unsat()),
        )),
        Box::new(SpecialtyBackend::new(
            "trust-vc",
            BackendRole::Ownership,
            handles_precondition,
            proved_by("trust-vc", ProofStrength::deductive()),
        )),
        Box::new(SpecialtyBackend::new(
            "ty",
            BackendRole::Temporal,
            handles_temporal,
            proved_by("ty", ProofStrength::inductive()),
        )),
        Box::new(SpecialtyBackend::new(
            "trust-mc",
            BackendRole::BoundedModelChecker,
            handles_l0,
            proved_by("trust-mc", ProofStrength::bounded(8)),
        )),
        Box::new(SpecialtyBackend::new(
            "trust-wp",
            BackendRole::Deductive,
            handles_postcondition,
            proved_by("trust-wp", ProofStrength::deductive()),
        )),
    ]);

    let safety_result = router.verify_one(&safety_vc);
    let post_result = router.verify_one(&post_vc);
    let pre_result = router.verify_one(&pre_vc);
    let domain_result = router.verify_one(&domain_vc);
    let fallback_result = router.verify_one(&fallback_vc);

    assert_eq!(router.backend_plan(&safety_vc)[0].name, "trust-mc");
    assert_eq!(router.backend_plan(&post_vc)[0].name, "trust-wp");
    assert_eq!(router.backend_plan(&pre_vc)[0].name, "trust-vc");
    assert_eq!(router.backend_plan(&domain_vc)[0].name, "ty");
    assert_eq!(router.backend_plan(&fallback_vc)[0].name, "constant-folder");

    assert_eq!(safety_result.solver_name(), "trust-mc");
    assert_eq!(post_result.solver_name(), "trust-wp");
    assert_eq!(pre_result.solver_name(), "trust-vc");
    assert_eq!(domain_result.solver_name(), "ty");
    assert_eq!(fallback_result.solver_name(), "constant-folder");

    let results = vec![
        (safety_vc, safety_result),
        (post_vc, post_result),
        (pre_vc, pre_result),
        (domain_vc, domain_result),
        (fallback_vc, fallback_result),
    ];
    let report = build_json_report("routing_pipeline", &results);
    assert_eq!(report.summary.total_obligations, 5);
    // These specialty backends establish routing, not publication authority.
    // Their freely constructible static Proved statuses remain Unknown, while
    // the bounded TrustMc status is honestly classified as runtime-checked.
    assert_eq!(report.summary.total_proved, 0);
    // The bounded TrustMc status classifies as runtime-checked only when its
    // replay validation cannot run; when a real ay is reachable (the
    // `ay-backend` feature, or an ambient sibling ay binary), the mock's
    // freely constructed bounded evidence faces real validation, cannot
    // survive it, and demotes to Unknown — fail-closed. Both worlds are
    // legitimate, so the pin asserts the invariant (never a third
    // classification, never a proof) and the exact legal pair.
    let pair = (report.summary.total_unknown, report.summary.total_runtime_checked);
    assert!(
        pair == (4, 1) || pair == (5, 0),
        "unexpected classification split: {pair:?}"
    );
}

