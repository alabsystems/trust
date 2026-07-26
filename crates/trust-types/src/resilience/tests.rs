use super::helpers::detect_panic_call;
use super::*;
use crate::{BlockId, SourceSpan, VerifiableFunction};

#[test]
fn test_failure_mode_display() {
    assert_eq!(FailureMode::Timeout.to_string(), "timeout");
    assert_eq!(FailureMode::Error.to_string(), "error");
    assert_eq!(FailureMode::Unavailable.to_string(), "unavailable");
    assert_eq!(FailureMode::Partial.to_string(), "partial");
    assert_eq!(FailureMode::Custom("rate_limited".into()).to_string(), "rate_limited");
}

#[test]
fn test_failure_model_empty() {
    let model = FailureModel::new("test_fn");
    assert!(model.is_empty());
    assert_eq!(model.failure_combination_count(), 1); // just "all healthy"
}

#[test]
fn test_failure_combination_count() {
    let model = FailureModel {
        function: "test_fn".to_string(),
        dependencies: vec![
            ExternalDependency {
                name: "redis".to_string(),
                failure_modes: vec![FailureMode::Timeout, FailureMode::Error],
                block: BlockId(0),
                span: SourceSpan::default(),
                call_path: "redis::get".to_string(),
            },
            ExternalDependency {
                name: "postgres".to_string(),
                failure_modes: vec![
                    FailureMode::Timeout,
                    FailureMode::Error,
                    FailureMode::Unavailable,
                ],
                block: BlockId(1),
                span: SourceSpan::default(),
                call_path: "sqlx::query".to_string(),
            },
        ],
    };

    // redis: 3 states (healthy + 2 failures), postgres: 4 states (healthy + 3 failures)
    // total: 3 * 4 = 12
    assert_eq!(model.failure_combination_count(), 12);
}

#[test]
fn test_failure_scenarios_generation() {
    let model = FailureModel {
        function: "test_fn".to_string(),
        dependencies: vec![
            ExternalDependency {
                name: "redis".to_string(),
                failure_modes: vec![FailureMode::Timeout],
                block: BlockId(0),
                span: SourceSpan::default(),
                call_path: "redis::get".to_string(),
            },
            ExternalDependency {
                name: "fs".to_string(),
                failure_modes: vec![FailureMode::Error],
                block: BlockId(1),
                span: SourceSpan::default(),
                call_path: "std::fs::read".to_string(),
            },
        ],
    };

    let scenarios = model.failure_scenarios();
    // redis: 2 states (healthy, timeout), fs: 2 states (healthy, error)
    // 2 * 2 = 4 scenarios
    assert_eq!(scenarios.len(), 4);

    // Verify all 4 combos exist:
    // (healthy, healthy), (healthy, error), (timeout, healthy), (timeout, error)
    assert!(scenarios.contains(&vec![None, None]));
    assert!(scenarios.contains(&vec![None, Some(FailureMode::Error)]));
    assert!(scenarios.contains(&vec![Some(FailureMode::Timeout), None]));
    assert!(scenarios.contains(&vec![Some(FailureMode::Timeout), Some(FailureMode::Error),]));
}

#[test]
fn test_failure_scenarios_empty_model() {
    let model = FailureModel::new("test_fn");
    let scenarios = model.failure_scenarios();
    assert_eq!(scenarios.len(), 1);
    assert_eq!(scenarios[0].len(), 0);
}

#[test]
fn test_match_external_call_http() {
    let result = match_external_call("reqwest::Client::<T>::get");
    assert!(result.is_some());
    let (service, modes) = result.unwrap();
    assert_eq!(service, "http");
    assert!(modes.contains(&FailureMode::Timeout));
    assert!(modes.contains(&FailureMode::Error));
    assert!(modes.contains(&FailureMode::Unavailable));
}

#[test]
fn test_match_external_call_database() {
    let result = match_external_call("sqlx::query");
    assert!(result.is_some());
    assert_eq!(result.unwrap().0, "database");
}

#[test]
fn test_match_external_call_redis() {
    let result = match_external_call("redis::Commands::get");
    assert!(result.is_some());
    assert_eq!(result.unwrap().0, "redis");
}

#[test]
fn test_match_external_call_filesystem() {
    let result = match_external_call("std::fs::File::open");
    assert!(result.is_some());
    let (service, modes) = result.unwrap();
    assert_eq!(service, "filesystem");
    assert!(modes.contains(&FailureMode::Error));
}

#[test]
fn test_match_external_call_network() {
    let result = match_external_call("std::net::TcpStream::connect");
    assert!(result.is_some());
    assert_eq!(result.unwrap().0, "network");

    let result = match_external_call("tokio::net::TcpStream::connect");
    assert!(result.is_some());
    assert_eq!(result.unwrap().0, "network");
}

#[test]
fn test_match_external_call_no_match() {
    assert!(match_external_call("std::vec::Vec::push").is_none());
    assert!(match_external_call("my_crate::do_thing").is_none());
}

#[test]
fn test_extract_failure_model() {
    use crate::*;

    let func = VerifiableFunction {
        name: "handle_request".to_string(),
        def_path: "server::handle_request".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Unit, name: Some("cache_result".into()) },
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("db_result".into()) },
            ],
            blocks: vec![
                // bb0: redis get
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "redis::Commands::get".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "server.rs".into(),
                            line_start: 10,
                            col_start: 4,
                            line_end: 10,
                            col_end: 30,
                        },
                        atomic: None,
                    },
                },
                // bb1: database query
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "sqlx::query".to_string(),
                        args: vec![],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: SourceSpan {
                            file: "server.rs".into(),
                            line_start: 15,
                            col_start: 4,
                            line_end: 15,
                            col_end: 25,
                        },
                        atomic: None,
                    },
                },
                // bb2: return
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let model = extract_failure_model(&func);
    assert_eq!(model.function, "server::handle_request");
    assert_eq!(model.dependencies.len(), 2);
    assert_eq!(model.dependencies[0].name, "redis");
    assert_eq!(model.dependencies[1].name, "database");

    // redis has 3 failure modes, database has 3: (1+3) * (1+3) = 16
    assert_eq!(model.failure_combination_count(), 16);
}

#[test]
fn test_extract_failure_model_no_externals() {
    use crate::*;

    let func = VerifiableFunction {
        name: "add".to_string(),
        def_path: "math::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::usize(), name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let model = extract_failure_model(&func);
    assert!(model.is_empty());
}

#[test]
fn test_resilience_check_result_serialization() {
    let result = ResilienceCheckResult {
        scenario: vec![
            ("redis".to_string(), Some(FailureMode::Timeout)),
            ("postgres".to_string(), None),
        ],
        is_resilient: false,
        violation: Some("unwrap on Result from redis call".to_string()),
        violation_block: Some(BlockId(3)),
    };

    let json = serde_json::to_string(&result).expect("serialize");
    let round: ResilienceCheckResult = serde_json::from_str(&json).expect("deserialize");
    assert!(!round.is_resilient);
    assert_eq!(round.scenario.len(), 2);
    assert_eq!(round.scenario[0].0, "redis");
    assert!(round.violation.is_some());
}

#[test]
fn test_failure_model_serialization_roundtrip() {
    let model = FailureModel {
        function: "test_fn".to_string(),
        dependencies: vec![ExternalDependency {
            name: "redis".to_string(),
            failure_modes: vec![FailureMode::Timeout, FailureMode::Error],
            block: BlockId(0),
            span: SourceSpan::default(),
            call_path: "redis::Commands::get".to_string(),
        }],
    };

    let json = serde_json::to_string(&model).expect("serialize");
    let round: FailureModel = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(round.function, "test_fn");
    assert_eq!(round.dependencies.len(), 1);
    assert_eq!(round.dependencies[0].failure_modes.len(), 2);
}

// -----------------------------------------------------------------------
// New tests: FaultModel, ResilienceProperty, ResilienceAnalysis
// -----------------------------------------------------------------------

#[test]
fn test_fault_model_display() {
    assert_eq!(FaultModel::PanicOnError.to_string(), "panic-on-error");
    assert_eq!(FaultModel::ReturnError.to_string(), "return-error");
    assert_eq!(FaultModel::SilentCorruption.to_string(), "silent-corruption");
    assert_eq!(FaultModel::ByzantineFault.to_string(), "byzantine-fault");
}

#[test]
fn test_resilience_property_display() {
    assert_eq!(ResilienceProperty::Idempotent.to_string(), "idempotent");
    assert_eq!(ResilienceProperty::Commutative.to_string(), "commutative");
    assert_eq!(ResilienceProperty::Monotonic.to_string(), "monotonic");
    assert_eq!(ResilienceProperty::CrashConsistent.to_string(), "crash-consistent");
}

#[test]
fn test_fault_model_serialization_roundtrip() {
    let models = [
        FaultModel::PanicOnError,
        FaultModel::ReturnError,
        FaultModel::SilentCorruption,
        FaultModel::ByzantineFault,
    ];
    for model in &models {
        let json = serde_json::to_string(model).expect("serialize");
        let round: FaultModel = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(*model, round);
    }
}

#[test]
fn test_resilience_property_serialization_roundtrip() {
    let props = [
        ResilienceProperty::Idempotent,
        ResilienceProperty::Commutative,
        ResilienceProperty::Monotonic,
        ResilienceProperty::CrashConsistent,
    ];
    for prop in &props {
        let json = serde_json::to_string(prop).expect("serialize");
        let round: ResilienceProperty = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(*prop, round);
    }
}

fn make_simple_return_func(name: &str) -> VerifiableFunction {
    use crate::*;
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{}", name),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Return,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn test_analyze_pure_function_low_risk() {
    let func = make_simple_return_func("pure_fn");
    let report = ResilienceAnalysis::analyze_function(&func);

    assert_eq!(report.function, "test::pure_fn");
    assert!(report.panic_paths.is_empty());
    assert!(report.unchecked_arithmetic.is_empty());
    assert_eq!(report.risk_score, 0.0);
    assert!(report.recommendations.is_empty());
    assert!(report.properties.contains(&ResilienceProperty::CrashConsistent));
}

#[test]
fn test_analyze_function_with_overflow_assert() {
    use crate::*;

    let func = VerifiableFunction {
        name: "add".to_string(),
        def_path: "math::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
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
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(3, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(1),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);

    assert_eq!(report.panic_paths.len(), 1);
    assert_eq!(report.panic_paths[0].kind, PanicKind::Overflow);
    assert!(report.risk_score > 0.0);
}

#[test]
fn test_analyze_function_with_unwrap_call() {
    use crate::*;

    let func = VerifiableFunction {
        name: "risky".to_string(),
        def_path: "mod::risky".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "std::result::Result::unwrap".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan {
                            file: "test.rs".into(),
                            line_start: 5,
                            col_start: 1,
                            line_end: 5,
                            col_end: 20,
                        },
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);

    assert_eq!(report.panic_paths.len(), 1);
    assert_eq!(report.panic_paths[0].kind, PanicKind::Unwrap);
    assert!(report.recommendations.iter().any(|r| r.contains("unwrap()")));
    assert!(report.risk_score > 0.0);
}

#[test]
fn test_analyze_function_with_unchecked_arithmetic() {
    use crate::*;

    let func = VerifiableFunction {
        name: "unchecked_add".to_string(),
        def_path: "math::unchecked_add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);

    assert_eq!(report.unchecked_arithmetic.len(), 1);
    assert_eq!(report.unchecked_arithmetic[0].op, BinOp::Add);
    assert!(report.recommendations.iter().any(|r| r.contains("checked arithmetic")));
}

#[test]
fn test_analyze_function_detects_division_risk() {
    use crate::*;

    let func = VerifiableFunction {
        name: "div".to_string(),
        def_path: "math::div".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);

    assert!(report.unchecked_arithmetic.iter().any(|u| u.op == BinOp::Div));
}

#[test]
fn test_analyze_function_detects_commutative() {
    use crate::*;

    let func = VerifiableFunction {
        name: "add".to_string(),
        def_path: "math::add".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::CheckedBinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);
    assert!(report.properties.contains(&ResilienceProperty::Commutative));
    assert!(report.properties.contains(&ResilienceProperty::CrashConsistent));
}

#[test]
fn test_analyze_function_with_external_deps_and_unwrap() {
    use crate::*;

    let func = VerifiableFunction {
        name: "fetch_and_unwrap".to_string(),
        def_path: "server::fetch_and_unwrap".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Unit, name: Some("resp".into()) },
                LocalDecl { index: 2, ty: Ty::Unit, name: Some("value".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "redis::Commands::get".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::result::Result::unwrap".to_string(),
                        args: vec![Operand::Move(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(2)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);

    // Has panic path from unwrap
    assert!(report.panic_paths.iter().any(|p| p.kind == PanicKind::Unwrap));
    // Has external dependency
    assert!(!report.failure_model.is_empty());
    assert_eq!(report.failure_model.dependencies[0].name, "redis");
    // Has error handling pattern classified as panicking
    assert!(
        report.error_handling.iter().any(|e| matches!(e, ErrorHandlingPattern::Panicking { .. }))
    );
    // Fault model should be PanicOnError
    assert_eq!(report.fault_model, FaultModel::PanicOnError);
    // Risk score should be notable
    assert!(report.risk_score > 0.1);
}

#[test]
fn test_resilience_report_serialization_roundtrip() {
    let func = make_simple_return_func("serde_test");
    let report = ResilienceAnalysis::analyze_function(&func);

    let json = serde_json::to_string(&report).expect("serialize report");
    let round: ResilienceReport = serde_json::from_str(&json).expect("deserialize report");
    assert_eq!(round.function, "test::serde_test");
    assert_eq!(round.fault_model, report.fault_model);
    assert_eq!(round.properties.len(), report.properties.len());
}

#[test]
fn test_risk_score_scales_with_issues() {
    // More panic paths + unchecked arithmetic = higher risk.
    let panic_paths_0: Vec<PanicPath> = vec![];
    let unchecked_0: Vec<UncheckedArithmetic> = vec![];
    let model_0 = FailureModel::new("f");
    let score_0 = ResilienceAnalysis::compute_risk_score(&panic_paths_0, &unchecked_0, &model_0);

    let panic_paths_2 = vec![
        PanicPath {
            block: BlockId(0),
            span: SourceSpan::default(),
            description: "unwrap".into(),
            kind: PanicKind::Unwrap,
        },
        PanicPath {
            block: BlockId(1),
            span: SourceSpan::default(),
            description: "expect".into(),
            kind: PanicKind::Expect,
        },
    ];
    let score_2 = ResilienceAnalysis::compute_risk_score(&panic_paths_2, &unchecked_0, &model_0);

    assert!(score_0 < score_2, "more panic paths = higher risk");
}

#[test]
fn test_detect_panic_call_patterns() {
    assert_eq!(detect_panic_call("core::result::Result::unwrap"), Some(PanicKind::Unwrap));
    assert_eq!(detect_panic_call("core::option::Option::expect"), Some(PanicKind::Expect));
    assert_eq!(detect_panic_call("std::panic"), Some(PanicKind::ExplicitPanic));
    assert_eq!(detect_panic_call("std::vec::Vec::push"), None);
    // unwrap_or should NOT be detected as a panic.
    assert_eq!(detect_panic_call("core::result::Result::unwrap_or"), None);
}

#[test]
fn test_error_handling_swallowing_detected() {
    use crate::*;

    // Build: bb0 calls "get_data", bb1 does NOT reference dest local at all.
    let func = VerifiableFunction {
        name: "swallow".to_string(),
        def_path: "test::swallow".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Unit, name: Some("result".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "get_data".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);
    assert!(
        report.error_handling.iter().any(|e| matches!(e, ErrorHandlingPattern::Swallowing { .. }))
    );
    assert_eq!(report.fault_model, FaultModel::SilentCorruption);
}

#[test]
fn test_unreachable_terminator_detected_as_panic() {
    use crate::*;

    let func = VerifiableFunction {
        name: "unreachable_fn".to_string(),
        def_path: "test::unreachable_fn".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: Ty::Unit, name: None }],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: Terminator::Unreachable,
            }],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };

    let report = ResilienceAnalysis::analyze_function(&func);
    assert_eq!(report.panic_paths.len(), 1);
    assert_eq!(report.panic_paths[0].kind, PanicKind::ExplicitPanic);
}

// -----------------------------------------------------------------------
// New tests: ResilienceLevel, RecoveryStrategy, FaultAssumptions
// -----------------------------------------------------------------------

#[test]
fn test_resilience_level_display() {
    assert_eq!(ResilienceLevel::Fragile.to_string(), "fragile");
    assert_eq!(ResilienceLevel::Tolerant.to_string(), "tolerant");
    assert_eq!(ResilienceLevel::Hardened.to_string(), "hardened");
    assert_eq!(ResilienceLevel::ByzantineFault.to_string(), "byzantine-fault");
}

#[test]
fn test_resilience_level_ordering() {
    assert!(ResilienceLevel::Fragile < ResilienceLevel::Tolerant);
    assert!(ResilienceLevel::Tolerant < ResilienceLevel::Hardened);
    assert!(ResilienceLevel::Hardened < ResilienceLevel::ByzantineFault);
}

#[test]
fn test_resilience_level_serialization_roundtrip() {
    let levels = [
        ResilienceLevel::Fragile,
        ResilienceLevel::Tolerant,
        ResilienceLevel::Hardened,
        ResilienceLevel::ByzantineFault,
    ];
    for level in &levels {
        let json = serde_json::to_string(level).expect("serialize");
        let round: ResilienceLevel = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(*level, round);
    }
}

#[test]
fn test_recovery_strategy_display() {
    assert_eq!(RecoveryStrategy::Propagate.to_string(), "propagate");
    assert_eq!(RecoveryStrategy::Retry { max_retries: 3 }.to_string(), "retry(3)");
    assert_eq!(RecoveryStrategy::Fallback.to_string(), "fallback");
    assert_eq!(
        RecoveryStrategy::CircuitBreaker { threshold: 5, reset_timeout_ms: 30000 }.to_string(),
        "circuit-breaker(5, 30000ms)"
    );
    assert_eq!(RecoveryStrategy::GracefulDegradation.to_string(), "graceful-degradation");
    assert_eq!(RecoveryStrategy::Compensate.to_string(), "compensate");
}

#[test]
fn test_recovery_strategy_serialization_roundtrip() {
    let strategies = [
        RecoveryStrategy::Propagate,
        RecoveryStrategy::Retry { max_retries: 5 },
        RecoveryStrategy::Fallback,
        RecoveryStrategy::CircuitBreaker { threshold: 10, reset_timeout_ms: 60000 },
        RecoveryStrategy::GracefulDegradation,
        RecoveryStrategy::Compensate,
    ];
    for strategy in &strategies {
        let json = serde_json::to_string(strategy).expect("serialize");
        let round: RecoveryStrategy = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(*strategy, round);
    }
}

#[test]
fn test_fault_assumptions_default() {
    let fa = FaultAssumptions::default();
    assert_eq!(fa.target_level, ResilienceLevel::Tolerant);
    assert!(fa.tolerated_failures.is_empty());
    assert!(fa.recovery_strategies.is_empty());
    assert_eq!(fa.max_latency_ms, None);
    assert!(!fa.idempotency_required);
}

#[test]
fn test_fault_assumptions_with_level() {
    let fa = FaultAssumptions::with_level(ResilienceLevel::Hardened);
    assert_eq!(fa.target_level, ResilienceLevel::Hardened);
}

#[test]
fn test_fault_assumptions_tolerate_and_query() {
    let mut fa = FaultAssumptions::with_level(ResilienceLevel::Hardened);
    fa.tolerate(FailureMode::Timeout, RecoveryStrategy::Retry { max_retries: 3 });
    fa.tolerate(FailureMode::Unavailable, RecoveryStrategy::Fallback);

    assert!(fa.tolerates(&FailureMode::Timeout));
    assert!(fa.tolerates(&FailureMode::Unavailable));
    assert!(!fa.tolerates(&FailureMode::Error));

    assert!(matches!(
        fa.recovery_for(&FailureMode::Timeout),
        Some(RecoveryStrategy::Retry { max_retries: 3 })
    ));
    assert!(matches!(fa.recovery_for(&FailureMode::Unavailable), Some(RecoveryStrategy::Fallback)));
    assert!(fa.recovery_for(&FailureMode::Error).is_none());
}

#[test]
fn test_fault_assumptions_serialization_roundtrip() {
    let mut fa = FaultAssumptions::with_level(ResilienceLevel::Hardened);
    fa.tolerate(FailureMode::Timeout, RecoveryStrategy::Retry { max_retries: 3 });
    fa.max_latency_ms = Some(5000);
    fa.idempotency_required = true;

    let json = serde_json::to_string(&fa).expect("serialize");
    let round: FaultAssumptions = serde_json::from_str(&json).expect("deserialize");
    assert_eq!(fa, round);
}

#[test]
fn test_classify_achieved_level_fragile_with_panics() {
    use crate::*;
    // Function with unwrap = Fragile
    let func = VerifiableFunction {
        name: "risky".to_string(),
        def_path: "test::risky".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::Unit, name: Some("r".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call { unwind: UnwindEdge::Unreachable, is_unsafe_sig: false, is_foreign: false,
                        func: "core::result::Result::unwrap".to_string(),
                        args: vec![],
                        dest: Place::local(1),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let report = ResilienceAnalysis::analyze_function(&func);
    assert_eq!(FaultAssumptions::classify_achieved_level(&report), ResilienceLevel::Fragile);
}

#[test]
fn test_classify_achieved_level_hardened_pure_function() {
    let func = make_simple_return_func("pure");
    let report = ResilienceAnalysis::analyze_function(&func);
    assert_eq!(FaultAssumptions::classify_achieved_level(&report), ResilienceLevel::Hardened);
}

#[test]
fn test_classify_achieved_level_tolerant_with_unchecked_arith() {
    use crate::*;
    let func = VerifiableFunction {
        name: "unchecked".to_string(),
        def_path: "test::unchecked".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::usize(), name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("b".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Add,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::usize(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    };
    let report = ResilienceAnalysis::analyze_function(&func);
    assert_eq!(FaultAssumptions::classify_achieved_level(&report), ResilienceLevel::Tolerant);
}
