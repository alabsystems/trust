use trust_router::{BackendRole, Router, VerificationBackend};
use trust_types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FormulaFamily {
    SeparationOwnership,
    Ffi,
    DataRace,
    TypestateProtocol,
}

struct CompatBackend {
    name: &'static str,
    role: BackendRole,
    family: FormulaFamily,
}

impl VerificationBackend for CompatBackend {
    fn name(&self) -> &str {
        self.name
    }

    fn role(&self) -> BackendRole {
        self.role
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        retained_formula_family(vc) == Some(self.family)
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        VerificationResult::Proved {
            solver: self.name.into(),
            time_ms: 0,
            strength: ProofStrength::smt_unsat(),
            proof_certificate: None,
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }
}

struct RejectingBackend;

impl VerificationBackend for RejectingBackend {
    fn name(&self) -> &str {
        "rejecting"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        false
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        panic!("rejecting backend must never receive an incompatible Formula family")
    }
}

struct PanickingBackend;

impl VerificationBackend for PanickingBackend {
    fn name(&self) -> &str {
        "panicking"
    }

    fn can_handle(&self, _vc: &VerificationCondition) -> bool {
        true
    }

    fn verify(&self, _vc: &VerificationCondition) -> VerificationResult {
        panic!("UnsupportedMir must fail closed before backend dispatch")
    }
}

struct CompatCase {
    label: &'static str,
    family: FormulaFamily,
    backend_name: &'static str,
    backend_role: BackendRole,
    vc: VerificationCondition,
}

#[test]
fn retained_formula_families_route_to_compatible_backends() {
    for case in compat_cases() {
        let router = Router::with_backends(vec![
            Box::new(RejectingBackend),
            Box::new(CompatBackend {
                name: "ownership-gate",
                role: BackendRole::Ownership,
                family: FormulaFamily::SeparationOwnership,
            }),
            Box::new(CompatBackend {
                name: "ffi-gate",
                role: BackendRole::SmtSolver,
                family: FormulaFamily::Ffi,
            }),
            Box::new(CompatBackend {
                name: "race-gate",
                role: BackendRole::Temporal,
                family: FormulaFamily::DataRace,
            }),
            Box::new(CompatBackend {
                name: "protocol-gate",
                role: BackendRole::Temporal,
                family: FormulaFamily::TypestateProtocol,
            }),
        ]);

        assert_eq!(
            retained_formula_family(&case.vc),
            Some(case.family),
            "{} should retain the expected Formula family",
            case.label
        );

        let plan = router.backend_plan(&case.vc);
        let selected = plan
            .iter()
            .find(|selection| selection.can_handle)
            .expect("expected a compatible backend in the plan");
        assert_eq!(selected.name.as_str(), case.backend_name, "{}", case.label);
        assert_eq!(selected.role, case.backend_role, "{}", case.label);

        let result = router.verify_one(&case.vc);
        assert!(result.is_proved(), "{} routed to {result:?}", case.label);
        assert_eq!(result.solver_name(), case.backend_name, "{}", case.label);
    }
}

#[test]
fn retained_formula_families_fail_closed_without_compatible_backend() {
    let router = Router::with_backends(vec![Box::new(RejectingBackend)]);

    for case in compat_cases() {
        let result = router.verify_one(&case.vc);
        assert!(
            matches!(
                result,
                VerificationResult::Unknown { solver, ref reason, .. }
                    if solver.as_str() == "none" && reason.contains("no backend can handle")
            ),
            "{} should fail closed without a compatible backend, got {result:?}",
            case.label
        );
    }
}

#[test]
fn unsupported_mir_fails_closed_before_formula_routing() {
    let vc = VerificationCondition {
        kind: VcKind::UnsupportedMir {
            kind: "TerminatorKind::CoroutineDrop".to_string(),
            detail: "valid MIR retained as opaque TrustIr".to_string(),
        },
        function: "unsupported_mir_gate".into(),
        location: SourceSpan::default(),
        formula: Formula::Bool(false),
        contract_metadata: None,
        obligation: None,
    };
    let router = Router::with_backends(vec![Box::new(PanickingBackend)]);

    assert!(router.backend_plan(&vc).is_empty());
    assert!(
        matches!(
            router.verify_one(&vc),
            VerificationResult::Unknown { solver, reason, .. }
                if solver.as_str() == "router" && reason.contains("unsupported MIR")
        ),
        "UnsupportedMir must be inconclusive, not discharged by a compatible-looking formula"
    );
}

fn compat_cases() -> Vec<CompatCase> {
    vec![
        CompatCase {
            label: "separation/ownership",
            family: FormulaFamily::SeparationOwnership,
            backend_name: "ownership-gate",
            backend_role: BackendRole::Ownership,
            vc: vc(
                VcKind::Assertion {
                    message: "[memory:region] non-aliasing: region_0 vs region_1".to_string(),
                },
                "ownership_gate",
                Formula::Not(Box::new(Formula::Eq(
                    Box::new(Formula::Var("region_0_base".to_string(), Sort::Int)),
                    Box::new(Formula::Var("region_1_base".to_string(), Sort::Int)),
                ))),
            ),
        },
        CompatCase {
            label: "FFI boundary",
            family: FormulaFamily::Ffi,
            backend_name: "ffi-gate",
            backend_role: BackendRole::SmtSolver,
            vc: vc(
                VcKind::FfiBoundaryViolation {
                    callee: "malloc".to_string(),
                    desc: "nonnull return contract".to_string(),
                },
                "ffi_gate",
                Formula::Not(Box::new(Formula::Eq(
                    Box::new(Formula::Select(
                        Box::new(Formula::Var(
                            "ffi_memory".to_string(),
                            Sort::Array(Box::new(Sort::Int), Box::new(Sort::BitVec(8))),
                        )),
                        Box::new(Formula::Var("ffi_ptr".to_string(), Sort::Int)),
                    )),
                    Box::new(Formula::BitVec { value: 0, width: 8 }),
                ))),
            ),
        },
        CompatCase {
            label: "data race",
            family: FormulaFamily::DataRace,
            backend_name: "race-gate",
            backend_role: BackendRole::Temporal,
            vc: vc(
                VcKind::DataRace {
                    variable: "shared_counter".to_string(),
                    thread_a: "worker_a".to_string(),
                    thread_b: "worker_b".to_string(),
                },
                "data_race_gate",
                Formula::And(vec![
                    Formula::Var("write_worker_a".to_string(), Sort::Bool),
                    Formula::Var("write_worker_b".to_string(), Sort::Bool),
                    Formula::Not(Box::new(Formula::Var(
                        "happens_before_worker_a_worker_b".to_string(),
                        Sort::Bool,
                    ))),
                ]),
            ),
        },
        CompatCase {
            label: "typestate/protocol",
            family: FormulaFamily::TypestateProtocol,
            backend_name: "protocol-gate",
            backend_role: BackendRole::Temporal,
            vc: vc(
                VcKind::ProtocolViolation {
                    protocol: "socket".to_string(),
                    violation: "send before connected".to_string(),
                },
                "protocol_gate",
                Formula::Forall(
                    vec![("state".into(), Sort::Int)],
                    Box::new(Formula::Implies(
                        Box::new(Formula::Var("socket_send".to_string(), Sort::Bool)),
                        Box::new(Formula::Var("socket_connected".to_string(), Sort::Bool)),
                    )),
                ),
            ),
        },
    ]
}

fn vc(kind: VcKind, function: &'static str, formula: Formula) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: function.into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    }
}

fn retained_formula_family(vc: &VerificationCondition) -> Option<FormulaFamily> {
    match &vc.kind {
        VcKind::Assertion { message }
            if message.starts_with("[memory:region]")
                && formula_has_var_prefix(&vc.formula, "region_") =>
        {
            Some(FormulaFamily::SeparationOwnership)
        }
        VcKind::FfiBoundaryViolation { .. } if formula_uses_select(&vc.formula) => {
            Some(FormulaFamily::Ffi)
        }
        VcKind::DataRace { .. } if formula_has_var_prefix(&vc.formula, "happens_before_") => {
            Some(FormulaFamily::DataRace)
        }
        VcKind::ProtocolViolation { .. } if matches!(vc.formula, Formula::Forall(..)) => {
            Some(FormulaFamily::TypestateProtocol)
        }
        _ => None,
    }
}

fn formula_has_var_prefix(formula: &Formula, prefix: &str) -> bool {
    formula_walk(formula, &mut |node| match node {
        Formula::Var(name, _) => name.starts_with(prefix),
        Formula::SymVar(symbol, _) => symbol.as_str().starts_with(prefix),
        _ => false,
    })
}

fn formula_uses_select(formula: &Formula) -> bool {
    formula_walk(formula, &mut |node| matches!(node, Formula::Select(..)))
}

fn formula_walk(formula: &Formula, predicate: &mut impl FnMut(&Formula) -> bool) -> bool {
    predicate(formula) || formula.children().into_iter().any(|child| formula_walk(child, predicate))
}
