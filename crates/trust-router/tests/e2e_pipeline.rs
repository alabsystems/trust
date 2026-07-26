// End-to-end pipeline tests for contracts, certificates, and config filtering.
//
// Part of #172
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use trust_proof_cert::{
    CertificateChain, CertificateStore, CertificationStatus, ChainStep, ChainStepType,
    FunctionHash, ProofCertificate, ProofStep, SolverInfo, VcSnapshot,
};
use trust_report::build_json_report;
use trust_router::Router;
use trust_types::*;
use trust_vcgen::generate_vcs;

fn contract(kind: ContractKind, body: &str) -> Contract {
    Contract {
        kind,
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 1,
            col_end: 1,
        },
        body: body.to_string(),
    }
}

fn contract_function(name: &str, def_path: &str, contracts: Vec<Contract>) -> VerifiableFunction {
    // Trust: mirror the production shape `trust-mir-extract` produces
    // (`parse_contract_specs`): every parseable `#[requires]`/`#[ensures]`
    // body is carried BOTH as its raw `Contract` string AND as a parsed
    // formula in `preconditions`/`postconditions` — the gated assumption /
    // obligation carriers the pipeline consumes. Hand-building the function
    // with empty formula fields (the old shape) dropped the requires
    // hypothesis from the ensures obligation, so a real solver refuted
    // `result >= 0` with a counterexample (`x = -1`) that violates the
    // declared `x > 0`.
    let preconditions = contracts
        .iter()
        .filter(|c| matches!(c.kind, ContractKind::Requires))
        .filter_map(|c| parse_spec_expr(&c.body))
        .collect();
    let postconditions = contracts
        .iter()
        .filter(|c| matches!(c.kind, ContractKind::Ensures))
        .filter_map(|c| parse_spec_expr(&c.body))
        .collect();
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
        span: SourceSpan {
            file: "src/pipeline.rs".to_string(),
            line_start: 1,
            col_start: 1,
            line_end: 3,
            col_end: 1,
        },
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: None },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            arg_count: 1,
            return_ty: Ty::i32(),
        },
        contracts,
        preconditions,
        postconditions,
        spec: Default::default(),
    }
}

fn checked_add_function(name: &str, def_path: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: def_path.to_string(),
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
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::Tuple(vec![Ty::u32(), Ty::Bool]), name: None },
                LocalDecl { index: 4, ty: Ty::u32(), name: None },
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
                            place: Place::local(0),
                            rvalue: Rvalue::Use(Operand::Copy(Place::local(4))),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u32(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn proved_result() -> VerificationResult {
    VerificationResult::Proved {
        solver: "constant-folder".into(),
        time_ms: 1,
        strength: ProofStrength::smt_unsat(),
        proof_certificate: None,
        solver_warnings: None,
        native_proof_envelope: None,
    }
}

fn solver_info(result: &VerificationResult) -> SolverInfo {
    match result {
        VerificationResult::Proved { solver, time_ms, strength, .. } => SolverInfo {
            name: solver.to_string(),
            version: "test".to_string(),
            time_ms: *time_ms,
            strength: strength.clone(),
            evidence: None,
        },
        other => panic!("expected proved result, got {other:?}"),
    }
}

fn certificate_chain(base_timestamp: &str) -> CertificateChain {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir-hash".to_string(),
        output_hash: "vc-hash".to_string(),
        time_ms: 1,
        timestamp: base_timestamp.to_string(),
    });
    chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "constant-folder".to_string(),
        tool_version: "test".to_string(),
        input_hash: "vc-hash".to_string(),
        output_hash: "proof-hash".to_string(),
        time_ms: 1,
        timestamp: base_timestamp.to_string(),
    });
    chain
}

fn proof_steps() -> Vec<ProofStep> {
    vec![
        ProofStep {
            index: 0,
            rule: "assume".to_string(),
            description: "load VC".to_string(),
            premises: vec![],
        },
        ProofStep {
            index: 1,
            rule: "unsat".to_string(),
            description: "discharge VC".to_string(),
            premises: vec![0],
        },
    ]
}

fn certificate_for_vc(
    func: &VerifiableFunction,
    vc: &VerificationCondition,
    result: &VerificationResult,
    timestamp: &str,
) -> ProofCertificate {
    let snapshot = VcSnapshot::from_vc(vc).expect("VC snapshot should serialize");
    let chain = certificate_chain(timestamp);
    ProofCertificate::new_trusted(
        func.def_path.clone(),
        FunctionHash::from_bytes(func.content_hash().as_bytes()),
        snapshot,
        solver_info(result),
        vec![1, 2, 3, 4],
        timestamp.to_string(),
    )
    .with_proof_steps(proof_steps())
    .with_chain(chain)
}

/// Run the router over only the functions named in `allowlist`.
///
/// The allowlist is spelled out here rather than loaded from a policy file:
/// project policy lives in the `[trust]` manifest table that `targo trust`
/// owns, and that surface is internal to the frontend binary. What these tests
/// pin is the pipeline downstream of selection — that a selected function
/// produces obligations, a certificate, and a report — so the selection itself
/// is a test fixture, not a configuration contract.
fn selected_crate_result(
    crate_name: &str,
    allowlist: &[&str],
    functions: &[VerifiableFunction],
) -> CrateVerificationResult {
    let router = Router::new();
    let mut crate_result = CrateVerificationResult::new(crate_name);

    for func in functions {
        if !allowlist.iter().any(|name| func.def_path.ends_with(name)) {
            continue;
        }

        let vcs = generate_vcs(func);
        let results = router.verify_all(&vcs);
        crate_result.add_function(FunctionVerificationResult {
            function_path: func.def_path.clone(),
            function_name: func.name.clone(),
            results,
            from_notes: 0,
            with_assumptions: 0,
        });
    }

    crate_result
}

fn obligation_kinds(report: &JsonProofReport, function: &str) -> Vec<String> {
    report
        .functions
        .iter()
        .find(|entry| entry.function == function)
        .expect("function should be present in report")
        .obligations
        .iter()
        .map(|obligation| obligation.kind.clone())
        .collect()
}

fn unique_temp_dir(label: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!("trust-router-{label}-{}-{nonce}", std::process::id()))
}

#[test]
fn contracts_flow_through_full_pipeline() {
    let func = contract_function(
        "contract_fn",
        "pipeline::contract_fn",
        vec![
            contract(ContractKind::Requires, "x > 0"),
            contract(ContractKind::Ensures, "result >= 0"),
        ],
    );

    let vcs = generate_vcs(&func);
    assert_eq!(vcs.len(), 2, "contracts should generate exactly two VCs");
    assert!(vcs.iter().any(|vc| matches!(vc.kind, VcKind::Precondition { .. })));
    assert!(vcs.iter().any(|vc| matches!(vc.kind, VcKind::Postcondition)));

    let results = Router::new().verify_all(&vcs);
    assert_eq!(results.len(), 2, "router should return one result per VC");
    // Trust: with the corrected encoding, a definition-site Precondition VC
    // is trivially provable (`Bool(false)` formula -- the actual obligation
    // is generated by `modular.rs` at each call site). The Postcondition VC
    // conjoins the declared requires as hypothesis:
    // `x > 0 AND _0 == x AND NOT(_0 >= 0)`. The stub ConstantFolderBackend
    // (default features) cannot act on the symbolic formula and reports
    // Unknown; the shipped in-process ay solver (`ay-backend` feature)
    // discharges it (UNSAT => Proved).
    let (precond, postcond): (Vec<_>, Vec<_>) =
        results.iter().partition(|(vc, _)| matches!(vc.kind, VcKind::Precondition { .. }));
    assert_eq!(precond.len(), 1);
    assert_eq!(postcond.len(), 1);
    assert!(matches!(precond[0].1, VerificationResult::Proved { .. }));
    #[cfg(feature = "ay-backend")]
    assert!(matches!(postcond[0].1, VerificationResult::Proved { .. }));
    #[cfg(not(feature = "ay-backend"))]
    assert!(matches!(postcond[0].1, VerificationResult::Unknown { .. }));

    let report = build_json_report("contracts-e2e", &results);
    let kinds = obligation_kinds(&report, "contract_fn");
    assert!(kinds.iter().any(|kind| kind == "precondition"));
    assert!(kinds.iter().any(|kind| kind == "postcondition"));
    // Raw router statuses are freely constructible diagnostic inputs. The
    // report publication boundary must not promote them without the
    // request-bound structured and transport proof evidence.
    assert_eq!(report.summary.total_unknown, 2);
    assert_eq!(report.summary.total_proved, 0);
}

#[test]
fn proof_certificate_generation_from_proved_vcs() {
    let func = contract_function(
        "cert_fn",
        "pipeline::cert_fn",
        vec![contract(ContractKind::Requires, "x > 0")],
    );
    let vcs = generate_vcs(&func);
    let routed = Router::new().verify_all(&vcs);
    // Trust: definition-site Precondition VC is encoded as `Bool(false)`
    // and discharged trivially by ConstantFolderBackend. The certificate
    // path is still exercised below against a manual proved result.
    assert!(matches!(routed[0].1, VerificationResult::Proved { .. }));

    let manual_result = proved_result();
    let cert = certificate_for_vc(&func, &vcs[0], &manual_result, "2026-03-29T12:00:00Z");
    let json = cert.to_json().expect("certificate should serialize");
    let restored = ProofCertificate::from_json(&json).expect("certificate should deserialize");

    assert_eq!(restored, cert);
    assert_eq!(restored.status, CertificationStatus::Trusted);
    assert!(restored.verify_vc_hash());
    assert!(restored.check_proof_step_shape().is_ok());
}

#[test]
fn selected_function_filtering() {
    let allowlist = ["target_fn"];
    let target = contract_function(
        "target_fn",
        "pipeline::target_fn",
        vec![contract(ContractKind::Requires, "x > 0")],
    );
    let skipped = contract_function(
        "helper_fn",
        "pipeline::helper_fn",
        vec![contract(ContractKind::Requires, "x > 0")],
    );

    let crate_result =
        selected_crate_result("selection-filtering", &allowlist, &[target.clone(), skipped.clone()]);
    assert_eq!(crate_result.function_count(), 1, "only the allowlisted function should run");
    assert_eq!(crate_result.functions[0].function_path, target.def_path);
    assert_eq!(crate_result.total_obligations(), 1);
    assert!(crate_result.all_results().iter().all(|(vc, _)| vc.function == target.name));
}

#[test]
fn multiple_contracts_report_correct_counts() {
    let func = contract_function(
        "mixed_contracts",
        "pipeline::mixed_contracts",
        vec![
            contract(ContractKind::Requires, "x > 0"),
            contract(ContractKind::Ensures, "result >= 0"),
        ],
    );

    let results = Router::new().verify_all(&generate_vcs(&func));
    let report = build_json_report("mixed-contracts", &results);
    let function = report
        .functions
        .iter()
        .find(|entry| entry.function == "mixed_contracts")
        .expect("function should be present in report");

    assert_eq!(function.summary.total_obligations, 2);
    // Solver status remains visible above, but raw statuses cannot become
    // published proof claims without structured/transport authority.
    assert_eq!(function.summary.unknown, 2);
    assert_eq!(function.summary.proved, 0);
    assert_eq!(
        function.obligations.iter().filter(|obligation| obligation.kind == "precondition").count(),
        1
    );
    assert_eq!(
        function.obligations.iter().filter(|obligation| obligation.kind == "postcondition").count(),
        1
    );
}

#[test]
fn invariant_contract_generates_assertion_vc() {
    let func = contract_function(
        "invariant_fn",
        "pipeline::invariant_fn",
        vec![contract(ContractKind::Invariant, "x > 0")],
    );

    let vcs = generate_vcs(&func);
    assert_eq!(vcs.len(), 1);
    assert!(matches!(&vcs[0].kind, VcKind::Assertion { message } if message == "invariant: x > 0"));

    let report = build_json_report("invariant-contract", &Router::new().verify_all(&vcs));
    let kinds = obligation_kinds(&report, "invariant_fn");
    assert_eq!(kinds, vec!["assertion".to_string()]);
}

#[test]
fn certificate_chain_and_store_round_trip() {
    let target = contract_function(
        "target_fn",
        "pipeline::target_fn",
        vec![contract(ContractKind::Requires, "x > 0")],
    );
    let helper = contract_function(
        "helper_fn",
        "pipeline::helper_fn",
        vec![contract(ContractKind::Ensures, "result >= 0")],
    );
    let target_vc = generate_vcs(&target).into_iter().next().expect("target VC should exist");
    let helper_vc = generate_vcs(&helper).into_iter().next().expect("helper VC should exist");
    let target_cert =
        certificate_for_vc(&target, &target_vc, &proved_result(), "2026-03-29T12:00:00Z");
    let helper_cert =
        certificate_for_vc(&helper, &helper_vc, &proved_result(), "2026-03-29T12:00:01Z");

    let mut store = CertificateStore::new("router-e2e");
    store.insert(target_cert.clone(), target_cert.chain.clone());
    store.insert(helper_cert.clone(), helper_cert.chain.clone());

    let found = store.find_by_function(&target.def_path);
    assert_eq!(found.len(), 1);
    assert_eq!(found[0].id, target_cert.id);
    assert_eq!(store.function_names(), vec![helper.def_path.clone(), target.def_path.clone()]);

    let dir = unique_temp_dir("cert-store");
    let _ = std::fs::remove_dir_all(&dir);
    let saved = store.save_to_dir(&dir).expect("store should save");
    assert!(saved.exists());

    let loaded =
        CertificateStore::load_from_dir(&dir).expect("store should load").expect("store exists");
    assert_eq!(loaded, store);
    assert_eq!(loaded.get(&helper_cert.id), Some(&helper_cert));

    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn full_pipeline_with_selection_contracts_and_certs() {
    let allowlist = ["target_fn"];
    let target = contract_function(
        "target_fn",
        "pipeline::target_fn",
        vec![
            contract(ContractKind::Requires, "x > 0"),
            contract(ContractKind::Ensures, "result >= 0"),
        ],
    );
    let skipped = contract_function(
        "skip_fn",
        "pipeline::skip_fn",
        vec![contract(ContractKind::Requires, "x > 0")],
    );

    let crate_result =
        selected_crate_result("full-e2e", &allowlist, &[target.clone(), skipped.clone()]);
    assert_eq!(crate_result.function_count(), 1);
    assert_eq!(crate_result.functions[0].function_name, target.name);

    let report = build_json_report(&crate_result.crate_name, &crate_result.all_results());
    assert_eq!(report.functions.len(), 1);
    assert_eq!(report.functions[0].function, target.name);
    assert_eq!(report.functions[0].summary.total_obligations, 2);

    let certs: Vec<_> = crate_result.functions[0]
        .results
        .iter()
        .enumerate()
        .map(|(index, (vc, _))| {
            certificate_for_vc(
                &target,
                vc,
                &proved_result(),
                &format!("2026-03-29T12:00:0{index}Z"),
            )
        })
        .collect();

    assert_eq!(certs.len(), 2);
    assert!(certs.iter().all(|cert| cert.verify_vc_hash()));
    assert!(certs.iter().all(|cert| cert.check_proof_step_shape().is_ok()));
}

#[test]
fn empty_contracts_produce_no_spec_vcs() {
    let func = checked_add_function("checked_add", "pipeline::checked_add");
    let vcs = generate_vcs(&func);

    assert!(!vcs.is_empty(), "checked add should still produce safety VCs");
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add, .. }))
    );
    assert!(
        vcs.iter()
            .all(|vc| !matches!(vc.kind, VcKind::Precondition { .. } | VcKind::Postcondition))
    );
    assert!(vcs.iter().all(|vc| {
        !matches!(&vc.kind, VcKind::Assertion { message } if message.starts_with("invariant: "))
    }));
}
