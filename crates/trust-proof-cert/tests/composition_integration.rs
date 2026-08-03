// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;

use trust_proof_cert::{
    CertificateId, CertificationStatus, ChainStep, ChainStepType, CompositionError,
    CompositionNodeStatus, DepGraph, FunctionHash, ProofCertificate, ProofChain, ProofComposition,
    Property, SolverInfo, VcSnapshot, check_composability, compose_proofs, is_chain_complete,
    modular_composition, strengthening_check, transitive_closure, verify_composition,
    verify_proof_chain, weakening,
};
use trust_types::{Formula, ProofStrength, SourceSpan, VcKind, VerificationCondition};

fn sample_solver(strength: ProofStrength, time_ms: u64) -> SolverInfo {
    SolverInfo {
        name: "ay".to_string(),
        version: "1.0.0".to_string(),
        time_ms,
        strength,
        evidence: None,
    }
}

fn sample_vc(function: &str) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::Assertion { message: "must hold".to_string() },
        function: function.into(),
        location: SourceSpan {
            file: "src/lib.rs".to_string(),
            line_start: 10,
            col_start: 4,
            line_end: 10,
            col_end: 18,
        },
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

fn sample_vc_snapshot(function: &str) -> VcSnapshot {
    VcSnapshot::from_vc(&sample_vc(function)).unwrap()
}

fn make_cert(function: &str, timestamp: &str, strength: ProofStrength) -> ProofCertificate {
    let mut cert = ProofCertificate::new_trusted(
        function.to_string(),
        FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
        sample_vc_snapshot(function),
        sample_solver(strength, 25),
        vec![1, 2, 3, 4],
        timestamp.to_string(),
    );
    cert.chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust-vcgen".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "source".to_string(),
        output_hash: "composition-vc".to_string(),
        time_ms: 1,
        timestamp: timestamp.to_string(),
    });
    cert.chain.push(ChainStep {
        step_type: ChainStepType::SolverProof,
        tool: "ay".to_string(),
        tool_version: "1.0.0".to_string(),
        input_hash: "composition-vc".to_string(),
        output_hash: "composition-proof".to_string(),
        time_ms: 25,
        timestamp: timestamp.to_string(),
    });
    cert
}

fn make_chain() -> ProofChain {
    let mut chain = ProofChain::new("demo-crate");
    chain.add_certificate(
        make_cert("foo", "2026-03-29T00:00:00Z", ProofStrength::smt_unsat()),
        vec!["bar".to_string()],
    );
    chain.add_certificate(
        make_cert("bar", "2026-03-29T00:01:00Z", ProofStrength::deductive()),
        vec![],
    );
    chain
}

#[test]
fn test_vc_to_cert_roundtrip() {
    let vc = sample_vc("alpha");
    let snapshot = VcSnapshot::from_vc(&vc).unwrap();
    let cert = ProofCertificate::new_trusted(
        vc.function.as_str().to_string(),
        FunctionHash::from_bytes(b"alpha-body"),
        snapshot.clone(),
        sample_solver(ProofStrength::smt_unsat(), 12),
        vec![9, 8, 7],
        "2026-03-29T00:02:00Z".to_string(),
    );

    let json_blob = cert.to_json().unwrap();
    let roundtrip = ProofCertificate::from_json(&json_blob).unwrap();
    let expected_id: CertificateId = cert.id.clone();
    let assertion = Property::new("Assertion");
    assert_eq!(roundtrip.id, expected_id);
    assert_eq!(roundtrip.vc_snapshot, snapshot);
    assert_eq!(roundtrip.status, CertificationStatus::Trusted);
    assert!(matches!(
        weakening(&roundtrip, &assertion),
        Err(CompositionError::ProofAuthorityUnavailable { operation: "weakening" })
    ));
    assert!(matches!(
        strengthening_check(&roundtrip, &assertion),
        Err(CompositionError::ProofAuthorityUnavailable { operation: "strengthening_check" })
    ));
}

#[test]
fn test_compose_two_distinct_certs() {
    let foo = make_cert("foo", "2026-03-29T00:03:00Z", ProofStrength::constructive());
    let bar = make_cert("bar", "2026-03-29T00:04:00Z", ProofStrength::bounded(3));

    let result = check_composability(&foo, &bar).unwrap();
    assert!(!result.composable);
    assert!(result.structurally_compatible);
    assert!(matches!(
        compose_proofs(&[&foo, &bar]),
        Err(CompositionError::ProofAuthorityUnavailable { operation: "compose_proofs" })
    ));
}

#[test]
fn test_chain_structural_inspection() {
    let chain = make_chain();
    let certs: Vec<&ProofCertificate> = chain
        .recorded_functions()
        .iter()
        .map(|function| chain.get_certificate(function).unwrap())
        .collect();
    let closure = transitive_closure(&certs, &chain.call_graph);
    let result = verify_proof_chain(&chain);

    assert!(!result.is_sound());
    assert!(result.structurally_complete);
    assert!(is_chain_complete(&chain));
    assert!(result.gaps.is_empty());
    assert_eq!(result.integrity_valid_record_coverage, 1.0);
    assert!(closure.contains("foo"));
    assert!(closure.contains("bar"));
}

#[test]
fn test_chain_verification_gap() {
    let mut chain = ProofChain::new("gap-crate");
    chain.add_certificate(
        make_cert("foo", "2026-03-29T00:05:00Z", ProofStrength::smt_unsat()),
        vec!["bar".to_string()],
    );

    let result = verify_proof_chain(&chain);

    assert!(!result.is_sound());
    assert!(!result.structurally_complete);
    assert!(!is_chain_complete(&chain));
    assert_eq!(result.gaps.len(), 1);
    assert_eq!(result.gaps[0].function, "bar");
}

#[test]
fn test_serialization_json_roundtrip() {
    use trust_proof_cert::serialization::{from_json, to_json};

    let chain = make_chain();
    let json_blob = to_json(&chain).unwrap();
    let roundtrip = from_json(&json_blob).unwrap();

    assert_eq!(roundtrip.name, chain.name);
    assert_eq!(roundtrip.len(), chain.len());
    assert_eq!(roundtrip.recorded_functions(), chain.recorded_functions());
}

#[test]
fn test_serialization_binary_roundtrip() {
    use trust_proof_cert::serialization::{from_binary, to_binary};

    let chain = make_chain();
    let bytes = to_binary(&chain).unwrap();
    let roundtrip = from_binary(&bytes).unwrap();

    assert_eq!(roundtrip.name, chain.name);
    assert_eq!(roundtrip.len(), chain.len());
    assert_eq!(roundtrip.recorded_functions(), chain.recorded_functions());
}

#[test]
fn test_dep_graph_analysis() {
    let mut graph = DepGraph::new();
    graph.add_function("a", vec!["b".to_string(), "c".to_string()], true);
    graph.add_function("b", vec!["c".to_string()], true);
    graph.add_function("c", vec![], true);

    let analysis = graph.analyze();
    let c_pos = analysis.topological_order.iter().position(|function| function == "c").unwrap();
    let b_pos = analysis.topological_order.iter().position(|function| function == "b").unwrap();
    let a_pos = analysis.topological_order.iter().position(|function| function == "a").unwrap();

    assert!(c_pos < b_pos);
    assert!(b_pos < a_pos);
}

#[test]
fn test_modular_composition_with_call_edges() {
    let caller = make_cert("caller", "2026-03-29T00:06:00Z", ProofStrength::deductive());
    let callee_one = make_cert("callee_one", "2026-03-29T00:07:00Z", ProofStrength::smt_unsat());
    let callee_two = make_cert("callee_two", "2026-03-29T00:08:00Z", ProofStrength::constructive());
    let needed = vec!["callee_one".to_string(), "callee_two".to_string()];
    let call_graph = BTreeMap::new();
    let composed: Result<_, CompositionError> =
        modular_composition(&caller, &[&callee_one, &callee_two], &needed, &call_graph);
    assert!(matches!(composed, Err(CompositionError::ProofAuthorityUnavailable { .. })));
}

#[test]
fn test_proof_composition_dag_cycle_detection() {
    let mut composition = ProofComposition::new();
    composition.add_certificate(
        make_cert("foo", "2026-03-29T00:09:00Z", ProofStrength::smt_unsat()),
        vec!["bar".to_string()],
    );
    composition.add_certificate(
        make_cert("bar", "2026-03-29T00:10:00Z", ProofStrength::smt_unsat()),
        vec!["foo".to_string()],
    );

    assert_eq!(composition.get_node("foo").unwrap().status, CompositionNodeStatus::Valid);

    let cycle = composition.detect_cycle().unwrap();

    assert!(cycle.contains(&"foo".to_string()));
    assert!(cycle.contains(&"bar".to_string()));
}

#[test]
fn test_verify_composition_soundness() {
    let mut composition = ProofComposition::new();
    composition.add_certificate(
        make_cert("foo", "2026-03-29T00:11:00Z", ProofStrength::deductive()),
        vec!["bar".to_string()],
    );
    composition.add_certificate(
        make_cert("bar", "2026-03-29T00:12:00Z", ProofStrength::constructive()),
        vec![],
    );

    let result = verify_composition(&composition);

    assert!(!result.sound);
    assert!(result.structurally_complete);
    assert!(result.composed.is_none());
}
