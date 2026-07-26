//! M-Pkg milestone-1: the CleanCic carrier-and-recheck contract, end-to-end
//! inside `crates/` (no `./x.py build`).
//!
//! Mints a real QF_LIA `CleanCic` proof term via `trust_certify::certify_violation`,
//! attaches it to a `FunctionCertificate`, round-trips through bincode
//! byte-identically, and kernel-rechecks the carried term OFFLINE on the
//! deserialized cert. Negative controls confirm a tampered term and a replay
//! onto a different obligation both fail closed — so the carried `Certified`
//! label is backed by a re-checkable proof, never out-running it.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_ir::ProofEvidence;
use trust_proof_cert::proof_bundle::{CarriedCleanCic, FunctionCertificate};
use trust_proof_cert::{
    CertificateChain, ChainStep, ChainStepType, FunctionHash, ProofCertificate, SolverInfo,
    VcSnapshot,
};
use trust_types::{Formula, ProofStrength, Sort};

/// `var >= 1 AND var <= 0` — an unsatisfiable linear-integer order constraint
/// that the QF_LIA bridge reconstructs to a kernel-checked `term : False`.
fn lia_contradiction(var: &str) -> Formula {
    let x = Formula::Var(var.to_string(), Sort::Int);
    Formula::And(vec![
        Formula::Ge(Box::new(x.clone()), Box::new(Formula::Int(1))),
        Formula::Le(Box::new(x), Box::new(Formula::Int(0))),
    ])
}

fn make_cert(function: &str) -> ProofCertificate {
    let vc_snapshot = VcSnapshot {
        kind: "Assertion".to_string(),
        formula_json: format!("{function}-vc"),
        location: None,
    };
    let solver = SolverInfo {
        name: "ay".to_string(),
        version: "1.0.0".to_string(),
        time_ms: 10,
        strength: ProofStrength::smt_unsat(),
        evidence: None,
    };
    ProofCertificate::new_trusted(
        function.to_string(),
        FunctionHash::from_bytes(format!("{function}-body").as_bytes()),
        vc_snapshot,
        solver,
        vec![1, 2, 3],
        "2026-06-16T00:00:00Z".to_string(),
    )
}

fn make_chain() -> CertificateChain {
    let mut chain = CertificateChain::new();
    chain.push(ChainStep {
        step_type: ChainStepType::VcGeneration,
        tool: "trust_vcgen".to_string(),
        tool_version: "0.1.0".to_string(),
        input_hash: "mir".to_string(),
        output_hash: "vc".to_string(),
        time_ms: 1,
        timestamp: "2026-06-16T00:00:00Z".to_string(),
    });
    chain
}

#[test]
fn cleancic_roundtrip_mints_carries_and_rechecks() {
    let violation = lia_contradiction("x");

    // 1. Mint a real kernel-checked CleanCic term for the QF_LIA obligation.
    let ev = trust_certify::certify_violation(&violation)
        .expect("QF_LIA order contradiction must certify to a CleanCic term");
    assert!(
        matches!(&ev, ProofEvidence::CleanCic { term, context, .. } if !term.is_empty() && !context.is_empty()),
        "evidence must be a non-empty CleanCic term, got {ev:?}"
    );

    // 2. Attach it to a FunctionCertificate via the cold packaging path.
    let fc =
        FunctionCertificate::from_existing(make_cert("f"), make_chain()).with_clean_cic(vec![ev]);
    assert_eq!(fc.clean_cic.len(), 1, "the CleanCic term must be carried");

    // 3. Serialize round-trip, byte-identical.
    let bytes = bincode::serialize(&fc).expect("serialize");
    let fc2: FunctionCertificate = bincode::deserialize(&bytes).expect("deserialize");
    assert_eq!(
        bincode::serialize(&fc2).expect("re-serialize"),
        bytes,
        "re-serialization of the deserialized cert must be byte-identical"
    );
    assert_eq!(fc.clean_cic, fc2.clean_cic, "the carried term must survive serialization");

    // 4. Offline kernel re-check on the DESERIALIZED cert (the real clean kernel,
    //    no rustc, no solver re-run): the carried bytes prove `False` under this
    //    obligation's environment.
    let cc: &CarriedCleanCic = &fc2.clean_cic[0];
    assert!(
        trust_certify::recheck_cleancic(&cc.term, &cc.context, &cc.lineage, &violation),
        "the carried term must kernel-recheck offline against its obligation"
    );

    // 5a. Negative control — tamper the term: the kernel rejects it.
    let mut tampered = cc.clone();
    tampered.term[0] ^= 0xff;
    assert!(
        !trust_certify::recheck_cleancic(
            &tampered.term,
            &tampered.context,
            &tampered.lineage,
            &violation
        ),
        "a tampered proof term must fail the kernel re-check"
    );

    // 5b. Negative control — replay onto a DIFFERENT obligation: lineage fails.
    let other = lia_contradiction("y");
    assert!(
        !trust_certify::recheck_cleancic(&cc.term, &cc.context, &cc.lineage, &other),
        "the cert must not re-check against a different obligation (no replay)"
    );
}
