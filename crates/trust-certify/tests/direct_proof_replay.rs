//! Proof bytes exported by another process must be checked in this process's
//! reference kernel. No persisted acceptance token grants authority.

use std::process::Command;

use trust_certify::{certify_vc, reference_certificate_for, replay_vc_evidence};
use trust_ir::ProofEvidence;
use trust_types::{Formula, Sort, SourceSpan, VcKind, VerificationCondition};

const EXPORT_PATH: &str = "TRUST_TEST_DIRECT_REPLAY_EXPORT_PATH";

fn obligation() -> VerificationCondition {
    let x = || Formula::Var("x".into(), Sort::Int);
    VerificationCondition {
        kind: VcKind::Assertion { message: "bounded x".into() },
        function: "direct_proof_replay::imported_obligation".into(),
        location: SourceSpan::default(),
        formula: Formula::And(vec![
            Formula::Lt(Box::new(x()), Box::new(Formula::Int(0))),
            Formula::Lt(Box::new(Formula::Int(0)), Box::new(x())),
        ]),
        contract_metadata: None,
        obligation: None,
    }
}

#[test]
fn export_proof_in_child_process() {
    let Some(path) = std::env::var_os(EXPORT_PATH) else { return };
    let vc = obligation();
    let evidence = certify_vc(&vc).expect("child must produce a proof");
    assert!(reference_certificate_for(&evidence).is_some());
    std::fs::write(path, serde_json::to_vec(&evidence).expect("serialize proof"))
        .expect("export proof");
}

#[test]
fn serialized_proof_earns_fresh_authority_in_the_consumer_process() {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock")
        .as_nanos();
    let dir =
        std::env::temp_dir().join(format!("trust-direct-replay-{}-{unique}", std::process::id()));
    std::fs::create_dir(&dir).expect("create private test directory");
    struct RemoveDir(std::path::PathBuf);
    impl Drop for RemoveDir {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = RemoveDir(dir.clone());
    let path = dir.join("proof.json");
    let output = Command::new(std::env::current_exe().expect("test executable"))
        .args(["--exact", "export_proof_in_child_process", "--nocapture"])
        .env(EXPORT_PATH, &path)
        .output()
        .expect("run independent producer");
    assert!(output.status.success(), "producer failed: {output:?}");
    let evidence: ProofEvidence =
        serde_json::from_slice(&std::fs::read(path).expect("read proof")).expect("decode proof");
    assert!(reference_certificate_for(&evidence).is_none(), "a file is not authority");
    let vc = obligation();
    assert!(replay_vc_evidence(&vc, &evidence));
    assert!(reference_certificate_for(&evidence).is_some(), "current kernel must accept");

    let mut changed = vc;
    changed.location.line_start = 10;
    assert!(!replay_vc_evidence(&changed, &evidence));
}
