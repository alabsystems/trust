use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};

use super::*;

#[test]
fn raw_process_helpers_refuse_after_original_scope_installation() {
    const NAME: &str = "utils::exec::untracked_tests::raw_process_helpers_refuse_after_original_scope_installation";
    const ACTOR: &str = "TRUST_RAW_PROCESS_GUARD_TEST";
    if std::env::var_os(ACTOR).is_none() {
        let mut out = tempfile::tempfile().unwrap();
        let mut err = tempfile::tempfile().unwrap();
        let mut child =
            crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
                .args(["--exact", NAME, "--nocapture"])
                .env(ACTOR, "1")
                .stdout(out.try_clone().unwrap())
                .stderr(err.try_clone().unwrap())
                .spawn()
                .unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() >= deadline {
                // Original unreaped direct Child, never a recycled-PID signal.
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("raw-process actor one-minute deadline");
            }
            std::thread::sleep(Duration::from_millis(2));
        };
        use std::io::Seek;
        out.rewind().unwrap();
        err.rewind().unwrap();
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        out.read_to_end(&mut stdout).unwrap();
        err.read_to_end(&mut stderr).unwrap();
        assert!(status.success(), "stdout={stdout:?}, stderr={stderr:?}");
        return;
    }
    require_standalone_process("before installation").unwrap();
    let root = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "native raw-path refusal control".into(),
        contract: "local restriction only".into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(root.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let work = ProtectedWorkScope::new(
        Arc::new(lease.into_withheld().unwrap()),
        Instant::now() + Duration::from_secs(20),
    )
    .unwrap();
    install_protected_scope(work.dispatcher()).unwrap();
    assert_eq!(
        require_standalone_process("after installation").unwrap_err().kind(),
        io::ErrorKind::Unsupported
    );
    let error = crate::utils::trust_repo_tools::query(Path::new("/usr/bin/true"), &[]).unwrap_err();
    assert!(error.contains("protected Bootstrap has no native process owner"));
    let _joined = work.seal().join().unwrap();
    assert!(require_standalone_process("after seal").is_err());
}
