//! Trust: malformed admission must refuse before config IO or tool execution.

use std::process::Command;

#[test]
fn invalid_admission_refuses_before_reading_config() {
    let directory = tempfile::tempdir().unwrap();
    let absent = directory.path().join("must-not-be-opened.toml");
    for share in [
        None,
        Some(""),
        Some("0"),
        Some("-1"),
        Some("+7"),
        Some("7.0"),
        Some(" 7"),
        Some("７"),
        Some("4294967296"),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_bootstrap"));
        command
            .args(["check", "--dry-run", "--jobs=1", "--config"])
            .arg(&absent)
            .env("BUILD_SLOT_HELD", "1")
            .env_remove("CARGO_BUILD_JOBS");
        if let Some(share) = share {
            command.env("CARGO_BUILD_JOBS", share);
        }
        let output = command.output().unwrap();
        assert!(!output.status.success(), "invalid share accepted: {share:?}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("requires a positive u32 CARGO_BUILD_JOBS share"), "{stderr}");
        assert!(!stderr.contains("failed to read config"), "{stderr}");
    }
    assert!(!absent.exists());
}
