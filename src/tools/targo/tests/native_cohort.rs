//! Actual discovery must not execute a configured compiler or an early mode.
#![cfg(unix)]

use std::os::unix::fs::PermissionsExt as _;
use std::time::Duration;

#[test]
fn discovery_never_executes_an_unpaired_configured_compiler() {
    let root = tempfile::tempdir().unwrap();
    let compiler = root.path().join("compiler");
    let marker = root.path().join("compiler-started");
    // This deliberately unqualified test compiler leaves an observable effect
    // on ANY execution, including a version probe. It creates no authority.
    std::fs::write(
        &compiler,
        "#!/bin/sh\nprintf ran > \"$COHORT_TEST_MARKER\"\nexit 1\n",
    )
    .unwrap();
    std::fs::set_permissions(&compiler, std::fs::Permissions::from_mode(0o700)).unwrap();
    for early in [false, true] {
        let mut command = cargo_util::ProcessBuilder::new(env!("CARGO_BIN_EXE_targo"));
        for (key, _) in std::env::vars_os() {
            if let Some(key) = key.to_str() {
                command.env_remove(key);
            }
        }
        command
            .env("HOME", root.path())
            .env("PATH", "/usr/bin:/bin")
            .env("RUSTC", &compiler)
            .env("COHORT_TEST_MARKER", &marker)
            .cwd(root.path())
            .args(&["--resource-capabilities", "--", "--unverified", "build"]);
        if early {
            command.args(&["--explain", "E0001"]);
        }
        let output = command.exec_with_capture(
            cargo_util::StreamingOutputLimits::new(1024, 4096)
                .with_timeout(Duration::from_secs(5))
                .with_child_exit_cleanup(),
        );
        assert!(
            output.succeeded(),
            "status {:?}; {}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let reply: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(reply["version"], 3);
        assert_eq!(reply["cpu_workers"], false);
        assert_eq!(reply["supports_invocation"], false);
        assert!(
            !marker.exists(),
            "discovery executed the configured compiler (early mode={early})"
        );
    }
}
