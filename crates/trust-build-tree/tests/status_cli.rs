#![cfg(all(feature = "machine-admission", any(target_os = "macos", target_os = "linux")))]

use std::process::Command;

const PROGRAM: &str = env!("CARGO_BIN_EXE_trust-build-status");

#[test]
fn status_cli_observes_the_existing_owner_schema() {
    let output = Command::new(PROGRAM).arg("--json").output().unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let direct =
        serde_json::to_value(trust_build_tree::admission::status::current().unwrap()).unwrap();
    assert_eq!(value["protocol"], "native-resource-status-v1");
    for key in ["native_capacity_bytes", "legacy_namespace_bytes"] {
        assert_eq!(value[key], direct[key]);
    }
    assert_eq!(
        value.as_object().unwrap().keys().collect::<Vec<_>>(),
        direct.as_object().unwrap().keys().collect::<Vec<_>>(),
    );
    assert!(
        value["available_memory_bytes"].is_null()
            || value["available_memory_bytes"].as_u64().is_some()
    );
}

#[test]
fn status_cli_help_and_unknown_options_create_no_namespace() {
    let temporary = tempfile::tempdir().unwrap();
    let absent = temporary.path().join("must-not-exist");
    for (args, success) in [
        (vec!["--help"], true),
        (vec!["--namespace", "ignored"], false),
        (vec!["--json", "--json"], false),
    ] {
        let output =
            Command::new(PROGRAM).args(args).env("BUILD_SLOT_DIR", &absent).output().unwrap();
        assert_eq!(output.status.success(), success);
        assert!(!absent.exists(), "status never creates or repairs a namespace");
        if !success {
            assert_eq!(output.status.code(), Some(2));
            assert!(output.stdout.is_empty());
        }
    }
}

#[test]
fn status_cli_rejects_a_noncanonical_namespace_without_creating_it() {
    let temporary = tempfile::tempdir().unwrap();
    let absent = temporary.path().join("must-not-exist");
    let output =
        Command::new(PROGRAM).arg("--json").env("BUILD_SLOT_DIR", &absent).output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert!(!absent.exists());
}
