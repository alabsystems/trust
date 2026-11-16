// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

use super::*;
use std::io::Write as _;
use std::sync::Mutex;

static CAPTURE: Mutex<()> = Mutex::new(());
const ACTOR: &str = "resource_fixed::attribution::tests::native_control_actor";
const ROLE: &str = "TARGO_FIXED_ATTRIBUTION_TEST_ACTOR";

fn record(path: &Path) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt as _;
    let mut encoded = String::new();
    for &byte in path.as_os_str().as_bytes() {
        if byte.is_ascii_alphanumeric() || b"/._-".contains(&byte) {
            encoded.push(byte as char);
        } else {
            encoded.push_str(&format!("%{byte:02X}"));
        }
    }
    format!("OK resources version=1 available=1 self_register=peer-pid-start group_signals=exec-inherit runner={encoded}\n").into_bytes()
}

#[test]
fn native_registration_contract_is_strict_and_preserves_path_bytes() {
    let root = tempfile::tempdir().unwrap();
    let path = root.path().join("real runner");
    std::fs::write(&path, b"locator only; never executed").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
    let valid = record(&path);
    assert_eq!(runner(&valid).unwrap(), path);
    for invalid in [
        valid.iter().copied().chain(b"version=1".iter().copied()).collect(),
        String::from_utf8(valid.clone()).unwrap().replace("available=1", "available=0").into_bytes(),
        String::from_utf8(valid.clone()).unwrap().replace("exec-inherit", "numeric-pid").into_bytes(),
        String::from_utf8(valid.clone()).unwrap().replace("peer-pid-start", "observed-pid").into_bytes(),
        b"OK resources version=1 available=1 self_register=peer-pid-start group_signals=exec-inherit runner=%ZZ".to_vec(),
        b"OK resources version=1 available=1 self_register=peer-pid-start group_signals=exec-inherit runner=%00".to_vec(),
        vec![b'x'; STATUS_LIMIT + 1],
    ] { assert!(runner(&invalid).is_err()); }
}

#[test]
fn display_label_is_bounded_unicode_metadata_without_controls_or_arguments() {
    let path = PathBuf::from(format!("/{}\n", "界".repeat(100)));
    let value = label(&path, OsStr::new("/bin/targo"));
    assert!(value.len() <= 200);
    assert!(!value.chars().any(char::is_control));
}

#[test]
fn native_control_actor() {
    let Some(role) = std::env::var_os(ROLE) else {
        return;
    };
    match role.to_str().unwrap() {
        "success" => std::io::stdout()
            .write_all(&record(&std::env::current_exe().unwrap()))
            .unwrap(),
        "overflow" => std::io::stdout()
            .write_all(&vec![b'x'; STATUS_LIMIT + 1])
            .unwrap(),
        "wait" => loop {
            std::thread::park();
        },
        _ => panic!("unknown fixture actor"),
    }
}

fn actor(role: &str) -> ProcessBuilder {
    let mut process = ProcessBuilder::new(std::env::current_exe().unwrap());
    process
        .args(&["--exact", ACTOR, "--nocapture"])
        .env(ROLE, role);
    process
}

#[test]
fn real_probe_output_limit_and_timeout_return_only_after_owned_cleanup() {
    let _serial = CAPTURE.lock().unwrap();
    let limits = StreamingOutputLimits::new(STATUS_LIMIT, STATUS_LIMIT)
        .with_timeout(Duration::from_secs(5))
        .with_child_exit_cleanup();
    let oversized = actor("overflow").exec_with_capture(limits);
    assert!(oversized.started);
    assert!(!oversized.succeeded());
    assert!(oversized.failure.is_some());
    assert!(
        oversized.stdout_truncated,
        "the actual output bound, not a startup timeout, refused this child"
    );
    assert!(
        oversized.status.is_some(),
        "the original child was actually reaped"
    );
    let stopped = actor("wait").exec_with_capture(limits.with_timeout(Duration::from_millis(200)));
    assert!(stopped.started);
    assert!(!stopped.succeeded());
    assert!(stopped.failure.is_some());
    assert!(
        stopped.status.is_some(),
        "timeout retains actual owning wait"
    );
}
