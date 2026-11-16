// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Actual provider caller controls in fresh processes: global owner installation
//! is irreversible. No credential service, native admission or SDK is simulated.
use super::{adaptor::BasicProcessCredential, process::CredentialProcessCredential};
use cargo_credential::{Action, Credential, CredentialResponse, Operation, RegistryInfo};
use cargo_util::{ExecStats, ProcessBuilder, ProcessExecutor, StreamingOutputLimits};
use std::{
    io,
    os::unix::fs::PermissionsExt as _,
    process::{Child, Command, ExitStatus, Output, Stdio},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::{Duration, Instant},
};

const ACTOR: &str = "util::credential::tests::credential_provider_process_actor";
const ROLE: &str = "TRUST_TEST_CREDENTIAL_PROCESS_OWNER";
const REFUSAL: &str =
    "external credential processes are unsupported by the mandatory execution owner";

struct Refuse(AtomicUsize);
impl ProcessExecutor for Refuse {
    fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Err(io::ErrorKind::PermissionDenied.into())
    }
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Err(io::ErrorKind::PermissionDenied.into())
    }
    fn streaming(
        &self,
        _: &ProcessBuilder,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: &mut dyn FnMut(&str) -> anyhow::Result<()>,
        _: bool,
        _: Option<StreamingOutputLimits>,
        _: bool,
    ) -> (ExecStats, anyhow::Result<Output>) {
        self.0.fetch_add(1, Ordering::SeqCst);
        (
            ExecStats::default(),
            Err(anyhow::anyhow!("unexpected credential dispatch")),
        )
    }
}

#[test]
fn credential_provider_process_actor() {
    let Ok(role) = std::env::var(ROLE) else {
        return;
    };
    assert!(matches!(role.as_str(), "owned" | "local"));
    let fixture = tempfile::tempdir().unwrap();
    let provider = fixture.path().join("provider");
    // Inert local fixture. Actual execution writes a physical marker before
    // yielding token bytes; the same bytes are invalid interactive hello DATA.
    std::fs::write(
        &provider,
        b"#!/bin/sh\nprintf called > \"$0.invoked\"\nprintf 'fixture-token\\r\\n'\n",
    )
    .unwrap();
    std::fs::set_permissions(&provider, std::fs::Permissions::from_mode(0o700)).unwrap();
    let marker = fixture.path().join("provider.invoked");
    let owner = Arc::new(Refuse(AtomicUsize::new(0)));
    if role == "owned" {
        cargo_util::install_process_executor(owner.clone()).unwrap();
        assert!(cargo_util::install_process_executor(owner.clone()).is_err());
        let installed = cargo_util::installed_process_executor().unwrap();
        let original: Arc<dyn ProcessExecutor> = owner.clone();
        assert!(Arc::ptr_eq(&installed, &original));
    }
    let registry = RegistryInfo {
        index_url: "https://credential-fixture.invalid/index",
        name: Some("fixture"),
        headers: vec![],
    };
    let action = Action::Get(Operation::Read);
    let command = provider.to_str().unwrap();
    let basic = BasicProcessCredential {};
    let basic_result = basic.perform(&registry, &action, &[command]);
    if role == "owned" {
        assert!(basic_result.unwrap_err().to_string().contains(REFUSAL));
        assert!(
            !marker.exists(),
            "token provider must not be born outside its owner"
        );
    } else {
        assert!(matches!(
            basic_result.unwrap(),
            CredentialResponse::Get { .. }
        ));
        assert!(
            marker.is_file(),
            "ordinary local provider actually executed"
        );
        std::fs::remove_file(&marker).unwrap();
    }
    let interactive = CredentialProcessCredential::new(command);
    let error = interactive.perform(&registry, &action, &[]).unwrap_err();
    if role == "owned" {
        assert!(error.to_string().contains(REFUSAL));
        assert!(
            !marker.exists(),
            "interactive provider must not be born outside its owner"
        );
        // Unsupported token-provider actions retain their ordinary refusal,
        // and malformed arguments do not turn into a dispatch attempt.
        assert!(basic.perform(&registry, &Action::Logout, &[]).is_err());
        assert!(basic.perform(&registry, &action, &[]).is_err());
        assert_eq!(owner.0.load(Ordering::SeqCst), 0);
    } else {
        assert!(!error.to_string().contains(REFUSAL));
        assert!(
            marker.is_file(),
            "ordinary interactive provider actually executed"
        );
    }
}

struct OwnedChild(Child);
impl Drop for OwnedChild {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
fn actor(role: &str, offline: bool) {
    // Each test owns only its actual child; no shared-global reset, owner
    // fabrication, arbitrary PID/PGID signal or timeout-derived success.
    let mut child = OwnedChild(
        Command::new(std::env::current_exe().unwrap())
            .args(["--exact", ACTOR, "--nocapture", "--test-threads=1"])
            .env(ROLE, role)
            .env("CARGO_NET_OFFLINE", if offline { "true" } else { "false" })
            .stdin(Stdio::null())
            .spawn()
            .unwrap(),
    );
    let by = Instant::now() + Duration::from_secs(30);
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            assert!(
                status.success(),
                "isolated credential caller control failed"
            );
            return;
        }
        assert!(
            Instant::now() < by,
            "isolated credential caller did not exit"
        );
        std::thread::sleep(Duration::from_millis(5));
    }
}
#[test]
fn mandatory_owner_refuses_both_external_providers_before_birth_even_offline() {
    actor("owned", true);
}
#[test]
fn mandatory_owner_refusal_is_not_a_caller_network_policy_override() {
    actor("owned", false);
}
#[test]
fn ordinary_unowned_credential_providers_still_execute() {
    actor("local", true);
}
