// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! This actual library caller must refuse before config without a dispatcher.
//! Projection fields are DATA, never native source/SDK/GNU or seed owners.
use super::*;
use cargo_util::{ExecStats, ProcessBuilder, ProcessExecutor, StreamingOutputLimits};
use std::{
    io,
    process::{ExitStatus, Output},
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};
use trust_resource_controller::bootstrap_graph::{GnuIdentity, Key, query::OperationKey};
use trust_resource_controller::{ContextQuery, FileIdentity, JobBinding};

const ROLE: &str = "TRUST_TEST_OFFLINE_PREPARATION_CASE";
const NAME: &str = "offline_preparation::tests::absent_dispatcher_refuses_before_project_configuration_or_workspace_resolution";
fn actor(role: &str) {
    struct OwnedChild(std::process::Child);
    impl Drop for OwnedChild {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut command = std::process::Command::new(std::env::current_exe().unwrap());
    command
        .args(["--exact", NAME, "--test-threads=1", "--nocapture"])
        .env(ROLE, role);
    if role == "no-early-capture" {
        // Hostile numeric DATA must not trigger a late import after the
        // test harness has already opened arbitrary descriptors.
        command.env("CARGO_MAKEFLAGS", "--jobserver-auth=99999,99998");
    }
    let mut child = OwnedChild(command.spawn().unwrap());
    let end = Instant::now() + std::time::Duration::from_secs(30);
    loop {
        if let Some(status) = child.0.try_wait().unwrap() {
            assert!(status.success());
            break;
        }
        assert!(
            Instant::now() < end,
            "unowned preparation caller did not exit"
        );
        std::thread::sleep(std::time::Duration::from_millis(5));
    }
}

struct Refuse(AtomicUsize);
impl ProcessExecutor for Refuse {
    fn status(&self, _: &ProcessBuilder) -> io::Result<ExitStatus> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Err(io::ErrorKind::PermissionDenied.into())
    }
    fn output(&self, _: &ProcessBuilder) -> io::Result<Output> {
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
            Err(anyhow::anyhow!("dispatcher must not be reached")),
        )
    }
}

#[test]
fn absent_dispatcher_refuses_before_project_configuration_or_workspace_resolution() {
    // Global dispatch installation is irreversible. Each caller owns a fresh
    // process; no unrelated fixture can reset or fabricate its original.
    let Ok(role) = std::env::var(ROLE) else {
        actor("unowned");
        return;
    };
    assert!(cargo_util::installed_process_executor().is_none());
    let dispatcher = Arc::new(Refuse(AtomicUsize::new(0)));
    let missing_early = role == "no-early-capture";
    assert!(missing_early || role == "unowned");
    if missing_early {
        cargo_util::install_process_executor(dispatcher.clone()).unwrap();
    }
    let world = tempfile::tempdir().unwrap();
    std::fs::create_dir(world.path().join(".cargo")).unwrap();
    // A configuration read would be a different real error, not our prebirth
    // refusal. No valid package, compiler or credential service is supplied.
    std::fs::write(world.path().join(".cargo/config.toml"), "[malformed").unwrap();
    let request = Request {
        key: OperationKey {
            graph: Key {
                query: ContextQuery {
                    binding: JobBinding {
                        session: "s-abcd".into(),
                        root_attempt: [1; 16],
                        capability: [9; 32],
                    },
                    call_attempt: [2; 16],
                },
                graph: [3; 16],
            },
            sequence: 1,
            operation: [4; 16],
        },
        gnu: GnuIdentity::NamedFifo {
            path: b"/fixture/credits".to_vec(),
            backing: FileIdentity {
                device: 1,
                inode: 2,
            },
        },
        control_sdk_root: b"/fixture/control".to_vec(),
        source_root: world.path().as_os_str().as_encoded_bytes().to_vec(),
        source_directory: FileIdentity {
            device: 1,
            inode: 10,
        },
        output_root: b"/fixture/output".to_vec(),
        output_directory: FileIdentity {
            device: 1,
            inode: 11,
        },
        output_lock: FileIdentity {
            device: 1,
            inode: 12,
        },
        configured_targo: b"/fixture/seed/bin/cargo".to_vec(),
        configured_compiler: b"/fixture/seed/bin/rustc".to_vec(),
        cargo_home: b"/fixture/cargo".to_vec(),
        environment: vec![(b"CARGO_NET_OFFLINE".to_vec(), b"true".to_vec())],
        budget_ns: 900_000_000_000,
    };
    let envelope = Envelope {
        manifests: vec![
            b"Cargo.toml".to_vec(),
            b"library/Cargo.toml".to_vec(),
            b"src/bootstrap/Cargo.toml".to_vec(),
        ],
        input_paths: vec![b"/fixture/source/Cargo.toml".to_vec()],
    };
    request.validate().unwrap();
    envelope.validate().unwrap();
    let error = execute_offline_envelope(
        &request,
        &envelope,
        Instant::now() + std::time::Duration::from_secs(30),
    )
    .unwrap_err();
    let expected = if missing_early {
        "requires the original early-imported GNU scheduler"
    } else {
        "requires the installed execution owner before configuration"
    };
    assert!(
        error.to_string().contains(expected),
        "wrong boundary: {error:#}"
    );
    assert_eq!(dispatcher.0.load(Ordering::SeqCst), 0);
    assert_eq!(
        cargo_util::installed_process_executor().is_some(),
        missing_early
    );
}

#[test]
fn installed_dispatcher_never_late_imports_environment_gnu_slots() {
    actor("no-early-capture");
}
