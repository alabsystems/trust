//! Real target and descendant activity under the same streaming group owner.
#![cfg(any(target_os = "linux", target_os = "macos"))]

use super::super::{ChildSupervision, ProcessBuilder, StreamingOutputLimits};
use super::CHILD_EXIT_TEST_LOCK;
use std::io::{self, Write};
use std::time::{Duration, Instant};

const ROLE: &str = "CARGO_UTIL_ACTIVITY_SUPERVISION_CHILD";
const CHILD: &str = "process_builder::tests::activity_supervision::controlled_child";
const RELEASE: &str = "CARGO_UTIL_ACTIVITY_BYSTANDER_RELEASE";
const COMPLETED: &str = "CARGO_UTIL_ACTIVITY_BYSTANDER_COMPLETED";
const MEMBER_COMPLETED: &str = "CARGO_UTIL_ACTIVITY_MEMBER_COMPLETED";

fn command(role: &str) -> ProcessBuilder {
    let mut command = ProcessBuilder::new(std::env::current_exe().unwrap());
    command
        .args(&["--exact", CHILD, "--nocapture", "--quiet"])
        .env(ROLE, role);
    command
}

fn limits(inactivity: Duration) -> StreamingOutputLimits {
    StreamingOutputLimits::new(4096, 64 * 1024)
        .with_timeout(Duration::from_secs(5))
        .with_child_supervision(ChildSupervision::new(inactivity, None).unwrap())
}

#[test]
fn controlled_child() {
    let Some(role) = std::env::var_os(ROLE) else {
        return;
    };
    match role.to_str().unwrap() {
        "idle" => {
            println!("actual-idle-body-started");
            io::stdout().flush().unwrap();
            loop {
                std::thread::park();
            }
        }
        "busy" | "long-busy" => {
            println!("actual-busy-body-started");
            io::stdout().flush().unwrap();
            let started = Instant::now();
            let duration = if role == "long-busy" {
                Duration::from_secs(4)
            } else {
                Duration::from_millis(900)
            };
            while started.elapsed() < duration {
                std::hint::black_box((0..1000_u64).fold(0_u64, u64::wrapping_add));
            }
            println!("actual-busy-body-completed");
        }
        "busy-descendant" => {
            let mut child = std::process::Command::new(std::env::current_exe().unwrap());
            child
                .args(["--exact", CHILD, "--nocapture", "--quiet"])
                .env(ROLE, "busy");
            assert!(child.spawn().unwrap().wait().unwrap().success());
            println!("actual-descendant-was-reaped");
        }
        "memory" => {
            println!("actual-memory-body-started");
            io::stdout().flush().unwrap();
            let mut memory = vec![0_u8; 96 * 1024 * 1024];
            for page in memory.chunks_mut(4096) {
                page[0] = 1;
            }
            std::hint::black_box(&memory);
            loop {
                std::thread::park();
            }
        }
        "bystander" => {
            let release = std::path::PathBuf::from(std::env::var_os(RELEASE).unwrap());
            let deadline = Instant::now() + Duration::from_secs(10);
            while !release.exists() {
                assert!(Instant::now() < deadline, "bystander release was lost");
                std::thread::sleep(Duration::from_millis(5));
            }
            std::fs::write(
                std::env::var_os(COMPLETED).unwrap(),
                b"actual-bystander-completed",
            )
            .unwrap();
        }
        "short-member" => {
            std::fs::write(
                std::env::var_os(MEMBER_COMPLETED).unwrap(),
                b"actual-short-member",
            )
            .unwrap();
        }
        "churn" => {
            assert_eq!(
                trust_resource_provenance::process::read_identity(std::process::id())
                    .unwrap()
                    .pid,
                std::process::id()
            );
            let root = tempfile::tempdir().unwrap();
            for index in 0..4 {
                let marker = root.path().join(index.to_string());
                let mut child = std::process::Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", CHILD, "--nocapture", "--quiet"])
                    .env(ROLE, "short-member")
                    .env(MEMBER_COMPLETED, &marker)
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .spawn()
                    .unwrap();
                let deadline = Instant::now() + Duration::from_secs(3);
                // SAFETY: this fixture owns the actual direct Child and is
                // its sole waiter; it keeps the child unreaped until below.
                while !unsafe {
                    trust_resource_provenance::process::unreaped_child_exit(
                        child.id() as libc::pid_t
                    )
                }
                .unwrap()
                {
                    assert!(Instant::now() < deadline, "actual member did not exit");
                    std::thread::sleep(Duration::from_millis(1));
                }
                // A positively exited, UNREAPED descendant remains present
                // across several native samples. It is not a permission error
                // or an unreadable live member and contributes no live RSS.
                std::thread::sleep(Duration::from_millis(250));
                assert!(
                    trust_resource_provenance::process::read_identity(child.id()).is_err(),
                    "terminal DATA must never satisfy the existing live execution-identity reader"
                );
                assert!(child.wait().unwrap().success());
                assert_eq!(std::fs::read(marker).unwrap(), b"actual-short-member");
            }
            println!("actual-churn-body-completed");
        }
        "exit-after-release" => {
            println!("actual-exit-race-body-started");
            io::stdout().flush().unwrap();
            let release = std::path::PathBuf::from(std::env::var_os(RELEASE).unwrap());
            let deadline = Instant::now() + Duration::from_secs(5);
            while !release.exists() {
                assert!(Instant::now() < deadline);
                std::thread::sleep(Duration::from_millis(1));
            }
            println!("actual-exit-race-body-completed");
        }
        other => panic!("unknown fixture role: {other}"),
    }
}

#[test]
fn silent_cpu_and_descendant_cpu_keep_the_original_child_live() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    for role in ["busy", "busy-descendant"] {
        let output = command(role)
            .exec_with_streaming_limits(
                &mut |_| Ok(()),
                &mut |_| Ok(()),
                true,
                limits(Duration::from_millis(300)),
            )
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("actual-busy-body-completed"), "{stdout}");
        if role == "busy-descendant" {
            assert!(stdout.contains("actual-descendant-was-reaped"), "{stdout}");
        }
    }
}

#[test]
fn actual_silent_body_is_stopped_without_stopping_an_unrelated_child() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let root = tempfile::tempdir().unwrap();
    let release = root.path().join("release");
    let completed = root.path().join("completed");
    let mut bystander = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", CHILD, "--nocapture", "--quiet"])
        .env(ROLE, "bystander")
        .env(RELEASE, &release)
        .env(COMPLETED, &completed)
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let mut body_started = false;
    let error = command("idle")
        .exec_with_streaming_limits(
            &mut |line| {
                body_started |= line.contains("actual-idle-body-started");
                Ok(())
            },
            &mut |_| Ok(()),
            false,
            limits(Duration::from_millis(300)),
        )
        .unwrap_err();
    assert!(
        body_started,
        "a zero-selected fixture cannot prove supervision"
    );
    assert!(
        format!("{error:#}").contains("inactivity window"),
        "{error:#}"
    );
    assert!(
        bystander.try_wait().unwrap().is_none(),
        "the unrelated child must still be live until its own release"
    );
    std::fs::write(&release, b"release original bystander").unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        if let Some(status) = bystander.try_wait().unwrap() {
            assert!(status.success());
            break;
        }
        if Instant::now() >= deadline {
            bystander.kill().unwrap();
            let _ = bystander.wait();
            panic!("the original bystander did not retire after release");
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    assert_eq!(
        std::fs::read(completed).unwrap(),
        b"actual-bystander-completed"
    );
}

#[test]
fn resident_limit_observes_actual_memory_and_keeps_its_cause() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let policy = ChildSupervision::new(
        Duration::from_secs(2),
        std::num::NonZeroU64::new(64 * 1024 * 1024),
    )
    .unwrap();
    let mut body_started = false;
    let error = command("memory")
        .exec_with_streaming_limits(
            &mut |line| {
                body_started |= line.contains("actual-memory-body-started");
                Ok(())
            },
            &mut |_| Ok(()),
            false,
            limits(Duration::from_secs(2)).with_child_supervision(policy),
        )
        .unwrap_err();
    assert!(body_started, "the actual allocation body must have started");
    assert!(
        format!("{error:#}").contains("resident-byte ceiling"),
        "{error:#}"
    );
}

#[test]
fn cpu_activity_does_not_cancel_the_existing_wall_deadline() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let mut completed = false;
    let mut started = false;
    let error = command("long-busy")
        .exec_with_streaming_limits(
            &mut |line| {
                started |= line.contains("actual-busy-body-started");
                completed |= line.contains("actual-busy-body-completed");
                Ok(())
            },
            &mut |_| Ok(()),
            false,
            limits(Duration::from_secs(3)).with_timeout(Duration::from_secs(2)),
        )
        .unwrap_err();
    assert!(
        started && !completed,
        "the actual running body must have been stopped"
    );
    assert!(
        format!("{error:#}").contains("wall-clock timeout"),
        "{error:#}"
    );
}

#[test]
fn resident_supervision_accepts_naturally_exited_and_reaped_descendants() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let policy = ChildSupervision::new(
        Duration::from_secs(2),
        std::num::NonZeroU64::new(512 * 1024 * 1024),
    )
    .unwrap();
    let output = command("churn")
        .exec_with_streaming_limits(
            &mut |_| Ok(()),
            &mut |_| Ok(()),
            true,
            limits(Duration::from_secs(2)).with_child_supervision(policy),
        )
        .unwrap();
    assert!(String::from_utf8_lossy(&output.stdout).contains("actual-churn-body-completed"));
}

#[test]
fn persistent_permission_failure_retires_the_actual_running_body() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let fault = super::super::activity_supervision::ObservationFault::scope();
    let policy = ChildSupervision::new(
        Duration::from_secs(2),
        std::num::NonZeroU64::new(512 * 1024 * 1024),
    )
    .unwrap();
    let mut started = false;
    let error = command("idle")
        .exec_with_streaming_limits(
            &mut |line| {
                if line.contains("actual-idle-body-started") {
                    started = true;
                    fault.activate();
                }
                Ok(())
            },
            &mut |_| Ok(()),
            false,
            limits(Duration::from_secs(2)).with_child_supervision(policy),
        )
        .unwrap_err();
    assert!(
        started,
        "the actual body must precede the persistent observation fault"
    );
    assert!(
        error.chain().any(|cause| cause
            .downcast_ref::<io::Error>()
            .is_some_and(|error| error.kind() == io::ErrorKind::PermissionDenied)),
        "{error:#}"
    );
}

#[test]
fn original_exit_between_precheck_and_sample_returns_to_the_original_owner() {
    let _owner = CHILD_EXIT_TEST_LOCK.lock().unwrap();
    let root = tempfile::tempdir().unwrap();
    let release = root.path().join("release-original");
    let fault = super::super::activity_supervision::ObservationFault::exiting(release.clone());
    let policy = ChildSupervision::new(
        Duration::from_secs(2),
        std::num::NonZeroU64::new(512 * 1024 * 1024),
    )
    .unwrap();
    let mut target = command("exit-after-release");
    target.env(RELEASE, &release);
    let output = target
        .exec_with_streaming_limits(
            &mut |line| {
                if line.contains("actual-exit-race-body-started") {
                    fault.activate();
                }
                Ok(())
            },
            &mut |_| Ok(()),
            true,
            limits(Duration::from_secs(2)).with_child_supervision(policy),
        )
        .unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("actual-exit-race-body-started")
            && stdout.contains("actual-exit-race-body-completed"),
        "{stdout}"
    );
}
