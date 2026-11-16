use std::os::fd::AsRawFd;
use std::process::Stdio;
use std::sync::Arc;

use build_helper::trust_repo_lock::management::{
    Acquire, Kind, LeaseAcquisition, Manager, ProtectedWorkScope,
};
use jobserver_utils::Jobserver;

use super::*;
use crate::utils::metadata_scheduler::{install_test_original, output};

const NAME: &str = "utils::metadata_scheduler::producer::tests::actual_producer_transport_and_exact_completion_controls";
const ROLE: &str = "TRUST_BOOTSTRAP_PRODUCER_TEST_ROLE";

fn identity(fd: i32) -> String {
    let mut stat = std::mem::MaybeUninit::<libc::stat>::uninit();
    // Observe descriptions without importing a scheduler or granting resources.
    assert_eq!(unsafe { libc::fstat(fd, stat.as_mut_ptr()) }, 0);
    let stat = unsafe { stat.assume_init() };
    assert_eq!(stat.st_mode & libc::S_IFMT, libc::S_IFIFO);
    format!("{}:{}", stat.st_dev, stat.st_ino)
}

fn scope() -> (tempfile::TempDir, ProtectedWorkScope) {
    let directory = tempfile::tempdir().unwrap();
    let request = Acquire {
        kind: Kind::Build,
        owner_pid: std::process::id(),
        purpose: "actual Bootstrap producer transport controls".into(),
        contract: "same scheduler and actual local child only; no Host/SDK/release authority"
            .into(),
        wait: Duration::ZERO,
        inherited_token: None,
        break_reason: None,
    };
    let lease = match Manager::open(directory.path()).unwrap().acquire_lease(&request).unwrap() {
        LeaseAcquisition::Granted(lease) => lease,
        LeaseAcquisition::Busy(_) => panic!("unexpected fixture contention"),
    };
    let actual = ProtectedWorkScope::new(
        Arc::new(lease.into_withheld().unwrap()),
        Instant::now() + Duration::from_secs(20),
    )
    .unwrap();
    (directory, actual)
}

fn child(server: &Jobserver) -> Command {
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.args(["--exact", NAME, "--nocapture"]);
    command.env(ROLE, "child");
    let expected = server
        .pipe_descriptors()
        .unwrap()
        .iter()
        .map(|fd| identity(fd.as_raw_fd()))
        .collect::<Vec<_>>()
        .join(",");
    command.env("TRUST_BOOTSTRAP_PRODUCER_EXPECTED_DESCRIPTIONS", expected);
    command.env_remove("MAKEFLAGS").env_remove("MFLAGS");
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    command
}

#[test]
fn actual_producer_transport_and_exact_completion_controls() {
    let Ok(role) = std::env::var(ROLE) else {
        for role in ["success", "wrong-child", "unresolved", "deadline", "spawn-failed", "late"] {
            let result =
                crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()))
                    .args(["--exact", NAME, "--nocapture"])
                    .env(ROLE, role)
                    .output()
                    .unwrap();
            assert!(result.status.success(), "actor {role}: {result:?}");
        }
        return;
    };
    if role == "child" {
        let flags = std::env::var("CARGO_MAKEFLAGS").unwrap();
        assert_eq!(std::env::var("MAKEFLAGS").unwrap(), flags);
        assert_eq!(std::env::var("MFLAGS").unwrap(), flags);
        let pair = flags
            .split_ascii_whitespace()
            .find_map(|word| word.strip_prefix("--jobserver-auth="))
            .unwrap();
        let observed = pair
            .split(',')
            .map(|number| identity(number.parse().unwrap()))
            .collect::<Vec<_>>()
            .join(",");
        assert_eq!(
            observed,
            std::env::var("TRUST_BOOTSTRAP_PRODUCER_EXPECTED_DESCRIPTIONS").unwrap()
        );
        println!("same-original-producer-descriptions");
        return;
    }
    let original = Jobserver::new(2).unwrap();
    let paid = original.client().acquire().unwrap();
    install_test_original(original.clone()).unwrap();
    let (_root, work) = scope();
    let dispatch = work.dispatcher();
    let other = if role == "wrong-child" {
        let (_directory, other) = scope();
        let completed = other
            .dispatcher()
            .register_launch()
            .unwrap()
            .spawn(&mut Command::new("/usr/bin/true"))
            .unwrap()
            .wait_with_output_and_join()
            .unwrap()
            .1;
        drop(other.seal().join().unwrap());
        Some(completed)
    } else {
        None
    };
    let registration = dispatch.register_launch().unwrap();
    let mut command = child(&original);
    let deadline =
        if role == "late" { Instant::now() + Duration::from_secs(2) } else { dispatch.deadline() };
    let borrowed = prepare_producer(&mut command, &registration, deadline).unwrap();
    assert_eq!(original.client().available().unwrap(), 1);
    if role == "spawn-failed" {
        assert!(registration.spawn(&mut Command::new("/no/such/producer")).is_err());
        drop(borrowed);
    } else {
        let (result, joined) =
            registration.spawn(&mut command).unwrap().wait_with_output_and_join().unwrap();
        assert!(result.status.success(), "{result:?}");
        assert!(String::from_utf8_lossy(&result.stdout).contains("same-original-producer"));
        if role == "deadline" {
            let pending = dispatch.register_launch().unwrap();
            let result = prepare_producer(
                &mut Command::new("/usr/bin/true"),
                &pending,
                Instant::now() + Duration::from_millis(20),
            );
            assert!(matches!(result, Err(error) if error.kind() == io::ErrorKind::TimedOut));
            drop(pending); // Permanently poisons the scope; no later spawn is eligible.
        }
        match role.as_str() {
            "wrong-child" => {
                assert!(borrowed.observe_join(other.unwrap()).is_err());
                drop(joined);
            }
            "unresolved" => {
                drop(joined);
                drop(borrowed);
            }
            "success" | "deadline" => {
                let pending = borrowed.observe_join(joined).unwrap();
                assert!(pending.unresolved().contains("retirement"));
            }
            "late" => {
                assert!(Instant::now() < deadline, "actual child must finish before the deadline");
                std::thread::sleep(
                    deadline.saturating_duration_since(Instant::now()) + Duration::from_millis(1),
                );
                let expected_stdout = result.stdout.clone();
                let expected_stderr = result.stderr.clone();
                let actual =
                    crate::utils::exec::UnresolvedOutput::after_join(result, borrowed, Ok(joined));
                assert!(actual.output.status.success());
                assert_eq!(actual.output.stdout, expected_stdout);
                assert_eq!(actual.output.stderr, expected_stderr);
                assert!(actual.reason.contains("producer completion deadline"));
            }
            _ => panic!("unknown actor"),
        }
    }
    let next = output(&mut Command::new("/usr/bin/true"), true, true);
    assert!(next.is_err(), "a local join cannot return the original implicit execution");
    assert_eq!(original.client().available().unwrap(), 1);
    drop(paid);
    assert_eq!(original.client().available().unwrap(), 2);
    if role == "deadline" {
        assert!(work.seal().join().is_err());
    } else {
        drop(work.seal().join().unwrap());
    }
}
