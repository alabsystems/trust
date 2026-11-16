//! Real authenticated-image execution must share native child custody.

use super::*;
use cargo_util::StreamingProcessScope;
use std::time::{Duration, Instant};

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "the authenticated image reads its actual inherited fixture mode and PID witness path before any Cargo context exists"
)]
fn authenticated_lifecycle_child_fixture() {
    let Some(mode) = env::var_os("TARGO_AUTH_LIFECYCLE") else {
        return;
    };
    let pidfile = env::var_os("TARGO_AUTH_LIFECYCLE_PID").unwrap();
    let child = std::process::Command::new("/bin/sleep")
        .arg("60")
        .spawn()
        .unwrap();
    // Trust: cancellation observers treat the final path as readiness. Writing
    // it directly exposes an empty file before the PID bytes are written, so
    // cancellation can kill the fixture in that gap. Publish only the closed,
    // complete witness; the pending path is never observed as ready.
    let pending = Path::new(&pidfile).with_extension("pending");
    fs::write(&pending, child.id().to_string()).unwrap();
    fs::rename(pending, pidfile).unwrap();
    // This intentionally leaves a same-group subprocess behind when the
    // harness ends, or when its owned execution scope cancels it.
    if mode == "wait" {
        std::thread::sleep(Duration::from_secs(60));
    }
}

pub(super) fn image(root: &Path, mode: &str) -> (TestExecutionAuthority, PathBuf, ProcessBuilder) {
    let executable = root.join("test-image");
    fs::copy(env::current_exe().unwrap(), &executable).unwrap();
    let executable = executable.canonicalize().unwrap();
    let (sha256, size) = exact_regular_test_executable_identity(&executable).unwrap();
    let entry = TestExecutionAuthorityEntry {
        target: "authenticated-lifecycle".into(),
        path: executable.to_str().unwrap().into(),
        sha256,
        size,
    };
    let authority = TestExecutionAuthority {
        executables: [(executable.clone(), entry)].into_iter().collect(),
        prepared: None,
    };
    let mut command = ProcessBuilder::new(&executable);
    command
        .arg("--exact")
        .arg("ops::cargo_test::authenticated_lifecycle::authenticated_lifecycle_child_fixture")
        .arg("--test-threads=1")
        .env("TARGO_AUTH_LIFECYCLE", mode)
        .env("TARGO_AUTH_LIFECYCLE_PID", root.join("child-pid"));
    strip_test_execution_authority_env(&mut command);
    (authority, executable, command)
}

pub(super) fn assert_child_stopped(pidfile: &Path) {
    let pid: libc::pid_t = fs::read_to_string(pidfile).unwrap().parse().unwrap();
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        // Observation only. The native executor has already performed its last
        // group signal while retaining the unreaped leader. Never signal this
        // numeric descendant PID from the regression observer.
        let status = std::process::Command::new("/bin/ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .unwrap();
        let state = String::from_utf8(status.stdout).unwrap();
        if state.trim().is_empty() || state.trim_start().starts_with('Z') {
            return;
        }
        assert!(
            Instant::now() < deadline,
            "authenticated descendant {pid} survived: {state}"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn authenticated_normal_exit_stops_same_group_descendants() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    let (authority, path, command) = image(&root, "background");
    execute_authenticated_test(&authority, &path, &command).unwrap();
    assert_child_stopped(&root.join("child-pid"));
}

#[test]
fn authenticated_cancellation_stops_harness_and_descendants() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    let (authority, path, mut command) = image(&root, "wait");
    let scope = StreamingProcessScope::new().unwrap();
    command.supervised_by(&scope);
    let pidfile = root.join("child-pid");
    let result = std::thread::scope(|threads| {
        let cancel = threads.spawn(|| {
            let deadline = Instant::now() + Duration::from_secs(10);
            while !pidfile.exists() && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(5));
            }
            let started = pidfile.exists();
            scope.cancel();
            started
        });
        let result = execute_authenticated_test(&authority, &path, &command);
        assert!(
            cancel.join().unwrap(),
            "authenticated harness never started"
        );
        result
    });
    assert!(
        result.is_err(),
        "cancelled authenticated execution cannot pass"
    );
    assert_child_stopped(&pidfile);
    scope.finish().unwrap();
}

#[cfg(target_os = "macos")]
#[test]
fn rejected_suspended_image_never_runs_user_code() {
    let root = tempfile::tempdir().unwrap();
    let root = root.path().canonicalize().unwrap();
    let (authority, path, command) = image(&root, "background");
    let mut snapshot = authority.mac_executable_snapshot(&path).unwrap();
    snapshot.cdhash = "0".repeat(snapshot.cdhash.len());
    let error = execute_authenticated_mac_snapshot(snapshot, &path, &command).unwrap_err();
    assert!(format!("{error:#}").contains("code identity differs"));
    assert!(
        !root.join("child-pid").exists(),
        "unauthorized suspended child ran"
    );
}
