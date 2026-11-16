//! Trust: exercise the actual native manager in separate processes, without a shell facade.

use std::fs::{self, File};
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use super::BuildLease;
use crate::trust_build_lock::{GUARD_NAME, NamespaceGuard};

struct OwnedChild(Option<Child>);

impl OwnedChild {
    fn spawn(command: &mut Command) -> Self {
        Self(Some(command.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap()))
    }

    fn pending(&mut self) {
        assert!(self.0.as_mut().unwrap().try_wait().unwrap().is_none());
    }

    fn finish(mut self) -> Output {
        // A hang watchdog, not a lock-latency requirement: namespace helpers
        // allow a 30-second contended flock and the native manager observes process state.
        let timeout = Duration::from_secs(60);
        let deadline = Instant::now() + timeout;
        loop {
            if self.0.as_mut().unwrap().try_wait().unwrap().is_some() {
                return self.0.take().unwrap().wait_with_output().unwrap();
            }
            assert!(Instant::now() < deadline, "namespace initializer actor did not finish");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

#[path = "native_actor.rs"]
mod native_actor;

fn manager_run(args: &[std::ffi::OsString]) -> u8 {
    crate::trust_repo_lock::management::cli::run(args)
}
fn lock_inherited(root: &Path, fd: std::os::fd::RawFd) -> std::io::Result<()> {
    crate::trust_build_lock::lock_inherited(root, fd)
}

pub(crate) fn command(root: &Path, args: &[&str]) -> Command {
    #[cfg(feature = "native-cli-tests")]
    {
        let executable = std::env::var_os("TRUST_BUILD_TREE_TARGO")
            .expect("native-cli-tests requires the actual newly built Targo executable");
        let mut child = Command::new(executable);
        child
            .args(["trust", "repo", "lock"])
            .args(args)
            .arg("--repo-root")
            .arg(root)
            .env("TRUST_REPO", root)
            .env_remove("TRUST_BUILD_LOCK_TOKEN")
            .env_remove("TRUST_BUILD_LOCK_WAIT")
            .env_remove("TRUST_BUILD_LOCK_BREAK");
        child
    }
    #[cfg(not(feature = "native-cli-tests"))]
    {
        native_actor::command(root, args)
    }
}

struct Fixture {
    _temp: tempfile::TempDir,
    root: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().canonicalize().unwrap();
        Self { _temp: temp, root }
    }
    fn command(&self, args: &[&str]) -> Command {
        command(&self.root, args)
    }
    fn acquire(&self) -> Command {
        self.command(&[
            "acquire",
            "--kind",
            "build",
            "--purpose",
            "namespace control",
            "--pid",
            &std::process::id().to_string(),
        ])
    }
}

#[test]
fn initializer_is_not_reclaimed_or_released_by_two_other_actors() {
    let fixture = Fixture::new();
    {
        let mut children = Vec::new();
        let native = BuildLease::acquire_after_claim(&fixture.root, false, || {
            assert!(!fixture.root.join(".trust-build-lock/info").exists());
            children.push(OwnedChild::spawn(&mut fixture.acquire()));
            children.push(OwnedChild::spawn(&mut fixture.command(&["release", "peer-token"])));
            std::thread::sleep(Duration::from_millis(150));
            for child in &mut children {
                child.pending();
            }
            assert!(fixture.root.join(".trust-build-lock").is_dir());
        })
        .unwrap();
        let mut outputs = children.into_iter().map(OwnedChild::finish);
        assert_eq!(outputs.next().unwrap().status.code(), Some(3));
        assert_eq!(outputs.next().unwrap().status.code(), Some(4));
        assert_eq!(
            fs::read_to_string(fixture.root.join(".trust-build-lock/info")).unwrap(),
            native.info
        );
        drop(native);
    }
}

include!("namespace_cases.rs");

// Bootstrap's harness includes namespace_cases.rs without `owner_only`, so the
// stale-holder case runs under umask 002 from here.
#[test]
fn stale_holder_case_passes_under_a_group_writable_umask() {
    crate::owner_only::under_umask_002(
        "trust_repo_lock::tests::namespace::stale_holder_case_passes_under_a_group_writable_umask",
        stale_recovery_is_serialized_and_exact_token_still_required,
    );
}
