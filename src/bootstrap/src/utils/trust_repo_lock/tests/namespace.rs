use std::fs::{self, File};
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};

use build_helper::trust_build_lock::{GUARD_NAME, NamespaceGuard};

use super::BuildLease;

struct OwnedChild(Option<Child>);
impl OwnedChild {
    fn spawn(command: &mut Command) -> Self {
        Self(Some(command.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap()))
    }
    fn pending(&mut self) {
        assert!(self.0.as_mut().unwrap().try_wait().unwrap().is_none());
    }
    fn finish(mut self) -> Output {
        // Trust: both namespace helpers permit a 30-second contended flock.
        // The native manager also observes process identity and writers while holding it.
        // This is a hung-child watchdog, not a lock-latency requirement: allow
        // the protocol to return before terminating a correctly serialized child.
        let timeout = Duration::from_secs(60);
        let deadline = Instant::now() + timeout;
        loop {
            if self.0.as_mut().unwrap().try_wait().unwrap().is_some() {
                return self.0.take().unwrap().wait_with_output().unwrap();
            }
            assert!(
                Instant::now() < deadline,
                "namespace control pid {} did not finish within {timeout:?}",
                self.0.as_ref().unwrap().id(),
            );
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

// Trust: the same native manager actor is compiled into each harness; no
// facade script or synthetic product executable is copied into the fixture.
mod native_actor {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../crates/trust-build-tree/src/trust_repo_lock/tests/native_actor.rs"
    ));
}
fn manager_run(args: &[std::ffi::OsString]) -> u8 {
    build_helper::trust_repo_lock::management::cli::run(args)
}
fn lock_inherited(root: &Path, fd: std::os::fd::RawFd) -> std::io::Result<()> {
    build_helper::trust_build_lock::lock_inherited(root, fd)
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
fn versioned_parent_release_refuses_old_bootstrap_and_missing_handoff_before_config() {
    use crate::core::config::flags::Flags;
    let args = [
        "test",
        "--stage",
        "1",
        "--trust-repo-check",
        "--trust-repo-parent-release-v1",
        "tests/ui/trust/one.rs",
    ]
    .map(str::to_owned);
    let flags = Flags::parse(&args);
    assert!(flags.cmd.trust_repo_check());
    assert!(flags.cmd.trust_repo_parent_release_v1());
    let ordinary = Flags::parse(&["test".to_owned(), "tests/ui/trust/one.rs".to_owned()]);
    assert!(!ordinary.cmd.trust_repo_check());
    assert!(!ordinary.cmd.trust_repo_parent_release_v1());
    let raw = Flags::parse(&[
        "test".to_owned(),
        "--trust-repo-check".to_owned(),
        "tests/ui/trust/one.rs".to_owned(),
    ]);
    assert!(raw.cmd.trust_repo_check());
    assert!(!raw.cmd.trust_repo_parent_release_v1());
}

#[cfg(feature = "native-cli-tests")]
#[test]
fn actual_current_parent_release_refuses_missing_handoff_before_config() {
    let args = [
        "test",
        "--stage",
        "1",
        "--trust-repo-check",
        "--trust-repo-parent-release-v1",
        "tests/ui/trust/one.rs",
    ];
    let fixture = Fixture::new();
    let command_for = |binary: &std::ffi::OsStr| {
        let mut command = Command::new(binary);
        command
            .args(&args)
            .arg("--src")
            .arg(&fixture.root)
            .arg("--config")
            .arg(fixture.root.join("must-not-read-missing.toml"))
            .current_dir(&fixture.root)
            .env_remove("TRUST_NATIVE_REPO_PARENT_PID")
            .env_remove("TRUST_NATIVE_REPO_PARENT_START")
            .env_remove("TRUST_NATIVE_REPO_PARENT_TOKEN")
            // Trust: EW18-LOCKUTC-1's zone-free start is part of the handoff too.
            .env_remove("TRUST_NATIVE_REPO_PARENT_START_UTC");
        command
    };
    let current = std::env::var_os("TRUST_NAMESPACE_BOOTSTRAP_CONTROL")
        .expect("native-cli-tests requires the actual newly built Bootstrap control");
    {
        for mode in ["absent", "partial", "wrong-parent"] {
            let mut command = command_for(&current);
            if mode != "absent" {
                command.env("TRUST_NATIVE_REPO_PARENT_PID", "1");
            }
            if mode == "wrong-parent" {
                command
                    .env("TRUST_NATIVE_REPO_PARENT_START", "previous parent")
                    .env("TRUST_NATIVE_REPO_PARENT_TOKEN", "trust-native-repo-owner-control");
            }
            let output = OwnedChild::spawn(&mut command).finish();
            assert_eq!(output.status.code(), Some(2), "{mode}: {output:?}");
            let error = String::from_utf8_lossy(&output.stderr);
            let expected = if mode == "absent" {
                "requires the validated actual-parent"
            } else if mode == "partial" {
                "incomplete native release handoff"
            } else {
                "does not identify our actual live parent"
            };
            assert!(error.contains(expected), "{mode}: {output:?}");
            assert!(
                !error.contains("must-not-read-missing.toml"),
                "config must not run: {output:?}"
            );
        }
        let mut command = Command::new(&current);
        command.args(["test", "--trust-repo-parent-release-v1"]).current_dir(&fixture.root);
        let output = OwnedChild::spawn(&mut command).finish();
        assert_eq!(output.status.code(), Some(2), "{output:?}");
        assert!(String::from_utf8_lossy(&output.stderr).contains("--trust-repo-check"));
    }
    assert!(!fixture.root.join(".trust-build-lock").exists());
    assert!(!fixture.root.join(GUARD_NAME).exists());
    assert!(!fixture.root.join("build").exists());
}

#[cfg(feature = "native-cli-tests")]
#[test]
fn actual_old_parent_release_spelling_is_refused_before_config() {
    let fixture = Fixture::new();
    let old = std::env::var_os("TRUST_NAMESPACE_OLD_BOOTSTRAP_CONTROL")
        .expect("native-cli-tests requires the actual old Bootstrap refusal control");
    let mut command = Command::new(old);
    command
        .args(["test", "--trust-repo-check", "--trust-repo-parent-release-v1"])
        .arg("--src")
        .arg(&fixture.root)
        .arg("--config")
        .arg(fixture.root.join("must-not-read-missing.toml"))
        .current_dir(&fixture.root);
    let output = OwnedChild::spawn(&mut command).finish();
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("unexpected argument '--trust-repo-parent-release-v1'"),
        "{output:?}"
    );
    assert!(!fixture.root.join(".trust-build-lock").exists());
    assert!(!fixture.root.join(GUARD_NAME).exists());
    assert!(!fixture.root.join("build").exists());
}

include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../crates/trust-build-tree/src/trust_repo_lock/tests/namespace_cases.rs"
));

#[test]
fn guard_errors_refuse_native_manager_and_cold_xpy_before_any_build() {
    use std::os::unix::fs::PermissionsExt;
    let fixture = Fixture::new();
    {
        let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        fs::copy(source.join("x.py"), fixture.root.join("x.py")).unwrap();
        let guard = fixture.root.join(GUARD_NAME);
        for kind in ["content", "writable", "symlink", "fifo"] {
            match kind {
                "content" => fs::write(&guard, b"invalid").unwrap(),
                "writable" => {
                    File::create(&guard).unwrap();
                    fs::set_permissions(&guard, fs::Permissions::from_mode(0o666)).unwrap();
                }
                "symlink" => {
                    fs::write(fixture.root.join("peer"), b"").unwrap();
                    std::os::unix::fs::symlink(fixture.root.join("peer"), &guard).unwrap();
                }
                _ => {
                    assert!(Command::new("mkfifo").arg(&guard).status().unwrap().success());
                }
            }
            assert!(BuildLease::acquire(&fixture.root).is_err(), "{kind}");
            let output = OwnedChild::spawn(&mut fixture.acquire()).finish();
            assert_eq!(output.status.code(), Some(2), "{kind}: {output:?}");
            assert!(!fixture.root.join(".trust-build-lock").exists());
            let mut xpy = Command::new("python3");
            xpy.arg(fixture.root.join("x.py")).arg("check").env("TRUST_SKIP_PREFLIGHT", "1");
            let output = OwnedChild::spawn(&mut xpy).finish();
            assert_eq!(output.status.code(), Some(1), "x.py {kind}: {output:?}");
            assert!(String::from_utf8_lossy(&output.stderr).contains("refusing unlocked"));
            fs::remove_file(&guard).unwrap();
        }
        drop(NamespaceGuard::acquire(&fixture.root).unwrap());
        let foreign = fixture.root.join("foreign");
        let file = File::create(&foreign).unwrap();
        use std::os::fd::AsRawFd;
        assert!(
            build_helper::trust_build_lock::lock_inherited(&fixture.root, file.as_raw_fd())
                .is_err()
        );
        assert!(build_helper::trust_build_lock::lock_inherited(&fixture.root, 2).is_err());
        assert!(build_helper::trust_build_lock::lock_inherited(&fixture.root, i32::MAX).is_err());
        // Native validation rejects foreign/closed/stdio descriptors directly;
        // an empty x.py is no longer on the native manager's lock path.
    }
}
