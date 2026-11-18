//! This module contains shared utilities for bootstrap tests.

use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

use tempfile::TempDir;

use crate::core::config::Config;
use crate::core::config::flags::Flags;

pub mod git;
// Trust: blessed env_mutation — these tests serialize process-env mutation
// behind a lock and restore on drop (see EnvVarGuard in the file).
#[allow(unknown_lints)]
#[allow(env_mutation)]
mod shim_utils_tests;
// Trust: compile the compiler crates' actual feature declarations with the seed.
mod seed_feature_tests;
// Trust: exercise the actual build-script compiler selection in this owner.
#[allow(dead_code)]
#[path = "../../../build.rs"]
pub(crate) mod bootstrap_build_script;
// Trust: compile the actual LLVM build-script integration in this maintained
// owner too; helper-only tests cannot detect type errors in its link loop.
#[allow(dead_code)]
#[allow(unexpected_cfgs, reason = "Trust: check_only is a feature of the actual LLVM crate")]
#[path = "../../../../../compiler/rustc_llvm/build.rs"]
pub(crate) mod rustc_llvm_build_script;

/// Holds temporary state of a bootstrap test.
/// Right now it is only used to redirect the build directory of the bootstrap
/// invocation, in the future it would be great if we could actually execute
/// the whole test with this directory set as the workdir.
pub struct TestCtx {
    directory: TempDir,
}

impl TestCtx {
    pub fn new() -> Self {
        let directory = TempDir::new().expect("cannot create temporary directory");
        eprintln!("Running test in {}", directory.path().display());
        Self { directory }
    }

    /// Keep failed fixture inputs; the test explicitly closes only after success.
    pub fn retain(mut self) -> Self {
        self.directory.disable_cleanup(true);
        self
    }

    /// Remove an explicitly retained fixture after all assertions have passed.
    pub fn close(self) -> std::io::Result<()> {
        self.directory.close()
    }

    pub fn dir(&self) -> &Path {
        self.directory.path()
    }

    /// Using backslashes fails with `--set`
    pub fn normalized_dir(&self) -> String {
        self.dir().to_string_lossy().replace("\\", "/")
    }

    /// Starts a new invocation of bootstrap that executes `kind` as its top level command
    /// (i.e. `x <kind>`). Returns a builder that configures the created config through CLI flags.
    pub fn config(&self, kind: &str) -> ConfigBuilder {
        ConfigBuilder::from_args(&[kind], self.directory.path().to_owned())
    }
}

/// Used to configure an invocation of bootstrap.
/// Currently runs in the rustc checkout, long-term it should be switched
/// to run in a (cache-primed) temporary directory instead.
pub struct ConfigBuilder {
    args: Vec<String>,
    directory: PathBuf,
    override_download_ci_llvm: bool,
    dry_run: bool,
    explicit_config: bool,
    // Trust: isolated admission variables; tests never inherit an outer share.
    environment: HashMap<OsString, OsString>,
}

impl ConfigBuilder {
    fn from_args(args: &[&str], directory: PathBuf) -> Self {
        Self {
            args: args.iter().copied().map(String::from).collect(),
            directory,
            override_download_ci_llvm: true,
            dry_run: true,
            explicit_config: true,
            environment: HashMap::new(),
        }
    }

    pub fn path(self, path: &str) -> Self {
        self.arg(path)
    }

    pub fn paths(self, paths: &[&str]) -> Self {
        self.args(paths)
    }

    pub fn arg(mut self, arg: &str) -> Self {
        self.args.push(arg.to_string());
        self
    }

    pub fn args(mut self, args: &[&str]) -> Self {
        for arg in args {
            self = self.arg(arg);
        }
        self
    }

    /// Trust: inject a bootstrap admission variable without process-env mutation.
    pub fn env(mut self, name: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> Self {
        self.environment.insert(name.as_ref().to_owned(), value.as_ref().to_owned());
        self
    }

    /// Set the specified target to be treated as a no_std target.
    pub fn override_target_no_std(self, target: &str) -> Self {
        self.args(&["--set", &format!("target.{target}.no-std=true")])
    }

    pub fn hosts(mut self, targets: &[&str]) -> Self {
        self.args.push("--host".to_string());
        self.args.push(targets.join(","));
        self
    }

    pub fn targets(mut self, targets: &[&str]) -> Self {
        self.args.push("--target".to_string());
        self.args.push(targets.join(","));
        self
    }

    pub fn stage(mut self, stage: u32) -> Self {
        self.args.push("--stage".to_string());
        self.args.push(stage.to_string());
        self
    }

    pub fn with_default_toml_config(mut self, config_toml: &str) -> Self {
        let toml_path = self.directory.join("bootstrap.toml");
        std::fs::write(&toml_path, config_toml).unwrap();
        self.explicit_config = false;
        self.args.push("--config".to_string());
        self.args.push(toml_path.display().to_string());
        self
    }

    pub fn no_override_download_ci_llvm(mut self) -> Self {
        self.override_download_ci_llvm = false;
        self
    }

    pub fn no_dry_run(mut self) -> Self {
        self.dry_run = false;
        self
    }

    pub fn create_config(self) -> Config {
        self.create_config_with_fixed_budget(None)
    }

    pub fn create_config_with_fixed_budget(mut self, fixed_jobs: Option<u32>) -> Config {
        if self.dry_run {
            // Run in dry-check, otherwise the test would be too slow
            self.args.push("--dry-run".to_string());
        }
        // Ignore submodules
        self.args.push("--set".to_string());
        self.args.push("build.submodules=false".to_string());

        if self.override_download_ci_llvm {
            // Override any external LLVM set and inhibit CI LLVM; pretend that we're always building
            // in-tree LLVM from sources.
            self.args.push("--set".to_string());
            self.args.push("llvm.download-ci-llvm=false".to_string());
        }

        // always use the bootstrap toml created in the
        // temporary directory and not from the <src>
        if self.explicit_config {
            self = self.with_default_toml_config("");
        }

        // Do not mess with the local rustc checkout build directory
        self.args.push("--build-dir".to_string());
        self.args.push(self.directory.join("build").display().to_string());

        Config::parse_with_env_and_fixed_budget(
            Flags::parse(&self.args),
            |name| self.environment.get(OsStr::new(name)).cloned(),
            fixed_jobs,
        )
    }
}

const ISOLATED: &str = "TRUST_BOOTSTRAP_ISOLATED_TEST";

/// Trust: runs `body` as the only test in a child process of this test binary.
/// A flock lock belongs to the open file description, and a process another
/// test thread starts holds descriptors for this process's open descriptions,
/// close-on-exec or not: a forked child until it exits, or until it execs for a
/// close-on-exec descriptor, as Rust opens every file (Command forks on its
/// fallbacks, among them a pre_exec closure, uid, gid or groups, chroot and a
/// changed PATH with a bare program name, which tests in this binary take), and
/// on macOS a posix_spawn for the spawn itself (measured on macOS only; the
/// commit that wrote this sentence describes the measurement and gives its
/// counts). So a lock a test released can still look held to that test's next
/// take. Isolate a test before its first fixture descriptor when it takes a lock
/// it released.
/// One exact test and a post-assert marker exclude an ignored, filtered-out or
/// early-success child; the bound is a watchdog, never another completion
/// condition. The child's output is read as it is written, so a long report
/// cannot fill a pipe and stall it (LAND-GATE-EW1-FOLLOWUP-REVIEW-4 (12)).
pub(crate) fn isolated(body: impl FnOnce()) {
    isolated_with_env(&[], body)
}

/// Use the same isolated actor with explicit child-only environment observations.
pub(crate) fn isolated_with_env(environment: &[(OsString, Option<OsString>)], body: impl FnOnce()) {
    use std::io::Read;
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    const COMPLETE: &str = "TRUST-ISOLATED-TEST-ASSERTIONS-COMPLETE:";
    let name = std::thread::current().name().expect("named test").to_owned();
    if std::env::var_os(ISOLATED).as_deref() == Some(OsStr::new(&name)) {
        body();
        eprintln!("{COMPLETE}{name}");
        return;
    }
    let mut command =
        crate::test_entry::uncaptured_actor(Command::new(std::env::current_exe().unwrap()));
    command
        .args(["--exact", &name, "--test-threads=1", "--nocapture"])
        .env(ISOLATED, &name)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    for (key, value) in environment {
        if let Some(value) = value {
            command.env(key, value);
        } else {
            command.env_remove(key);
        }
    }
    let mut child = command.spawn().unwrap();
    let drain = |mut pipe: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            pipe.read_to_end(&mut bytes).unwrap();
            String::from_utf8_lossy(&bytes).into_owned()
        })
    };
    let stdout = drain(Box::new(child.stdout.take().unwrap()));
    let stderr = drain(Box::new(child.stderr.take().unwrap()));
    let until = Instant::now() + Duration::from_secs(60);
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break Some(status);
        }
        if Instant::now() >= until {
            child.kill().unwrap();
            child.wait().unwrap();
            break None;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    let (stdout, stderr) = (stdout.join().unwrap(), stderr.join().unwrap());
    let status = status.unwrap_or_else(|| panic!("{name} timed out: {stdout}{stderr}"));
    assert!(status.success(), "{name}: {stdout}{stderr}");
    assert!(stdout.contains("test result: ok. 1 passed;"), "{name}: {stdout}{stderr}");
    assert!(stderr.contains(&format!("{COMPLETE}{name}")), "{name}: {stdout}{stderr}");
}

/// Trust: whether this process is an `isolated` test's child.
pub(crate) fn in_isolated_child() -> bool {
    std::env::var_os(ISOLATED).is_some()
}
