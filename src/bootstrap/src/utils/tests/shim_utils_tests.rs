//! Code in the `shim_utils` crate can be tested here as part of `./x test bootstrap`.
//!
//! Trust: this also carries the shared-helpers unit tests that lived in
//! `shared_helpers_tests.rs` before the 1.101 port moved the helpers into
//! `shim_utils` (upstream's rename of this file).

use std::ffi::{OsStr, OsString};
use std::process::Command;
use std::sync::{Mutex, MutexGuard};
use std::{env, fs};

use shim_utils::{
    cargo_test_no_verify_requested, compile_uses_trust_bootstrap_no_verify, expand_rustc_argfiles,
    finalize_trust_no_verify, maybe_dump, parse_value_from_args,
    trust_bootstrap_shim_marker_enabled,
};

static ENV_LOCK: Mutex<()> = Mutex::new(());

struct EnvVarGuard {
    key: &'static str,
    previous: Option<OsString>,
    _lock: MutexGuard<'static, ()>,
}

impl EnvVarGuard {
    fn set(key: &'static str, value: impl AsRef<OsStr>) -> Self {
        let lock = ENV_LOCK.lock().unwrap();
        let previous = env::var_os(key);
        // SAFETY: this test serializes process environment mutation with ENV_LOCK
        // and restores the original value when the guard is dropped.
        unsafe {
            env::set_var(key, value);
        }
        Self { key, previous, _lock: lock }
    }
}

impl Drop for EnvVarGuard {
    fn drop(&mut self) {
        // SAFETY: see EnvVarGuard::set.
        unsafe {
            if let Some(previous) = &self.previous {
                env::set_var(self.key, previous);
            } else {
                env::remove_var(self.key);
            }
        }
    }
}

#[test]
fn maybe_dump_creates_dump_directory() {
    let tempdir = tempfile::TempDir::new().unwrap();
    let dump_dir = tempdir.path().join("nested").join("bootstrap-shims-dump");
    assert!(!dump_dir.exists());

    let _dump_env = EnvVarGuard::set("DUMP_BOOTSTRAP_SHIMS", &dump_dir);
    let mut cmd = Command::new("rustc");
    cmd.arg("--version");

    maybe_dump("stage1-rustc".to_string(), &cmd);

    let dump_file = dump_dir.join("stage1-rustc");
    assert!(dump_dir.is_dir());
    let dump = fs::read_to_string(dump_file).unwrap();
    assert!(dump.contains("rustc"));
    assert!(dump.contains("--version"));
}

#[test]
fn expands_line_and_shell_rustc_argfiles_before_policy_inspection() {
    let tempdir = tempfile::TempDir::new().unwrap();
    let line_args = tempdir.path().join("line.args");
    fs::write(&line_args, "--target\naarch64-unknown-linux-gnu\n--crate-name\nfixture\n").unwrap();
    let shell_args = tempdir.path().join("shell.args");
    fs::write(&shell_args, "--cfg 'feature=\"fixture shell\"'").unwrap();

    let raw = vec![
        OsString::from(format!("@{}", line_args.display())),
        OsString::from("-Zshell-argfiles"),
        OsString::from(format!("@shell:{}", shell_args.display())),
    ];
    assert_eq!(
        expand_rustc_argfiles(&raw).unwrap(),
        vec![
            OsString::from("--target"),
            OsString::from("aarch64-unknown-linux-gnu"),
            OsString::from("--crate-name"),
            OsString::from("fixture"),
            OsString::from("-Zshell-argfiles"),
            OsString::from("--cfg"),
            OsString::from("feature=\"fixture shell\""),
        ],
    );
}

#[test]
fn compile_classifier_accepts_direct_inputs_and_rejects_queries() {
    let args = |values: &[&str]| values.iter().map(OsString::from).collect::<Vec<_>>();

    assert!(compile_uses_trust_bootstrap_no_verify(&args(&["src/lib.rs", "--crate-type=lib",])));
    assert!(compile_uses_trust_bootstrap_no_verify(&args(
        &["-", "--crate-name", "stdin_fixture",]
    )));
    assert!(!compile_uses_trust_bootstrap_no_verify(&args(&[
        "-",
        "--crate-name",
        "___",
        "--print=file-names",
    ])));
    assert!(!compile_uses_trust_bootstrap_no_verify(&[]));
    assert!(!compile_uses_trust_bootstrap_no_verify(&args(&["-Vv"])));
    assert!(!compile_uses_trust_bootstrap_no_verify(&args(&["-Z", "help"])));
    assert!(compile_uses_trust_bootstrap_no_verify(&args(&[
        "src/lib.rs",
        "--",
        "--print=file-names",
    ])));
}

#[test]
fn final_no_verify_policy_overrides_late_conflicts_and_strips_unsupported_drivers() {
    let mut supported = vec![
        OsString::from("src/lib.rs"),
        OsString::from("-Ztrust-verify=on"),
        OsString::from("-Z"),
        OsString::from("trust_verify=on"),
    ];
    finalize_trust_no_verify(&mut supported, true, true);
    assert_eq!(supported, vec![OsString::from("src/lib.rs"), OsString::from("-Ztrust-verify=off")],);

    let mut unsupported = supported;
    finalize_trust_no_verify(&mut unsupported, false, true);
    assert_eq!(unsupported, vec![OsString::from("src/lib.rs")]);
}

#[test]
fn authenticated_targo_frontend_cannot_be_downgraded_by_cargo_test_isolation() {
    assert!(cargo_test_no_verify_requested(true, false));
    assert!(!cargo_test_no_verify_requested(true, true));
    assert!(!cargo_test_no_verify_requested(false, false));
}

#[test]
fn bootstrap_shim_marker_accepts_only_the_exact_internal_value() {
    assert!(trust_bootstrap_shim_marker_enabled(Some(OsStr::new("1"))));
    for value in [None, Some(OsStr::new("")), Some(OsStr::new("true")), Some(OsStr::new("0"))] {
        assert!(!trust_bootstrap_shim_marker_enabled(value));
    }
}

#[test]
fn test_parse_value_from_args() {
    let args = vec![
        "--stage".into(),
        "1".into(),
        "--version".into(),
        "2".into(),
        "--target".into(),
        "x86_64-unknown-linux".into(),
    ];

    assert_eq!(parse_value_from_args(args.as_slice(), "--stage").unwrap(), "1");
    assert_eq!(parse_value_from_args(args.as_slice(), "--version").unwrap(), "2");
    assert_eq!(parse_value_from_args(args.as_slice(), "--target").unwrap(), "x86_64-unknown-linux");
    assert!(parse_value_from_args(args.as_slice(), "random-key").is_none());

    let args = vec![
        "app-name".into(),
        "--key".into(),
        "value".into(),
        "random-value".into(),
        "--sysroot=/x/y/z".into(),
    ];
    assert_eq!(parse_value_from_args(args.as_slice(), "--key").unwrap(), "value");
    assert_eq!(parse_value_from_args(args.as_slice(), "--sysroot").unwrap(), "/x/y/z");
}
