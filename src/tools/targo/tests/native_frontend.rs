//! Automatic worker sizing must preserve explicit stable compiler policy.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn compile(root: &Path, target: &Path, bootstrap: Option<&str>, wrapper: Option<&Path>) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_targo"));
    cmd.current_dir(root)
        .env_clear()
        .env("HOME", root)
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("CARGO_HOME", root.join("cargo-home"))
        .env("CARGO_TARGET_DIR", target)
        .env("RUSTC", std::env::var_os("RUSTC").expect("test compiler"))
        .args(["--unverified", "build", "--offline", "-j", "2", "-vv"]);
    if let Some(value) = bootstrap {
        cmd.env("RUSTC_BOOTSTRAP", value);
    }
    if let Some(wrapper) = wrapper {
        cmd.env("RUSTC_WORKSPACE_WRAPPER", wrapper);
    }
    cmd.output().unwrap()
}

fn check(root: &Path, name: &str, bootstrap: Option<&str>, wrapper: Option<&Path>, sized: bool) {
    let target = root.join(name);
    let output = compile(root, &target, bootstrap, wrapper);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{name}: {stderr}");
    assert_eq!(stderr.contains("-Zthreads="), sized, "{name}: {stderr}");
    let binary = target.join("debug").join(format!(
        "stable_frontend_fixture{}",
        std::env::consts::EXE_SUFFIX
    ));
    let run = Command::new(binary).output().unwrap();
    assert!(run.status.success());
    assert_eq!(run.stdout, b"17");
}

#[test]
fn automatic_frontend_respects_effective_stable_policy() {
    let temporary = tempfile::tempdir_in(std::env::current_dir().unwrap()).unwrap();
    let root = temporary.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname='stable_frontend_fixture'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/main.rs"), "fn main() { print!(\"17\"); }\n").unwrap();
    let version = Command::new(std::env::var_os("RUSTC").expect("test compiler"))
        .arg("-vV")
        .output()
        .unwrap();
    assert!(version.status.success());
    let trust = String::from_utf8(version.stdout)
        .unwrap()
        .lines()
        .any(|line| line.starts_with("trust: "));
    check(root, "normal", None, None, trust);
    check(root, "ambient-stable", Some("-1"), None, false);

    fs::create_dir(root.join(".cargo")).unwrap();
    fs::write(
        root.join(".cargo/config.toml"),
        "[env]\nRUSTC_BOOTSTRAP = { value = '-1', force = true }\n",
    )
    .unwrap();
    // Authenticated Targo retains its separate authority-environment refusal.
    // Neither a forced config entry nor the worker-sizing fix may bypass it.
    let configured = compile(root, &root.join("configured-stable"), Some("1"), None);
    assert!(!configured.status.success());
    let error = String::from_utf8_lossy(&configured.stderr);
    assert!(error.contains("reserved authority environment variable `RUSTC_BOOTSTRAP`"));
    assert!(!error.contains("-Zthreads="));
    fs::remove_file(root.join(".cargo/config.toml")).unwrap();

    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let wrapper = root.join("compiler-wrapper");
        fs::write(&wrapper, "#!/bin/sh\nexec \"$@\"\n").unwrap();
        fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).unwrap();
        check(root, "wrapped-stable", Some("-1"), Some(&wrapper), false);
        check(root, "wrapped-normal", None, Some(&wrapper), trust);
    }
}
