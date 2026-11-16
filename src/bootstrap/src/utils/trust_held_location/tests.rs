// Trust: this file is Trust-owned. It pins the start-of-build refusal of a
// location the held-input rule refuses later (`trust_held_location.rs`).

use std::fs;
use std::os::unix::fs::PermissionsExt as _;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use trust_resource_provenance::program::HeldDirectoryInput;

use super::{RUNBOOK, check, ensure_with_cargo_home};
use crate::core::config::Config;
use crate::core::config::flags::Flags;

/// A private directory under this test binary's own build output, whose
/// ancestors meet the rule (unlike world-writable /tmp).
fn scratch() -> tempfile::TempDir {
    let base = std::env::current_exe().unwrap().parent().unwrap().canonicalize().unwrap();
    tempfile::Builder::new().prefix("held-location-").tempdir_in(base).unwrap()
}

/// `root/<name>0/<name>1/...`, each directory created with `modes[i]`, read back.
fn chain(root: &Path, name: &str, modes: &[u32]) -> Vec<PathBuf> {
    let mut path = root.to_owned();
    let mut created = Vec::new();
    for (index, &mode) in modes.iter().enumerate() {
        path.push(format!("{name}{index}"));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
        let actual = fs::metadata(&path).unwrap().permissions().mode() & 0o7777;
        assert_eq!(actual, mode, "fixture mode did not stick on {}", path.display());
        created.push(path.clone());
    }
    created
}

/// What the real held capture says about the same existing directory.
fn captured(path: &Path) -> bool {
    HeldDirectoryInput::open(path, Instant::now() + Duration::from_secs(30)).is_ok()
}

fn euid() -> u32 {
    // SAFETY: geteuid only reads this process's effective account.
    unsafe { libc::geteuid() }
}

fn assert_refused_at(error: &str, directory: &Path, mode: &str, role: &str, path: &Path) {
    for needle in [
        format!("Trust build location refused: {} (owner ", directory.display()),
        format!("(uid {}), mode {mode}) is on the path to the {role} {}: ", euid(), path.display()),
        // The runbook bullet names this mask; the message states the same one.
        "(mode & 0o7022 == 0)".to_owned(),
        RUNBOOK.to_owned(),
    ] {
        assert!(error.contains(&needle), "missing {needle:?} in:\n{error}");
    }
}

#[test]
fn a_world_writable_sticky_parent_is_refused_by_name_owner_and_mode() {
    // `<shared>` is mode 1777 (root-owned there; this account's here).
    let scratch = scratch();
    let dirs = chain(scratch.path(), "shared", &[0o1777, 0o700]);
    let error = check(&[("checkout", &dirs[1])]).unwrap_err();
    assert_refused_at(&error, &dirs[0], "1777", "checkout", &dirs[1]);
    assert!(error.contains("native input has unsupported kind or writable/special mode"));
    assert!(!captured(&dirs[1]), "the held capture must refuse what the preflight refuses");
}

#[test]
fn an_owner_only_chain_is_accepted() {
    let scratch = scratch();
    let dirs = chain(scratch.path(), "private", &[0o755, 0o700, 0o750]);
    // The pairing canonicalizes before it walks, so a symlink on the way (as
    // `/tmp` is) is judged by the directory it names, not refused as a link.
    let link = scratch.path().join("link");
    std::os::unix::fs::symlink(&dirs[1], &link).unwrap();
    check(&[
        ("checkout", &dirs[2]),
        ("build directory", &link.join("private2")),
        ("Cargo home", &dirs[2].join("not-yet").join("created")),
    ])
    .unwrap();
    assert!(captured(&dirs[2]), "the held capture must accept what the preflight accepts");
}

#[test]
fn a_group_writable_parent_is_refused() {
    let scratch = scratch();
    let dirs = chain(scratch.path(), "group", &[0o755, 0o775, 0o700]);
    let error = check(&[("stage0 seed sysroot", &dirs[2])]).unwrap_err();
    assert_refused_at(&error, &dirs[1], "0775", "stage0 seed sysroot", &dirs[2]);
    assert!(!captured(&dirs[2]), "the held capture must refuse what the preflight refuses");
}

#[test]
fn every_forbidden_bit_is_refused_at_the_first_directory_carrying_it() {
    let scratch = scratch();
    for (name, mode) in [("world", 0o757), ("setgid", 0o2755), ("sticky", 0o1755)] {
        let dirs = chain(scratch.path(), name, &[0o755, mode, 0o700]);
        let error = check(&[("Cargo home", &dirs[2])]).unwrap_err();
        assert_refused_at(&error, &dirs[1], &format!("{mode:04o}"), "Cargo home", &dirs[2]);
        assert!(!captured(&dirs[2]), "{name}: the held capture must refuse it too");
    }
    let dirs = chain(scratch.path(), "first", &[0o775, 0o1777, 0o700]);
    let error = check(&[("checkout", &dirs[2])]).unwrap_err();
    assert_refused_at(&error, &dirs[0], "0775", "checkout", &dirs[2]);
}

#[test]
fn a_path_not_yet_created_is_judged_by_its_existing_parents() {
    // A fresh tree's build directory, or a Cargo home made by the first fetch.
    let scratch = scratch();
    let dirs = chain(scratch.path(), "shared", &[0o1777]);
    let build = dirs[0].join("cut").join("build");
    let error = check(&[("build directory", &build)]).unwrap_err();
    assert_refused_at(&error, &dirs[0], "1777", "build directory", &build);
}

fn configuration(arguments: &[&str], build: &Path) -> Config {
    let temp = tempfile::TempDir::new().unwrap();
    let config = temp.path().join("bootstrap.toml");
    fs::write(&config, "").unwrap();
    let mut args = vec![
        "--config".to_owned(),
        config.display().to_string(),
        "--build-dir".to_owned(),
        build.display().to_string(),
        "--set".to_owned(),
        "build.submodules=false".to_owned(),
        "--set".to_owned(),
        "llvm.download-ci-llvm=false".to_owned(),
    ];
    args.extend(arguments.iter().map(|argument| (*argument).to_owned()));
    Config::parse_with_env(Flags::parse(&args), |_| None)
}

#[test]
fn a_build_checks_its_build_directory_seed_sysroot_and_cargo_home() {
    let scratch = scratch();
    let good = chain(scratch.path(), "good", &[0o700]).remove(0);
    let shared = chain(scratch.path(), "shared", &[0o1777]).remove(0);
    let bad = shared.join("cut");

    let config = configuration(&["build"], &bad.join("build"));
    let error = ensure_with_cargo_home(&config, &good, Some(&good)).unwrap_err();
    assert_refused_at(&error, &shared, "1777", "build directory", &bad.join("build"));

    let config = configuration(&["build"], &good.join("build"));
    let error = ensure_with_cargo_home(&config, &bad, Some(&good)).unwrap_err();
    assert_refused_at(&error, &shared, "1777", "stage0 seed sysroot", &bad);
    let error = ensure_with_cargo_home(&config, &good, Some(&bad)).unwrap_err();
    assert_refused_at(&error, &shared, "1777", "Cargo home", &bad);
    ensure_with_cargo_home(&config, &good, Some(&good)).unwrap();
}

#[test]
fn dry_runs_and_maintenance_commands_hold_nothing_and_are_not_refused() {
    let scratch = scratch();
    let shared = chain(scratch.path(), "shared", &[0o1777]).remove(0);
    let bad = shared.join("cut");
    for arguments in [&["build", "--dry-run"][..], &["fmt"], &["clean"], &["vendor"]] {
        let config = configuration(arguments, &bad.join("build"));
        ensure_with_cargo_home(&config, &bad, Some(&bad)).unwrap();
    }
}
