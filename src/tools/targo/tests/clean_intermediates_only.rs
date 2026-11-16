//! Actual native cleanup with compiler queries and new filesystem writes unavailable.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates
#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[path = "clean_intermediates_only/physical_alias.rs"]
mod physical_alias;

#[expect(
    clippy::disallowed_methods,
    reason = "native fixture captures its actual original toolchain before configuration"
)]
fn command(world: &Path) -> Command {
    let mut command = Command::new(
        std::env::var_os("TARGO_CLEAN_TEST_BINARY")
            .filter(|value| !value.is_empty())
            .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into()),
    );
    command.current_dir(world).env_clear().envs([
        ("HOME", world.as_os_str()),
        ("CARGO_HOME", world.join("home").as_os_str()),
        ("CARGO_TARGET_DIR", world.join("target").as_os_str()),
    ]);
    command
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("original rustdoc"),
        )
        .env("CARGO_TERM_COLOR", "never")
        .env("CARGO_INCREMENTAL", "0");
    command
}

fn recorded(command: &mut Command, world: &Path, label: &str) -> Output {
    let output = command.output().unwrap();
    fs::write(world.join(format!("{label}.stdout")), &output.stdout).unwrap();
    fs::write(world.join(format!("{label}.stderr")), &output.stderr).unwrap();
    fs::write(
        world.join(format!("{label}.status")),
        output.status.to_string(),
    )
    .unwrap();
    output
}

fn success(output: &Output, world: &Path) {
    assert!(
        output.status.success(),
        "world={} status={}\n{}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn world(split: bool) -> PathBuf {
    world_with_package_names(split, ["selected", "protected"])
}

fn world_with_package_names(split: bool, names: [&str; 2]) -> PathBuf {
    let base = std::env::temp_dir().join(".ubd/native-clean-intermediates.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("world-")
        .tempdir_in(base)
        .unwrap()
        .keep();
    fs::create_dir_all(world.join(".cargo")).unwrap();
    fs::write(world.join("Cargo.toml"), "[workspace]\nmembers=['selected','protected']\nresolver='2'\n[profile.dev]\ndebug=0\n[profile.custom]\ninherits='dev'\n").unwrap();
    let mut config = "[unstable]\nbuild-dir-new-layout=true\n".to_owned();
    if split {
        config.push_str(&format!(
            "[build]\nbuild-dir={:?}\n",
            world.join("build-data")
        ));
    }
    fs::write(world.join(".cargo/config.toml"), config).unwrap();
    for (package, name) in ["selected", "protected"].into_iter().zip(names) {
        fs::create_dir_all(world.join(package).join("src")).unwrap();
        fs::write(
            world.join(package).join("Cargo.toml"),
            format!("[package]\nname='{name}'\nversion='0.1.0'\nedition='2021'\n[[bin]]\nname='{package}'\npath='src/main.rs'\n"),
        )
        .unwrap();
        fs::write(
            world.join(package).join("src/main.rs"),
            "fn main(){println!(\"42\");}\n",
        )
        .unwrap();
    }
    success(
        &recorded(
            command(&world).args([
                "--unverified",
                "build",
                "--workspace",
                "--offline",
                "--jobs=1",
            ]),
            &world,
            "build",
        ),
        &world,
    );
    world
}

#[derive(Debug, PartialEq, Eq)]
enum Entry {
    File(Vec<u8>),
    Link(PathBuf),
}
fn snapshot(root: &Path, omit: Option<&Path>) -> BTreeMap<PathBuf, Entry> {
    walkdir::WalkDir::new(root)
        .follow_root_links(false)
        .into_iter()
        .filter_entry(|entry| Some(entry.path()) != omit)
        .map(Result::unwrap)
        .filter_map(|entry| {
            let path = entry.path().strip_prefix(root).unwrap().to_owned();
            if entry.file_type().is_symlink() {
                Some((path, Entry::Link(fs::read_link(entry.path()).unwrap())))
            } else if entry.file_type().is_file() {
                Some((path, Entry::File(fs::read(entry.path()).unwrap())))
            } else {
                None
            }
        })
        .collect()
}

fn enospc_library(world: &Path) -> PathBuf {
    let library = world.join(if cfg!(target_os = "macos") {
        "enospc.dylib"
    } else {
        "enospc.so"
    });
    let mut cc = Command::new("cc");
    cc.args(if cfg!(target_os = "macos") {
        vec!["-dynamiclib"]
    } else {
        vec!["-shared", "-fPIC"]
    });
    cc.arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/clean-enospc.c"))
        .arg("-o")
        .arg(&library);
    if cfg!(target_os = "linux") {
        cc.arg("-ldl");
    }
    success(&recorded(&mut cc, world, "compile-enospc"), world);
    let probe = world.join("enospc-probe");
    success(
        &recorded(
            Command::new("cc")
                .arg(
                    Path::new(env!("CARGO_MANIFEST_DIR"))
                        .join("tests/fixtures/clean-enospc-probe.c"),
                )
                .arg("-o")
                .arg(&probe),
            world,
            "compile-enospc-probe",
        ),
        world,
    );
    let existing = world.join("probe-existing");
    let removable = world.join("probe-removable");
    fs::write(&existing, b"unchanged").unwrap();
    fs::write(&removable, b"removable").unwrap();
    success(
        &recorded(
            injected(
                Command::new(probe)
                    .arg(world.join("probe-created"))
                    .arg(&existing)
                    .arg(world.join("probe-directory"))
                    .arg(&removable),
                world,
                &library,
            ),
            world,
            "enospc-probe",
        ),
        world,
    );
    assert_eq!(fs::read(existing).unwrap(), b"unchanged");
    assert!(!removable.exists());
    assert!(!world.join("probe-created").exists());
    assert!(!world.join("probe-directory").exists());
    library
}

fn injected<'a>(command: &'a mut Command, world: &Path, library: &Path) -> &'a mut Command {
    command
        .env(
            if cfg!(target_os = "macos") {
                "DYLD_INSERT_LIBRARIES"
            } else {
                "LD_PRELOAD"
            },
            library,
        )
        .env("TMPDIR", world.join("scratch"))
}

#[test]
fn clean_intermediates_recovers_with_real_enospc_and_keeps_compiled_outputs() {
    for split in [false, true] {
        let world = world(split);
        let target = world.join("target");
        let build = if split {
            world.join("build-data")
        } else {
            target.clone()
        };
        let selected = build.join("debug/build/selected");
        assert!(
            selected.is_dir(),
            "actual unit layout missing: {}",
            world.display()
        );
        assert!(build.join("debug/build/protected").is_dir());
        let library = enospc_library(&world);
        fs::create_dir(world.join("scratch")).unwrap();
        let lockfile = fs::read(world.join("Cargo.lock")).unwrap();
        let before = snapshot(&world.join("target"), None);
        let build_before = snapshot(&build, None);
        // The old selected full clean really needs a new control/scratch write.
        let old = recorded(
            injected(
                command(&world).args(["clean", "-p", "selected"]),
                &world,
                &library,
            ),
            &world,
            "original-full-clean",
        );
        assert!(!old.status.success());
        let stderr = String::from_utf8_lossy(&old.stderr);
        assert!(stderr.contains("CLEAN_ENOSPC_ACTIVE"), "{stderr}");
        assert!(stderr.contains("No space left on device"), "{stderr}");
        assert_eq!(snapshot(&target, None), before);
        assert_eq!(snapshot(&build, None), build_before);
        for (label, dry) in [("preview", true), ("apply", false)] {
            let mut clean = command(&world);
            clean.args(["clean", "--intermediates-only", "-p", "selected"]);
            // This also proves the operation does not need a compiler child.
            clean.env("RUSTC", world.join("compiler-must-not-start"));
            if dry {
                clean.arg("--dry-run");
            }
            let output = recorded(injected(&mut clean, &world, &library), &world, label);
            success(&output, &world);
            assert!(String::from_utf8_lossy(&output.stderr).contains("CLEAN_ENOSPC_ACTIVE"));
            if dry {
                assert_eq!(snapshot(&target, None), before);
                assert_eq!(snapshot(&build, None), build_before);
            }
        }
        assert!(!selected.exists());
        let protected = snapshot(&build, Some(&selected));
        let expected = build_before
            .into_iter()
            .filter(|(path, _)| !path.starts_with("debug/build/selected"))
            .collect();
        assert_eq!(protected, expected);
        if split {
            assert_eq!(snapshot(&target, None), before);
        }
        assert_eq!(fs::read(world.join("Cargo.lock")).unwrap(), lockfile);
        for package in ["selected", "protected"] {
            let output = Command::new(target.join("debug").join(package))
                .output()
                .unwrap();
            success(&output, &world);
            assert_eq!(output.stdout, b"42\n");
        }
    }
}

#[test]
#[expect(
    clippy::disallowed_methods,
    reason = "fixture independently holds the actual native output lock"
)]
fn clean_intermediates_refuses_missing_busy_or_aliased_original_locks() {
    physical_alias::package_directories();
    physical_alias::terminal_symlink();
    use std::os::unix::fs::symlink;
    let world = world(false);
    let target = world.join("target");
    let lock = target.join("debug/.cargo-artifact-lock");
    let held = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(&lock)
        .unwrap();
    held.try_lock().unwrap();
    let before = snapshot(&target, None);
    let busy = recorded(
        command(&world).args(["clean", "--intermediates-only", "-p", "selected"]),
        &world,
        "busy",
    );
    assert!(!busy.status.success());
    assert!(String::from_utf8_lossy(&busy.stderr).contains("output is busy"));
    assert_eq!(snapshot(&target, None), before);
    drop(held);
    fs::remove_file(&lock).unwrap();
    let before = snapshot(&target, None);
    let missing = recorded(
        command(&world).args(["clean", "--intermediates-only", "-p", "selected"]),
        &world,
        "missing",
    );
    assert!(!missing.status.success());
    assert_eq!(snapshot(&target, None), before);
    assert!(!lock.exists());
    fs::write(world.join("foreign-lock"), b"protected").unwrap();
    symlink(world.join("foreign-lock"), &lock).unwrap();
    let before = snapshot(&target, None);
    let alias = recorded(
        command(&world).args(["clean", "--intermediates-only", "-p", "selected"]),
        &world,
        "alias",
    );
    assert!(!alias.status.success());
    assert_eq!(snapshot(&target, None), before);
    assert_eq!(fs::read(world.join("foreign-lock")).unwrap(), b"protected");
}

#[test]
fn clean_intermediates_refuses_nested_final_artifact_root_before_unlink() {
    physical_alias::nested_output();
    let world = world(true);
    let build = world.join("build-data");
    let nested = build.join("debug/build/selected/final-artifacts");
    // This is a supported normal layout: build and final-artifact roots can
    // nest. Produce real final outputs and native locks there before cleaning.
    success(
        &recorded(
            command(&world).env("CARGO_TARGET_DIR", &nested).args([
                "--unverified",
                "build",
                "--workspace",
                "--offline",
                "--jobs=1",
            ]),
            &world,
            "nested-build",
        ),
        &world,
    );
    let before = snapshot(&build, None);
    let refused = recorded(
        command(&world).env("CARGO_TARGET_DIR", &nested).args([
            "clean",
            "--intermediates-only",
            "-p",
            "selected",
        ]),
        &world,
        "nested-refusal",
    );
    assert!(!refused.status.success());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("protected output root"));
    assert_eq!(snapshot(&build, None), before);
    for package in ["selected", "protected"] {
        let output = Command::new(nested.join("debug").join(package))
            .output()
            .unwrap();
        success(&output, &world);
        assert_eq!(output.stdout, b"42\n");
    }
}

#[test]
fn clean_intermediates_honors_custom_profile_and_explicit_target() {
    let world = world(false);
    success(
        &recorded(
            command(&world).args([
                "--unverified",
                "build",
                "--workspace",
                "--offline",
                "--jobs=1",
                "--profile",
                "custom",
            ]),
            &world,
            "custom-build",
        ),
        &world,
    );
    let target = world.join("target");
    let host_selected = target.join("custom/build/selected");
    assert!(host_selected.is_dir());
    // Explicit-target cleanup needs no cross compiler. Create owned layout
    // DATA and real existing lock files for that additional target namespace;
    // only the ordinary host outputs above claim actual compilation.
    let selector = "targo-clean-fixture";
    let profile = target.join(selector).join("custom");
    let selected = profile.join("build/selected");
    fs::create_dir_all(&selected).unwrap();
    fs::write(selected.join("owned-cache-data"), b"reclaim").unwrap();
    fs::create_dir_all(profile.join("build/protected")).unwrap();
    fs::write(profile.join("build/protected/owned-data"), b"keep").unwrap();
    for lock in [".cargo-build-lock", ".cargo-lock", ".cargo-artifact-lock"] {
        fs::write(profile.join(lock), b"").unwrap();
    }
    assert!(selected.is_dir());
    let before = snapshot(&target, Some(&selected))
        .into_iter()
        .filter(|(path, _)| !path.starts_with("custom/build/selected"))
        .collect::<BTreeMap<_, _>>();
    let output = recorded(
        command(&world)
            .env("RUSTC", world.join("compiler-must-not-start"))
            .args([
                "clean",
                "--intermediates-only",
                "-p",
                "selected",
                "--profile",
                "custom",
                "--target",
                selector,
            ]),
        &world,
        "custom-clean",
    );
    success(&output, &world);
    assert!(!selected.exists());
    assert!(!host_selected.exists());
    assert_eq!(snapshot(&target, Some(&selected)), before);
}
