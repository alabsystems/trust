//! Trust: a package dry run must count the same native artifacts it removes.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated fixture binds its original CLI/compiler before project configuration"
)]
fn command(world: &Path, arguments: &[&str], label: &str) -> Output {
    let executable = std::env::var_os("TARGO_CLEAN_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let output = Command::new(executable)
        .args(arguments)
        .current_dir(world)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("CARGO_TERM_COLOR", "never")
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching original rustdoc"),
        )
        // This case explicitly exercises Cargo's unstable new-layout profile.
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly")
        .output()
        .unwrap();
    fs::write(world.join(format!("{label}.stdout")), &output.stdout).unwrap();
    fs::write(world.join(format!("{label}.stderr")), &output.stderr).unwrap();
    fs::write(
        world.join(format!("{label}.status")),
        output.status.to_string(),
    )
    .unwrap();
    assert!(
        output.status.success(),
        "world={} status={}\n{}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn summary(output: &Output, status: &str) -> String {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .find_map(|line| line.trim().strip_prefix(status))
        .unwrap_or_else(|| {
            panic!(
                "missing {status}: {}",
                String::from_utf8_lossy(&output.stderr)
            )
        })
        .trim()
        .to_owned()
}

fn retained_world() -> std::path::PathBuf {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-clean-host-layout.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("clean")
        .tempdir_in(base)
        .unwrap()
        .keep();
    fs::create_dir_all(world.join("src")).unwrap();
    fs::write(
        world.join("Cargo.toml"),
        "[package]\nname='clean_native_subject'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(world.join("src/lib.rs"), "").unwrap();
    command(&world, &["generate-lockfile", "--offline"], "lockfile");
    world
}

#[test]
fn native_package_dry_run_matches_removal_and_preserves_other_packages() {
    let world = retained_world();

    // Exercise the real package/layout selector without compiling or borrowing
    // any SDK artifacts. Only this fixture's private target contains these bytes.
    let selected = world.join("target/debug/build/clean_native_subject/unit/out/subject");
    let other = world.join("target/debug/build/other_package/unit/out/other");
    fs::create_dir_all(selected.parent().unwrap()).unwrap();
    fs::create_dir_all(other.parent().unwrap()).unwrap();
    fs::write(&selected, vec![b'x'; 1024]).unwrap();
    fs::write(&other, b"unselected artifact").unwrap();
    let dry = command(
        &world,
        &[
            "clean",
            "--locked",
            "--offline",
            "-Zbuild-dir-new-layout",
            "-p",
            "clean_native_subject",
            "--dry-run",
        ],
        "dry-run",
    );
    assert_eq!(fs::read(&selected).unwrap(), vec![b'x'; 1024]);
    assert_eq!(fs::read(&other).unwrap(), b"unselected artifact");
    let actual = command(
        &world,
        &[
            "clean",
            "--locked",
            "--offline",
            "-Zbuild-dir-new-layout",
            "-p",
            "clean_native_subject",
        ],
        "removal",
    );
    assert!(!selected.exists());
    assert_eq!(fs::read(&other).unwrap(), b"unselected artifact");
    assert_eq!(
        summary(&dry, "Summary"),
        summary(&actual, "Removed"),
        "world={}",
        world.display()
    );
    assert_eq!(summary(&actual, "Removed"), "1 file, 1.0KiB total");
}

#[cfg(unix)]
#[test]
fn two_selected_hardlinks_count_once_before_and_after_unlink() {
    use std::os::unix::fs::MetadataExt as _;

    let world = retained_world();
    let selected = world.join("target/debug/build/clean_native_subject/unit/out/one");
    let alias = selected.with_file_name("two");
    let other = world.join("target/debug/build/other_package/unit/out/other");
    fs::create_dir_all(selected.parent().unwrap()).unwrap();
    fs::create_dir_all(other.parent().unwrap()).unwrap();
    fs::write(&selected, vec![b'h'; 1024]).unwrap();
    fs::hard_link(&selected, &alias).unwrap();
    fs::write(&other, b"unselected artifact").unwrap();
    let first = fs::metadata(&selected).unwrap();
    let second = fs::metadata(&alias).unwrap();
    fs::write(world.join("hardlink-before.json"), serde_json::to_vec_pretty(&serde_json::json!({
        "first":{"dev":first.dev(),"ino":first.ino(),"nlink":first.nlink(),"len":first.len()},
        "second":{"dev":second.dev(),"ino":second.ino(),"nlink":second.nlink(),"len":second.len()}
    })).unwrap()).unwrap();
    assert_eq!((first.dev(), first.ino()), (second.dev(), second.ino()));
    assert_eq!((first.nlink(), second.nlink(), first.len()), (2, 2, 1024));
    let dry = command(
        &world,
        &[
            "clean",
            "--locked",
            "--offline",
            "-Zbuild-dir-new-layout",
            "-p",
            "clean_native_subject",
            "--dry-run",
        ],
        "hardlink-dry-run",
    );
    assert_eq!(fs::read(&selected).unwrap(), vec![b'h'; 1024]);
    assert_eq!(fs::read(&alias).unwrap(), vec![b'h'; 1024]);
    assert_eq!(fs::read(&other).unwrap(), b"unselected artifact");
    let actual = command(
        &world,
        &[
            "clean",
            "--locked",
            "--offline",
            "-Zbuild-dir-new-layout",
            "-p",
            "clean_native_subject",
        ],
        "hardlink-removal",
    );
    assert!(!selected.exists());
    assert!(!alias.exists());
    assert_eq!(fs::read(&other).unwrap(), b"unselected artifact");
    assert_eq!(summary(&dry, "Summary"), "2 files, 1.0KiB total");
    assert_eq!(
        summary(&dry, "Summary"),
        summary(&actual, "Removed"),
        "world={}",
        world.display()
    );
}
