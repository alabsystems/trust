//! Actual filesystem aliases, never an inferred case/Unicode normalization rule.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use super::*;
use std::io::Write as _;
use std::os::unix::fs::{MetadataExt as _, symlink};

fn identity(path: &Path) -> (u64, u64) {
    let metadata = fs::symlink_metadata(path).unwrap();
    (metadata.dev(), metadata.ino())
}

fn locks(build: &Path, artifacts: &Path) -> Vec<(PathBuf, (u64, u64))> {
    [
        build.join(".cargo-build-lock"),
        artifacts.join(".cargo-lock"),
        artifacts.join(".cargo-artifact-lock"),
    ]
    .into_iter()
    .map(|path| {
        let metadata = fs::symlink_metadata(&path).unwrap();
        assert!(metadata.is_file() && !metadata.is_symlink());
        let id = identity(&path);
        (path, id)
    })
    .collect()
}

fn same_locks(originals: &[(PathBuf, (u64, u64))]) {
    for (path, expected) in originals {
        assert_eq!(
            identity(path),
            *expected,
            "original lock: {}",
            path.display()
        );
    }
}

pub(super) fn package_directories() {
    let mut aliased = 0;
    let mut distinct = 0;
    for names in [
        ["cache_alias", "CACHE_ALIAS"],
        ["caf\u{e9}_cache", "cafe\u{301}_cache"],
    ] {
        // Distinct source directories and explicit ASCII bin names let both
        // genuine packages compile without final-output filename collisions.
        let world = world_with_package_names(false, names);
        let lock: toml::Value =
            toml::from_str(&fs::read_to_string(world.join("Cargo.lock")).unwrap()).unwrap();
        for (package, name) in ["selected", "protected"].into_iter().zip(names) {
            let manifest: toml::Value = toml::from_str(
                &fs::read_to_string(world.join(package).join("Cargo.toml")).unwrap(),
            )
            .unwrap();
            assert_eq!(manifest["package"]["name"].as_str(), Some(name));
            assert!(
                lock["package"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|row| row["name"].as_str() == Some(name))
            );
        }
        let target = world.join("target");
        let profile = target.join("debug");
        let selected = profile.join("build").join(names[0]);
        let protected = profile.join("build").join(names[1]);
        assert!(selected.is_dir() && protected.is_dir());
        let aliases = identity(&selected) == identity(&protected);
        let originals = locks(&profile, &profile);
        let before = snapshot(&target, None);
        fs::write(
            world.join("physical-package-alias.txt"),
            format!("names={names:?}\nphysical_alias={aliases}\nlocks={originals:?}\n"),
        )
        .unwrap();
        writeln!(
            std::io::stderr(),
            "CLEAN_PHYSICAL_PACKAGE_WORLD={} aliases={aliases}",
            world.display()
        )
        .unwrap();
        let output = recorded(
            command(&world)
                .env("RUSTC", world.join("compiler-must-not-start"))
                .args(["clean", "--intermediates-only", "-p", names[0]]),
            &world,
            "physical-package-alias",
        );
        if aliases {
            assert!(!output.status.success(), "world={}", world.display());
            assert_eq!(snapshot(&target, None), before, "world={}", world.display());
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("alias one physical directory")
            );
            assert!(selected.is_dir() && protected.is_dir());
            aliased += 1;
        } else {
            success(&output, &world);
            let selected = selected.strip_prefix(&target).unwrap();
            let expected = before
                .into_iter()
                .filter(|(path, _)| !path.starts_with(selected))
                .collect::<BTreeMap<_, _>>();
            assert_eq!(snapshot(&target, None), expected);
            assert!(!target.join(selected).exists() && protected.is_dir());
            distinct += 1;
        }
        same_locks(&originals);
        for binary in ["selected", "protected"] {
            let output = Command::new(profile.join(binary)).output().unwrap();
            success(&output, &world);
            assert_eq!(output.stdout, b"42\n");
        }
    }
    assert_eq!(aliased + distinct, 2);
    writeln!(
        std::io::stderr(),
        "CLEAN_PHYSICAL_PACKAGE_WORLDS aliased={aliased} distinct={distinct}"
    )
    .unwrap();
}

pub(super) fn terminal_symlink() {
    let world = world(false);
    let target = world.join("target");
    let profile = target.join("debug");
    let selected = profile.join("build/selected");
    fs::remove_dir_all(&selected).unwrap();
    symlink(&target, &selected).unwrap();
    let originals = locks(&profile, &profile);
    let before = snapshot(&target, Some(&selected));
    let output = recorded(
        command(&world).args(["clean", "--intermediates-only", "-p", "selected"]),
        &world,
        "terminal-symlink",
    );
    success(&output, &world);
    assert!(fs::symlink_metadata(&selected).is_err());
    assert_eq!(snapshot(&target, None), before);
    same_locks(&originals);
    writeln!(
        std::io::stderr(),
        "CLEAN_TERMINAL_SYMLINK_WORLDS=1 world={}",
        world.display()
    )
    .unwrap();
}

pub(super) fn nested_output() {
    let world = world(true);
    let probe = world.join("CaseAliasProbe");
    fs::create_dir(&probe).unwrap();
    let alternate = world.join("casealiasprobe");
    if fs::symlink_metadata(&alternate).is_err() || identity(&probe) != identity(&alternate) {
        writeln!(
            std::io::stderr(),
            "CLEAN_NESTED_PHYSICAL_ALIAS_WORLDS=0 filesystem_distinct=1"
        )
        .unwrap();
        return;
    }
    let build = world.join("build-data");
    let selected = build.join("debug/build/selected");
    let nested = selected.join("final-artifacts");
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
            "physical-nested-build",
        ),
        &world,
    );
    // Two-step renames establish the stored spellings even on filesystems
    // where a direct case-only rename is treated as renaming an entry to itself.
    let temporary = build.join("debug/build/renamed-selected");
    fs::rename(&selected, &temporary).unwrap();
    fs::rename(&temporary, build.join("debug/build/SELECTED")).unwrap();
    let temporary = build.join("renamed-profile");
    fs::rename(build.join("debug"), &temporary).unwrap();
    fs::rename(&temporary, build.join("DEBUG")).unwrap();
    let nested = build
        .join("DEBUG/build/SELECTED/final-artifacts")
        .canonicalize()
        .unwrap();
    assert_eq!(
        identity(&build.join("debug/build/selected")),
        identity(&build.join("DEBUG/build/SELECTED"))
    );
    let originals = locks(&build.join("DEBUG"), &nested.join("debug"));
    let before = snapshot(&build, None);
    fs::write(
        world.join("physical-nested-alias.txt"),
        format!("target={nested:?}\nlocks={originals:?}\n"),
    )
    .unwrap();
    let output = recorded(
        command(&world)
            .env("CARGO_TARGET_DIR", &nested)
            .env("RUSTC", world.join("compiler-must-not-start"))
            .args(["clean", "--intermediates-only", "-p", "selected"]),
        &world,
        "physical-nested-refusal",
    );
    assert!(!output.status.success(), "world={}", world.display());
    assert_eq!(snapshot(&build, None), before, "world={}", world.display());
    assert!(String::from_utf8_lossy(&output.stderr).contains("protected output root"));
    same_locks(&originals);
    for binary in ["selected", "protected"] {
        let output = Command::new(nested.join("debug").join(binary))
            .output()
            .unwrap();
        success(&output, &world);
        assert_eq!(output.stdout, b"42\n");
    }
    writeln!(
        std::io::stderr(),
        "CLEAN_NESTED_PHYSICAL_ALIAS_WORLDS=1 world={}",
        world.display()
    )
    .unwrap();
}
