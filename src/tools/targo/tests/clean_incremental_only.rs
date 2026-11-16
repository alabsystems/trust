//! Native incremental cleanup preserves the actual compiled outputs it accompanies.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, Instant};

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture binds its original CLI/compiler before configuration"
)]
fn command(world: &Path) -> Command {
    let executable = std::env::var_os("TARGO_CLEAN_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(world)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("CARGO_TERM_COLOR", "never")
        .env("CARGO_INCREMENTAL", "0")
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching original rustdoc"),
        );
    command
}

fn recorded(command: &mut Command, world: &Path, label: &str) -> Output {
    fs::write(
        world.join(format!("{label}.command.json")),
        serde_json::to_vec_pretty(&serde_json::json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg|arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
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
        "world={} status={}\nstdout={}\nstderr={}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Bound the actual owned CLI child, with file-backed output and a positive
/// owning wait after any timeout kill. No numeric group or descendant signals.
fn bounded(command: &mut Command, world: &Path, label: &str) -> Output {
    command
        .stdout(fs::File::create(world.join(format!("{label}.stdout"))).unwrap())
        .stderr(fs::File::create(world.join(format!("{label}.stderr"))).unwrap());
    fs::write(
        world.join(format!("{label}.command.json")),
        serde_json::to_vec_pretty(&serde_json::json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg|arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
    let start = Instant::now();
    let mut child = command.spawn().unwrap();
    let original_pid = child.id();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break (status, false);
        }
        if start.elapsed() >= Duration::from_secs(10) {
            // try_wait just observed our original child unreaped. It remains
            // pinned until this owning wait, even if it exits before kill.
            let killed = child.kill();
            let status = child.wait().unwrap();
            killed.unwrap();
            break (status, true);
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    fs::write(world.join(format!("{label}.status")), status.to_string()).unwrap();
    fs::write(
        world.join(format!("{label}.wait.json")),
        serde_json::to_vec_pretty(&serde_json::json!({
            "original_child":original_pid,
            "timed_out":timed_out,
            "owning_wait_complete":true,
            "elapsed_ms":start.elapsed().as_millis(),
        }))
        .unwrap(),
    )
    .unwrap();
    Output {
        status,
        stdout: fs::read(world.join(format!("{label}.stdout"))).unwrap(),
        stderr: fs::read(world.join(format!("{label}.stderr"))).unwrap(),
    }
}

fn world(split: bool) -> PathBuf {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-clean-incremental-only.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix(if split { "split" } else { "ordinary" })
        .tempdir_in(base)
        .unwrap()
        .keep();
    fs::create_dir_all(world.join("src")).unwrap();
    fs::write(world.join("Cargo.toml"), "[package]\nname='incremental_clean_subject'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=true\n[profile.release]\ndebug=0\nincremental=true\n[profile.selected]\ninherits='dev'\n").unwrap();
    fs::write(world.join("src/lib.rs"), "pub fn value()->u32 {42}\n").unwrap();
    fs::write(
        world.join("src/main.rs"),
        "fn main(){println!(\"{}\",incremental_clean_subject::value());}\n",
    )
    .unwrap();
    if split {
        fs::create_dir_all(world.join(".cargo")).unwrap();
        fs::write(
            world.join(".cargo/config.toml"),
            format!("[build]\nbuild-dir={:?}\n", world.join("build-data")),
        )
        .unwrap();
    }
    let output = recorded(
        command(&world).args(["generate-lockfile", "--offline"]),
        &world,
        "lockfile",
    );
    success(&output, &world);
    world
}

fn cache(root: &Path, profile: &str, contents: &[u8]) -> PathBuf {
    let path = root.join(profile).join("incremental/owned-marker");
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(&path, contents).unwrap();
    path
}

fn tag(root: &Path) {
    fs::write(
        root.join("CACHEDIR.TAG"),
        "Signature: 8a477f597d28d172789f06886806bc55\n",
    )
    .unwrap();
}

#[derive(Debug, PartialEq, Eq)]
enum Entry {
    File(Vec<u8>),
    Link(PathBuf),
}

fn snapshot(root: &Path, omit_incremental: bool) -> BTreeMap<PathBuf, Entry> {
    walkdir::WalkDir::new(root)
        .follow_root_links(false)
        .into_iter()
        .filter_entry(|entry| !omit_incremental || entry.path() != root.join("incremental"))
        .map(Result::unwrap)
        .filter_map(|entry| {
            let relative = entry.path().strip_prefix(root).unwrap().to_owned();
            if entry.file_type().is_symlink() {
                Some((relative, Entry::Link(fs::read_link(entry.path()).unwrap())))
            } else if entry.file_type().is_file() {
                Some((relative, Entry::File(fs::read(entry.path()).unwrap())))
            } else {
                None
            }
        })
        .collect()
}

fn summary(output: &Output, status: &str) -> String {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .find_map(|line| line.trim().strip_prefix(status))
        .unwrap_or_else(|| panic!("missing {status}: {:?}", output))
        .trim()
        .to_owned()
}

#[test]
fn actual_incremental_builds_keep_outputs_and_other_profiles_in_both_layouts() {
    for split in [false, true] {
        let world = world(split);
        let target = world.join("target");
        let build = if split {
            world.join("build-data")
        } else {
            target.clone()
        };
        for (label, extra) in [("dev", None), ("release", Some("--release"))] {
            let mut build_command = command(&world);
            build_command.env("CARGO_INCREMENTAL", "1").args([
                "--unverified",
                "build",
                "--locked",
                "--offline",
                "--jobs=1",
            ]);
            if let Some(extra) = extra {
                build_command.arg(extra);
            }
            let output = recorded(&mut build_command, &world, &format!("build-{label}"));
            success(&output, &world);
        }
        let incremental = build.join("debug/incremental");
        assert!(
            !snapshot(&incremental, false).is_empty(),
            "world={}",
            world.display()
        );
        let binary = target.join("debug").join(format!(
            "incremental_clean_subject{}",
            std::env::consts::EXE_SUFFIX
        ));
        assert!(binary.is_file());
        assert!(
            target
                .join("debug/libincremental_clean_subject.rlib")
                .is_file()
        );
        let artifacts = snapshot(&target.join("debug"), true);
        let intermediates = snapshot(&build.join("debug"), true);
        assert!(
            intermediates
                .keys()
                .any(|path| path
                    .components()
                    .any(|part| part.as_os_str() == "fingerprint"
                        || part.as_os_str() == ".fingerprint"))
        );
        let release = snapshot(&build.join("release"), false);
        assert!(!snapshot(&build.join("release/incremental"), false).is_empty());
        let before = snapshot(&incremental, false);
        let dry = recorded(
            command(&world).args(["clean", "--incremental-only", "--dry-run"]),
            &world,
            "dry-dev",
        );
        success(&dry, &world);
        assert_eq!(snapshot(&incremental, false), before);
        let actual = recorded(
            command(&world).args(["clean", "--incremental-only"]),
            &world,
            "remove-dev",
        );
        success(&actual, &world);
        assert!(!incremental.exists());
        assert_eq!(snapshot(&target.join("debug"), true), artifacts);
        assert_eq!(snapshot(&build.join("debug"), true), intermediates);
        assert_eq!(snapshot(&build.join("release"), false), release);
        assert_eq!(summary(&dry, "Summary"), summary(&actual, "Removed"));
        let ran = recorded(
            Command::new(&binary).current_dir(&world),
            &world,
            "run-retained-binary",
        );
        success(&ran, &world);
        assert_eq!(ran.stdout, b"42\n");
        let release_outputs = snapshot(&build.join("release"), true);
        let removed = recorded(
            command(&world).args(["clean", "--incremental-only", "--release"]),
            &world,
            "remove-release",
        );
        success(&removed, &world);
        assert!(!build.join("release/incremental").exists());
        assert_eq!(snapshot(&build.join("release"), true), release_outputs);
    }
}

#[test]
fn profile_and_target_selection_leave_unselected_caches() {
    let world = world(false);
    let target = world.join("target");
    let dev = cache(&target, "debug", b"unselected dev");
    let selected = cache(&target, "selected", b"selected profile");
    tag(&target);
    let output = recorded(
        command(&world).args(["clean", "--incremental-only", "--profile=selected"]),
        &world,
        "selected-profile",
    );
    success(&output, &world);
    assert!(!selected.exists());
    assert_eq!(fs::read(&dev).unwrap(), b"unselected dev");
    // Only synthetic owned cache DATA occupies this foreign selector. No
    // foreign compilation, target std or SDK eligibility is asserted.
    let foreign = "wasm32-unknown-unknown";
    let selected = cache(&target.join(foreign), "debug", b"selected target DATA");
    let output = recorded(
        command(&world).args(["clean", "--incremental-only", "--target", foreign]),
        &world,
        "selected-target",
    );
    success(&output, &world);
    assert!(!selected.exists());
    assert_eq!(fs::read(dev).unwrap(), b"unselected dev");
}

#[test]
fn invalid_tags_and_conflicting_selections_leave_the_cache_unchanged() {
    let world = world(false);
    let target = world.join("target");
    cache(&target, "debug", b"preserve");
    fs::write(target.join("CACHEDIR.TAG"), b"invalid tag").unwrap();
    let before = snapshot(&target, false);
    let output = recorded(
        command(&world).args(["clean", "--incremental-only"]),
        &world,
        "invalid-tag",
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("CACHEDIR.TAG"));
    assert_eq!(snapshot(&target, false), before);
    tag(&target);
    let before = snapshot(&target, false);
    for (label, arguments) in [
        ("doc", vec!["--doc"]),
        ("package", vec!["--package", "incremental_clean_subject"]),
        ("workspace", vec!["--workspace"]),
    ] {
        let output = recorded(
            command(&world)
                .args(["clean", "--incremental-only"])
                .args(arguments),
            &world,
            &format!("conflict-{label}"),
        );
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("cannot be used with"));
        assert_eq!(snapshot(&target, false), before);
    }
}

#[cfg(unix)]
#[test]
fn intermediate_symlink_refuses_but_terminal_incremental_link_is_only_unlinked() {
    use std::os::unix::fs::symlink;
    let world = world(false);
    let target = world.join("target");
    let victim = world.join("unselected-victim");
    cache(&victim, "debug", b"victim cache");
    fs::create_dir(&target).unwrap();
    tag(&target);
    symlink(victim.join("debug"), target.join("debug")).unwrap();
    let before = snapshot(&victim, false);
    let target_before = snapshot(&target, false);
    let output = recorded(
        command(&world).args(["clean", "--incremental-only"]),
        &world,
        "intermediate-alias",
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("symlink"));
    assert_eq!(snapshot(&victim, false), before);
    assert_eq!(snapshot(&target, false), target_before);
    fs::remove_file(target.join("debug")).unwrap();
    fs::create_dir(target.join("debug")).unwrap();
    symlink(
        victim.join("debug/incremental"),
        target.join("debug/incremental"),
    )
    .unwrap();
    let dry = recorded(
        command(&world).args(["clean", "--incremental-only", "--dry-run"]),
        &world,
        "terminal-dry",
    );
    success(&dry, &world);
    assert!(
        fs::symlink_metadata(target.join("debug/incremental"))
            .unwrap()
            .is_symlink()
    );
    assert_eq!(snapshot(&victim, false), before);
    let output = recorded(
        command(&world).args(["clean", "--incremental-only"]),
        &world,
        "terminal-remove",
    );
    success(&output, &world);
    assert!(fs::symlink_metadata(target.join("debug/incremental")).is_err());
    assert_eq!(snapshot(&victim, false), before);
    assert_eq!(summary(&dry, "Summary"), summary(&output, "Removed"));

    // A later invalid selection must refuse before deleting an earlier valid
    // selection. Both namespaces contain only this fixture's foreign cache DATA.
    let first = "wasm32-unknown-unknown";
    let second = "thumbv7em-none-eabi";
    let first_marker = cache(&target.join(first), "debug", b"earlier valid selection");
    fs::create_dir_all(target.join(second)).unwrap();
    symlink(victim.join("debug"), target.join(second).join("debug")).unwrap();
    let selected_before = snapshot(&target, false);
    let refused = recorded(
        command(&world).args([
            "clean",
            "--incremental-only",
            "--target",
            first,
            "--target",
            second,
        ]),
        &world,
        "later-invalid-selection",
    );
    assert!(!refused.status.success());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("symlink"));
    assert_eq!(snapshot(&target, false), selected_before);
    assert_eq!(fs::read(first_marker).unwrap(), b"earlier valid selection");
    assert_eq!(snapshot(&victim, false), before);
}

#[cfg(unix)]
#[test]
fn aliased_target_leases_finish_without_blocking_their_own_cli() {
    use std::os::unix::fs::MetadataExt as _;
    for split in [false, true] {
        let world = world(split);
        let target = world.join("target");
        let build = if split {
            world.join("build-data")
        } else {
            target.clone()
        };
        let first = "wasm32-unknown-unknown";
        let second = if split {
            "thumbv7em-none-eabi"
        } else {
            "WASM32-UNKNOWN-UNKNOWN"
        };
        let selected = cache(&build.join(first), "debug", b"first selected cache DATA");
        let case_alias = selected.parent().unwrap() == build.join(second).join("debug/incremental")
            || fs::metadata(build.join(second).join("debug/incremental")).is_ok();
        let other = build.join(second).join("debug/incremental/owned-marker");
        if !other.exists() {
            cache(&build.join(second), "debug", b"second selected cache DATA");
        }
        let unselected = cache(&build, "debug", b"unselected native cache DATA");
        fs::create_dir_all(&target).unwrap();
        tag(&target);
        tag(&build);
        let (one_lock, two_lock) = if split {
            // Distinct build parents still share an actual artifact lease.
            // Build-directory inode dedup alone cannot prevent this deadlock.
            for triple in [first, second] {
                fs::create_dir_all(target.join(triple).join("debug")).unwrap();
            }
            (
                target.join(first).join("debug/.cargo-artifact-lock"),
                target.join(second).join("debug/.cargo-artifact-lock"),
            )
        } else {
            (
                build.join(first).join("debug/.cargo-build-lock"),
                build.join(second).join("debug/.cargo-build-lock"),
            )
        };
        fs::write(&one_lock, b"").unwrap();
        if !two_lock.exists() {
            // A case-sensitive filesystem exercises the same actual physical
            // lease alias through owned DATA hardlinks instead of skipping.
            fs::hard_link(&one_lock, &two_lock).unwrap();
        }
        let one = fs::metadata(&one_lock).unwrap();
        let two = fs::metadata(&two_lock).unwrap();
        assert_eq!((one.dev(), one.ino()), (two.dev(), two.ino()));
        fs::write(world.join("physical-lease-alias.json"), serde_json::to_vec_pretty(&serde_json::json!({
            "split":split,"case_alias":case_alias,
            "one":{"dev":one.dev(),"ino":one.ino()},
            "two":{"dev":two.dev(),"ino":two.ino()},
            "source_scope":"synthetic owned foreign cache and lock DATA; no foreign compilation",
        })).unwrap()).unwrap();
        let before = fs::read(&selected).unwrap();
        let other_before = fs::read(&other).unwrap();
        let dry = bounded(
            command(&world).args([
                "clean",
                "--incremental-only",
                "--target",
                first,
                "--target",
                second,
                "--dry-run",
            ]),
            &world,
            "aliased-dry",
        );
        success(&dry, &world);
        assert_eq!(fs::read(&selected).unwrap(), before);
        assert_eq!(fs::read(&other).unwrap(), other_before);
        let actual = bounded(
            command(&world).args([
                "clean",
                "--incremental-only",
                "--target",
                first,
                "--target",
                second,
            ]),
            &world,
            "aliased-remove",
        );
        success(&actual, &world);
        assert!(!selected.exists() && !other.exists());
        assert_eq!(
            fs::read(unselected).unwrap(),
            b"unselected native cache DATA"
        );
        assert_eq!(summary(&dry, "Summary"), summary(&actual, "Removed"));
    }
}
