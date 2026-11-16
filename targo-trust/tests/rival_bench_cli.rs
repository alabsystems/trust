//! `targo trust benchmark rival` (docs/PLAN.md PKG-LIVE-11) against fake
//! tools: an honest pair passes `--check` and writes the report; a rival that
//! serves a stale program, a rival that prints a different value, and a
//! missing rival each fail it; a worker a rival leaves running is measured
//! and then stopped; an `--out` this command did not make is refused.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }
    let mut path = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.join(format!("targo-trust{}", std::env::consts::EXE_SUFFIX))
}

/// A fake tool. Its last argument is the lane; `run` prints `run_body`'s
/// output, computed in the generated crate's directory.
fn fake(dir: &Path, name: &str, run_body: &str) -> PathBuf {
    fake_with(dir, name, "", run_body)
}

/// A fake tool that runs `every` before each lane command.
fn fake_with(dir: &Path, name: &str, every: &str, run_body: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(
        &path,
        format!(
            "#!/bin/sh\n\
             PATH=/usr/bin:/bin\n\
             for lane; do :; done\n\
             case \"$lane\" in --version) ;; *) {every} ;; esac\n\
             case \"$lane\" in\n\
             \x20 --version) echo \"{name} 1.0\" ;;\n\
             \x20 check|build) test -f Cargo.toml || exit 9 ;;\n\
             \x20 run) test -f Cargo.toml || exit 9; {run_body} ;;\n\
             \x20 *) exit 8 ;;\n\
             esac\n"
        ),
    )
    .unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    path
}

const HONEST: &str = "cat src/*.rs | cksum | cut -d' ' -f1";

fn rival(dir: &Path, trust: &Path, blaze: Option<&Path>, extra: &[&str]) -> Output {
    let mut command = Command::new(targo_trust_binary());
    command
        .current_dir(dir)
        .env("PATH", dir.join("empty"))
        .args([
            "trust",
            "benchmark",
            "rival",
            "--out",
            "out",
            "--subject",
            "tiny=3x2",
            "--edits",
            "2",
        ])
        .arg("--trust")
        .arg(trust);
    if let Some(blaze) = blaze {
        command.arg("--blaze").arg(blaze);
    }
    command.args(extra).output().expect("run targo-trust")
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn an_honest_pair_passes_check_and_writes_the_report() {
    let dir = tempfile::tempdir().unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    let blaze = fake(dir.path(), "blaze", HONEST);
    let output = rival(dir.path(), &trust, Some(&blaze), &["--check"]);
    assert!(output.status.success(), "{}", stderr(&output));
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Nine timed axes, then resident-mb, disk-mb and runs.
    assert!(stdout.contains("of 12 rows at least as good as blaze (12 judged"), "{stdout}");
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(dir.path().join("out/rival.json")).unwrap()).unwrap();
    assert_eq!(report["schema"], "trust.benchmark.rival.v1");
    assert_eq!(report["rows"].as_array().unwrap().len(), 12);
    let row = |axis: &str| {
        report["rows"].as_array().unwrap().iter().find(|row| row["axis"] == axis).unwrap().clone()
    };
    assert_eq!(row("runs")["trust"], 1.0);
    assert_eq!(row("resident-mb")["blaze"], 0.0);
    assert!(row("disk-mb")["trust"].as_f64().is_some());
    assert_eq!(report["problems"].as_array().unwrap().len(), 0);
    // Each tool and lane: cold, no-op, two edits.
    assert_eq!(report["samples"].as_array().unwrap().len(), 2 * 3 * 4);
    assert_eq!(report["tools"][1]["version"], "blaze 1.0");

    // The directory is this command's own, so a second run may reuse it.
    let again = rival(dir.path(), &trust, Some(&blaze), &["--axis", "edit-run", "--check"]);
    assert!(again.status.success(), "{}", stderr(&again));
}

#[test]
fn a_rival_serving_a_stale_program_fails_check() {
    let dir = tempfile::tempdir().unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    let blaze = fake(dir.path(), "blaze", "echo 42");
    let output = rival(dir.path(), &trust, Some(&blaze), &["--axis", "edit-run", "--check"]);
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let err = stderr(&output);
    assert!(
        err.contains("blaze: edit 1 did not change the printed value (stale program)"),
        "{err}"
    );
    assert!(err.contains("printed"), "{err}");

    // Without --check the same run reports and succeeds.
    let output = rival(dir.path(), &trust, Some(&blaze), &["--axis", "edit-run"]);
    assert!(output.status.success(), "{}", stderr(&output));
}

#[test]
fn a_rival_printing_another_value_fails_check() {
    let dir = tempfile::tempdir().unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    let blaze = fake(dir.path(), "blaze", &format!("{HONEST} | sed 's/$/0/'"));
    let output =
        rival(dir.path(), &trust, Some(&blaze), &["--axis", "noop-run,edit-run", "--check"]);
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(stderr(&output).contains("tiny run #2: trust printed"), "{}", stderr(&output));
}

#[test]
fn a_missing_or_failing_rival_fails_check() {
    let dir = tempfile::tempdir().unwrap();
    fs::create_dir(dir.path().join("empty")).unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    let output = rival(dir.path(), &trust, None, &["--axis", "edit-build", "--check"]);
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    let err = stderr(&output);
    assert!(err.contains("no blaze executable (pass --blaze <PATH>)"), "{err}");
    assert!(err.contains("tiny edit-build: no blaze row"), "{err}");

    let broken = dir.path().join("broken");
    fs::write(&broken, "#!/bin/sh\nexit 3\n").unwrap();
    fs::set_permissions(&broken, fs::Permissions::from_mode(0o755)).unwrap();
    let output = rival(dir.path(), &trust, Some(&broken), &["--axis", "edit-build", "--check"]);
    assert_eq!(output.status.code(), Some(1), "{}", stderr(&output));
    assert!(
        stderr(&output).contains("tiny blaze cold-build #0: exit status: 3"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn an_out_directory_it_did_not_make_is_refused() {
    let dir = tempfile::tempdir().unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    let blaze = fake(dir.path(), "blaze", HONEST);
    fs::create_dir(dir.path().join("out")).unwrap();
    fs::write(dir.path().join("out/keep.txt"), "someone else's").unwrap();
    let output = rival(dir.path(), &trust, Some(&blaze), &[]);
    assert_eq!(output.status.code(), Some(2), "{}", stderr(&output));
    assert!(stderr(&output).contains("was not made by this command"), "{}", stderr(&output));
    assert_eq!(fs::read_to_string(dir.path().join("out/keep.txt")).unwrap(), "someone else's");
}

/// Not a test of its own: the worker the fake rival below leaves running.
#[test]
#[ignore = "started by a_resident_worker_is_measured_and_then_stopped"]
fn resident_holder() {
    if std::env::var_os("RIVAL_TEST_HOLD").is_some() {
        std::thread::sleep(std::time::Duration::from_secs(300));
    }
}

#[test]
fn a_resident_worker_is_measured_and_then_stopped() {
    let dir = tempfile::tempdir().unwrap();
    let holder = std::env::current_exe().unwrap();
    let trust = fake(dir.path(), "trust", HONEST);
    // The first command in each crate starts one worker; it outlives the command.
    let start = format!(
        "[ -f .held ] || {{ touch .held; RIVAL_TEST_HOLD=1 '{}' --ignored --exact resident_holder \
         >/dev/null 2>&1 & }}",
        holder.display()
    );
    let blaze = fake_with(dir.path(), "blaze", &start, HONEST);
    let output = rival(dir.path(), &trust, Some(&blaze), &["--axis", "edit-run", "--check"]);
    assert!(output.status.success(), "{}", stderr(&output));
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(dir.path().join("out/rival.json")).unwrap()).unwrap();
    let resident = report["rows"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["axis"] == "resident-mb")
        .unwrap()
        .clone();
    assert!(resident["blaze"].as_f64().unwrap() > 0.0, "{resident}");
    assert_eq!(resident["trust"], 0.0);
    assert_eq!(resident["trust_at_least_as_good"], true);
    let held = report["samples"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|s| s["tool"] == "blaze")
        .all(|s| s["resident_processes"] == 1);
    assert!(held, "{}", report["samples"]);
    // Stopped once the subject was done.
    let ps = Command::new("/bin/ps").args(["-axww", "-o", "command="]).output().unwrap();
    let holder = holder.display().to_string();
    let left = String::from_utf8_lossy(&ps.stdout)
        .lines()
        .filter(|line| line.contains(&holder) && line.contains("resident_holder"))
        .count();
    assert_eq!(left, 0);
}
