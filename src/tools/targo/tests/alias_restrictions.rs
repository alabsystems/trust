//! Intermediate aliases must retain explicit restrictions and shell options.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

use serde_json::json;

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated metadata fixture selects only its original CLI/compiler tools and PATH before project configuration exists"
)]
fn command(project: &Path, world: &Path) -> Command {
    let executable = std::env::var_os("TARGO_ALIAS_RESTRICTION_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(project)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching original rustdoc"),
        );
    command
}

fn record(command: &mut Command, evidence: &Path) -> Output {
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
    let output = command.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    fs::write(
        evidence.join("status.json"),
        serde_json::to_vec_pretty(&json!({
            "success":output.status.success(), "code":output.status.code(),
            "display":output.status.to_string(),
        }))
        .unwrap(),
    )
    .unwrap();
    output
}

fn lockfile(project: &Path) -> Option<Vec<u8>> {
    match fs::read(project.join("Cargo.lock")) {
        Ok(bytes) => Some(bytes),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => panic!("cannot inspect fixture lockfile: {error}"),
    }
}

#[test]
fn nested_locked_alias_cannot_create_a_lockfile() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-alias-restrictions.noindex");
    fs::create_dir_all(&base).unwrap();
    // Keep both metadata-only outcomes, including a baseline's forbidden write.
    let world = tempfile::Builder::new()
        .prefix("locked")
        .tempdir_in(base)
        .unwrap()
        .keep();
    for label in ["direct", "nested"] {
        let project = world.join(label);
        fs::create_dir_all(project.join("src")).unwrap();
        fs::create_dir_all(project.join(".cargo")).unwrap();
        fs::create_dir_all(world.join("evidence").join(label)).unwrap();
        fs::write(project.join("Cargo.toml"), "[package]\nname='alias_restriction_sample'\nversion='0.0.0'\nedition='2021'\n[workspace]\n").unwrap();
        fs::write(project.join("src/lib.rs"), "pub fn value() -> u32 { 1 }\n").unwrap();
        fs::write(
            project.join(".cargo/config.toml"),
            "[alias]\nouter=['--locked','inner']\ninner=['generate-lockfile','--offline']\n",
        )
        .unwrap();
    }
    let direct = world.join("direct");
    let nested = world.join("nested");
    let before = [lockfile(&direct), lockfile(&nested)];
    let direct_output = record(
        command(&direct, &world).args(["--locked", "generate-lockfile", "--offline"]),
        &world.join("evidence/direct"),
    );
    let nested_output = record(
        command(&nested, &world).arg("outer"),
        &world.join("evidence/nested"),
    );
    let after = [lockfile(&direct), lockfile(&nested)];
    let observed = json!({
        "lockfiles_before":before, "lockfiles_after":after,
        "direct_success":direct_output.status.success(),
        "nested_success":nested_output.status.success(),
    });
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    assert!(
        before.iter().all(Option::is_none),
        "world={} {observed}",
        world.display()
    );
    for (label, output, lockfile) in [
        ("direct", &direct_output, &after[0]),
        ("nested", &nested_output, &after[1]),
    ] {
        assert!(
            !output.status.success(),
            "{label} discarded --locked: world={} {observed}",
            world.display()
        );
        assert!(
            lockfile.is_none(),
            "{label} created a forbidden lockfile: world={} {observed}",
            world.display()
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("cannot create the lock file")
                && stderr.contains("because --locked was passed to prevent this"),
            "{label}: world={} stderr={stderr}",
            world.display()
        );
    }
}

fn scalar_world(prefix: &str, configuration: &str, labels: &[&str]) -> (PathBuf, PathBuf) {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-alias-restrictions.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix(prefix)
        .tempdir_in(base)
        .unwrap()
        .keep();
    let project = world.join("project");
    fs::create_dir_all(project.join("src")).unwrap();
    fs::create_dir_all(project.join(".cargo")).unwrap();
    for label in labels {
        fs::create_dir_all(world.join("evidence").join(label)).unwrap();
    }
    fs::write(
        project.join("Cargo.toml"),
        "[package]\nname='alias_scalar_sample'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(project.join("src/lib.rs"), "pub fn value() -> u32 { 1 }\n").unwrap();
    fs::write(project.join(".cargo/config.toml"), configuration).unwrap();
    (world, project)
}

fn scalar_conflict(caller: &str, middle: &str, prefix: &str) {
    let configuration = format!(
        "[alias]\nscalar-flat=[\"{middle}\",'locate-project','--message-format=plain']\nscalar-outer=[\"{middle}\",'scalar-inner']\nscalar-inner=['locate-project','--message-format=plain']\n"
    );
    let (world, project) = scalar_world(prefix, &configuration, &["direct", "flat", "nested"]);
    let direct = record(
        command(&project, &world).args([
            caller,
            middle,
            "locate-project",
            "--message-format=plain",
        ]),
        &world.join("evidence/direct"),
    );
    let flat = record(
        command(&project, &world).args([caller, "scalar-flat"]),
        &world.join("evidence/flat"),
    );
    let nested = record(
        command(&project, &world).args([caller, "scalar-outer"]),
        &world.join("evidence/nested"),
    );
    let observed = json!({
        "caller":caller,"middle":middle,
        "success":[direct.status.success(),flat.status.success(),nested.status.success()],
        "stdout":[direct.stdout,flat.stdout,nested.stdout],
        "lockfile":lockfile(&project),"target_created":world.join("target").exists(),
    });
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    for (label, output) in [("direct", &direct), ("flat", &flat), ("nested", &nested)] {
        assert!(
            !output.status.success(),
            "{label} lost scalar conflict: world={} {observed}",
            world.display()
        );
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("cannot set both --verbose and --quiet"),
            "{label}: world={} stderr={}",
            world.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            output.stdout.is_empty(),
            "{label}: world={} {observed}",
            world.display()
        );
    }
    assert!(
        lockfile(&project).is_none() && !world.join("target").exists(),
        "world={} {observed}",
        world.display()
    );
}

#[test]
fn nested_quiet_alias_preserves_explicit_verbose_conflict() {
    scalar_conflict("--verbose", "--quiet", "quiet-conflict");
}

#[test]
fn nested_verbose_alias_preserves_explicit_quiet_conflict() {
    scalar_conflict("--quiet", "--verbose", "verbose-conflict");
}

#[test]
fn nested_color_alias_overrides_invalid_term_configuration() {
    let configuration = "[term]\ncolor='invalid-color-for-test'\n[alias]\nscalar-flat=['--color=never','locate-project','--message-format=plain']\nscalar-outer=['--color=never','scalar-inner']\nscalar-inner=['locate-project','--message-format=plain']\n";
    let (world, project) = scalar_world(
        "color-override",
        configuration,
        &["invalid", "direct", "flat", "nested"],
    );
    let invalid = record(
        command(&project, &world).args(["locate-project", "--message-format=plain"]),
        &world.join("evidence/invalid"),
    );
    let direct = record(
        command(&project, &world).args([
            "--color=never",
            "locate-project",
            "--message-format=plain",
        ]),
        &world.join("evidence/direct"),
    );
    let flat = record(
        command(&project, &world).arg("scalar-flat"),
        &world.join("evidence/flat"),
    );
    let nested = record(
        command(&project, &world).arg("scalar-outer"),
        &world.join("evidence/nested"),
    );
    let observed = json!({
        "success":[invalid.status.success(),direct.status.success(),flat.status.success(),nested.status.success()],
        "stdout":[invalid.stdout,direct.stdout,flat.stdout,nested.stdout],
        "lockfile":lockfile(&project),"target_created":world.join("target").exists(),
    });
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();
    assert!(
        !invalid.status.success(),
        "invalid config was accepted: world={} {observed}",
        world.display()
    );
    assert!(
        String::from_utf8_lossy(&invalid.stderr)
            .contains("argument for --color must be auto, always, or"),
        "world={} stderr={}",
        world.display(),
        String::from_utf8_lossy(&invalid.stderr)
    );
    let expected = format!("{}\n", project.join("Cargo.toml").display());
    for (label, output) in [("direct", &direct), ("flat", &flat), ("nested", &nested)] {
        assert!(
            output.status.success(),
            "{label} lost explicit color: world={} {observed} stderr={}",
            world.display(),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            output.stdout,
            expected.as_bytes(),
            "{label}: world={} {observed}",
            world.display()
        );
    }
    assert!(
        lockfile(&project).is_none() && !world.join("target").exists(),
        "world={} {observed}",
        world.display()
    );
}

struct BoundedAliasOutput {
    status: Option<ExitStatus>,
    timed_out: bool,
    errors: Vec<String>,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

impl BoundedAliasOutput {
    fn completed(&self) -> bool {
        self.status.is_some() && !self.timed_out && self.errors.is_empty()
    }
}

fn record_bounded_alias(command: &mut Command, evidence: &Path) -> BoundedAliasOutput {
    const TIMEOUT: Duration = Duration::from_secs(60);
    fs::create_dir_all(evidence).unwrap();
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(), "timeout_seconds":TIMEOUT.as_secs(),
        }))
        .unwrap(),
    )
    .unwrap();
    // No pipe reader can keep the test waiting after the owned leader exits.
    command
        .stdin(Stdio::null())
        .stdout(fs::File::create(evidence.join("stdout")).unwrap())
        .stderr(fs::File::create(evidence.join("stderr")).unwrap());
    let started = Instant::now();
    let mut status = None;
    let mut pid = None;
    let mut timed_out = false;
    let mut errors = Vec::new();
    match command.spawn() {
        Err(error) => errors.push(format!("spawn: {error}")),
        Ok(mut child) => {
            pid = Some(child.id());
            loop {
                match child.try_wait() {
                    Ok(Some(terminal)) => {
                        status = Some(terminal);
                        break;
                    }
                    Ok(None) if started.elapsed() < TIMEOUT => {
                        std::thread::sleep(Duration::from_millis(10));
                    }
                    Ok(None) => {
                        timed_out = true;
                        break;
                    }
                    Err(error) => {
                        errors.push(format!("try_wait: {error}"));
                        break;
                    }
                }
            }
            if status.is_none() {
                // A natural exit can race kill. Always perform our owning wait,
                // including when kill fails, without signaling any other PID.
                if let Err(error) = child.kill() {
                    errors.push(format!("kill: {error}"));
                }
                match child.wait() {
                    Ok(terminal) => status = Some(terminal),
                    Err(error) => errors.push(format!("wait: {error}")),
                }
            }
        }
    }
    let elapsed = started.elapsed();
    fs::write(
        evidence.join("status.json"),
        serde_json::to_vec_pretty(&json!({
            "pid":pid, "success":status.as_ref().map(ExitStatus::success),
            "code":status.as_ref().and_then(ExitStatus::code),
            "signal":status.as_ref().and_then(ExitStatusExt::signal),
            "display":status.as_ref().map(ToString::to_string),
            "timed_out":timed_out, "elapsed_ns":elapsed.as_nanos(), "errors":errors,
        }))
        .unwrap(),
    )
    .unwrap();
    BoundedAliasOutput {
        status,
        timed_out,
        errors,
        stdout: fs::read(evidence.join("stdout")).unwrap(),
        stderr: fs::read(evidence.join("stderr")).unwrap(),
    }
}

fn alias_depth_project(world: &Path, label: &str, configuration: &str) -> PathBuf {
    let project = world.join(label);
    fs::create_dir_all(project.join("src")).unwrap();
    fs::create_dir_all(project.join(".cargo")).unwrap();
    fs::write(
        project.join("Cargo.toml"),
        "[package]\nname='alias_depth_sample'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(project.join("src/lib.rs"), "pub fn value() -> u32 { 1 }\n").unwrap();
    fs::write(project.join(".cargo/config.toml"), configuration).unwrap();
    project
}

#[test]
fn native_alias_depth_ladder_finishes_without_process_failure() {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-alias-restrictions.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix("depth-ladder")
        .tempdir_in(base)
        .unwrap()
        .keep();
    let cycle = alias_depth_project(
        &world,
        "cycle",
        "[alias]\ncycle-a=['cycle-b']\ncycle-b=['cycle-a']\n",
    );
    // Persist every flat alias table and project before launching the first
    // child. A failing depth stops execution without discarding earlier cases.
    let mut cases = Vec::new();
    for depth in [32, 128, 512, 2048] {
        let mut configuration = String::from("[alias]\n");
        for index in 0..depth {
            let expansion = if index + 1 == depth {
                "['locate-project','--message-format=plain']".to_owned()
            } else {
                format!("['depth-{:04}']", index + 1)
            };
            configuration.push_str(&format!("depth-{index:04}={expansion}\n"));
        }
        let project = alias_depth_project(&world, &format!("depth-{depth}"), &configuration);
        cases.push((depth, project));
    }
    fs::write(
        world.join("inputs.json"),
        serde_json::to_vec_pretty(&json!({
            "cycle":cycle, "cases":cases, "timeout_seconds_per_child":60,
            "scope":"metadata-only alias expansion; no compiler or network work",
        }))
        .unwrap(),
    )
    .unwrap();

    let mut observations = Vec::new();
    let output = record_bounded_alias(
        command(&cycle, &world).arg("cycle-a"),
        &world.join("evidence/cycle"),
    );
    let expected_cycle =
        "error: alias cycle-a has unresolvable recursive definition: cycle-a -> cycle-b -> cycle-a";
    observations.push(json!({
        "case":"cycle", "completed":output.completed(),
        "code":output.status.as_ref().and_then(ExitStatus::code),
        "signal":output.status.as_ref().and_then(ExitStatusExt::signal),
        "exact_diagnostic":String::from_utf8_lossy(&output.stderr).lines()
            .any(|line| line == expected_cycle),
        "stdout_empty":output.stdout.is_empty(), "lockfile":lockfile(&cycle),
        "target_created":world.join("target").exists(),
    }));
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observations).unwrap(),
    )
    .unwrap();
    assert!(
        output.completed()
            && output.status.as_ref().and_then(ExitStatus::code) == Some(101)
            && output.stdout.is_empty()
            && observations[0]["exact_diagnostic"] == true
            && lockfile(&cycle).is_none()
            && !world.join("target").exists(),
        "short-cycle control: world={} observations={observations:?}",
        world.display()
    );

    for (depth, project) in cases {
        let output = record_bounded_alias(
            command(&project, &world).arg("depth-0000"),
            &world.join("evidence").join(format!("depth-{depth}")),
        );
        let expected = format!("{}\n", project.join("Cargo.toml").display());
        let correct_stdout = output.stdout == expected.as_bytes();
        observations.push(json!({
            "depth":depth, "completed":output.completed(),
            "code":output.status.as_ref().and_then(ExitStatus::code),
            "signal":output.status.as_ref().and_then(ExitStatusExt::signal),
            "correct_stdout":correct_stdout, "lockfile":lockfile(&project),
            "target_created":world.join("target").exists(),
        }));
        fs::write(
            world.join("observed.json"),
            serde_json::to_vec_pretty(&observations).unwrap(),
        )
        .unwrap();
        assert!(
            output.completed()
                && output.status.as_ref().is_some_and(ExitStatus::success)
                && correct_stdout
                && lockfile(&project).is_none()
                && !world.join("target").exists(),
            "depth={depth}: world={} observations={observations:?}",
            world.display()
        );
    }
}
