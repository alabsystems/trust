// Trust: late build-script cfg operands may contain compiler response files.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy, Debug)]
enum Directive {
    Cfg,
    CheckCfg,
}

impl Directive {
    fn name(self) -> &'static str {
        match self {
            Self::Cfg => "cfg",
            Self::CheckCfg => "check-cfg",
        }
    }

    fn contents(self, changed: bool) -> &'static str {
        match (self, changed) {
            (Self::Cfg, false) => "first\n",
            (Self::Cfg, true) => "second\n",
            (Self::CheckCfg, false) => "cfg(first)\n--check-cfg\ncfg(second)\n--cfg\nfirst\n",
            (Self::CheckCfg, true) => "cfg(first)\n--check-cfg\ncfg(second)\n--cfg\nsecond\n",
        }
    }
}

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture selects only PATH and its explicit genuine compiler tools"
)]
fn command(project: &Path, world: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_targo"));
    cmd.current_dir(project)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit native compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching native rustdoc"),
        )
        .args([
            "--unverified",
            "build",
            "--offline",
            "-vv",
            "-j1",
            "--message-format=json",
        ]);
    if project.join("Cargo.lock").is_file() {
        cmd.arg("--locked");
    }
    cmd
}

fn record(world: &Path, label: &str, output: &std::process::Output) {
    fs::write(world.join(format!("{label}.stdout")), &output.stdout).unwrap();
    fs::write(world.join(format!("{label}.stderr")), &output.stderr).unwrap();
    fs::write(
        world.join(format!("{label}.status")),
        output.status.to_string(),
    )
    .unwrap();
}

fn build(project: &Path, world: &Path, label: &str) -> (serde_json::Value, Vec<serde_json::Value>) {
    let mut cmd = command(project, world);
    fs::write(
        world.join(format!("{label}.command.json")),
        serde_json::to_vec(&serde_json::json!({
            "targo":cmd.get_program().to_string_lossy(),
            "args":cmd.get_args().map(|arg| arg.to_string_lossy()).collect::<Vec<_>>(),
            "project":project
        }))
        .unwrap(),
    )
    .unwrap();
    let output = cmd.output().unwrap();
    record(world, label, &output);
    assert!(
        output.status.success(),
        "world={}\nstatus={}\n{}",
        world.display(),
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let rows: Vec<_> = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .collect();
    let bins: Vec<_> = rows
        .iter()
        .filter(|row| {
            row["reason"] == "compiler-artifact" && row["target"]["name"] == "argfile_consumer"
        })
        .collect();
    assert_eq!(bins.len(), 1, "{rows:?}");
    ((*bins[0]).clone(), rows)
}

fn execute(world: &Path, row: &serde_json::Value, label: &str) -> Vec<u8> {
    let executable = row["executable"].as_str().expect("real binary output");
    let output = Command::new(executable).output().unwrap();
    record(world, &format!("{label}-binary"), &output);
    assert!(
        output.status.success(),
        "world={}\n{}",
        world.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn receipt(world: &Path) -> Option<(PathBuf, serde_json::Value)> {
    let paths: Vec<_> = walkdir::WalkDir::new(world.join("target"))
        .into_iter()
        .map(Result::unwrap)
        .filter(|entry| entry.file_name() == "outputs-bin-argfile_consumer.json")
        .map(|entry| entry.into_path())
        .collect();
    assert!(paths.len() <= 1, "{paths:?}");
    paths.into_iter().next().map(|path| {
        let value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        (path, value)
    })
}

fn qualify(directive: Directive) {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-build-script-argfiles.noindex");
    fs::create_dir_all(&base).unwrap();
    let world = tempfile::Builder::new()
        .prefix(directive.name())
        .tempdir_in(base)
        .unwrap()
        .keep();
    let project = world.join("project");
    fs::create_dir_all(project.join("src")).unwrap();
    let args = world.join("external.args");
    fs::write(&args, directive.contents(false)).unwrap();
    let runs = world.join("script-runs");
    fs::write(&runs, []).unwrap();
    fs::write(project.join("Cargo.toml"), "[package]\nname='argfile_consumer'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(
        project.join("src/main.rs"),
        r#"
#[cfg(all(first, second))] compile_error!("expected one selected cfg");
#[cfg(not(any(first, second)))] compile_error!("expected one selected cfg");
fn main() {
    #[cfg(first)] println!("first");
    #[cfg(second)] println!("second");
}
"#,
    )
    .unwrap();
    let emitted = format!("cargo::rustc-{}=@{}", directive.name(), args.display());
    fs::write(
        project.join("build.rs"),
        format!(
            r#"
use std::io::Write;
fn main() {{
    std::fs::OpenOptions::new().append(true).open({runs:?}).unwrap().write_all(b"ran\n").unwrap();
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rustc-check-cfg=cfg(first)");
    println!("cargo::rustc-check-cfg=cfg(second)");
    println!({emitted:?});
}}
"#,
            runs = runs.to_str().unwrap()
        ),
    )
    .unwrap();
    for label in ["first", "second", "witness", "repeat"] {
        for suffix in ["stdout", "stderr", "status", "command.json"] {
            fs::write(world.join(format!("{label}.{suffix}")), []).unwrap();
            fs::write(world.join(format!("{label}-binary.{suffix}")), []).unwrap();
        }
    }
    fs::write(world.join("observed.json"), []).unwrap();
    let source_before = fs::read(project.join("src/main.rs")).unwrap();
    let script_before = fs::read(project.join("build.rs")).unwrap();
    let (first, first_rows) = build(&project, &world, "first");
    let first_output = execute(&world, &first, "first");
    let first_runs = fs::read(&runs).unwrap();
    let first_receipt = receipt(&world);
    let script_output = first_rows
        .iter()
        .find(|row| row["reason"] == "build-script-executed")
        .unwrap();
    let out_dir = PathBuf::from(script_output["out_dir"].as_str().unwrap());
    assert!(args.strip_prefix(&project).is_err() && args.strip_prefix(&out_dir).is_err());

    // The response file is not a declared build-script input. Its bytes are
    // the ONLY edit; original script directives, source and flags stay fixed.
    fs::write(&args, directive.contents(true)).unwrap();
    let (second, second_rows) = build(&project, &world, "second");
    let second_output = execute(&world, &second, "second");
    let second_runs = fs::read(&runs).unwrap();
    let second_receipt = receipt(&world);
    let second_stderr = fs::read_to_string(world.join("second.stderr")).unwrap();
    let second_opaque_dirty_reason = second_stderr.lines().find(|line| {
        line.trim_start().starts_with("Dirty argfile_consumer ")
            && line.contains("cached output integrity failed at `")
            && line.ends_with(
                "caller response-file arguments are opaque to Cargo's expected output inventory",
            )
    });

    // A genuinely compiled second result proves the changed file is valid,
    // even when the baseline reused its first executable without running rustc.
    let witness = if second["fresh"] == true {
        let path = &second_receipt
            .as_ref()
            .expect("baseline receipt before forced compile")
            .0;
        let name = path
            .file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .strip_prefix("outputs-")
            .unwrap()
            .strip_suffix(".json")
            .unwrap();
        let short = path.parent().unwrap().join(name);
        assert!(fs::symlink_metadata(&short).unwrap().file_type().is_file());
        let short_bytes = fs::read(&short).unwrap();
        fs::remove_file(&short).unwrap();
        let (row, rows) = build(&project, &world, "witness");
        let output = execute(&world, &row, "witness");
        Some(
            serde_json::json!({"artifact":row,"rows":rows,"stdout":output,
            "removed_short_fingerprint":short,"removed_short_bytes":short_bytes,"receipt":receipt(&world)}),
        )
    } else {
        None
    };
    let (repeat, repeat_rows) = build(&project, &world, "repeat");
    let repeat_output = execute(&world, &repeat, "repeat");
    let repeat_runs = fs::read(&runs).unwrap();
    let repeat_receipt = receipt(&world);
    let observed = serde_json::json!({"directive":directive.name(),"external_args":args,
        "initial_args":directive.contents(false),"changed_args":directive.contents(true),
        "first":first,"first_rows":first_rows,"first_stdout":first_output,"first_runs":first_runs,"first_receipt":first_receipt,
        "second":second,"second_rows":second_rows,"second_stdout":second_output,"second_runs":second_runs,"second_receipt":second_receipt,
        "second_opaque_dirty_reason":second_opaque_dirty_reason,
        "forced_compile_witness":witness,
        "repeat":repeat,"repeat_rows":repeat_rows,"repeat_stdout":repeat_output,"repeat_runs":repeat_runs,"repeat_receipt":repeat_receipt});
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&observed).unwrap(),
    )
    .unwrap();

    assert_eq!(first["fresh"], false, "{observed}");
    assert_eq!(first_output, b"first\n", "{observed}");
    assert_eq!(first_runs, b"ran\n", "{observed}");
    assert!(
        first_receipt.is_none(),
        "cold opaque inputs must not publish a receipt: {observed}"
    );
    assert_eq!(
        second_runs, first_runs,
        "the script itself must stay cached: {observed}"
    );
    assert_eq!(
        repeat_runs, first_runs,
        "the script itself must stay cached: {observed}"
    );
    assert_eq!(
        fs::read(project.join("src/main.rs")).unwrap(),
        source_before
    );
    assert_eq!(fs::read(project.join("build.rs")).unwrap(), script_before);
    if let Some(witness) = &witness {
        assert_eq!(witness["artifact"]["fresh"], false, "{observed}");
        assert_eq!(
            witness["stdout"],
            serde_json::json!(b"second\n".as_slice()),
            "{observed}"
        );
    }
    assert_eq!(
        second["fresh"], false,
        "changed late response contents must not be Fresh: {observed}"
    );
    // This must come from planning with the cached, receipt-bound script
    // controls, before a missing consumer receipt could independently miss.
    assert!(
        second_opaque_dirty_reason.is_some(),
        "cached script controls must select the opaque response-file policy: {observed}"
    );
    assert_eq!(second_output, b"second\n", "{observed}");
    assert!(
        second_receipt.is_none(),
        "opaque compiler input cannot publish an output receipt: {observed}"
    );
    assert_eq!(
        repeat["fresh"], false,
        "opaque compiler input must remain uncacheable: {observed}"
    );
    assert_eq!(repeat_output, b"second\n", "{observed}");
    assert!(repeat_receipt.is_none(), "{observed}");
}

#[test]
fn late_build_script_cfg_response_file_cannot_reuse_old_binary() {
    qualify(Directive::Cfg);
}

#[test]
fn late_build_script_check_cfg_response_file_cannot_reuse_old_binary() {
    qualify(Directive::CheckCfg);
}
