//! Native command levels and alias frames retain accumulating options.
// SPDX-License-Identifier: MIT OR Apache-2.0
// Copyright 2026 Andrew Yates

#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde_json::{Value, json};

#[expect(
    clippy::disallowed_methods,
    reason = "the native fixture selects the caller's original tools before loading project configuration"
)]
fn command(world: &Path) -> Command {
    let executable = std::env::var_os("TARGO_GLOBAL_OPTIONS_TEST_BINARY")
        .unwrap_or_else(|| env!("CARGO_BIN_EXE_targo").into());
    let mut command = Command::new(executable);
    command
        .current_dir(world.join("project"))
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("original compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching rustdoc"),
        )
        .env("__CARGO_TEST_CHANNEL_OVERRIDE_DO_NOT_USE_THIS", "nightly");
    command
}

fn world() -> PathBuf {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-global-options.noindex");
    fs::create_dir_all(&base).unwrap();
    // Retain all input/output worlds, including a failure before an assertion.
    let world = tempfile::Builder::new()
        .prefix("args")
        .tempdir_in(base)
        .unwrap()
        .keep();
    for path in [
        world.join("project/src"),
        world.join("project/.cargo"),
        world.join("home"),
    ] {
        fs::create_dir_all(path).unwrap();
    }
    fs::write(world.join("project/Cargo.toml"), "[package]\nname='native_global_options'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(world.join("project/src/main.rs"), r#"fn main() {
    println!("{}|{}", option_env!("CLI_ROOT").unwrap_or("missing"), option_env!("CLI_ORDER").unwrap_or("missing"));
    for argument in std::env::args().skip(1) { println!("arg={argument}"); }
}
"#).unwrap();
    world
}

fn recorded(mut command: Command, world: &Path, label: &str) -> Output {
    let evidence = world.join(label);
    fs::create_dir(&evidence).unwrap();
    fs::write(
        evidence.join("command.json"),
        serde_json::to_vec_pretty(&json!({
            "program":command.get_program().to_string_lossy(),
            "args":command.get_args().map(|arg|arg.to_string_lossy()).collect::<Vec<_>>(),
            "cwd":command.get_current_dir(),
        }))
        .unwrap(),
    )
    .unwrap();
    let output = command.output().unwrap();
    fs::write(evidence.join("stdout"), &output.stdout).unwrap();
    fs::write(evidence.join("stderr"), &output.stderr).unwrap();
    fs::write(evidence.join("status.json"), serde_json::to_vec_pretty(&json!({
        "success":output.status.success(),"code":output.status.code(),"display":output.status.to_string(),
    })).unwrap()).unwrap();
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

#[test]
fn native_mixed_global_options_reach_compiler_and_keep_program_tails_opaque() {
    let world = world();
    let mut compile = command(&world);
    compile.env("CARGO_BUILD_ANALYSIS_ENABLED", "true").args([
        "--config",
        "env.CLI_ROOT='from-root'",
        "--config",
        "env.CLI_ORDER='root'",
        "-Zbuild-analysis",
        "--unverified",
        "build",
        "--config",
        "env.CLI_ORDER='leaf'",
        "-Zmem-stats",
        "--offline",
        "-j1",
        "--message-format=json",
    ]);
    let build = recorded(compile, &world, "build");
    success(&build, &world);
    let rows = build
        .stdout
        .split(|byte| *byte == b'\n')
        .filter(|line| !line.is_empty())
        .map(|line| serde_json::from_slice::<Value>(line).unwrap())
        .collect::<Vec<_>>();
    fs::write(
        world.join("build-rows.json"),
        serde_json::to_vec_pretty(&rows).unwrap(),
    )
    .unwrap();
    let sessions = rows
        .iter()
        .filter(|row| row["reason"] == "build-analysis-session")
        .collect::<Vec<_>>();
    let artifact = rows
        .iter()
        .find(|row| row["reason"] == "compiler-artifact" && row["executable"].is_string())
        .unwrap();
    let program = recorded(
        Command::new(artifact["executable"].as_str().unwrap()),
        &world,
        "program",
    );
    let report = sessions.first().map(|session| {
        let run = session["run_id"].as_str().unwrap();
        let mut report = command(&world);
        report.args([
            "-Zbuild-analysis",
            "report",
            "execution",
            "--id",
            run,
            "--json",
        ]);
        let output = recorded(report, &world, "execution-report");
        fs::copy(
            world.join("home/log").join(format!("{run}.jsonl")),
            world.join("analysis.jsonl"),
        )
        .unwrap();
        output
    });
    let mut run = command(&world);
    run.args([
        "--config",
        "env.CLI_ROOT='from-root'",
        "--config",
        "env.CLI_ORDER='root'",
        "--unverified",
        "run",
        "--offline",
        "--config",
        "env.CLI_ORDER='leaf'",
        "--",
        "-Zbuild-analysis",
        "--config",
        "demo.scalar='program-tail'",
        "--unverified",
    ]);
    let run = recorded(run, &world, "run-tail");
    let mut no_consent = command(&world);
    no_consent.args(["run", "--offline", "--", "--unverified"]);
    let no_consent = recorded(no_consent, &world, "tail-cannot-consent");
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&json!({
            "sessions":sessions,"program_stdout":program.stdout,"run_stdout":run.stdout,
            "report_success":report.as_ref().map(|output|output.status.success()),
            "tail_without_consent_success":no_consent.status.success(),
        }))
        .unwrap(),
    )
    .unwrap();
    success(&program, &world);
    success(&run, &world);
    assert_eq!(program.stdout, b"from-root|leaf\n");
    assert_eq!(run.stdout, b"from-root|leaf\narg=-Zbuild-analysis\narg=--config\narg=demo.scalar='program-tail'\narg=--unverified\n");
    assert_eq!(sessions.len(), 1, "world={}", world.display());
    let report = report.unwrap();
    success(&report, &world);
    let report: Value = serde_json::from_slice(&report.stdout).unwrap();
    assert_eq!(report["availability"], "complete");
    assert_eq!(report["compiler_activity"]["rusage_requested"], true);
    assert_eq!(
        report["compiler_activity"]["successful_primary_processes"],
        1
    );
    success(&no_consent, &world);
    assert_eq!(no_consent.stdout, b"missing|missing\narg=--unverified\n");
    // `run` has no verified counterpart and currently selects the unverified
    // lane itself. A flag in the program tail must not become typed consent.
    let warning = String::from_utf8_lossy(&no_consent.stderr);
    assert!(
        warning.contains("has no verified lane, so Trust verification is off; nobody was asked"),
        "{warning}"
    );
    assert!(!warning.contains("was explicitly authorized"), "{warning}");
}

#[test]
fn native_nested_commands_and_aliases_keep_order_without_minting_consent() {
    let world = world();
    fs::write(world.join("project/.cargo/config.toml"), r#"[alias]
outer = ["--config", "demo.order=['outer']", "--config", "demo.scalar='outer'", "inner"]
inner = ["--config", "demo.order=['inner']", "--config", "demo.scalar='inner'", "config", "get", "demo", "--format=json-value"]
bad = ["build", "--unverified"]
bad-chain = ["bad"]
"#).unwrap();
    let mut query = command(&world);
    query.args([
        "-Zunstable-options",
        "--config",
        "demo.order=['root']",
        "--config",
        "demo.scalar='root'",
        "config",
        "-Zbuild-analysis",
        "--config",
        "demo.order=['middle']",
        "--config",
        "demo.scalar='middle'",
        "get",
        "demo",
        "--format=json-value",
        "-Zmem-stats",
        "--config",
        "demo.order=['leaf']",
        "--config",
        "demo.scalar='leaf'",
    ]);
    let query = recorded(query, &world, "nested-query");
    let mut alias = command(&world);
    alias.args([
        "-Zunstable-options",
        "--config",
        "demo.order=['root']",
        "--config",
        "demo.scalar='root'",
        "outer",
        "--config",
        "demo.order=['tail']",
        "--config",
        "demo.scalar='tail'",
    ]);
    let alias = recorded(alias, &world, "alias-query");
    let mut help = command(&world);
    help.args(["report", "execution", "-Zhelp"]);
    let help = recorded(help, &world, "nested-help");
    let mut refused = command(&world);
    refused.arg("bad-chain");
    let refused = recorded(refused, &world, "alias-cannot-consent");
    fs::write(world.join("observed.json"), serde_json::to_vec_pretty(&json!({
        "query_success":query.status.success(),"alias_success":alias.status.success(),
        "help_success":help.status.success(),"injected_consent_success":refused.status.success(),
        "target_exists":world.join("target").exists(),
    })).unwrap()).unwrap();
    success(&query, &world);
    success(&alias, &world);
    success(&help, &world);
    assert_eq!(
        serde_json::from_slice::<Value>(&query.stdout).unwrap(),
        json!({"order":["root","middle","leaf"],"scalar":"leaf"})
    );
    assert_eq!(
        serde_json::from_slice::<Value>(&alias.stdout).unwrap(),
        json!({"order":["root","outer","inner","tail"],"scalar":"tail"})
    );
    assert!(String::from_utf8_lossy(&help.stdout).contains("build-analysis"));
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr)
            .contains("alias attempted to inject `--unverified`")
    );
    assert!(refused.stdout.is_empty());
    assert!(
        !world.join("target").exists(),
        "metadata and refused aliases must not start a compilation"
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn native_bootstrap_short_and_long_help_match_without_admission() {
    let world = world();
    let mut accepted = Vec::new();
    let mut refused = Vec::new();
    for (route, prefix) in [
        (
            "direct",
            &["--unverified", "resource", "bootstrap-runtime"][..],
        ),
        (
            "hosted",
            &[
                "--resource-worker-v3",
                "--resource-subgroups-v3",
                "--unverified",
                "resource",
                "bootstrap-runtime",
            ][..],
        ),
    ] {
        for (spelling, flag) in [("long", "--help"), ("short", "-h")] {
            let mut help = command(&world);
            help.args(prefix).arg(flag);
            accepted.push(recorded(
                help,
                &world,
                &format!("bootstrap-{route}-{spelling}"),
            ));
            let mut extra = command(&world);
            extra.args(prefix).args([flag, "extra"]);
            refused.push(recorded(
                extra,
                &world,
                &format!("bootstrap-{route}-{spelling}-extra"),
            ));
        }
    }
    // Record every result before asserting so the old short-help refusals and
    // both valid long-help controls survive the native regression's failure.
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&json!({
            "help_success":accepted.iter().map(|output| output.status.success()).collect::<Vec<_>>(),
            "extra_success":refused.iter().map(|output| output.status.success()).collect::<Vec<_>>(),
            "target_exists":world.join("target").exists(),
        }))
        .unwrap(),
    )
    .unwrap();
    assert!(
        accepted[0]
            .stdout
            .starts_with(b"Usage: targo --unverified resource bootstrap-runtime")
    );
    for output in &accepted {
        success(output, &world);
        assert_eq!(output.status.code(), Some(0));
        assert_eq!(output.stdout, accepted[0].stdout);
        assert!(output.stderr.is_empty());
    }
    for output in &refused {
        assert!(!output.status.success(), "world={}", world.display());
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
    }
    assert!(
        !world.join("target").exists(),
        "Bootstrap help and malformed help must not start a compilation"
    );
}

#[test]
fn native_alias_directory_change_uses_destination_config_and_parser_color() {
    let original_directory = std::env::current_dir().unwrap();
    let world = world();
    let before = world.join("project");
    let after = world.join("after");
    fs::create_dir_all(after.join(".cargo")).unwrap();
    fs::create_dir_all(after.join("src")).unwrap();
    fs::write(
        after.join("Cargo.toml"),
        "[package]\nname='native_directory_context'\nversion='0.0.0'\nedition='2021'\n[workspace]\n",
    )
    .unwrap();
    fs::write(after.join("src/main.rs"), "fn main() {}\n").unwrap();
    for (side, directory, color) in [("before", &before, "never"), ("after", &after, "always")] {
        fs::write(
            directory.join(".cargo/config.toml"),
            format!(
                r#"[term]
color='{color}'
[marker]
origin='{side}'
order=['{side}-file']
selected='{side}-file'
[alias]
directory-outer=['--config',"marker.order=['{side}-outer']",'--config',"marker.selected='{side}-outer'",'directory-inner']
directory-inner=['--config',"marker.order=['{side}-inner']",'--config',"marker.selected='{side}-inner'",'config','get','marker','--format=json-value']
directory-help-outer=['directory-help-inner']
directory-help-inner=['locate-project','--help']
"#
            ),
        )
        .unwrap();
    }
    let mut queries = Vec::new();
    let mut help = Vec::new();
    for (side, change_directory) in [("before", false), ("after", true)] {
        let mut query = command(&world);
        query.current_dir(&before).arg("-Zunstable-options");
        if change_directory {
            query.arg("-C").arg(&after);
        }
        query.args([
            "--config",
            "marker.order=['caller']",
            "--config",
            "marker.selected='caller'",
            "directory-outer",
        ]);
        queries.push(recorded(query, &world, &format!("directory-{side}-query")));

        let mut output = command(&world);
        output.current_dir(&before).arg("-Zunstable-options");
        if change_directory {
            output.arg("-C").arg(&after);
        }
        output.arg("directory-help-outer");
        help.push(recorded(output, &world, &format!("directory-{side}-help")));
    }
    let observed_directory = std::env::current_dir().unwrap();
    let has_ansi = |output: &Output| output.stdout.windows(2).any(|bytes| bytes == b"\x1b[");
    let lockfiles = [
        before.join("Cargo.lock").exists(),
        after.join("Cargo.lock").exists(),
    ];
    // Keep all child outcomes and state observations before asserting. Only
    // child Command::current_dir and the child's original -C may change cwd.
    fs::write(
        world.join("observed.json"),
        serde_json::to_vec_pretty(&json!({
            "test_cwd_before":original_directory,"test_cwd_after":observed_directory,
            "query_success":queries.iter().map(|output| output.status.success()).collect::<Vec<_>>(),
            "help_success":help.iter().map(|output| output.status.success()).collect::<Vec<_>>(),
            "help_ansi":help.iter().map(has_ansi).collect::<Vec<_>>(),
            "lockfiles":lockfiles,"target_exists":world.join("target").exists(),
        }))
        .unwrap(),
    )
    .unwrap();
    assert_eq!(observed_directory, original_directory);
    for (side, output) in [("before", &queries[0]), ("after", &queries[1])] {
        success(output, &world);
        assert_eq!(
            serde_json::from_slice::<Value>(&output.stdout).unwrap(),
            json!({
                "origin":side,
                "order":[format!("{side}-file"),"caller",format!("{side}-outer"),format!("{side}-inner")],
                "selected":format!("{side}-inner"),
            }),
            "world={}",
            world.display()
        );
    }
    for output in &help {
        success(output, &world);
        assert!(output.stderr.is_empty());
        assert!(String::from_utf8_lossy(&output.stdout).contains("locate-project"));
        assert!(String::from_utf8_lossy(&output.stdout).contains("Usage:"));
    }
    assert!(!has_ansi(&help[0]), "world={}", world.display());
    assert!(has_ansi(&help[1]), "world={}", world.display());
    assert!(lockfiles.iter().all(|exists| !exists));
    assert!(!world.join("target").exists());
}
