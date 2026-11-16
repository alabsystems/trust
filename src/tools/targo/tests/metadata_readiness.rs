#![cfg(any(target_os = "linux", target_os = "macos"))]

//! Real native producer notifications must authorize pipelined consumer dispatch.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

// A compiled-in-place Rust wrapper follows the maintained scheduling fixture
// pattern. It changes only one genuine, successful bar metadata notification.
const PROXY: &str = r###"
use std::io::Write;
use std::path::Path;
use std::process::{Command, Stdio};

fn write_output(bytes: &[u8], stderr: bool) {
    let result = if stderr { std::io::stderr().write_all(bytes) }
                 else { std::io::stdout().write_all(bytes) };
    if let Err(error) = result {
        // The coordinator may close its reader after refusing a notification.
        if error.kind() != std::io::ErrorKind::BrokenPipe { panic!("{error}"); }
    }
}
fn main() {
    let mut words = std::env::args_os().skip(1);
    let compiler = words.next().unwrap();
    let words: Vec<_> = words.collect();
    let name = words.windows(2).find(|pair| pair[0] == "--crate-name")
        .and_then(|pair| pair[1].to_str());
    let actual = !words.iter().any(|arg| arg == "-vV" || arg.to_string_lossy().starts_with("--print"));
    let control = std::env::var_os("METADATA_CONTROL").map(std::path::PathBuf::from);
    if actual && matches!(name, Some("bar" | "foo")) {
        let control = control.as_ref().unwrap();
        std::fs::write(control.join(format!("{}.started", name.unwrap())), b"actual compile").unwrap();
    }
    if !actual || name != Some("bar") {
        // This std child does not forward Cargo's supervised descriptor
        // handoff. Drop unusable advertisements rather than restoring raw
        // tokens. Targo still owns the wrapper job; the fixture is CPU-bound.
        let status = Command::new(compiler).args(words)
            .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
            .env_remove("CARGO_JOBSERVER_HANDOFF").status().unwrap();
        std::process::exit(status.code().unwrap_or(101));
    }
    let control = control.unwrap();
    let result = Command::new(compiler).args(words)
        .env_remove("CARGO_MAKEFLAGS").env_remove("MAKEFLAGS").env_remove("MFLAGS")
        .env_remove("CARGO_JOBSERVER_HANDOFF").stdout(Stdio::piped()).stderr(Stdio::piped())
        .output().unwrap();
    std::fs::write(control.join("bar.stdout"), &result.stdout).unwrap();
    std::fs::write(control.join("bar.stderr"), &result.stderr).unwrap();
    std::fs::write(control.join("bar.status"), result.status.code().unwrap_or(101).to_string()).unwrap();
    std::fs::write(control.join("bar.cwd"), std::env::current_dir().unwrap().as_os_str().as_encoded_bytes()).unwrap();
    if !result.status.success() {
        write_output(&result.stdout, false);
        write_output(&result.stderr, true);
        std::process::exit(result.status.code().unwrap_or(101));
    }
    // Match the real compiler's compact artifact record, not diagnostics that
    // merely mention metadata. The outer test independently decodes this JSON.
    let prefix = "{\"$message_type\":\"artifact\",\"artifact\":\"";
    let suffix = "\",\"emit\":\"metadata\"}";
    let text = String::from_utf8(result.stderr.clone()).unwrap();
    let reports: Vec<_> = text.lines().filter_map(|line| {
        line.strip_prefix(prefix).and_then(|tail| tail.strip_suffix(suffix)).map(|path| (line, path))
    }).collect();
    assert_eq!(reports.len(), 1, "expected exactly one actual metadata record: {text}");
    let (report, path) = reports[0];
    // Fixture paths have no JSON escapes; an unsupported path fails the honest
    // positive too, rather than becoming a purported protocol rejection.
    assert!(!path.contains('\\') && !path.contains('"'));
    assert!(Path::new(path).is_absolute() && std::fs::metadata(path).unwrap().is_file());
    std::fs::write(control.join("bar.metadata.json"), report).unwrap();
    let mode = std::env::var("METADATA_MODE").unwrap();
    let sent = match mode.as_str() {
        "exact" => Some(report.to_owned()),
        "path" => {
            let wrong = control.join("different.rmeta");
            std::fs::copy(path, &wrong).unwrap();
            let wrong = wrong.to_str().unwrap();
            assert!(!wrong.contains('\\') && !wrong.contains('"'));
            Some(format!("{prefix}{wrong}{suffix}"))
        }
        "kind" => Some(format!("{prefix}{path}\",\"emit\":\"link\"}}")),
        "missing" => None,
        "malformed" => Some(format!("{report}\n{{\"$message_type\":\"artifact\",\"artifact\":null,\"emit\":\"metadata\"}}")),
        _ => panic!("unknown mode"),
    };
    std::fs::write(control.join("bar.sent.json"), sent.as_deref().unwrap_or("")).unwrap();
    write_output(&result.stdout, false);
    for line in text.lines() {
        if line == report {
            if let Some(sent) = &sent { write_output(format!("{sent}\n").as_bytes(), true); }
        } else {
            write_output(format!("{line}\n").as_bytes(), true);
        }
    }
    std::io::stderr().flush().unwrap_or_else(|error| {
        if error.kind() != std::io::ErrorKind::BrokenPipe { panic!("{error}"); }
    });
    if mode == "exact" {
        // Hang detection only: successful execution requires real dependent
        // dispatch while this producer wrapper has not returned success.
        let end = std::time::Instant::now() + std::time::Duration::from_secs(60);
        while !control.join("foo.started").exists() {
            assert!(std::time::Instant::now() < end, "consumer did not start before producer completion");
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
        std::fs::write(control.join("pipeline.observed"), b"foo started before bar wrapper returned").unwrap();
    }
    std::process::exit(0);
}
"###;

#[expect(
    clippy::disallowed_methods,
    reason = "the isolated native fixture explicitly inherits only PATH and its selected compiler tools before project configuration exists"
)]
fn command(root: &Path, world: &Path) -> Command {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_targo"));
    cmd.current_dir(root)
        .env_clear()
        .env("HOME", world)
        .env("CARGO_HOME", world.join("home"))
        .env("CARGO_TARGET_DIR", world.join("target"))
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env(
            "RUSTC",
            std::env::var_os("RUSTC").expect("explicit native fixture compiler"),
        )
        .env(
            "RUSTDOC",
            std::env::var_os("RUSTDOC").expect("matching fixture rustdoc"),
        )
        .args([
            "--unverified",
            "build",
            "--offline",
            "--message-format=json",
        ]);
    if root.join("Cargo.lock").exists() {
        cmd.arg("--locked");
    }
    cmd
}

fn artifacts(output: &Output) -> Vec<serde_json::Value> {
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| serde_json::from_str::<serde_json::Value>(line).ok())
        .filter(|row| row["reason"] == "compiler-artifact")
        .collect()
}

fn run_case(mode: &str) {
    let base = std::env::current_dir()
        .unwrap()
        .join(".ubd/native-metadata-readiness.noindex");
    fs::create_dir_all(&base).unwrap();
    // Retain executable locations and failed inputs in place; never copy or
    // rename the Rust proxy or delete a newly assessed executable afterward.
    let world = tempfile::Builder::new()
        .prefix(mode)
        .tempdir_in(base)
        .unwrap()
        .keep();
    let proxy_root = world.join("proxy");
    fs::create_dir_all(proxy_root.join("src")).unwrap();
    fs::write(proxy_root.join("Cargo.toml"), "[package]\nname='metadata_proxy'\nversion='0.0.0'\nedition='2021'\n[workspace]\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(proxy_root.join("src/main.rs"), PROXY).unwrap();
    let proxy_build = command(&proxy_root, &world).arg("-j1").output().unwrap();
    fs::write(world.join("proxy.stdout"), &proxy_build.stdout).unwrap();
    fs::write(world.join("proxy.stderr"), &proxy_build.stderr).unwrap();
    assert!(
        proxy_build.status.success(),
        "proxy build: {}",
        String::from_utf8_lossy(&proxy_build.stderr)
    );
    let proxy = artifacts(&proxy_build)
        .into_iter()
        .find(|row| row["target"]["name"] == "metadata_proxy")
        .and_then(|row| row["executable"].as_str().map(PathBuf::from))
        .unwrap();
    let graph = world.join("graph");
    let control = world.join("control");
    fs::create_dir_all(&control).unwrap();
    fs::create_dir_all(graph.join("bar/src")).unwrap();
    fs::create_dir_all(graph.join("foo/src")).unwrap();
    fs::write(graph.join("Cargo.toml"), "[workspace]\nmembers=['bar','foo']\nresolver='2'\n[profile.dev]\ndebug=0\nincremental=false\n").unwrap();
    fs::write(
        graph.join("bar/Cargo.toml"),
        "[package]\nname='bar'\nversion='0.0.0'\nedition='2021'\n[lib]\ncrate-type=['rlib']\n",
    )
    .unwrap();
    fs::write(
        graph.join("bar/src/lib.rs"),
        "pub fn value() -> u32 { 42 }\n",
    )
    .unwrap();
    fs::write(graph.join("foo/Cargo.toml"), "[package]\nname='foo'\nversion='0.0.0'\nedition='2021'\n[lib]\ncrate-type=['rlib']\n[dependencies]\nbar={path='../bar'}\n").unwrap();
    fs::write(
        graph.join("foo/src/lib.rs"),
        "pub fn value() -> u32 { bar::value() }\n",
    )
    .unwrap();
    let build = |label: &str| {
        let output = command(&graph, &world)
            .env("RUSTC_WRAPPER", &proxy)
            .env("METADATA_CONTROL", &control)
            .env("METADATA_MODE", mode)
            .args(["-j2", "-p", "foo", "--lib"])
            .output()
            .unwrap();
        fs::write(world.join(format!("{label}.stdout")), &output.stdout).unwrap();
        fs::write(world.join(format!("{label}.stderr")), &output.stderr).unwrap();
        output
    };
    let cold = build("cold");
    let detail = format!(
        "world={}\n{}\n{}",
        world.display(),
        String::from_utf8_lossy(&cold.stdout),
        String::from_utf8_lossy(&cold.stderr)
    );
    assert_eq!(
        fs::read_to_string(control.join("bar.status")).unwrap(),
        "0",
        "{detail}"
    );
    let actual: serde_json::Value =
        serde_json::from_slice(&fs::read(control.join("bar.metadata.json")).unwrap()).unwrap();
    assert_eq!(actual["$message_type"], "artifact");
    assert_eq!(actual["emit"], "metadata");
    let actual_path = PathBuf::from(actual["artifact"].as_str().unwrap());
    assert!(
        actual_path.is_absolute() && actual_path.is_file(),
        "{detail}"
    );
    assert!(PathBuf::from(fs::read_to_string(control.join("bar.cwd")).unwrap()).is_absolute());
    let sent = fs::read(control.join("bar.sent.json")).unwrap();
    match mode {
        "exact" => {
            assert_eq!(
                serde_json::from_slice::<serde_json::Value>(&sent).unwrap(),
                actual
            );
            assert!(cold.status.success(), "{detail}");
            assert!(control.join("pipeline.observed").is_file(), "{detail}");
            assert!(control.join("foo.started").is_file(), "{detail}");
            for name in ["bar.started", "foo.started"] {
                fs::remove_file(control.join(name)).unwrap();
            }
            let warm = build("warm");
            assert!(
                warm.status.success(),
                "{detail}\n{}",
                String::from_utf8_lossy(&warm.stderr)
            );
            let rows = artifacts(&warm);
            assert_eq!(rows.len(), 2, "{rows:?}");
            assert!(rows.iter().all(|row| row["fresh"] == true), "{rows:?}");
            assert!(!control.join("bar.started").exists() && !control.join("foo.started").exists());
        }
        "path" | "kind" | "missing" => {
            if mode == "missing" {
                assert!(sent.is_empty());
            } else {
                let sent: serde_json::Value = serde_json::from_slice(&sent).unwrap();
                if mode == "path" {
                    assert_ne!(sent["artifact"], actual["artifact"]);
                    assert_eq!(sent["emit"], "metadata");
                    assert_eq!(
                        fs::read(sent["artifact"].as_str().unwrap()).unwrap(),
                        fs::read(actual_path).unwrap()
                    );
                } else {
                    assert_eq!(sent["artifact"], actual["artifact"]);
                    assert_eq!(sent["emit"], "link");
                }
            }
            assert!(
                !cold.status.success(),
                "native protocol must refuse invalid readiness: {detail}"
            );
            assert!(
                String::from_utf8_lossy(&cold.stderr).contains("native pipelined metadata"),
                "{detail}"
            );
            assert!(
                !control.join("foo.started").exists(),
                "consumer started after invalid readiness: {detail}"
            );
        }
        "malformed" => {
            let records: Vec<_> = String::from_utf8(sent)
                .unwrap()
                .lines()
                .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
                .collect();
            assert_eq!(records.len(), 2);
            assert_eq!(records[0], actual);
            assert_eq!(records[1]["$message_type"], "artifact");
            assert_eq!(records[1]["emit"], "metadata");
            assert!(records[1]["artifact"].is_null());
            assert!(
                !cold.status.success(),
                "malformed report after readiness must fail completion: {detail}"
            );
            assert!(
                String::from_utf8_lossy(&cold.stderr).contains("native pipelined metadata"),
                "{detail}"
            );
            // The preceding exact report legitimately allowed foo to start.
            // This control asserts invalid final completion, not retroactive
            // cancellation of already-authorized dependent work.
        }
        _ => unreachable!(),
    }
}

#[test]
fn exact_metadata_releases_consumer_before_producer_completion_and_reuses_warm_units() {
    run_case("exact");
}
#[test]
fn redirected_metadata_report_cannot_release_consumer() {
    run_case("path");
}
#[test]
fn wrong_kind_at_expected_metadata_path_cannot_release_consumer() {
    run_case("kind");
}
#[test]
fn missing_metadata_report_cannot_use_successful_job_fallback() {
    run_case("missing");
}

#[test]
fn malformed_report_after_exact_metadata_invalidates_completion() {
    run_case("malformed");
}
