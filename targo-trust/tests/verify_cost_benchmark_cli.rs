//! `targo trust benchmark verify-cost` driven end to end through a fake trustc.
//!
//! The fake is a POSIX shell script: it answers `-vV`, accepts the
//! verification-off compile, and for the verification-on compile prints the
//! `TRUST_JSON:` rows a verifying compiler prints for the generated crate,
//! bent by `FAKE_MODE`. The judging logic itself is unit-tested beside the
//! command (`targo-trust/src/verify_cost.rs`); this pins what only a real
//! process shows: the exit status, the wall-clock and memory budgets, and the
//! usage errors.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

#![cfg(unix)]

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Output};

const FAKE_TRUSTC: &str = r#"#!/bin/sh
if [ "$1" = "-vV" ]; then
  echo "rustc 9.9.9-fake (trustc fake)"
  exit 0
fi
src=
for arg in "$@"; do
  case "$arg" in
    -Ztrust-verify=off) exit 0 ;;
  esac
  src=$arg
done
case "$FAKE_MODE" in
  exit-1) echo "error: the fake refuses" >&2; exit 1 ;;
  slow) sleep 1 ;;
esac
awk -v crate=verify_cost '
function emit(row) { print "TRUST_JSON:{\"crate_name\":\"" crate "\"," row "}" }
function pair(key, value) { return "\"" key "\":" value }
/^pub fn / {
  name = $3; sub(/\(.*/, "", name); n++
  shape = name; sub(/_[0-9]+$/, "", shape)
  kind = (shape == "identity" || shape == "compare") ? "no_obligations" : "overflow:add"
  outcome = (ENVIRON["FAKE_MODE"] == "unknown" && n == 1) ? "unknown" : "proved"
  if (outcome == "proved") proved++; else unknown++
  result = "[{" pair("kind", "\"" kind "\"") "," pair("outcome", "\"" outcome "\"") "}]"
  emit(pair("type", "\"function_result\"") "," pair("function", "\"" crate "::" name "\"") \
    "," pair("cached", 0) "," pair("results", result))
}
END {
  emit(pair("type", "\"coverage_summary\"") "," pair("eligible", n) "," pair("processed", n))
  summary = pair("type", "\"crate_summary\"") "," pair("functions_analyzed", n)
  summary = summary "," pair("functions_verified", n) "," pair("total_obligations", n)
  summary = summary "," pair("total_proved", proved + 0) "," pair("total_unknown", unknown + 0)
  summary = summary "," pair("total_failed", 0) "," pair("total_timed_out", 0)
  summary = summary "," pair("total_skipped", 0) "," pair("total_runtime_checked", 0)
  emit(summary)
}' "$src" >&2
"#;

struct Scratch {
    root: PathBuf,
}

impl Scratch {
    fn new(name: &str) -> Self {
        let root = std::env::temp_dir()
            .join(format!("targo-trust-verify-cost-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).expect("create scratch directory");
        let trustc = root.join("trustc");
        fs::write(&trustc, FAKE_TRUSTC).expect("write fake trustc");
        fs::set_permissions(&trustc, fs::Permissions::from_mode(0o755)).expect("chmod fake trustc");
        Self { root }
    }

    fn trustc(&self) -> PathBuf {
        self.root.join("trustc")
    }

    fn run(&self, mode: &str, extra: &[&str]) -> Output {
        let out_dir = self.root.join(format!("out-{mode}-{}", extra.len()));
        Command::new(targo_trust_binary())
            .args(["trust", "benchmark", "verify-cost", "--functions", "16", "--trustc"])
            .arg(self.trustc())
            .arg("--out-dir")
            .arg(&out_dir)
            .args(extra)
            .env("FAKE_MODE", mode)
            .output()
            .expect("run verify-cost")
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

#[test]
fn help_is_rust_owned_and_listed() {
    let output = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "--help"])
        .output()
        .expect("run benchmark help");
    assert_eq!(output.status.code(), Some(0), "{}", text(&output));
    assert!(text(&output).contains("verify-cost"));
    let output = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "verify-cost", "--help"])
        .output()
        .expect("run verify-cost help");
    let out = text(&output);
    assert_eq!(output.status.code(), Some(0), "{out}");
    for needle in
        ["--trustc PATH", "--max-wall-s", "--max-rss-mb", "--by-shape", "Python is not used"]
    {
        assert!(out.contains(needle), "{needle:?} missing from help:\n{out}");
    }
}

#[test]
fn an_honest_run_within_budget_passes() {
    let scratch = Scratch::new("honest");
    let output = scratch.run("honest", &["--max-wall-s", "60", "--max-rss-mb", "100000"]);
    let out = text(&output);
    assert_eq!(output.status.code(), Some(0), "{out}");
    assert!(out.contains("PASS:"), "{out}");
    assert!(out.contains("16 proved of 16 reported (12 safety checks)"), "{out}");
    assert!(out.contains("trustc: rustc 9.9.9-fake"), "{out}");
}

#[test]
fn a_run_over_the_wall_budget_fails() {
    let scratch = Scratch::new("slow");
    let output = scratch.run("slow", &["--max-wall-s", "0.3", "--max-rss-mb", "100000"]);
    let out = text(&output);
    assert_eq!(output.status.code(), Some(1), "{out}");
    assert!(out.contains("over the 0.3 s budget"), "{out}");
    assert!(!out.contains("PASS:"), "{out}");
}

#[test]
fn a_run_over_the_memory_budget_fails() {
    let scratch = Scratch::new("rss");
    let output = scratch.run("honest", &["--max-wall-s", "60", "--max-rss-mb", "0.001"]);
    let out = text(&output);
    assert_eq!(output.status.code(), Some(1), "{out}");
    assert!(out.contains("over the 0.001 MB budget"), "{out}");
}

#[test]
fn an_unproved_obligation_fails_a_fast_run() {
    let scratch = Scratch::new("unknown");
    let output = scratch.run("unknown", &["--max-wall-s", "60", "--max-rss-mb", "100000"]);
    let out = text(&output);
    assert_eq!(output.status.code(), Some(1), "{out}");
    assert!(out.contains("overflow:add is unknown"), "{out}");
    assert!(out.contains("total_unknown = 1"), "{out}");
    assert!(!out.contains("PASS:"), "{out}");
}

#[test]
fn a_compiler_that_exits_nonzero_fails() {
    let scratch = Scratch::new("exit");
    let output = scratch.run("exit-1", &["--max-wall-s", "60", "--max-rss-mb", "100000"]);
    let out = text(&output);
    assert_eq!(output.status.code(), Some(1), "{out}");
    assert!(out.contains("the compiler exited 1: error: the fake refuses"), "{out}");
}

#[test]
fn usage_errors_exit_2() {
    let scratch = Scratch::new("usage");
    let missing = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "verify-cost", "--trustc"])
        .arg(scratch.root.join("absent"))
        .output()
        .expect("run with a missing trustc");
    assert_eq!(missing.status.code(), Some(2), "{}", text(&missing));
    let full = scratch.root.join("full");
    fs::create_dir_all(&full).expect("create full directory");
    fs::write(full.join("x"), "x").expect("fill directory");
    let non_empty = Command::new(targo_trust_binary())
        .args(["trust", "benchmark", "verify-cost", "--trustc"])
        .arg(scratch.trustc())
        .arg("--out-dir")
        .arg(&full)
        .output()
        .expect("run with a non-empty out-dir");
    assert_eq!(non_empty.status.code(), Some(2), "{}", text(&non_empty));
    assert!(text(&non_empty).contains("is not empty"));
}

fn targo_trust_binary() -> PathBuf {
    if let Some(path) = option_env!("CARGO_BIN_EXE_targo-trust") {
        return PathBuf::from(path);
    }
    let mut path: PathBuf = std::env::current_exe().expect("current test executable path");
    path.pop();
    if path.ends_with("deps") {
        path.pop();
    }
    path.push(format!("targo-trust{}", std::env::consts::EXE_SUFFIX));
    path
}
