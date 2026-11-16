//! `targo trust meter` (edit-loop plan step 1, METER) over fixture records:
//! a Rust `trust.package.v1` record, a Lean `trust.lean-run.v1` record, gate
//! run records and pre-push hook logs give the expected table, JSON and
//! `--check` exit codes; and a real `targo trust check <file.lean>` writes the
//! Lean record the meter reads.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, UNIX_EPOCH};

/// 2026-11-13 12:00 UTC: every fixture record's mtime, so the landed window
/// line is fixed.
const FIXTURE_MTIME_S: u64 = 1_794_571_200;

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

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests").join("fixtures").join("meter")
}

/// Copy the fixtures into a new directory, every file's mtime fixed.
fn workspace() -> tempfile::TempDir {
    fn copy(from: &Path, to: &Path) {
        fs::create_dir_all(to).unwrap();
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let target = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copy(&entry.path(), &target);
            } else {
                fs::copy(entry.path(), &target).unwrap();
                fs::File::options()
                    .write(true)
                    .open(&target)
                    .unwrap()
                    .set_modified(UNIX_EPOCH + Duration::from_secs(FIXTURE_MTIME_S))
                    .unwrap();
            }
        }
    }
    let dir = tempfile::tempdir().unwrap();
    copy(&fixtures(), dir.path());
    dir
}

fn meter(dir: &Path, args: &[&str]) -> Output {
    Command::new(targo_trust_binary())
        .current_dir(dir)
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .args(["trust", "meter"])
        .args(args)
        .output()
        .expect("run targo trust meter")
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("UTF-8 output")
}

/// Every source here measures every phase it knows: the table, largest wait
/// first, and `--check` exits 0. The Lean record lives in a target directory
/// with no package record, so the Rust record is left out of this run. The
/// gate run's legs that ran are each one check (its push-rows leg was not
/// judged, so it waited for nothing), and its checkout worker start-up, which
/// runs before the run's clock starts, is a row of its own added to the gate's
/// wait, not taken from `gate other`. Each hook lane is marked with the phase
/// that ran it.
#[test]
fn a_lean_run_a_gate_run_and_a_hook_log_fully_measured_give_the_table_and_check_passes() {
    let dir = workspace();
    fs::remove_dir_all(dir.path().join("target/trust/packages")).unwrap();
    let output = meter(
        dir.path(),
        &[
            "--target-dir",
            "target",
            "--gate-record",
            "runs/gate-complete/record.json",
            "--hook-log",
            "push-hook.txt",
            "--top",
            "0",
            "--check",
        ],
    );
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let lean = "target/trust/lean/Basics-0123456789abcdef.json";
    let gate = "runs/gate-complete/record.json";
    let expected = format!(
        "\
targo trust meter: read 3 source(s)
Waited: gate 27m 16s · push 31.0 s · lean 900 ms
No source read here records: compiles outside the gate and the hook, test runs outside the gate and the hook, tool rebuilds, the gate's waits before its run clock starts (such as build-slot admission and `land`'s publication lease, but not its checkout start-up), gate runs that end before making their run directory, the pre-push hook's time outside its `TIMING:` lines (a run refused before its `phase=prepare` line, and the steps after `hook-before-verdict`: the shadow launch and, when `land` hands the hook its `targo-trust` leg, `landing-hook-finish`'s checkout read)

     WAIT  PHASE                         ITEM                 SOURCE
  21m 31s  gate other (derived)          -                    {gate}
   3m 38s  gate checkout reads           3 reads              {gate}
   1m 20s  gate leg                      tcb-panic-ratchet    {gate}
   38.9 s  gate leg                      ir-cohort            {gate}
   22.0 s  push fast-lanes               -                    push-hook.txt
   21.0 s  push lane (in fast-lanes)     live.reach           push-hook.txt
    7.2 s  gate checkout start-up        -                    {gate}
    5.0 s  push scoped-lanes             -                    push-hook.txt
    4.0 s  push prepare                  -                    push-hook.txt
    3.0 s  push lane (in fast-lanes)     fast.seed-freshness  push-hook.txt
   850 ms  lean session start (prelude)  proofs/Basics.lean   {lean}
    30 ms  lean other (derived)          proofs/Basics.lean   {lean}
    15 ms  lean elaborate+kernel check   Basics.double_comm   {lean}
     3 ms  lean elaborate+kernel check   Basics.double        {lean}
     1 ms  lean import                   Helper               {lean}
    40 us  lean command                  [anonymous]          {lean}

Landed through the gate: 0 of 1 gate run(s), records written 2026-11-13 12:00 .. 2026-11-13 12:00 UTC; pushes made outside the gate are not in these records
Landed per agent-hour and per processor-hour: not derivable yet (no record holds the agent-hours or processor-hours behind a landed change)
Unread work: not derivable yet (no record says which computed results an agent read)
"
    );
    assert_eq!(stdout, expected, "stderr:\n{stderr}");
    assert!(stderr.is_empty(), "{stderr}");
}

/// The default table stops at 20 rows and says what it left out.
#[test]
fn the_default_table_is_bounded_and_names_what_it_left_out() {
    let dir = workspace();
    let output = meter(
        dir.path(),
        &[
            "--target-dir",
            "target",
            "--gate-runs",
            "runs",
            "--hook-log",
            "push-hook.txt",
            "--top",
            "3",
        ],
    );
    let stdout = text(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{stdout}");
    let table: Vec<&str> =
        stdout.lines().skip_while(|line| !line.trim_start().starts_with("WAIT")).collect();
    assert!(table[1].contains("gate other (derived)"), "{stdout}");
    assert!(table[4].starts_with("… "), "{stdout}");
    assert!(table[4].contains("--top 0 prints every row"), "{stdout}");
}

/// A Rust package record yields its proof time, and the five compiler phases
/// no timer measures yet are named: `--check` exits 1 naming each. Those
/// phases are waits of the package's that its row `time_ms` sum leaves out,
/// so the proof wait is never called totalled.
#[test]
fn a_rust_package_record_names_the_compiler_phases_not_measured_and_check_fails() {
    let dir = workspace();
    fs::remove_dir_all(dir.path().join("target/trust/lean")).unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.contains("Waited: proof 4.2 s + untotalled\n"), "{stdout}");
    let json = meter(dir.path(), &["--target-dir", "target", "--json"]);
    let value: serde_json::Value = serde_json::from_slice(&json.stdout).unwrap();
    assert_eq!(
        value["waited"]["proof"],
        serde_json::json!({"every_source_totalled": false, "wait_us": 4_200_000})
    );
    assert!(
        stdout.contains(
            "    4.2 s  rust proof (row time_ms sum)  demo  target/trust/packages/demo.json\n"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("Landed: not derivable yet (no gate run record was read)\n"));
    assert!(
        stderr.starts_with("targo trust meter --check: 5 phase(s) not measured:\n"),
        "{stderr}"
    );
    for phase in ["load", "std-decode", "obligation-generation", "solving", "kernel-check"] {
        let line = format!(
            "  rust {phase} demo (target/trust/packages/demo.json): not measured: needs compiler \
             phase timers (PKG-LIVE-1 remaining)\n"
        );
        assert!(stderr.contains(&line), "missing {line:?} in\n{stderr}");
        assert!(
            stdout.contains(&format!(
                "  rust {phase}: not measured: needs compiler phase timers (PKG-LIVE-1 \
                 remaining): demo (target/trust/packages/demo.json)\n"
            )),
            "{stdout}"
        );
    }
}

/// The JSON names the same rows, the phases not measured, landed changes
/// from a gate record whose push exited 0, and what no record can say.
#[test]
fn the_json_carries_rows_missing_phases_and_landed_changes() {
    let dir = workspace();
    let output = meter(
        dir.path(),
        &[
            "--target-dir",
            "target",
            "--gate-runs",
            "runs",
            "--hook-log",
            "push-hook-unavailable.txt",
            "--json",
        ],
    );
    let stdout = text(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{stdout}");
    // Canonical JSON: one object on one line, one LF.
    assert!(stdout.starts_with("{\"complete\":false,") && stdout.ends_with("}\n"), "{stdout}");
    assert_eq!(stdout.matches('\n').count(), 1, "{stdout}");
    let value: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(value["schema"], "trust.meter.v1");
    assert_eq!(value["complete"], false);
    assert_eq!(
        value["not_recorded"],
        serde_json::json!([
            "compiles outside the gate and the hook",
            "test runs outside the gate and the hook",
            "tool rebuilds",
            "the gate's waits before its run clock starts (such as build-slot admission and \
             `land`'s publication lease, but not its checkout start-up)",
            "gate runs that end before making their run directory",
            "the pre-push hook's time outside its `TIMING:` lines (a run refused before its \
             `phase=prepare` line, and the steps after `hook-before-verdict`: the shadow launch \
             and, when `land` hands the hook its `targo-trust` leg, `landing-hook-finish`'s \
             checkout read)"
        ])
    );
    let rows = value["rows"].as_array().unwrap();
    let waits: Vec<u64> = rows.iter().map(|row| row["wait_us"].as_u64().unwrap()).collect();
    assert!(waits.windows(2).all(|pair| pair[0] >= pair[1]), "largest wait first: {waits:?}");
    assert_eq!(
        rows[0],
        serde_json::json!({
            "category": "gate", "count": 1, "derived": true, "item": "-",
            "phase": "gate other (derived)", "source": "runs/gate-complete/record.json",
            "wait_us": 1_291_183_422u64,
        })
    );
    let row = |phase: &str, item: &str| {
        rows.iter()
            .find(|row| row["phase"] == phase && row["item"] == item)
            .unwrap_or_else(|| panic!("no row {phase} {item} in {stdout}"))
            .clone()
    };
    assert_eq!(row("rust proof (row time_ms sum)", "demo")["wait_us"], 4_200_000);
    assert_eq!(row("lean elaborate+kernel check", "Basics.double_comm")["wait_us"], 15_000);
    assert_eq!(row("lean session start (prelude)", "proofs/Basics.lean")["wait_us"], 850_000);
    // The landed run's legs: 400 s less 183 s and 38.9 s.
    let landed_other = rows
        .iter()
        .find(|row| {
            row["phase"] == "gate other (derived)"
                && row["source"] == "runs/gate-landed/record.json"
        })
        .unwrap();
    assert_eq!(landed_other["wait_us"], 178_100_000);
    // gate-complete's checkout worker start-up: python 0.023644 s + native
    // 7.173539 s, before the run's clock, so outside `seconds` and its
    // derived remainder (1629.6 s less 80.6, 38.9 and 218.916578 s of reads).
    assert_eq!(row("gate checkout start-up", "-")["wait_us"], 7_197_183);
    assert_eq!(row("push prepare", "-")["wait_us"], 4_000_000);
    assert_eq!(
        value["waited"]["push"],
        serde_json::json!({"every_source_totalled": true, "wait_us": 9_000_000})
    );
    let missing: Vec<(String, String)> = value["not_measured"]
        .as_array()
        .unwrap()
        .iter()
        .map(|missing| {
            (missing["phase"].as_str().unwrap().into(), missing["item"].as_str().unwrap().into())
        })
        .collect();
    assert!(
        missing.contains(&("push lane (in fast-lanes)".into(), "live.reach".into())),
        "{missing:?}"
    );
    assert!(missing.contains(&("gate ordinary push".into(), "-".into())), "{missing:?}");
    assert!(missing.contains(&("rust solving".into(), "demo".into())), "{missing:?}");
    // push-rows of gate-landed and of gate-rows, and gate-rows' crates-tests
    // and ui-trust: legs of several rows with only a total.
    let row_times: Vec<&(String, String)> =
        missing.iter().filter(|(phase, _)| phase == "gate row time").collect();
    assert_eq!(row_times.len(), 4, "{missing:?}");
    // gate-landed has no `checkout_startup`.
    assert!(missing.contains(&("gate checkout start-up".into(), "-".into())), "{missing:?}");
    assert_eq!(missing.len(), 12, "{missing:?}");
    assert_eq!(value["landed"]["gate_runs"], 3);
    assert_eq!(value["landed"]["through_gate"], 1);
    assert_eq!(value["landed"]["window"]["from_unix_s"], FIXTURE_MTIME_S);
    assert_eq!(value["landed"]["per_agent_hour"]["absent"], "PKG-LIVE-1");
    assert_eq!(value["unread_work"]["absent"], "PKG-LIVE-1");
}

/// A hook lane whose clock was unavailable, and a gate record that pushed
/// without a time, each fail `--check` by name.
#[test]
fn an_unavailable_hook_clock_and_an_untimed_push_fail_check_by_name() {
    let dir = workspace();
    let output = meter(dir.path(), &["--hook-log", "push-hook-unavailable.txt", "--check"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  push lane (in fast-lanes) \
         live.reach (push-hook-unavailable.txt): elapsed_s=unavailable\n"
    );
    let output = meter(dir.path(), &["--gate-record", "runs/gate-landed/record.json", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(stdout.contains("Landed through the gate: 1 of 1 gate run(s)"), "{stdout}");
    assert!(
        stderr.contains("gate ordinary push - (runs/gate-landed/record.json): record.json keeps")
    );
    assert!(
        stderr.starts_with("targo trust meter --check: 3 phase(s) not measured:\n"),
        "{stderr}"
    );
}

/// A gate leg that runs several rows records only its total: `--check` names
/// its per-row time as not measured, for push-rows, a leg of several targets
/// and a suite leg, while a leg that is one check (tidy) passes and a leg that
/// did not run is neither a row nor a missing phase.
#[test]
fn a_gate_leg_of_several_rows_fails_check_on_its_per_row_time() {
    let dir = workspace();
    let output = meter(
        dir.path(),
        &["--gate-record", "runs/gate-rows/record.json", "--top", "0", "--check"],
    );
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    let why = "record.json keeps only the leg's total `seconds`; needs per-row time in \
               scripts/land_gate.py's run record (PKG-LIVE-1 remaining)";
    assert_eq!(
        stderr,
        format!(
            "targo trust meter --check: 3 phase(s) not measured:\n  gate row time crates-tests \
             (runs/gate-rows/record.json): its plan names 3 target(s), each one row or more; \
             {why}\n  gate row time push-rows (runs/gate-rows/record.json): it runs \
             push-profile rows (`bash tests/run_trust_comprehensive_harness.sh --list push`), and \
             its log has no per-row time; {why}\n  gate row time ui-trust \
             (runs/gate-rows/record.json): it is not a leg the meter knows to be one check \
             (compiler-check, tidy, tcb-panic-ratchet, ir-cohort, olean-audit), so it may run \
             several rows; {why}\n"
        )
    );
    // Each leg's total is still a row; 700 s less 120, 300, 200, 30 and 20.
    for (wait, leg) in [
        ("5m 00s", "crates-tests"),
        ("3m 20s", "ui-trust"),
        ("2m 00s", "push-rows"),
        ("30.0 s", "tidy"),
    ] {
        assert!(
            stdout.lines().any(|line| line.trim_start().starts_with(wait)
                && line.contains("gate leg")
                && line.split_whitespace().any(|word| word == leg)),
            "{wait} {leg} in\n{stdout}"
        );
    }
    assert!(stdout.contains("   30.0 s  gate other (derived)  "), "{stdout}");
    assert!(!stdout.contains("compiler-unit-tests"), "{stdout}");
    assert!(!stdout.contains("gate checkout start-up"), "a run with no pool: {stdout}");

    // `targets` is the leg's plan, written before the cache answers for some
    // members: the reason counts those, and never says the leg ran them all.
    let record = dir.path().join("runs/gate-rows/record.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&record).unwrap()).unwrap();
    value["legs"]["crates-tests"]["cached_members"] = serde_json::json!(["crates/b", "crates/z"]);
    fs::write(&record, serde_json::to_string(&value).unwrap()).unwrap();
    let output = meter(dir.path(), &["--gate-record", "runs/gate-rows/record.json", "--check"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains(
            "gate row time crates-tests (runs/gate-rows/record.json): its plan names 3 target(s), \
             1 of them answered by a cached PASS, each one row or more; "
        ),
        "{stderr}"
    );
    assert!(!stderr.contains("it runs 3 target(s)"), "{stderr}");
}

/// A `--gate-record` named on the command line but written before the
/// window is a source that yields nothing: `--check` fails naming it, rather
/// than passing on the sources left.
#[test]
fn a_named_gate_record_outside_the_window_fails_check() {
    let dir = workspace();
    fs::File::options()
        .write(true)
        .open(dir.path().join("runs/gate-complete/record.json"))
        .unwrap()
        .set_modified(UNIX_EPOCH + Duration::from_secs(1_577_836_800))
        .unwrap();
    let output = meter(
        dir.path(),
        &[
            "--hook-log",
            "push-hook.txt",
            "--gate-record",
            "runs/gate-complete/record.json",
            "--window",
            "1h",
            "--check",
        ],
    );
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(stdout.starts_with("targo trust meter: read 1 source(s)\n"), "{stdout}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  records - \
         (runs/gate-complete/record.json): the record was not written in the window (or its file \
         time cannot be read)\n"
    );
}

/// A source named on the command line that yields nothing fails `--check`;
/// a malformed argument is a usage error.
#[test]
fn an_empty_source_fails_check_and_a_bad_argument_is_a_usage_error() {
    let dir = workspace();
    let empty = dir.path().join("empty");
    fs::create_dir(&empty).unwrap();
    let output = meter(dir.path(), &["--target-dir", "empty", "--check"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(text(&output.stderr).contains("records - (empty): no trust.package.v1 record"));
    for bad in [&["--window", "3w"][..], &["--top", "x"], &["--frobnicate"], &["--hook-log"]] {
        let output = meter(dir.path(), bad);
        assert_eq!(output.status.code(), Some(2), "{bad:?}");
        assert!(text(&output.stderr).contains("Usage: targo trust meter"), "{bad:?}");
    }
}

/// The Lean case end to end: a real `targo trust check <file.lean>` writes
/// its `trust.lean-run.v1` record under `--target-dir`, and the meter reads
/// it. The session start (the kernel prelude) is measured. Clean's module
/// batch, which the lane runs, times no declaration yet, so `--check` names
/// the per-declaration phase as not measured, with that reason, rather than
/// reading the empty list as nothing elaborated.
#[test]
fn a_real_lean_check_writes_the_record_the_meter_reads() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("Double.lean"),
        "def double (n : Nat) : Nat := n + n\ntheorem double_zero : double 0 = 0 := rfl\n",
    )
    .unwrap();
    let check = || {
        Command::new(targo_trust_binary())
            .current_dir(dir.path())
            .args(["trust", "check", "Double.lean", "--target-dir", "out"])
            .output()
            .expect("run targo trust check")
    };
    let first = check();
    assert_eq!(
        first.status.code(),
        Some(0),
        "stdout:\n{}\nstderr:\n{}",
        text(&first.stdout),
        text(&first.stderr)
    );
    let records: Vec<PathBuf> = fs::read_dir(dir.path().join("out/trust/lean"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    assert_eq!(records.len(), 1, "{records:?}");
    let name = records[0].file_name().unwrap().to_string_lossy().into_owned();
    assert!(name.starts_with("Double-") && name.ends_with(".json"), "{name}");
    let record: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&records[0]).unwrap()).unwrap();
    assert_eq!(record["schema"], "trust.lean-run.v1");
    assert_eq!(record["outcome"], "accepted");
    assert_eq!(record["registered"], serde_json::json!(["double", "double_zero"]), "{record}");
    assert_eq!(record["files"], serde_json::json!(["Double.lean"]));
    let attempts = record["cost"]["attempts"].as_array().unwrap();
    assert_eq!(attempts.len(), 1, "{record}");
    assert!(attempts[0]["session_start_us"].as_u64().unwrap() > 0, "{record}");
    let total = record["cost"]["wall_clock_us"].as_u64().unwrap();
    assert!(total >= attempts[0]["check_us"].as_u64().unwrap(), "{record}");

    // A rerun of the same invocation replaces its own record.
    assert_eq!(check().status.code(), Some(0));
    assert_eq!(fs::read_dir(dir.path().join("out/trust/lean")).unwrap().count(), 1);

    let output = meter(dir.path(), &["--target-dir", "out", "--json", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stdout}\n{stderr}");
    let value: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let phases: Vec<(&str, &str)> = value["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| (row["phase"].as_str().unwrap(), row["item"].as_str().unwrap()))
        .collect();
    // No declaration is timed, so the remainder carries their elaboration
    // and kernel check, and its name says so.
    for expected in [
        ("lean session start (prelude)", "Double.lean"),
        ("lean other incl. elaboration+kernel check (derived)", "Double.lean"),
    ] {
        assert!(phases.contains(&expected), "{expected:?} not in {phases:?}");
    }
    let missing = value["not_measured"].as_array().unwrap();
    assert_eq!(missing.len(), 1, "{stdout}");
    assert_eq!(missing[0]["phase"], "lean elaborate+kernel check");
    assert!(
        missing[0]["why"].as_str().unwrap().starts_with("not measured: Clean's module batch"),
        "{stdout}"
    );
    assert!(stderr.contains("lean elaborate+kernel check Double.lean ("), "{stderr}");
}

/// Set the modification time of `path`, a file or a directory.
fn set_mtime(path: &Path, time: std::time::SystemTime) {
    fs::File::open(path).unwrap().set_modified(time).unwrap();
}

/// The gate writes record.json only when a run ends, so a run that was
/// interrupted or is still running leaves a directory of logs and no record.
/// Its wait is real: `--gate-runs` names that directory as not measured, so
/// `--check` fails where it passed on the complete run alone, the landed line
/// says the run is not counted, and the gate wait is not called totalled.
#[test]
fn a_gate_run_that_left_no_record_fails_check_by_name() {
    let dir = tempfile::tempdir().unwrap();
    let runs = dir.path().join("runs");
    fs::create_dir_all(runs.join("a")).unwrap();
    fs::copy(fixtures().join("runs/gate-complete/record.json"), runs.join("a/record.json"))
        .unwrap();
    let output = meter(dir.path(), &["--gate-runs", "runs", "--check"]);
    assert_eq!(output.status.code(), Some(0), "{}", text(&output.stderr));
    assert!(text(&output.stdout).contains("Waited: gate 27m 16s\n"), "{}", text(&output.stdout));

    fs::create_dir(runs.join("b")).unwrap();
    fs::write(runs.join("b/push-rows.log"), "push-rows: running fast.seed-freshness\n").unwrap();
    let output = meter(dir.path(), &["--gate-runs", "runs", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  records - (runs/b): run left no \
         record.json (interrupted, still running, or stopped by an error before writing it); \
         its time is not measured\n"
    );
    assert!(
        stdout.contains(
            "Landed through the gate: 0 of 1 gate run(s) (1 more run(s) left no record.json and \
             are not counted), records written"
        ),
        "{stdout}"
    );
    assert!(stdout.contains("Waited: gate 27m 16s + untotalled\n"), "{stdout}");
    let output = meter(dir.path(), &["--gate-runs", "runs", "--json"]);
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(value["landed"]["runs_without_record"], 1);
    assert_eq!(value["complete"], false);
    assert_eq!(value["waited"]["gate"]["every_source_totalled"], false, "{value}");
}

/// A record or log the meter cannot read, or one that names another schema,
/// is a source whose wait is in no total: it is named as not measured, and
/// its category's wait is not called totalled, even when it is the only one.
#[test]
fn a_source_the_meter_cannot_read_leaves_its_category_untotalled() {
    let dir = workspace();
    fs::remove_dir_all(dir.path().join("target/trust/packages")).unwrap();
    fs::write(dir.path().join("target/trust/lean/Broken-0000000000000000.json"), "{").unwrap();
    fs::write(dir.path().join("other-schema.json"), "{\"schema\":\"trust-land-gate/1\"}\n")
        .unwrap();
    let output = meter(
        dir.path(),
        &[
            "--target-dir",
            "target",
            "--gate-record",
            "other-schema.json",
            "--hook-log",
            "no-such-hook.txt",
            "--json",
        ],
    );
    let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    for category in ["lean", "gate", "push"] {
        assert_eq!(
            value["waited"][category]["every_source_totalled"], false,
            "{category}: {value}"
        );
    }
    // The readable Lean record's own total is still summed.
    assert_eq!(value["waited"]["lean"]["wait_us"], 900_000, "{value}");
    let unread: Vec<&str> = value["not_measured"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|missing| missing["phase"] == "records")
        .map(|missing| missing["source"].as_str().unwrap())
        .collect();
    assert_eq!(
        unread,
        ["other-schema.json", "target/trust/lean/Broken-0000000000000000.json", "no-such-hook.txt"],
        "{value}"
    );
    let output = meter(dir.path(), &["--hook-log", "no-such-hook.txt"]);
    assert!(text(&output.stdout).contains("Waited: push 0 us + untotalled\n"));
}

/// When `land` hands the `targo-trust` leg to the ordinary push, the leg has
/// no exit or time in the record, and the push that ran it leaves
/// `live_targo`: the leg's time is named as not measured, not read as a leg
/// that waited for nothing. The same leg with no `live_targo` (no push ran)
/// did not run and is neither a row nor a missing phase.
#[test]
fn a_leg_land_handed_to_the_ordinary_push_names_its_time_not_measured() {
    let dir = workspace();
    let record = dir.path().join("runs/gate-landed/record.json");
    let mut value: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&record).unwrap()).unwrap();
    value["legs"]["targo-trust"] = serde_json::json!({
        "selected": true, "reasons": ["fixture"], "command": ["true"], "targets": null,
        "outcome": "PENDING (ordinary pre-push execution, not a PASS)",
    });
    fs::write(&record, serde_json::to_string(&value).unwrap()).unwrap();
    let run = || {
        let output =
            meter(dir.path(), &["--gate-record", "runs/gate-landed/record.json", "--check"]);
        assert_eq!(output.status.code(), Some(1), "{}", text(&output.stderr));
        text(&output.stderr)
    };
    let stderr = run();
    assert!(!stderr.contains("targo-trust"), "{stderr}");

    value["legs"]["targo-trust"]["outcome"] = "PASS (executed by ordinary pre-push)".into();
    value["live_targo"] = serde_json::json!({"mode": "ordinary push mandatory suite",
                                             "state": "complete", "error": null});
    fs::write(&record, serde_json::to_string(&value).unwrap()).unwrap();
    let stderr = run();
    assert!(
        stderr.contains(
            "  gate leg targo-trust (runs/gate-landed/record.json): `land` handed the leg to the \
             ordinary push (`live_targo`), whose pre-push hook runs it; record.json keeps no exit \
             or time for it, so any time it took is inside the push's, in `gate other`\n"
        ),
        "{stderr}"
    );
}

/// `--window` judges a run directory without a record by its newest file: a
/// record-less run whose files all predate the window is not a source, one
/// with a file inside it is named, and a directory holding only old runs
/// still says it yielded nothing in the window.
#[test]
fn the_window_judges_a_run_without_a_record_by_its_newest_file() {
    let dir = tempfile::tempdir().unwrap();
    let runs = dir.path().join("runs");
    let old = UNIX_EPOCH + Duration::from_secs(1_577_836_800);
    for run in ["old", "new"] {
        fs::create_dir_all(runs.join(run)).unwrap();
        fs::write(runs.join(run).join("crates-tests.log"), "log\n").unwrap();
        set_mtime(&runs.join(run).join("crates-tests.log"), old);
        set_mtime(&runs.join(run), old);
    }
    // The new run's newest file is now: its older file and directory times
    // do not move it out of the window.
    fs::write(runs.join("new/ui-trust.log"), "log\n").unwrap();
    set_mtime(&runs.join("new"), old);
    let output = meter(dir.path(), &["--gate-runs", "runs", "--window", "1d", "--check"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  records - (runs/new): run left \
         no record.json (interrupted, still running, or stopped by an error before writing \
         it); its time is not measured\n"
    );

    fs::remove_dir_all(runs.join("new")).unwrap();
    let output = meter(dir.path(), &["--gate-runs", "runs", "--window", "1d", "--check"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        text(&output.stderr),
        "targo trust meter --check: 1 phase(s) not measured:\n  records - (runs): no \
         */record.json under it in the window\n"
    );
}

/// Per-declaration Lean time is measured only when every declaration the
/// batch registered was timed: a record that times two of three names the
/// phase as not measured, naming the untimed one, and its remainder row says
/// it holds their elaboration and kernel check.
#[test]
fn a_lean_run_that_times_some_declarations_fails_check_naming_the_untimed() {
    let dir = workspace();
    fs::remove_dir_all(dir.path().join("target/trust/packages")).unwrap();
    let record = dir.path().join("target/trust/lean/Basics-0123456789abcdef.json");
    let text_of_record = fs::read_to_string(&record).unwrap();
    let names = "\"registered\":[\"Basics.double\",\"Basics.double_comm\"],";
    assert!(text_of_record.contains(names));
    fs::write(
        &record,
        text_of_record.replace(
            names,
            "\"registered\":[\"Basics.double\",\"Basics.double_comm\",\"Basics.triple\"],",
        ),
    )
    .unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(
        stderr.starts_with(
            "targo trust meter --check: 1 phase(s) not measured:\n  lean elaborate+kernel check \
             proofs/Basics.lean (target/trust/lean/Basics-0123456789abcdef.json): not measured: \
             Clean's module batch"
        ),
        "{stderr}"
    );
    assert!(
        stderr.ends_with(" (1 of 3 registered declaration(s) untimed: Basics.triple)\n"),
        "{stderr}"
    );
    // Some declarations are timed, so the reason never says none is.
    assert!(stderr.contains("did not time every declaration it registered"), "{stderr}");
    assert!(!stderr.contains("times no declaration"), "{stderr}");
    assert!(
        stdout.contains("lean other incl. untimed elaboration+kernel check (derived)"),
        "{stdout}"
    );
    // The timed declarations are still rows of their own.
    assert!(
        stdout.lines().any(|line| line.contains("  lean elaborate+kernel check  ")
            && line.contains("Basics.double_comm")),
        "{stdout}"
    );
}

/// Coverage is judged by name, not by count. Clean's timer can time a
/// declaration the batch then leaves unregistered (Trust's island policy
/// refuses it), so a record that times two declarations of a batch that
/// registered two can still leave a registered one untimed: `--check` names
/// it, the refused declaration's time stays a row of its own, and a record
/// that gives only a count (no names) cannot be judged complete.
#[test]
fn a_lean_run_whose_timed_set_is_not_the_registered_set_fails_check_by_name() {
    let dir = workspace();
    fs::remove_dir_all(dir.path().join("target/trust/packages")).unwrap();
    let record = dir.path().join("target/trust/lean/Basics-0123456789abcdef.json");
    let original = fs::read_to_string(&record).unwrap();
    let names = "\"registered\":[\"Basics.double\",\"Basics.double_comm\"],";
    assert!(original.contains(names));
    assert!(original.contains("\"name\":\"Basics.double_comm\""));
    // Two timed, two registered: `Basics.double` and the policy-refused
    // `Basics.refused_by_strict_policy` timed; `Basics.half` registered but
    // untimed.
    let equal_counts = original
        .replace(names, "\"registered\":[\"Basics.double\",\"Basics.half\"],")
        .replace("\"name\":\"Basics.double_comm\"", "\"name\":\"Basics.refused_by_strict_policy\"");
    fs::write(&record, &equal_counts).unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert!(
        stderr.starts_with(
            "targo trust meter --check: 1 phase(s) not measured:\n  lean elaborate+kernel check \
             proofs/Basics.lean (target/trust/lean/Basics-0123456789abcdef.json): not measured: \
             Clean's module batch"
        ),
        "{stderr}"
    );
    assert!(
        stderr.ends_with(" (1 of 2 registered declaration(s) untimed: Basics.half)\n"),
        "{stderr}"
    );
    // Some declarations are timed, so the reason never says none is.
    assert!(stderr.contains("did not time every declaration it registered"), "{stderr}");
    assert!(!stderr.contains("times no declaration"), "{stderr}");
    assert!(
        stdout.contains("lean other incl. untimed elaboration+kernel check (derived)"),
        "{stdout}"
    );
    assert!(!stdout.contains("lean other (derived)"), "{stdout}");
    assert!(
        stdout.lines().any(|line| line.contains("  lean elaborate+kernel check  ")
            && line.contains("Basics.refused_by_strict_policy")),
        "{stdout}"
    );

    // Every registered declaration untimed, but others timed: still "did not
    // time every declaration", never "times no declaration".
    fs::write(&record, original.replace(names, "\"registered\":[\"Basics.half\"],")).unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("did not time every declaration it registered"), "{stderr}");
    assert!(stderr.ends_with(" (1 of 1 registered declaration(s) untimed: Basics.half)\n"));
    assert!(!stderr.contains("times no declaration"), "{stderr}");
    assert!(stdout.contains("lean other incl. untimed elaboration+kernel check (derived)"));

    // Nothing registered and nothing timed, but a session start recorded:
    // the batch may have elaborated and refused each declaration, so the
    // remainder says it may hold that time, and the reason does not say
    // nothing was elaborated, nor that the session surely started (the
    // producer records a failed start's time too).
    let refused = original
        .replace(names, "\"registered\":[],")
        .replace("\"kind\":\"declaration\"", "\"kind\":\"command\"");
    fs::write(&record, refused).unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.ends_with(
            ": the batch registered no declaration after its recorded session start (it refused \
             each one or had none, or the session failed to start), so any declaration's \
             elaboration and kernel check is untimed and inside the `lean other incl. \
             elaboration+kernel check (derived)` row\n"
        ),
        "{stderr}"
    );
    assert!(stdout.contains("lean other incl. elaboration+kernel check (derived)"), "{stdout}");

    // A count is not names: the meter cannot say which declarations it covers.
    fs::write(&record, original.replace(names, "\"registered\":2,")).unwrap();
    let output = meter(dir.path(), &["--target-dir", "target", "--top", "0", "--check"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.ends_with(
            ": the record names no `registered` declarations, so 2 timed declaration(s) cannot \
             be judged complete\n"
        ),
        "{stderr}"
    );
}

/// With no target directory named, a `.lean` check run from a workspace
/// member's directory writes its records under the workspace root's target/,
/// where Cargo writes a crate-mode check's package records: its timing record
/// and, with a caller session, its `trust.obligations.v1` record and snapshot,
/// all by one resolver. A bare `targo trust meter` run from the same
/// directory reads the timing record there.
#[test]
fn the_default_target_dir_is_the_workspace_roots_from_a_subdirectory() {
    let dir = tempfile::tempdir().unwrap();
    let root = fs::canonicalize(dir.path()).unwrap();
    fs::write(root.join("Cargo.toml"), "[workspace]\nmembers = [\"member\"]\nresolver = \"2\"\n")
        .unwrap();
    let member = root.join("member");
    fs::create_dir_all(member.join("src")).unwrap();
    fs::write(
        member.join("Cargo.toml"),
        "[package]\nname = \"member\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
    )
    .unwrap();
    fs::write(member.join("src/lib.rs"), "").unwrap();
    fs::write(member.join("Double.lean"), "def double (n : Nat) : Nat := n + n\n").unwrap();
    let check = Command::new(targo_trust_binary())
        .current_dir(&member)
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .env_remove("CLAUDE_CODE_SESSION_ID")
        .env("ATERM_SESSION_ID", "meter-workspace-root")
        .args(["trust", "check", "Double.lean"])
        .output()
        .expect("run targo trust check");
    assert_eq!(check.status.code(), Some(0), "{}", text(&check.stderr));
    assert!(!member.join("target").exists(), "the record went under the member");
    let records: Vec<PathBuf> = fs::read_dir(root.join("target/trust/lean"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    assert_eq!(records.len(), 1, "{records:?}");
    let obligations = fs::read_dir(root.join("target/trust/obligations")).unwrap().count();
    assert_eq!(obligations, 1, "the obligation record under the workspace root's target/");
    let snapshots = fs::read_dir(root.join("target/trust/snapshots"))
        .unwrap()
        .filter(|entry| entry.as_ref().unwrap().path().is_file())
        .count();
    assert_eq!(snapshots, 1, "the snapshot under the workspace root's target/");

    let output = meter(&member, &["--json"]);
    let stdout = text(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{stdout}\n{}", text(&output.stderr));
    let value: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    let sources: Vec<&str> = value["sources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|source| source["path"].as_str().unwrap())
        .collect();
    assert_eq!(sources, [records[0].to_str().unwrap()], "{stdout}");
}

/// A gate run whose boundaries were partly answered by the last complete
/// pass (`SourceBinding`, READS-ONCE-WINDOW-1): only complete passes count as
/// checkout reads, and reused boundaries, which read no file, are counted
/// apart, in the table and in the JSON. Each boundary's Git-state guard
/// (`guard_seconds`) is its own row, out of the derived remainder.
#[test]
fn reused_checkout_boundaries_are_counted_apart_from_reads() {
    let dir = workspace();
    let gate = "gate-reused/record.json";
    let output = meter(dir.path(), &["--gate-record", gate, "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(0), "stdout:\n{stdout}\nstderr:\n{stderr}");
    // 400 s less the legs (60 + 90), the three complete passes (40 + 45 +
    // 50) and the eight guards (19 s).
    let expected = format!(
        "\
targo trust meter: read 1 source(s)
Waited: gate 6m 40s
No source read here records: compiles outside the gate and the hook, test runs outside the gate and the hook, tool rebuilds, the gate's waits before its run clock starts (such as build-slot admission and `land`'s publication lease, but not its checkout start-up), gate runs that end before making their run directory, the pre-push hook's time outside its `TIMING:` lines (a run refused before its `phase=prepare` line, and the steps after `hook-before-verdict`: the shadow launch and, when `land` hands the hook its `targo-trust` leg, `landing-hook-finish`'s checkout read)

     WAIT  PHASE                 ITEM                          SOURCE
   2m 15s  gate checkout reads   3 reads, 5 reused boundaries  {gate}
   1m 36s  gate other (derived)  -                             {gate}
   1m 30s  gate leg              tcb-panic-ratchet             {gate}
   1m 00s  gate leg              ir-cohort                     {gate}
   19.0 s  gate checkout guard   8 guarded boundaries          {gate}

Landed through the gate: 0 of 1 gate run(s), records written 2026-11-13 12:00 .. 2026-11-13 12:00 UTC; pushes made outside the gate are not in these records
Landed per agent-hour and per processor-hour: not derivable yet (no record holds the agent-hours or processor-hours behind a landed change)
Unread work: not derivable yet (no record says which computed results an agent read)
"
    );
    assert_eq!(stdout, expected, "stderr:\n{stderr}");
    assert!(!stdout.contains("8 reads"), "reused boundaries are never reads: {stdout}");

    let output = meter(dir.path(), &["--gate-record", gate, "--json"]);
    let stdout = text(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{stdout}");
    let value: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(
        value["sources"][0]["checkout"],
        serde_json::json!({"reads": 3, "reused_boundaries": 5})
    );
    let rows = value["rows"].as_array().unwrap();
    let row = |phase: &str| {
        rows.iter()
            .find(|row| row["phase"] == phase)
            .unwrap_or_else(|| panic!("no row {phase} in {stdout}"))
            .clone()
    };
    assert_eq!(row("gate checkout reads")["item"], "3 reads, 5 reused boundaries");
    assert_eq!(row("gate checkout reads")["wait_us"], 135_000_000);
    assert_eq!(row("gate checkout guard")["item"], "8 guarded boundaries");
    assert_eq!(row("gate checkout guard")["wait_us"], 19_000_000);
    assert_eq!(row("gate other (derived)")["wait_us"], 96_000_000);

    // A reused boundary that read the Git state without timing it fails
    // `--check` by name rather than being taken as free.
    let path = dir.path().join(gate);
    let mut record: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
    record["checkout_checks"][7].as_object_mut().unwrap().remove("guard_seconds");
    fs::write(&path, serde_json::to_string(&record).unwrap()).unwrap();
    let output = meter(dir.path(), &["--gate-record", gate, "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(
        stderr,
        format!(
            "targo trust meter --check: 1 phase(s) not measured:\n  gate checkout guard before \
             final record ({gate}): the reused boundary read the Git state but has no \
             `guard_seconds`\n"
        )
    );
    assert!(stdout.contains("3 reads, 5 reused boundaries"), "{stdout}");
    assert!(stdout.contains("7 guarded boundaries"), "{stdout}");
}

/// A record's `seconds` longer than any run since gate records began (the
/// epoch-minus-uptime the gate wrote before its run-clock fix) is not a wall
/// time: `--check` names the gate total as not measured, with that one reason
/// and not a second, false "has no `seconds`", and no `gate other` row is
/// derived from it. A `seconds` that is no non-negative number and an absent
/// one each give their own single reason.
#[test]
fn a_gate_record_whose_seconds_is_not_a_wall_time_fails_check() {
    let dir = workspace();
    let record = dir.path().join("runs/gate-complete/record.json");
    let original = fs::read_to_string(&record).unwrap();
    assert!(original.contains("\"seconds\": 1629.6,"), "{original}");
    let mtime = fs::metadata(&record).unwrap().modified().unwrap();
    let check_with = |replacement: &str| {
        fs::write(&record, original.replace("\"seconds\": 1629.6,", replacement)).unwrap();
        fs::File::options().write(true).open(&record).unwrap().set_modified(mtime).unwrap();
        let output = meter(
            dir.path(),
            &["--gate-record", "runs/gate-complete/record.json", "--top", "0", "--check"],
        );
        let stdout = text(&output.stdout);
        let stderr = text(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
        assert!(!stdout.contains("gate other (derived)"), "{stdout}");
        assert!(stdout.contains("gate leg"), "the legs are still rows: {stdout}");
        assert!(stdout.contains("Waited: gate 0 us + untotalled\n"), "{stdout}");
        stderr
    };
    let one_reason = |why: &str| {
        format!(
            "targo trust meter --check: 1 phase(s) not measured:\n  gate total - \
             (runs/gate-complete/record.json): {why}\n"
        )
    };
    assert_eq!(
        check_with("\"seconds\": 1794570000.0,"),
        one_reason(
            "`seconds` is 1794570000 s, longer than any run since gate records began (2026-01-01 \
             00:00 UTC); not a wall time (scripts/land_gate.py before its run-clock fix wrote \
             epoch minus uptime there in development and source-diagnostic runs)"
        )
    );
    assert_eq!(
        check_with("\"seconds\": -5.0,"),
        one_reason("the record's `seconds` is `-5.0`, not a non-negative number of seconds")
    );
    assert_eq!(
        check_with("\"seconds\": \"1629.6\","),
        one_reason("the record's `seconds` is `\"1629.6\"`, not a non-negative number of seconds")
    );
    assert_eq!(check_with(""), one_reason("the record has no `seconds`"));
}

/// A gate run's checkout worker start-up is outside `seconds`, so when the
/// record's `checkout_startup` is unreadable, absent or not an object, the
/// phase is named, `--check` fails, and the gate's wait is not called totalled.
#[test]
fn a_gate_record_with_an_unreadable_checkout_start_up_is_not_totalled() {
    let dir = workspace();
    let record = dir.path().join("runs/gate-complete/record.json");
    let original: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&record).unwrap()).unwrap();
    assert!(original["checkout_startup"]["native_seconds"].is_number(), "{original}");
    let mut unreadable = original.clone();
    unreadable["checkout_startup"]["native_seconds"] = serde_json::json!("unavailable");
    let mut absent = original.clone();
    absent.as_object_mut().unwrap().remove("checkout_startup");
    let mut not_an_object = original.clone();
    not_an_object["checkout_startup"] = serde_json::json!("pending");
    for (case, value) in [("unreadable", unreadable), ("absent", absent), ("text", not_an_object)] {
        fs::write(&record, serde_json::to_string(&value).unwrap()).unwrap();
        let args = ["--gate-record", "runs/gate-complete/record.json"];
        let output = meter(dir.path(), &[&args[..], &["--json"]].concat());
        let value: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(value["waited"]["gate"]["every_source_totalled"], false, "{case}: {value}");
        assert_eq!(value["not_measured"][0]["phase"], "gate checkout start-up", "{case}: {value}");
        let output = meter(dir.path(), &[&args[..], &["--check"]].concat());
        assert_eq!(output.status.code(), Some(1), "{case}: {}", text(&output.stderr));
    }
}

/// A hook log whose last run stopped before its verdict: the earlier run's
/// total is read, `--check` names the last run's total as not measured, and
/// the push wait is not called totalled.
#[test]
fn a_hook_log_whose_last_run_has_no_verdict_fails_check() {
    let dir = workspace();
    let log = dir.path().join("push-hook.txt");
    let mut text_of_log = fs::read_to_string(&log).unwrap();
    text_of_log.push_str("pre-push: development main push hook\n");
    text_of_log.push_str("TIMING: phase=prepare lane=- elapsed_s=6 exit=- clock=bash-seconds\n");
    fs::write(&log, text_of_log).unwrap();
    let output = meter(dir.path(), &["--hook-log", "push-hook.txt", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  push hook total - \
         (push-hook.txt): the last hook run stopped before its verdict: 1 `TIMING:` line(s) \
         follow the last `phase=hook-before-verdict`, and its total is not in the hook total\n"
    );
    assert!(stdout.contains("Waited: push 31.0 s + untotalled\n"), "{stdout}");
}

/// The hook writes `phase=prepare` first in every run, so a `prepare` line
/// after lines with no verdict between starts a new run: the run before it
/// stopped before its verdict. Every such run is named, not only the last,
/// and a lane it left with no phase line after it is marked unfinished, not
/// filed under the next run's `prepare`.
#[test]
fn a_hook_log_with_an_earlier_run_stopped_before_its_verdict_fails_check() {
    let dir = workspace();
    let log = dir.path().join("push-hook.txt");
    let complete = fs::read_to_string(&log).unwrap();
    let stopped = "pre-push: development main push hook\n\
                   TIMING: phase=prepare lane=- elapsed_s=2 exit=- clock=bash-seconds\n\
                   TIMING: phase=lane lane=lane.a elapsed_s=1 exit=0 clock=bash-seconds\n";
    fs::write(&log, format!("{stopped}{complete}")).unwrap();
    let output = meter(dir.path(), &["--hook-log", "push-hook.txt", "--top", "0", "--check"]);
    let stdout = text(&output.stdout);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  push hook total - \
         (push-hook.txt): 1 hook run(s) stopped before their verdict, so their totals are not in \
         the hook total: 1 run(s) end at the next run's `phase=prepare` line with no \
         `phase=hook-before-verdict` before it\n"
    );
    assert!(
        stdout.lines().any(|line| line.contains("  push lane (in an unfinished phase)  ")
            && line.contains("lane.a")),
        "{stdout}"
    );
    assert!(!stdout.contains("(in prepare)"), "{stdout}");
    assert!(stdout.contains("Waited: push 31.0 s + untotalled\n"), "{stdout}");

    // The last run stopped too: both runs are counted in the one reason.
    fs::write(&log, format!("{stopped}{complete}{stopped}")).unwrap();
    let output = meter(dir.path(), &["--hook-log", "push-hook.txt", "--check"]);
    let stderr = text(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert_eq!(
        stderr,
        "targo trust meter --check: 1 phase(s) not measured:\n  push hook total - \
         (push-hook.txt): 2 hook run(s) stopped before their verdict, so their totals are not in \
         the hook total: 1 run(s) end at the next run's `phase=prepare` line with no \
         `phase=hook-before-verdict` before it, and the last run, 2 `TIMING:` line(s), ends the \
         log without one\n"
    );
}

/// `targo trust help` names the meter with the meter's own synopsis (the
/// opening lines of `targo trust meter --help`, joined), so the index lists
/// every option the meter takes, each repeatable source as repeatable, and
/// says `--check` exits 1.
#[test]
fn the_help_index_carries_the_meters_own_synopsis() {
    let run = |args: &[&str]| {
        let output = Command::new(targo_trust_binary())
            .args(["trust"])
            .args(args)
            .output()
            .expect("run targo trust");
        assert!(output.status.success(), "{args:?}: {}", text(&output.stderr));
        text(&output.stdout)
    };
    let own = run(&["meter", "--help"]);
    let synopsis: Vec<&str> =
        own.lines().take_while(|line| !line.is_empty()).map(str::trim).collect();
    let synopsis = synopsis.join(" ");
    let synopsis = synopsis.strip_prefix("Usage: ").expect("the meter's help opens with its usage");
    let index = run(&["help"]);
    let line = index
        .lines()
        .map(str::trim_start)
        .find(|line| line.starts_with("targo trust meter "))
        .expect("the help index names the meter");
    let (named, summary) = line.split_once("  ").expect("a synopsis, then the summary");
    assert_eq!(named, synopsis);
    assert!(summary.contains("--check exits 1 naming every phase not measured"), "{summary}");
}
