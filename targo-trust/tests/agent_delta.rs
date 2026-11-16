//! Live-edit-loop step 2 (DELTA), the exit test: after an edit the agent sees
//! only the rows that changed and one summary line per package; a rerun with
//! no edit is one line; agents sharing a target directory never diff against
//! each other's runs.
//!
//! Lean is driven end to end: `targo-trust check <file.lean>` checks the file
//! in process with the linked Clean kernel, writes its `trust.obligations.v1`
//! record (a row for the file's verdict and one per declaration Clean parsed)
//! and snapshot, and prints the delta. Every assertion is on the check's whole
//! stdout: its verdict line, the changed rows (and every row not proved, which
//! prints on every run), the summary line and the capability line, nothing
//! else.
//!
//! Rust is driven here through the same snapshot and comparison layer by
//! `targo-trust delta` over `trust.obligations.v1` records this test writes in
//! the format a crate check writes (the reader refuses any other); running the
//! Rust verifier inside this test needs a sealed `trustc` and is not done. The
//! crate-mode check's own path — the production record writer over a real
//! `trustc` capture, the snapshot, and the terminal report with and without a
//! base — is `report::tests::a_real_runs_terminal_report_shows_only_what_changed_since_the_callers_base`.
//! A compile error is driven the same way here (a record with a
//! `compile_error` line); the path from Cargo's `compiler-message` stream to
//! that line is `agent_delta::tests::a_compile_error_is_a_row_keyed_by_file_code_and_message_and_prints_on_every_run`.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

/// The variables a caller session is read from (`agent_delta::CALLER_SESSION_ENV`).
const SESSION_ENV: [&str; 2] = ["ATERM_SESSION_ID", "CLAUDE_CODE_SESSION_ID"];

fn binary() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_targo-trust"))
}

/// A command for the caller `session` (or none), with the target directory
/// `target` and nothing inherited that names another session or target.
fn command(session: Option<&str>, target: &Path, cwd: &Path) -> Command {
    let mut command = Command::new(binary());
    for name in SESSION_ENV {
        command.env_remove(name);
    }
    if let Some(session) = session {
        command.env("ATERM_SESSION_ID", session);
    }
    command.env("CARGO_TARGET_DIR", target).env_remove("CARGO_BUILD_TARGET_DIR").current_dir(cwd);
    command
}

fn text(output: &Output) -> (String, String) {
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// The token a summary line names as `(now <token>)`.
fn now_token(summary: &str) -> String {
    let start = summary.find("(now ").expect("a summary line names its token") + 5;
    summary[start..start + 16].to_string()
}

// --- Rust: records of a crate check ------------------------------------------------

const FUNCTIONS: usize = 40;
const PER_FUNCTION: usize = 5;
const KINDS: [&str; PER_FUNCTION] =
    ["overflow:add", "overflow:mul", "overflow:sub", "divzero", "remzero"];

fn local_id(function: usize, index: usize) -> String {
    format!("{:08x}{:08x}", function * 7919 + 1, index * 104_729 + 3)
}

fn source_digest(function: usize, edited: bool) -> String {
    format!("{:064x}", function * 1_000_003 + usize::from(edited))
}

/// A crate's `trust.obligations.v1` record: forty functions of five proved
/// obligations each. `edited` is the function whose body changed: its source
/// digest moves, its division row is refuted, its overflow on `*` is still
/// proved but now rests on a `requires-link` premise, and its remainder row
/// moved down a line.
fn crate_record(edited: Option<usize>) -> String {
    let mut out = String::new();
    out.push_str(concat!(
        r#"{"schema":"trust.obligations.v1","package":"delta-fixture","lane":"strict","#,
        r#""policy":"strict","selection":"default","seal":{"absent":"A8"},"#,
        r#""targo_trust_commit":"0123456789abcdef0123456789abcdef01234567","#,
        r#""profile":"c870797a6939da587fae99d7b0aa4c5e64be43e1e0798966417b011f955f05f9","#,
        r#""outcome":"measured","vector":"00","coverage_complete":true,"concluded":true,"#,
        r#""degraded_anchors":0}"#,
        "\n"
    ));
    for function in 0..FUNCTIONS {
        let is_edited = edited == Some(function);
        let name = format!("delta_fixture::f{function:02}");
        out.push_str(&format!(
            "{{\"fn\":\"{name}\",\"source\":\"{}\"}}\n",
            source_digest(function, is_edited)
        ));
        let mut rows: Vec<(String, String)> = (0..PER_FUNCTION)
            .map(|index| {
                let status = if is_edited && index == 3 { "failed" } else { "proved" };
                let (encoding, discharge, basis) = if status == "proved" {
                    ("unvalidated-encoder", "solver-asserted", "")
                } else {
                    ("ungraded", "ungraded", ",\"basis\":\"refuted\"")
                };
                let premises = if is_edited && index == 1 { "\"requires-link\"" } else { "" };
                let line = function * 8 + 2 + index + usize::from(is_edited && index == 4);
                let id = local_id(function, index);
                (
                    id.clone(),
                    format!(
                        "{{\"key\":\"{name}#{id}\",\"kind\":\"{}\",\"status\":\"{status}\",\
                         \"stop\":\"solved\",\"file\":\"src/lib.rs\",\"line\":{line},\"col\":13,\
                         \"encoding\":\"{encoding}\",\"discharge\":\"{discharge}\",\
                         \"premises\":[{premises}]{basis}}}\n",
                        KINDS[index]
                    ),
                )
            })
            .collect();
        rows.sort();
        for (_, row) in rows {
            out.push_str(&row);
        }
    }
    out
}

fn delta(session: Option<&str>, target: &Path, record: &Path, extra: &[&str]) -> Vec<String> {
    let output = command(session, target, target)
        .arg("trust")
        .arg("delta")
        .args(extra)
        .arg("--target-dir")
        .arg(target)
        .arg(record)
        .output()
        .expect("run targo-trust delta");
    let (stdout, stderr) = text(&output);
    assert!(output.status.success(), "delta failed\nstdout:\n{stdout}\nstderr:\n{stderr}");
    stdout.lines().map(str::to_string).collect()
}

#[test]
fn rust_records_print_only_the_edited_function_and_one_line_when_unchanged() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let before = root.path().join("before.ndjson");
    let after = root.path().join("after.ndjson");
    std::fs::write(&before, crate_record(None)).expect("write record");
    std::fs::write(&after, crate_record(Some(17))).expect("write record");
    let total = FUNCTIONS * PER_FUNCTION;

    // First run of session A: no base, one line naming the token.
    let first = delta(Some("session-a"), &target, &before, &[]);
    assert_eq!(first.len(), 1, "{first:?}");
    assert!(first[0].starts_with(&format!("delta-fixture  {total} obligation(s)  (now ")));
    let base = now_token(&first[0]);
    assert!(target.join("trust/snapshots").join(&base).is_file());

    // A rerun with no edit: one line.
    let again = delta(Some("session-a"), &target, &before, &[]);
    assert_eq!(again, [format!("delta-fixture  0 of {total} changed since {base}  (now {base})")]);

    // One function edited: its changed rows, each with the listing's label,
    // and one summary line. The refuted row and the proof that now rests on a
    // new premise changed; the remainder row only moved a line.
    let edited = delta(Some("session-a"), &target, &after, &[]);
    assert_eq!(edited.len(), 3, "{edited:#?}");
    assert!(edited[0].starts_with("LOST        [FAILED]  delta_fixture::f17#"), "{edited:#?}");
    assert!(edited[0].contains("divzero  failed (was proved)  solved"), "{edited:#?}");
    assert!(edited[1].starts_with("CHANGED     [PROVED]  delta_fixture::f17#"), "{edited:#?}");
    assert!(
        edited[1].contains(
            "overflow:mul  proved (graded unvalidated-encoder/solver-asserted+requires-link, was \
             unvalidated-encoder/solver-asserted)"
        ),
        "{edited:#?}"
    );
    let now = now_token(&edited[2]);
    assert_ne!(now, base);
    assert_eq!(edited[2], format!("delta-fixture  2 of {total} changed since {base}  (now {now})"));

    // Session B shares the target directory: its first run has no base of its
    // own, and A's runs are not one.
    let other = delta(Some("session-b"), &target, &before, &[]);
    assert_eq!(other, [format!("delta-fixture  {total} obligation(s)  (now {base})")]);
    // A's next run diffs against A's own last run (`after`), not B's: nothing
    // changed, and the refuted row prints again, as every failing row does.
    let mine = delta(Some("session-a"), &target, &after, &[]);
    assert_eq!(mine.len(), 2, "{mine:#?}");
    assert!(mine[0].starts_with("STILL       [FAILED]  delta_fixture::f17#"), "{mine:#?}");
    assert_eq!(mine[1], format!("delta-fixture  0 of {total} changed since {now}  (now {now})"));
    // B's next run diffs against B's own (`before`).
    let theirs = delta(Some("session-b"), &target, &after, &[]);
    assert_eq!(theirs.len(), 3, "{theirs:#?}");
    assert!(theirs[2].contains(&format!("2 of {total} changed since {base}")));

    // `--since` names any snapshot, and a caller with no session gets the full
    // count with no base.
    let since = delta(None, &target, &before, &["--since", &now]);
    assert_eq!(since.len(), 3, "{since:#?}");
    assert!(since[0].starts_with("CHANGED     [PROVED]  delta_fixture::f17#"), "{since:#?}");
    assert!(since[1].starts_with("GAINED      [PROVED]  delta_fixture::f17#"), "{since:#?}");
    assert!(since[1].contains("divzero  proved (was failed)"), "{since:#?}");
    let nobody = delta(None, &target, &before, &[]);
    assert_eq!(nobody, [format!("delta-fixture  {total} obligation(s)  (now {base})")]);

    // `--all-rows` lists every row as well.
    let all = delta(Some("session-c"), &target, &before, &["--all-rows"]);
    assert_eq!(all.len(), total + 1);
}

/// The key a check gives a compile error: file, code, and the first twelve
/// hex digits of the SHA-256 of the whitespace-normalized message
/// (`obligations::compile_error_key`).
fn compile_error_key(file: &str, code: &str, message: &str) -> String {
    use sha2::Digest;
    let digest = sha2::Sha256::digest(message.as_bytes());
    let hex: String = digest[..6].iter().map(|byte| format!("{byte:02x}")).collect();
    format!("{file}#{code}-{hex}")
}

const MISMATCH: &str = "mismatched types";

/// The record a crate check writes for the fixture crate when an edit broke
/// its build: the package could not run (no unit published coverage, so no
/// function and no obligation is recorded) and the record carries the
/// compiler's error, at `line` of `src/lib.rs`.
fn broken_record(line: usize) -> String {
    format!(
        concat!(
            r#"{{"schema":"trust.obligations.v1","package":"delta-fixture","lane":"strict","#,
            r#""policy":"strict","selection":"default","seal":{{"absent":"A8"}},"#,
            r#""targo_trust_commit":"0123456789abcdef0123456789abcdef01234567","#,
            r#""profile":"c870797a6939da587fae99d7b0aa4c5e64be43e1e0798966417b011f955f05f9","#,
            r#""outcome":"could-not-run","vector":"00","coverage_complete":false,"#,
            r#""concluded":false,"degraded_anchors":0}}"#,
            "\n",
            r#"{{"compile_error":"{key}","code":"E0308","message":"{message}","#,
            r#""file":"src/lib.rs","line":{line},"col":18}}"#,
            "\n"
        ),
        key = compile_error_key("src/lib.rs", "E0308", MISMATCH),
        message = MISMATCH,
        line = line,
    )
}

/// A compile error is a row: it prints while the build is broken, on every
/// run, under a key an edit elsewhere in the file does not move; fixing it is
/// one `CLEARED` line beside what changed since the last run that compiled;
/// and a rerun with nothing failing is one line.
#[test]
fn a_compile_error_prints_until_it_is_fixed_and_its_key_survives_unrelated_edits() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let clean = root.path().join("clean.ndjson");
    let broken = root.path().join("broken.ndjson");
    std::fs::write(&clean, crate_record(None)).expect("write record");
    let total = FUNCTIONS * PER_FUNCTION;
    let key = compile_error_key("src/lib.rs", "E0308", MISMATCH);

    let first = delta(Some("s"), &target, &clean, &[]);
    let base = now_token(&first[0]);

    // An edit breaks the build: the error row, the header facts that moved,
    // and a summary that says the obligations were not compared.
    std::fs::write(&broken, broken_record(6)).expect("write record");
    let lines = delta(Some("s"), &target, &broken, &[]);
    assert_eq!(lines.len(), 4, "{lines:#?}");
    assert_eq!(lines[0], format!("NEW ERROR   [ERROR E0308]  {key}  {MISMATCH}  src/lib.rs:6:18"));
    assert_eq!(lines[1], "RUN         coverage_complete true -> false");
    assert_eq!(lines[2], "RUN         outcome measured -> could-not-run");
    let first_broken = now_token(&lines[3]);
    assert_eq!(
        lines[3],
        format!(
            "delta-fixture  1 compiler error(s); obligations not compared since {base}  \
             (now {first_broken})"
        )
    );

    // Lines inserted above the error: the same key, at its new line, still
    // printed, and still compared with the last run that compiled.
    std::fs::write(&broken, broken_record(9)).expect("write record");
    let lines = delta(Some("s"), &target, &broken, &[]);
    assert_eq!(lines.len(), 4, "{lines:#?}");
    assert_eq!(lines[0], format!("STILL       [ERROR E0308]  {key}  {MISMATCH}  src/lib.rs:9:18"));
    let moved = now_token(&lines[3]);
    assert_ne!(moved, first_broken, "the record carries the error's location");
    assert!(lines[3].contains(&format!("not compared since {base}")), "{lines:#?}");

    // The same broken build again: nothing changed, and the error prints.
    let again = delta(Some("s"), &target, &broken, &[]);
    assert_eq!(again, lines, "a failing build prints its error on every run");

    // Fixed: the error goes away in one line, and nothing else changed since
    // the run before the break.
    let fixed = delta(Some("s"), &target, &clean, &[]);
    assert_eq!(
        fixed,
        [
            format!("CLEARED     [ERROR E0308]  {key}  {MISMATCH}  src/lib.rs:9:18"),
            format!("delta-fixture  0 of {total} changed since {base}  (now {base})"),
        ]
    );

    // A rerun with nothing failing: one line.
    let rerun = delta(Some("s"), &target, &clean, &[]);
    assert_eq!(rerun, [format!("delta-fixture  0 of {total} changed since {base}  (now {base})")]);

    // A caller whose first run is the broken build sees the error with no base.
    let fresh = delta(Some("t"), &target, &broken, &[]);
    assert_eq!(
        fresh,
        [
            format!("[ERROR E0308]  {key}  {MISMATCH}  src/lib.rs:9:18"),
            format!("delta-fixture  1 compiler error(s); 0 obligation(s)  (now {moved})"),
        ]
    );
}

/// The records a crate check writes when a dependency of the fixture crate
/// did not compile: the fixture crate was never built (no unit of it
/// published coverage, so its record did not conclude and holds no function),
/// and the dependency `helper` carries the error.
fn dependency_broken_records(dir: &Path) -> (PathBuf, PathBuf) {
    let header = |package: &str| {
        format!(
            concat!(
                r#"{{"schema":"trust.obligations.v1","package":"{package}","lane":"strict","#,
                r#""policy":"strict","selection":"default","seal":{{"absent":"A8"}},"#,
                r#""targo_trust_commit":"0123456789abcdef0123456789abcdef01234567","#,
                r#""profile":"c870797a6939da587fae99d7b0aa4c5e64be43e1e0798966417b011f955f05f9","#,
                r#""outcome":"could-not-run","vector":"00","coverage_complete":false,"#,
                r#""concluded":false,"degraded_anchors":0}}"#,
                "\n"
            ),
            package = package
        )
    };
    let fixture = dir.join("unbuilt.ndjson");
    let helper = dir.join("helper.ndjson");
    std::fs::write(&fixture, header("delta-fixture")).expect("write record");
    std::fs::write(
        &helper,
        format!(
            "{}{{\"compile_error\":\"{}\",\"code\":\"E0308\",\"message\":\"{MISMATCH}\",\
             \"file\":\"src/lib.rs\",\"line\":2,\"col\":5}}\n",
            header("helper"),
            compile_error_key("src/lib.rs", "E0308", MISMATCH)
        ),
    )
    .expect("write record");
    (fixture, helper)
}

/// A dependency that did not compile leaves the selected crate unbuilt. Its
/// record did not conclude, so its 200 obligations are not compared (never
/// 40 `REMOVED` rows), and it does not become the base: after the fix the
/// view compares with the last run that concluded and says `0 of 200`.
#[test]
fn a_dependency_that_did_not_compile_neither_empties_nor_rebases_the_crate() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let clean = root.path().join("clean.ndjson");
    std::fs::write(&clean, crate_record(None)).expect("write record");
    let total = FUNCTIONS * PER_FUNCTION;
    let key = compile_error_key("src/lib.rs", "E0308", MISMATCH);
    let base = now_token(&delta(Some("s"), &target, &clean, &[])[0]);

    let (unbuilt, helper) = dependency_broken_records(root.path());
    let record = |path: &Path| path.to_str().expect("utf-8 path").to_string();
    let helper_path = record(&helper);
    let lines = delta(Some("s"), &target, &unbuilt, &[&helper_path]);
    assert!(lines.iter().all(|line| !line.starts_with("REMOVED")), "{lines:#?}");
    // The records in the order named: the dependency (given first), then
    // the crate.
    assert_eq!(lines.len(), 5, "{lines:#?}");
    assert_eq!(lines[0], format!("[ERROR E0308]  {key}  {MISMATCH}  src/lib.rs:2:5"));
    assert!(lines[1].starts_with("helper  1 compiler error(s); 0 obligation(s)  (now "));
    assert_eq!(lines[2], "RUN         coverage_complete true -> false");
    assert_eq!(lines[3], "RUN         outcome measured -> could-not-run");
    let unbuilt_token = now_token(&lines[4]);
    assert_eq!(
        lines[4],
        format!(
            "delta-fixture  not concluded; obligations not compared since {base}  \
             (now {unbuilt_token})"
        )
    );

    // The dependency fixed: the crate's record is the one before the break,
    // compared with the last run that concluded.
    let fixed = delta(Some("s"), &target, &clean, &[]);
    assert_eq!(fixed, [format!("delta-fixture  0 of {total} changed since {base}  (now {base})")]);
}

#[test]
fn a_snapshot_unused_for_a_week_is_removed_when_another_is_written() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let before = root.path().join("before.ndjson");
    let after = root.path().join("after.ndjson");
    std::fs::write(&before, crate_record(None)).expect("write record");
    std::fs::write(&after, crate_record(Some(3))).expect("write record");
    let base = now_token(&delta(Some("a"), &target, &before, &[])[0]);
    let old = target.join("trust/snapshots").join(&base);
    let eight_days = std::time::Duration::from_secs(8 * 24 * 60 * 60);
    std::fs::File::options()
        .write(true)
        .open(&old)
        .and_then(|file| file.set_modified(std::time::SystemTime::now() - eight_days))
        .expect("age the snapshot");
    let now = now_token(delta(Some("b"), &target, &after, &[]).last().expect("a line"));
    assert!(!old.exists(), "a snapshot unused for 8 days is removed");
    assert!(target.join("trust/snapshots").join(now).is_file());
    // A's base is gone: A is told so and gets the full count.
    let lines = delta(Some("a"), &target, &before, &[]);
    assert!(lines[0].starts_with("note: your previous snapshot"), "{lines:#?}");
    assert!(lines[1].contains("obligation(s)"), "{lines:#?}");
}

// --- Lean: a real check of a `.lean` file ------------------------------------------

const DECLARATIONS: usize = 50;

fn lean_source(edit: Option<&str>) -> String {
    let mut out = String::from("namespace Fixture\n\n");
    for index in 0..DECLARATIONS {
        let declaration = if index % 2 == 0 {
            format!("theorem t{index:02} : {index} = {index} := rfl\n")
        } else {
            format!("def d{index:02} : Nat := {index}\n")
        };
        out.push_str(&declaration);
        out.push('\n');
    }
    out.push_str("end Fixture\n");
    match edit {
        Some(edit) => out.replace("theorem t08 : 8 = 8 := rfl", edit),
        None => out,
    }
}

fn lean_check(session: &str, target: &Path, dir: &Path, file: &Path) -> (Output, Vec<String>) {
    let output = command(Some(session), target, dir)
        .arg("check")
        .arg(file)
        .output()
        .expect("run targo-trust check on a .lean file");
    let (stdout, _) = text(&output);
    (output, stdout.lines().map(str::to_string).collect())
}

/// The capability line every `.lean` check ends with.
const CAPABILITY: &str = "checked in process by the Clean CIC kernel; `.lean` imports resolve from \
                          local source only; external `.olean` imports are unsupported";

/// The whole stdout of a check of `file`: its verdict line, `middle`, and the
/// capability line.
fn whole(verdict: &str, middle: &[String]) -> Vec<String> {
    let mut lines = vec![verdict.to_string()];
    lines.extend(middle.iter().cloned());
    lines.push(CAPABILITY.to_string());
    lines
}

#[test]
fn lean_declarations_print_only_the_edited_declaration_and_one_line_when_unchanged() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let dir = root.path().join("src");
    std::fs::create_dir_all(&dir).expect("source dir");
    let file = dir.join("Fixture.lean");
    std::fs::write(&file, lean_source(None)).expect("write fixture");
    let package = std::fs::canonicalize(&file).expect("canonical").display().to_string();
    let proved =
        format!("PROVED {} — {DECLARATIONS} declaration(s) kernel-checked", file.display());
    let rejected = format!("REJECTED {}", file.display());
    // One row per declaration and one for the file's own verdict.
    let rows = DECLARATIONS + 1;

    let (output, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert!(output.status.success(), "{stdout:#?}\n{}", text(&output).1);
    assert_eq!(stdout.len(), 3, "{stdout:#?}");
    let base = now_token(&stdout[1]);
    assert_eq!(stdout, whole(&proved, &[format!("{package}  {rows} obligation(s)  (now {base})")]));
    // The record holds one row per declaration under its stable name.
    let record = std::fs::read_to_string(target.join("trust/snapshots").join(&base))
        .expect("the snapshot is stored");
    assert_eq!(record.matches("\"key\":\"Fixture.t08#").count(), 1, "{record}");
    assert_eq!(record.matches("\"status\":\"proved\"").count(), rows, "{record}");

    // A rerun with no edit: one line besides the verdict and capability lines.
    let (_, stdout) = lean_check("lean-a", &target, &dir, &file);
    let unchanged =
        |token: &str| format!("{package}  0 of {rows} changed since {token}  (now {token})");
    assert_eq!(stdout, whole(&proved, &[unchanged(&base)]));

    // A reformat and a comment change no row: N is 0. The token moves,
    // because the record carries each row's location and the later
    // declarations moved down three lines.
    std::fs::write(
        &file,
        lean_source(Some("-- reformatted\ntheorem   t08 :\n    8 = 8 :=\n  rfl")),
    )
    .expect("reformat");
    let (_, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert_eq!(stdout.len(), 3, "{stdout:#?}");
    assert!(
        stdout[1].starts_with(&format!("{package}  0 of {rows} changed since {base}")),
        "{stdout:#?}"
    );
    let reformatted = now_token(&stdout[1]);
    assert_ne!(reformatted, base, "locations moved, so the record and its token did");

    // One declaration's statement edited: its old claim vanished and its new
    // one is proved; nothing else is printed.
    std::fs::write(&file, lean_source(Some("theorem t08 : 8 + 0 = 8 := rfl"))).expect("edit");
    let (output, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert!(output.status.success(), "{stdout:#?}");
    assert_eq!(stdout.len(), 5, "{stdout:#?}");
    assert!(stdout[1].starts_with("GAINED      [PROVED]  Fixture.t08#"), "{stdout:#?}");
    assert!(stdout[2].starts_with("VANISHED    Fixture.t08#"), "{stdout:#?}");
    assert!(stdout[3].starts_with(&format!("{package}  2 of {rows} changed since {reformatted}")));
    assert_eq!(stdout[4], CAPABILITY);
    let edited = now_token(&stdout[3]);

    // One declaration's proof broken. The batch is all or nothing, so the file
    // row and that declaration are failed (their proof rejected, not their
    // statement refuted) and the other 49, which the refused batch did not
    // decide, are unknown: every one is its own LOST line.
    std::fs::write(&file, lean_source(Some("theorem t08 : 8 + 0 = 8 := Nat.le_refl 3")))
        .expect("break");
    let (output, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert!(!output.status.success(), "a broken proof is rejected: {stdout:#?}");
    expect_refused(&stdout, &rejected, &package, &edited, rows, Some("Fixture.t08#"));
    let broken = now_token(&stdout[stdout.len() - 2]);

    // The same broken file again: nothing changed, and every row that is not
    // proved prints again, so the failure is never reduced to a count.
    let (output, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert!(!output.status.success());
    assert_eq!(stdout.len(), rows + 3, "{stdout:#?}");
    assert_eq!(stdout[0], rejected);
    assert!(stdout[1].starts_with(&format!("STILL       [{FAILED_CLOSED}]  <file>#")));
    assert!(stdout[2].starts_with(&format!("STILL       [{FAILED_CLOSED}]  Fixture.t08#")));
    assert!(stdout[3..rows + 1].iter().all(|l| l.starts_with("STILL       [UNKNOWN]  Fixture.")));
    assert_eq!(stdout[rows + 1], unchanged(&broken));

    // Fixed again: the same rows come back, GAINED, and nothing else.
    std::fs::write(&file, lean_source(Some("theorem t08 : 8 + 0 = 8 := rfl"))).expect("fix");
    let (output, stdout) = lean_check("lean-a", &target, &dir, &file);
    assert!(output.status.success(), "{stdout:#?}");
    assert_eq!(stdout.len(), rows + 4, "{stdout:#?}");
    assert_eq!(stdout[1], "RUN         coverage_complete false -> true");
    assert!(stdout[2..rows + 2].iter().all(|l| l.starts_with("GAINED      [PROVED]  ")));
    assert!(stdout[rows + 2].starts_with(&format!("{package}  {rows} of {rows} changed since ")));
    assert_eq!(now_token(&stdout[rows + 2]), edited, "the fixed file's record is the edited one's");

    // Session B shares the target directory and has no base of its own.
    let (_, stdout) = lean_check("lean-b", &target, &dir, &file);
    assert_eq!(
        stdout,
        whole(&proved, &[format!("{package}  {rows} obligation(s)  (now {edited})")])
    );
}

/// The listing's label of a row that failed with nothing refuting it: a Lean
/// declaration whose proof was rejected.
const FAILED_CLOSED: &str = "FAILED: unproved, no counterexample; failed closed";

/// A refused run's whole stdout against an accepted base: the verdict line,
/// the coverage change, the file row LOST (failed), the declaration `failed`
/// names LOST (failed), every other declaration LOST (unknown, undecided) on
/// its own line, the summary line and the capability line.
fn expect_refused(
    stdout: &[String],
    rejected: &str,
    package: &str,
    base: &str,
    rows: usize,
    failed: Option<&str>,
) {
    let failing = 1 + usize::from(failed.is_some());
    assert_eq!(stdout.len(), rows + 4, "{stdout:#?}");
    assert_eq!(stdout[0], rejected);
    assert_eq!(stdout[1], "RUN         coverage_complete true -> false");
    let lost = |l: &String, label: &str, key: &str, status: &str| {
        l.starts_with(&format!("LOST        [{label}]  {key}"))
            && l.contains(&format!("{status} (was proved)"))
    };
    assert!(lost(&stdout[2], FAILED_CLOSED, "<file>#", "failed"), "{stdout:#?}");
    assert!(
        stdout[2].contains("failed (was proved)  solver-incomplete"),
        "not `solved`: {stdout:#?}"
    );
    if let Some(key) = failed {
        assert!(lost(&stdout[3], FAILED_CLOSED, key, "failed"), "{stdout:#?}");
    }
    assert!(
        stdout[2 + failing..rows + 2]
            .iter()
            .all(|l| lost(l, "UNKNOWN", "Fixture.", "unknown") && l.contains("not-dispatched")),
        "{stdout:#?}"
    );
    assert!(
        stdout[rows + 2].starts_with(&format!("{package}  {rows} of {rows} changed since {base}")),
        "{stdout:#?}"
    );
    assert_eq!(stdout[rows + 3], CAPABILITY);
}

/// The review's regressions: `rfl` replaced by `sorry` (refused by the
/// publish audit, whose diagnostic is placed at byte 0, not in the theorem)
/// and an error in no declaration (`#check` of a missing name) each change the
/// record and show LOST rows; neither leaves a row `proved`.
#[test]
fn a_sorry_or_an_error_outside_every_declaration_is_never_proved() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let dir = root.path().join("src");
    std::fs::create_dir_all(&dir).expect("source dir");
    let file = dir.join("Fixture.lean");
    std::fs::write(&file, lean_source(None)).expect("write fixture");
    let package = std::fs::canonicalize(&file).expect("canonical").display().to_string();
    let rejected = format!("REJECTED {}", file.display());
    let rows = DECLARATIONS + 1;

    let (_, stdout) = lean_check("s", &target, &dir, &file);
    let base = now_token(&stdout[1]);

    std::fs::write(&file, lean_source(Some("theorem t08 : 8 = 8 := sorry"))).expect("sorry");
    let (output, stdout) = lean_check("s", &target, &dir, &file);
    assert!(!output.status.success(), "{stdout:#?}");
    // The publish audit names the declaration that reached `sorry`.
    expect_refused(&stdout, &rejected, &package, &base, rows, Some("Fixture.t08#"));
    let sorry = now_token(&stdout[rows + 2]);
    let record = std::fs::read_to_string(target.join("trust/snapshots").join(&sorry)).unwrap();
    assert!(!record.contains("\"status\":\"proved\""), "{record}");

    // Back to the accepted file, then a `#check` of a missing name at column 0.
    std::fs::write(&file, lean_source(None)).expect("restore");
    let (output, _) = lean_check("s", &target, &dir, &file);
    assert!(output.status.success());
    std::fs::write(&file, format!("{}#check nonexistentThing\n", lean_source(None)))
        .expect("check");
    let (output, stdout) = lean_check("s", &target, &dir, &file);
    assert!(!output.status.success(), "{stdout:#?}");
    // No declaration is refused: the file row is, and all 50 are undecided.
    expect_refused(&stdout, &rejected, &package, &base, rows, None);
    assert_ne!(
        now_token(&stdout[rows + 2]),
        base,
        "a rejected file never has the accepted file's token"
    );
}

/// LEAN-PROVED-BESIDE-REFUSED-1, driven through the real two-file check. One
/// invocation is one all-or-nothing Clean batch: with `B.lean` rejected, the
/// batch commits nothing, so `A.lean`, whose own declaration the kernel
/// checked, is NOT ACCEPTED with `B.lean` named, never PROVED. Its verdict
/// line, its JSON row and the changed-only view's rows of its record all say
/// the same thing, and the exit status is failure as before.
#[test]
fn a_file_beside_a_rejected_sibling_is_never_printed_proved() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let dir = root.path().join("src");
    std::fs::create_dir_all(&dir).expect("source dir");
    let a = dir.join("A.lean");
    let b = dir.join("B.lean");
    std::fs::write(&a, "theorem a : 1 = 1 := rfl\n").expect("write A");
    std::fs::write(&b, "theorem b : 2 = 2 := rfl\n").expect("write B");
    let check = |extra: &[&str]| {
        let output = command(Some("pair"), &target, &dir)
            .arg("check")
            .arg(&a)
            .arg(&b)
            .args(extra)
            .output()
            .expect("run targo-trust check on two .lean files");
        let (stdout, stderr) = text(&output);
        (output, stdout.lines().map(str::to_string).collect::<Vec<_>>(), stderr)
    };

    // Both accepted: the base the next run compares with.
    let (output, stdout, stderr) = check(&[]);
    assert!(output.status.success(), "{stdout:#?}\n{stderr}");
    assert_eq!(stdout[0], format!("PROVED {} — 1 declaration(s) kernel-checked", a.display()));
    assert_eq!(stdout[1], format!("PROVED {} — 1 declaration(s) kernel-checked", b.display()));

    // B rejected: A is not accepted, and no line calls it (or any row) proved.
    std::fs::write(&b, "theorem b : 1 = 2 := rfl\n").expect("break B");
    let (output, stdout, stderr) = check(&[]);
    assert!(!output.status.success(), "{stdout:#?}\n{stderr}");
    assert_eq!(
        stdout[0],
        format!(
            "NOT ACCEPTED {} — its batch was refused by {}; 1 declaration(s) kernel-checked in \
             the refused batch, none accepted",
            a.display(),
            b.display()
        ),
        "{stdout:#?}"
    );
    assert_eq!(stdout[1], format!("REJECTED {}", b.display()));
    assert!(!stdout.iter().any(|line| line.starts_with("PROVED")), "{stdout:#?}");
    assert!(!stdout.iter().any(|line| line.contains("[PROVED]")), "{stdout:#?}");
    // The changed-only view's rows of A's record: its file row and its
    // declaration were proved and now are unknown, the batch never dispatched.
    let a_location = format!("{}:", a.display());
    let lost_unknown = |key: &str| {
        stdout.iter().any(|line| {
            line.starts_with(&format!("LOST        [UNKNOWN]  {key}"))
                && line.contains("unknown (was proved)  not-dispatched")
                && line.contains(&a_location)
        })
    };
    assert!(lost_unknown("<file>#"), "{stdout:#?}");
    assert!(lost_unknown("a#"), "{stdout:#?}");

    // The JSON form carries the same per-file status.
    let (output, stdout, stderr) = check(&["--json"]);
    assert!(!output.status.success(), "{stdout:#?}\n{stderr}");
    let json: serde_json::Value =
        serde_json::from_str(&stdout.join("\n")).expect("the JSON form is one JSON document");
    let files = json["files"].as_array().expect("a files array");
    assert_eq!(files.len(), 2, "{json:#}");
    assert_eq!(files[0]["path"], a.display().to_string());
    assert_eq!(files[0]["status"], "not-accepted", "{json:#}");
    assert_eq!(files[0]["accepted"], false, "{json:#}");
    assert_eq!(files[0]["batch_refused_by"], serde_json::json!([b.display().to_string()]));
    assert_eq!(files[0]["diagnostics"], serde_json::json!([]));
    assert_eq!(files[1]["path"], b.display().to_string());
    assert_eq!(files[1]["status"], "rejected", "{json:#}");
    assert_eq!(files[1]["accepted"], false);
    assert_eq!(json["accepted"], 0, "{json:#}");
    assert_eq!(json["not_accepted"], 1, "{json:#}");
    assert_eq!(json["rejected"], 1, "{json:#}");
}

/// A `.lean` check outside every Cargo workspace with no target directory
/// named writes no record (neither its obligation records nor its timing
/// record) and prints what it printed before this slice, plus one `note:` on
/// stderr saying why. With a caller session the note is the changed-only
/// view's own, printed with it on stdout, and still the only one.
#[test]
fn a_bare_lean_check_writes_nothing_where_it_runs() {
    let root = tempfile::tempdir().expect("tempdir");
    let dir = root.path().join("bare");
    std::fs::create_dir_all(&dir).expect("dir");
    let file = dir.join("K.lean");
    std::fs::write(&file, "theorem k : 1 = 1 := rfl\n").expect("write");
    let mut command = Command::new(binary());
    for name in SESSION_ENV {
        command.env_remove(name);
    }
    let output = command
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .current_dir(&dir)
        .arg("check")
        .arg("K.lean")
        .output()
        .expect("run");
    let (stdout, stderr) = text(&output);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert_eq!(
        stdout.lines().collect::<Vec<_>>(),
        ["PROVED K.lean — 1 declaration(s) kernel-checked", CAPABILITY]
    );
    let entries: Vec<_> =
        std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.file_name()).collect();
    assert_eq!(entries, [std::ffi::OsString::from("K.lean")], "nothing written beside the file");
    let notes: Vec<&str> = stderr.lines().filter(|line| line.starts_with("note:")).collect();
    assert_eq!(notes, [NO_RECORD_NOTE], "{stderr}");

    let mut command = Command::new(binary());
    for name in SESSION_ENV {
        command.env_remove(name);
    }
    let output = command
        .env("ATERM_SESSION_ID", "bare-session")
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .current_dir(&dir)
        .arg("check")
        .arg("K.lean")
        .output()
        .expect("run");
    let (stdout, stderr) = text(&output);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert_eq!(
        stdout.lines().collect::<Vec<_>>(),
        ["PROVED K.lean — 1 declaration(s) kernel-checked", NO_RECORD_NOTE, CAPABILITY]
    );
    assert!(!stderr.contains("note:"), "{stderr}");
    let entries: Vec<_> =
        std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.file_name()).collect();
    assert_eq!(entries, [std::ffi::OsString::from("K.lean")], "nothing written beside the file");
}

/// The one note a `.lean` check prints when no target directory resolves.
const NO_RECORD_NOTE: &str = "note: no record written: no --target-dir, CARGO_TARGET_DIR or \
                              CARGO_BUILD_TARGET_DIR, and no Cargo workspace at or above the \
                              current directory; pass --target-dir DIR to keep this run's records";

// --- Existing consumers of the per-row listing -------------------------------------

/// Spellings by which an in-tree script greps the per-row listing a
/// crate-mode `targo trust check` prints (`  [LABEL] [kind] message`).
const LISTING_GREPS: [&str; 7] = [
    "\\[FAILED",
    "\\[PROVED",
    "\\[RUNTIME-CHECKED",
    "\\[UNKNOWN",
    "\\[ASSUMED",
    "\\[TIMEOUT",
    "\\[postcondition\\]",
];

/// Every in-tree shell script that greps the per-row listing passes
/// `--all-rows` on each crate-mode `targo trust check` it runs (one naming a
/// package or `--lib`, in the terminal format), so what it reads never
/// depends on whether the environment names a caller session: from an aterm
/// tab, a second run in the same target directory would otherwise print the
/// changed-only view in place of the listing. The listing on that path is
/// `report::tests::a_gate_scripts_check_run_twice_in_one_session_still_prints_the_listing`.
#[test]
fn every_script_that_reads_the_listing_asks_for_every_row() {
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).parent().expect("the repository");
    let mut consumers = Vec::new();
    let mut missing = Vec::new();
    for dir in ["scripts", "tests"] {
        for entry in std::fs::read_dir(repo.join(dir)).expect("read the directory").flatten() {
            let path = entry.path();
            if path.extension().is_none_or(|extension| extension != "sh") {
                continue;
            }
            let text = std::fs::read_to_string(&path).expect("read the script");
            if !LISTING_GREPS.iter().any(|grep| text.contains(grep)) {
                continue;
            }
            for (number, line) in text.lines().enumerate() {
                let code = line.trim_start();
                let crate_mode = code.contains(" -p ") || code.contains("--lib");
                if code.starts_with('#')
                    || !code.contains("trust check")
                    || !crate_mode
                    || code.contains("--format json")
                {
                    continue;
                }
                consumers.push(format!("{}:{}", path.display(), number + 1));
                if !code.contains("--all-rows") {
                    missing.push(format!("{}:{}: {code}", path.display(), number + 1));
                }
            }
        }
    }
    assert!(
        consumers.iter().any(|at| at.contains("trust_hex_strict_gate.sh"))
            && consumers.iter().any(|at| at.contains("e2e_instance_discharge_accounting.sh")),
        "the scan found the known consumers: {consumers:#?}"
    );
    assert!(
        missing.is_empty(),
        "checks whose listing a script reads without --all-rows:\n{missing:#?}"
    );
}
