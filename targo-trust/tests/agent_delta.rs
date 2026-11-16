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

    // With no base the refuted row still prints, on its own line before the
    // count: a first run never reduces a failure to a number.
    let fresh = delta(Some("session-d"), &target, &after, &[]);
    assert_eq!(fresh.len(), 2, "{fresh:#?}");
    assert!(fresh[0].starts_with("[FAILED]  delta_fixture::f17#"), "{fresh:#?}");
    assert_eq!(fresh[1], format!("delta-fixture  {total} obligation(s)  (now {now})"));

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

// --- Rust: a crate's `clean { … }` island declarations --------------------------

const ISLAND_DECLARATIONS: usize = 50;
const ISLAND_CRATE: &str = "delta_fixture";

/// How an island declaration of the fixture reads in one run.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Decl {
    /// `proved`/`solved`.
    Proved,
    /// `failed`/`solver-incomplete`, basis `unproved_fail_closed`.
    Refused,
    /// `unknown`/`not-dispatched`.
    NotDispatched,
    /// No row: its island was not enumerated.
    Absent,
}

/// The island section a crate check writes for the fixture's fifty island
/// declarations `Fixture.t00` … `Fixture.t49`, in the format of
/// `targo-trust`'s `obligations` (CLEAN ISLANDS). `statement` is the
/// declaration whose statement was edited (a new key), `proof` the one whose
/// proof was edited (the same key, a new source digest), and `decl` says how
/// each one reads.
fn island_section(
    phase: &str,
    problems: &[&str],
    statement: Option<usize>,
    proof: Option<usize>,
    decl: impl Fn(usize) -> Decl,
) -> String {
    let mut out = format!(
        "{{\"clean_islands\":\"{ISLAND_CRATE}\",\"phase\":\"{phase}\",\"islands\":10,\
         \"complete\":{},\"problems\":{}}}\n",
        problems.is_empty(),
        serde_json::to_string(problems).unwrap()
    );
    for n in 0..ISLAND_DECLARATIONS {
        let (status, stop, basis) = match decl(n) {
            Decl::Proved => ("proved", "solved", ""),
            Decl::Refused => ("failed", "solver-incomplete", ",\"basis\":\"unproved_fail_closed\""),
            Decl::NotDispatched => ("unknown", "not-dispatched", ""),
            Decl::Absent => continue,
        };
        let id = format!("{:016x}", n * 104_729 + 1 + usize::from(statement == Some(n)));
        let source = format!("{:064x}", n * 7919 + 1 + usize::from(proof == Some(n)));
        out.push_str(&format!(
            "{{\"clean_decl\":\"{ISLAND_CRATE}::Fixture.t{n:02}#{id}\",\"kind\":\"lean:theorem\",\
             \"status\":\"{status}\",\"stop\":\"{stop}\",\"file\":\"src/lib.rs\",\"line\":{},\
             \"col\":3,\"source\":\"{source}\"{basis}}}\n",
            400 + n * 3
        ));
    }
    out
}

/// `record` with `islands` after its compile-error lines and before its first
/// function line, where a check writes them, behind the line saying its one
/// proof unit published them.
fn with_islands(record: &str, islands: &str) -> String {
    with_units(record, 1, Some(1), islands)
}

/// `record` with `islands` behind the line saying `published` of the
/// package's `proof_units` compilation units published island rows.
fn with_units(record: &str, published: u32, proof_units: Option<u32>, islands: &str) -> String {
    let units = format!(
        "{{\"clean_island_units\":{published},\"proof_units\":{}}}\n",
        proof_units.map_or("null".to_string(), |units| units.to_string())
    );
    let at = record.find("{\"fn\"").unwrap_or(record.len());
    format!("{}{units}{islands}{}", &record[..at], &record[at..])
}

/// The record a crate check writes when the build broke on a refused island
/// proof: the resolver's batch is the only check that ran, and its refusal is
/// a compile error.
const ISLAND_ERROR: &str = "Clean island rejected: `sorry` reaches `Fixture.t08`";

fn island_error_record() -> String {
    format!(
        concat!(
            r#"{{"schema":"trust.obligations.v1","package":"delta-fixture","lane":"strict","#,
            r#""policy":"strict","selection":"default","seal":{{"absent":"A8"}},"#,
            r#""targo_trust_commit":"0123456789abcdef0123456789abcdef01234567","#,
            r#""profile":"c870797a6939da587fae99d7b0aa4c5e64be43e1e0798966417b011f955f05f9","#,
            r#""outcome":"could-not-run","vector":"00","coverage_complete":false,"#,
            r#""concluded":false,"degraded_anchors":0}}"#,
            "\n",
            r#"{{"compile_error":"{key}","code":null,"message":"{message}","#,
            r#""file":"src/lib.rs","line":424,"col":3}}"#,
            "\n"
        ),
        key = compile_error_key("src/lib.rs", "error", ISLAND_ERROR),
        message = ISLAND_ERROR,
    )
}

/// PKG-LIVE-2's exit, for the island declarations of a crate (the
/// 200-obligation crate record with fifty island declarations beside it):
/// a rerun with no edit is one line; a statement edit is that declaration's
/// two rows; a proof edit that is still accepted is no row; a broken proof
/// that stopped the Rust front end is its own row and one count line, never
/// fifty rows; an island that did not parse is `NOT MEASURED`, never
/// `VANISHED`; a Rust error that published no island row leaves the islands'
/// base where it was. The records are in the format a crate check writes;
/// the compiler's emitter of the rows (not yet built) is not driven here.
#[test]
fn island_declarations_print_only_the_edited_declaration_and_one_line_when_unchanged() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("record.ndjson");
    let total = FUNCTIONS * PER_FUNCTION;
    let run = |text: String| {
        std::fs::write(&record, text).expect("write record");
        delta(Some("s"), &target, &record, &[])
    };
    let measured = |statement, proof| {
        with_islands(
            &crate_record(None),
            &island_section("verified", &[], statement, proof, |_| Decl::Proved),
        )
    };

    // First run: one line naming both counts.
    let first = run(measured(None, None));
    assert_eq!(first.len(), 1, "{first:#?}");
    let base = now_token(&first[0]);
    assert_eq!(
        first[0],
        format!(
            "delta-fixture  {total} obligation(s); {ISLAND_DECLARATIONS} island declaration(s)  \
             (now {base})"
        )
    );

    // A rerun with no edit: one line.
    let again = run(measured(None, None));
    assert_eq!(
        again,
        [format!(
            "delta-fixture  0 of {total} changed since {base}; 0 of {ISLAND_DECLARATIONS} island \
             declaration(s) changed  (now {base})"
        )]
    );

    // t08's statement edited: its new key proved, its old key gone, nothing
    // else.
    let edited = run(measured(Some(8), None));
    assert_eq!(edited.len(), 3, "{edited:#?}");
    assert!(
        edited[0].starts_with("GAINED      [PROVED]  delta_fixture::Fixture.t08#"),
        "{edited:#?}"
    );
    assert!(
        edited[0].contains("lean:theorem  proved (new)  solved  src/lib.rs:424:3"),
        "{edited:#?}"
    );
    assert!(edited[1].starts_with("VANISHED    delta_fixture::Fixture.t08#"), "{edited:#?}");
    assert!(edited[1].contains("lean:theorem  (was proved)  src/lib.rs:424:3"), "{edited:#?}");
    let statement = now_token(&edited[2]);
    assert_eq!(
        edited[2],
        format!(
            "delta-fixture  0 of {total} changed since {base}; 2 of {ISLAND_DECLARATIONS} island \
             declaration(s) changed  (now {statement})"
        )
    );

    // t08's proof edited and still accepted: no row (the same key and
    // status), and the token moves (the record carries its source digest).
    let proof = run(measured(Some(8), Some(8)));
    assert_eq!(proof.len(), 1, "{proof:#?}");
    let accepted = now_token(&proof[0]);
    assert_ne!(accepted, statement);
    assert!(
        proof[0].contains(&format!("; 0 of {ISLAND_DECLARATIONS} island declaration(s) changed")),
        "{proof:#?}"
    );

    // t08's proof broken: the resolver refused it, a Rust front-end error
    // stopped the crate, and no other declaration was checked. The view is
    // the compile error, t08's row, one count line, and the header facts the
    // failed build moved; never fifty island rows.
    let broken_islands = island_section("front-end-error", &[], Some(8), Some(8), |n| {
        if n == 8 { Decl::Refused } else { Decl::NotDispatched }
    });
    let broken = run(with_islands(&island_error_record(), &broken_islands));
    let error_key = compile_error_key("src/lib.rs", "error", ISLAND_ERROR);
    assert_eq!(broken.len(), 6, "{broken:#?}");
    assert_eq!(
        broken[0],
        format!("NEW ERROR   [ERROR]  {error_key}  {ISLAND_ERROR}  src/lib.rs:424:3")
    );
    assert!(
        broken[1].starts_with(
            "LOST        [FAILED: unproved, no counterexample; failed closed]  \
             delta_fixture::Fixture.t08#"
        ),
        "{broken:#?}"
    );
    assert!(broken[1].contains("failed (was proved)  solver-incomplete"), "{broken:#?}");
    assert_eq!(
        broken[2],
        "NOT CHECKED  49 island declaration(s) of `delta_fixture` not checked: a Rust front-end \
         error stopped the crate before verification (`--all-rows` lists them)"
    );
    assert_eq!(broken[3], "RUN         coverage_complete true -> false");
    assert_eq!(broken[4], "RUN         outcome measured -> could-not-run");
    let stopped = now_token(&broken[5]);
    assert_eq!(
        broken[5],
        format!(
            "delta-fixture  1 compiler error(s); obligations not compared since {accepted}; 1 of \
             {ISLAND_DECLARATIONS} island declaration(s) changed  (now {stopped})"
        )
    );
    // The same broken build again: the error is `STILL`, and the island lines
    // are the same, still against the last run that measured the islands.
    let mut still = broken.clone();
    still[0] = still[0].replacen("NEW ERROR   ", "STILL       ", 1);
    assert_eq!(run(with_islands(&island_error_record(), &broken_islands)), still);

    // An island that did not parse (t10 … t14 are in it): its rows were not
    // measured, never deleted claims.
    let unparsed = island_section(
        "front-end-error",
        &[
            "island 3 was not enumerated: it did not parse, or its unit was refused before elaboration",
        ],
        Some(8),
        Some(8),
        |n| if (10..15).contains(&n) { Decl::Absent } else { Decl::NotDispatched },
    );
    let lines = run(with_islands(&island_error_record(), &unparsed));
    assert!(lines.iter().all(|line| !line.starts_with("VANISHED")), "{lines:#?}");
    let not_measured: Vec<&String> =
        lines.iter().filter(|line| line.starts_with("NOT MEASURED  ")).collect();
    assert_eq!(not_measured.len(), 5, "{lines:#?}");
    assert!(not_measured[0].contains("delta_fixture::Fixture.t10#"), "{lines:#?}");
    assert!(not_measured[0].contains("not measured this run (was proved)"), "{lines:#?}");
    assert!(lines.iter().any(|line| line.starts_with("NOT CHECKED  45 island declaration(s)")));
    assert!(
        lines.last().unwrap().contains(
            "; 5 of 45 island declaration(s) changed; islands incomplete: delta_fixture: island 3 \
             was not enumerated"
        ),
        "{lines:#?}"
    );

    // A Rust parse error published no island row and the package did not
    // conclude: one count line standing for the base's unfailed rows, one
    // clause, and the base stays.
    let unparsed_rust = run(island_error_record());
    assert_eq!(unparsed_rust.len(), 5, "{unparsed_rust:#?}");
    assert_eq!(
        unparsed_rust[1],
        format!(
            "NOT MEASURED  {ISLAND_DECLARATIONS} island declaration(s) of `delta_fixture` not \
             measured this run: no compilation unit of the package published island rows"
        ),
        "{unparsed_rust:#?}"
    );
    assert!(unparsed_rust[4].contains("obligations not compared since"), "{unparsed_rust:#?}");
    assert!(
        unparsed_rust[4].contains(
            "; islands not measured this run: no compilation unit of the package published \
             island rows  (now "
        ),
        "{unparsed_rust:#?}"
    );

    // Fixed: the error clears, and nothing changed since the last run that
    // measured the obligations and the islands.
    let fixed = run(measured(Some(8), Some(8)));
    assert_eq!(
        fixed,
        [
            format!("CLEARED     [ERROR]  {error_key}  {ISLAND_ERROR}  src/lib.rs:424:3"),
            format!(
                "delta-fixture  0 of {total} changed since {accepted}; 0 of \
                 {ISLAND_DECLARATIONS} island declaration(s) changed  (now {accepted})"
            ),
        ]
    );

    // `--all-rows` lists every island row too.
    let all = delta(Some("other"), &target, &record, &["--all-rows"]);
    assert_eq!(all.len(), total + ISLAND_DECLARATIONS + 1, "{all:#?}");
}

/// The island section of a binary crate `delta_fixture_cli` of the same
/// package, with a failed declaration and a proved one.
fn cli_section(proved: bool) -> String {
    let good = if proved {
        r#""status":"proved","stop":"solved""#
    } else {
        r#""status":"unknown","stop":"not-dispatched""#
    };
    format!(
        concat!(
            r#"{{"clean_islands":"delta_fixture_cli","phase":"verified","islands":1,"#,
            r#""complete":true,"problems":[]}}"#,
            "\n",
            r#"{{"clean_decl":"delta_fixture_cli::Cli.bad#00000000000000aa","kind":"lean:theorem","#,
            r#""status":"failed","stop":"solver-incomplete","file":"src/main.rs","line":10,"#,
            r#""col":3,"source":null,"basis":"unproved_fail_closed"}}"#,
            "\n",
            r#"{{"clean_decl":"delta_fixture_cli::Cli.good#00000000000000bb","kind":"lean:theorem","#,
            r#"{good},"file":"src/main.rs","line":12,"col":3,"source":null}}"#,
            "\n",
        ),
        good = good
    )
}

/// A package whose library and binary both carry islands: the binary stops
/// on a Rust parse error before its islands are read, so it publishes no
/// island row, while the library concludes. The binary's declarations are not
/// deleted claims (no `VANISHED`), its failed one stays in sight, the
/// library's rows (which the record states unproved: they are no measurement
/// of the package) are one count line, and the islands' base stays where it
/// was until every unit publishes again.
#[test]
fn a_unit_that_published_no_island_row_is_not_measured_and_keeps_the_base() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("record.ndjson");
    let run = |text: String| {
        std::fs::write(&record, text).expect("write record");
        delta(Some("s"), &target, &record, &[])
    };
    let lib = |decl: Decl| island_section("verified", &[], None, None, |_| decl);
    let both =
        || with_units(&crate_record(None), 2, Some(2), &(lib(Decl::Proved) + &cli_section(true)));
    let first = run(both());
    // Only the failed binary declaration prints, with no base.
    assert_eq!(first.len(), 2, "{first:#?}");
    assert!(first[0].contains("delta_fixture_cli::Cli.bad#"), "{first:#?}");
    let base = now_token(&first[1]);

    let lib_only = || with_units(&crate_record(None), 1, Some(2), &lib(Decl::NotDispatched));
    for _ in 0..2 {
        let lines = run(lib_only());
        assert!(lines.iter().all(|line| !line.starts_with("VANISHED")), "{lines:#?}");
        assert!(lines.iter().all(|line| !line.starts_with("LOST")), "{lines:#?}");
        assert_eq!(lines.len(), 4, "{lines:#?}");
        assert_eq!(
            lines[0],
            "NOT MEASURED  1 island declaration(s) of `delta_fixture_cli` not measured this run: \
             1 of 2 compilation unit(s) of the package published no island rows"
        );
        assert!(
            lines[1].starts_with("NOT MEASURED  delta_fixture_cli::Cli.bad#00000000000000aa"),
            "{lines:#?}"
        );
        assert!(lines[1].contains("not measured this run (was failed)"), "{lines:#?}");
        assert_eq!(
            lines[2],
            format!(
                "NOT CHECKED  {ISLAND_DECLARATIONS} island declaration(s) of `delta_fixture` not \
                 checked: 1 of 2 compilation unit(s) of the package published no island rows \
                 (`--all-rows` lists them)"
            )
        );
        assert!(
            lines[3]
                .contains(&format!("; 1 of {ISLAND_DECLARATIONS} island declaration(s) changed")),
            "{lines:#?}"
        );
        assert!(
            lines[3].contains(
                "; islands not measured: 1 of 2 compilation unit(s) of the package published no \
                 island rows  (now "
            ),
            "{lines:#?}"
        );
    }
    // Every unit published again: compared with the first run, nothing
    // changed.
    let again = run(both());
    assert_eq!(again.len(), 2, "{again:#?}");
    assert!(again[0].starts_with("STILL       "), "{again:#?}");
    assert!(again[0].contains("delta_fixture_cli::Cli.bad#"), "{again:#?}");
    assert!(
        again[1].contains(&format!(
            "; 0 of {} island declaration(s) changed since {base}  (now {base})",
            ISLAND_DECLARATIONS + 2
        )),
        "{again:#?}"
    );
}

/// A verified section that is not a measurement (the session was tainted:
/// every sibling of the refused declaration is not dispatched) is the refused
/// row and one count line, on the run it broke and on every rerun, never a
/// `LOST` line per declaration.
#[test]
fn a_verified_section_that_is_incomplete_is_one_count_line_not_a_row_per_declaration() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("record.ndjson");
    let run = |text: String| {
        std::fs::write(&record, text).expect("write record");
        delta(Some("s"), &target, &record, &[])
    };
    let measured = with_islands(
        &crate_record(None),
        &island_section("verified", &[], None, None, |_| Decl::Proved),
    );
    let first = run(measured.clone());
    assert_eq!(first.len(), 1, "{first:#?}");
    let tainted = with_islands(
        &crate_record(None),
        &island_section("verified", &["the crate's Clean session was tainted"], None, None, |n| {
            if n == 3 { Decl::Refused } else { Decl::NotDispatched }
        }),
    );
    for _ in 0..2 {
        let lines = run(tainted.clone());
        assert_eq!(lines.len(), 3, "{lines:#?}");
        assert!(
            lines[0].starts_with(
                "LOST        [FAILED: unproved, no counterexample; failed closed]  \
                 delta_fixture::Fixture.t03#"
            ),
            "{lines:#?}"
        );
        assert_eq!(
            lines[1],
            format!(
                "NOT CHECKED  {} island declaration(s) of `delta_fixture` not checked: its island \
                 rows are incomplete (`--all-rows` lists them)",
                ISLAND_DECLARATIONS - 1
            )
        );
        assert!(
            lines[2]
                .contains(&format!("; 1 of {ISLAND_DECLARATIONS} island declaration(s) changed")),
            "{lines:#?}"
        );
        assert!(
            lines[2].contains(
                "; islands incomplete: delta_fixture: the crate's Clean session was tainted  (now "
            ),
            "{lines:#?}"
        );
    }
    // Repaired: nothing changed since the last measurement.
    let fixed = run(measured);
    assert_eq!(fixed.len(), 1, "{fixed:#?}");
    assert!(
        fixed[0].contains(&format!("; 0 of {ISLAND_DECLARATIONS} island declaration(s) changed"))
    );
}

/// `--since` names the islands' base too: a snapshot it names that is not
/// alike gives the islands no base, as it gives the obligations none, rather
/// than the caller's last measured snapshot.
#[test]
fn since_a_snapshot_that_is_not_alike_gives_the_islands_no_base() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("record.ndjson");
    let run = |text: String, session: &str, extra: &[&str]| {
        std::fs::write(&record, text).expect("write record");
        delta(Some(session), &target, &record, extra)
    };
    let islands = |decl: fn(usize) -> Decl| {
        with_islands(&crate_record(None), &island_section("verified", &[], None, None, decl))
    };
    // Another selection's snapshot, by another session.
    let other = run(
        islands(|_| Decl::Proved).replace(r#""selection":"default""#, r#""selection":"other""#),
        "t",
        &[],
    );
    let other = now_token(&other[0]);
    // This session's measured base, then t03 refused, compared with `other`.
    run(islands(|_| Decl::Proved), "s", &[]);
    let lines = run(
        islands(|n| if n == 3 { Decl::Refused } else { Decl::Proved }),
        "s",
        &["--since", &other],
    );
    assert!(lines.iter().all(|line| !line.starts_with("LOST")), "{lines:#?}");
    let summary = lines.last().unwrap();
    assert!(
        summary.contains(&format!("; {ISLAND_DECLARATIONS} island declaration(s)  (now ")),
        "{lines:#?}"
    );
}

/// The island clause names its base when it is not the obligations' base: a
/// run whose islands were not measured compares them with an earlier run than
/// its obligations.
#[test]
fn the_island_clause_names_its_base_when_it_is_not_the_obligations_base() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("record.ndjson");
    let run = |text: String| {
        std::fs::write(&record, text).expect("write record");
        delta(Some("s"), &target, &record, &[])
    };
    let measured = |decl: fn(usize) -> Decl| {
        with_islands(&crate_record(None), &island_section("verified", &[], None, None, decl))
    };
    let first = run(measured(|_| Decl::Proved));
    let base = now_token(&first[0]);
    // The obligations concluded; the islands were incomplete.
    let incomplete = with_islands(
        &crate_record(None),
        &island_section("verified", &["the crate's Clean session was tainted"], None, None, |_| {
            Decl::NotDispatched
        }),
    );
    let second = run(incomplete.clone());
    let second_token = now_token(second.last().unwrap());
    let third = run(incomplete);
    let summary = third.last().unwrap();
    assert!(summary.contains(&format!("changed since {second_token};")), "{third:#?}");
    assert!(
        summary.contains(&format!(
            "; 0 of {ISLAND_DECLARATIONS} island declaration(s) changed since {base}"
        )),
        "{third:#?}"
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

/// Without `--target-dir`, snapshots are kept under the target directory whose
/// `trust/obligations/` holds the record, however the path is spelled and
/// wherever delta runs from; a record held anywhere else names none, and a
/// note says where they go instead (the `.lean` lane's directory), or, with
/// none here, delta refuses. `--target-dir` takes exactly one directory, not
/// empty and not starting with `-`, in either spelling, as the `.lean` lane's
/// does; a package named twice, or a record whose key cannot be matched, is
/// refused.
#[test]
fn snapshots_are_kept_under_the_records_own_target_directory() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("ws/target");
    let records = target.join("trust/obligations");
    std::fs::create_dir_all(&records).expect("records dir");
    let record = records.join("delta-fixture.ndjson");
    std::fs::write(&record, crate_record(None)).expect("write record");
    let member = root.path().join("ws/member");
    std::fs::create_dir_all(&member).expect("member dir");
    // `CARGO_TARGET_DIR` names another directory, and delta runs in a member.
    let elsewhere = root.path().join("elsewhere");
    let run = |record: &Path| {
        let output = command(Some("s"), &elsewhere, &member)
            .arg("trust")
            .arg("delta")
            .arg(record)
            .output()
            .expect("run targo-trust delta");
        let (stdout, stderr) = text(&output);
        assert!(output.status.success(), "stdout:\n{stdout}\nstderr:\n{stderr}");
        stdout.lines().map(str::to_string).collect::<Vec<_>>()
    };
    let first = run(&record);
    assert_eq!(first.len(), 1, "{first:#?}");
    let token = now_token(&first[0]);
    assert!(target.join("trust/snapshots").join(&token).is_file());
    assert!(!elsewhere.exists(), "nothing is kept under CARGO_TARGET_DIR");
    // The rerun finds its base there, by another spelling of the same path.
    let total = FUNCTIONS * PER_FUNCTION;
    let unchanged = [format!("delta-fixture  0 of {total} changed since {token}  (now {token})")];
    assert_eq!(run(&record), unchanged);
    assert_eq!(run(&records.join("../obligations/delta-fixture.ndjson")), unchanged);

    let loose = root.path().join("loose.ndjson");
    std::fs::copy(&record, &loose).expect("copy the record");
    let lines = run(&loose);
    assert_eq!(lines.len(), 2, "{lines:#?}");
    assert!(lines[0].starts_with("note: the records named are not all under one"), "{lines:#?}");
    let kept = elsewhere.join("trust/snapshots");
    assert!(lines[0].contains(&kept.display().to_string()), "{lines:#?}");
    assert!(kept.join(&token).is_file());

    // Outside every workspace, with no target directory in the environment,
    // there is nowhere to keep them: refused, and nothing written here.
    let output = command(Some("s"), &elsewhere, root.path())
        .env_remove("CARGO_TARGET_DIR")
        .arg("trust")
        .arg("delta")
        .arg(&loose)
        .output()
        .expect("run targo-trust delta");
    assert_eq!(output.status.code(), Some(2), "{:?}", text(&output));
    assert!(text(&output).1.contains("pass --target-dir <dir>"), "{:?}", text(&output));
    assert!(!root.path().join("target").exists());

    // The same refusals in both spellings, from delta and from a `.lean`
    // check, which share the rule.
    let lean = root.path().join("K.lean");
    std::fs::write(&lean, "theorem k : 1 = 1 := rfl\n").expect("write");
    let dir = target.display().to_string();
    for bad in [
        &["--target-dir="][..],
        &["--target-dir=-x"][..],
        &["--target-dir", ""][..],
        &["--target-dir", "-x"][..],
        &["--target-dir", &dir, "--target-dir", &dir][..],
    ] {
        for (verb, operand) in [("delta", &record), ("check", &lean)] {
            let output = command(None, &elsewhere, &member)
                .arg("trust")
                .arg(verb)
                .args(bad)
                .arg(operand)
                .output()
                .expect("run targo-trust");
            let stderr = text(&output).1;
            assert_eq!(output.status.code(), Some(2), "{verb} {bad:?}: {stderr}");
            assert!(
                stderr.contains("--target-dir requires exactly one directory"),
                "{verb} {bad:?}: {stderr}"
            );
        }
    }

    let refused = |paths: &[&Path], why: &str| {
        let output = command(None, &elsewhere, &member)
            .arg("trust")
            .arg("delta")
            .args(paths)
            .output()
            .expect("run targo-trust delta");
        assert_eq!(output.status.code(), Some(2), "{paths:?}: {:?}", text(&output));
        assert!(text(&output).1.contains(why), "{paths:?}: {:?}", text(&output));
    };
    refused(&[record.as_path(), loose.as_path()], "name one record per package");
    let unkeyed = root.path().join("unkeyed.ndjson");
    let key = format!("delta_fixture::f00#{}", local_id(0, 0));
    std::fs::write(&unkeyed, crate_record(None).replacen(&key, "delta_fixture::f00#zz", 1))
        .expect("write record");
    refused(&[unkeyed.as_path()], "obligation key `delta_fixture::f00#zz` is not");
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

// --- Rust: a test run's record, with each case's outcome ---------------------------
//
// The path from a real libtest harness (passing, failing, ignored and aborting
// cases, a case that forges result lines on stdout, a missing or truncated
// result file) to these lines is `test_results::tests`; here the record a test
// run writes goes through `targo-trust delta` as a crate check's does.

const UNIT_CASES: usize = 20;
const INTEGRATION_CASES: usize = 5;
const UNIT_HARNESS: &str = "lib/delta_fixture";
const INTEGRATION_HARNESS: &str = "test/integration";

/// How the unit-test harness of the test-run fixture ended.
#[derive(Clone, Copy)]
enum UnitHarness {
    /// Ran to its end; the case of this index, if any, failed.
    Concluded(Option<usize>),
    /// Aborted after its first ten cases; the case of this index, if any, of
    /// those ten failed.
    Aborted(Option<usize>),
}

/// The record of a `targo trust test` run of `delta-fixture`: the crate
/// record's obligations, a unit-test harness of twenty cases and an
/// integration-test harness of five, one of them ignored.
fn test_run_record(unit: UnitHarness) -> String {
    let body = crate_record(None);
    let (header, obligations) = body.split_once('\n').expect("a header line");
    let mut out =
        header.replacen("\"degraded_anchors\":0}", "\"degraded_anchors\":0,\"tests\":[]}", 1);
    out.push('\n');
    let mut harnesses = vec![(INTEGRATION_HARNESS.to_string(), None)];
    let (ran, failed) = match unit {
        UnitHarness::Concluded(failed) => {
            harnesses.push((UNIT_HARNESS.to_string(), None));
            (UNIT_CASES, failed)
        }
        UnitHarness::Aborted(failed) => {
            harnesses.push((UNIT_HARNESS.to_string(), Some("ended by signal 6")));
            (10, failed)
        }
    };
    harnesses.sort();
    for (key, reason) in &harnesses {
        out.push_str(&match reason {
            None => format!("{{\"test_harness\":\"{key}\",\"concluded\":true,\"reason\":null}}\n"),
            Some(reason) => format!(
                "{{\"test_harness\":\"{key}\",\"concluded\":false,\"reason\":\"{reason}\"}}\n"
            ),
        });
    }
    let mut cases: Vec<(String, &str)> = (0..INTEGRATION_CASES)
        .map(|index| {
            let outcome = if index == 4 { "ignored" } else { "passed" };
            (format!("{INTEGRATION_HARNESS}::case_{index}"), outcome)
        })
        .collect();
    cases.extend((0..ran).map(|index| {
        let outcome = if failed == Some(index) {
            "failed"
        } else if matches!(unit, UnitHarness::Aborted(_)) {
            "not concluded"
        } else {
            "passed"
        };
        (format!("{UNIT_HARNESS}::tests::case_{index:02}"), outcome)
    }));
    cases.sort();
    for (key, outcome) in cases {
        out.push_str(&format!("{{\"test\":\"{key}\",\"outcome\":\"{outcome}\"}}\n"));
    }
    out.push_str(obligations);
    out
}

#[test]
fn a_test_run_prints_only_the_edited_test_and_one_line_when_unchanged() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let record = root.path().join("tests.ndjson");
    let run = |unit: UnitHarness| {
        std::fs::write(&record, test_run_record(unit)).expect("write record");
        delta(Some("session-t"), &target, &record, &[])
    };
    let total = FUNCTIONS * PER_FUNCTION;
    let cases = UNIT_CASES + INTEGRATION_CASES;
    let truth = "(reported by each test binary's own harness)";

    // First run: no base, nothing failed: one line.
    let first = run(UnitHarness::Concluded(None));
    assert_eq!(first.len(), 1, "{first:#?}");
    let base = now_token(&first[0]);
    assert_eq!(
        first[0],
        format!(
            "delta-fixture  {total} obligation(s); {cases} test case(s): 24 passed, 0 failed, 1 \
             ignored, 0 not concluded {truth}  (now {base})"
        )
    );

    // A rerun with no edit: one line.
    let again = run(UnitHarness::Concluded(None));
    assert_eq!(
        again,
        [format!(
            "delta-fixture  0 of {total} changed since {base}; 0 of {cases} test case(s) changed: \
             24 passed, 0 failed, 1 ignored, 0 not concluded {truth}  (now {base})"
        )]
    );

    // One test edited so that it fails: only its row and the summary.
    let edited = run(UnitHarness::Concluded(Some(7)));
    assert_eq!(edited.len(), 2, "{edited:#?}");
    assert_eq!(
        edited[0],
        format!(
            "NEW FAILED  [TEST failed]  {UNIT_HARNESS}::tests::case_07  test  failed (was passed)  \
             reported by its harness  -"
        )
    );
    let now = now_token(&edited[1]);
    assert!(
        edited[1].starts_with(&format!(
            "delta-fixture  0 of {total} changed since {base}; 1 of {cases} test case(s) changed: \
             23 passed, 1 failed"
        )),
        "{edited:#?}"
    );

    // A failing case prints on every run, as a failing obligation does.
    let still = run(UnitHarness::Concluded(Some(7)));
    assert_eq!(
        still,
        [
            format!(
                "STILL       [TEST failed]  {UNIT_HARNESS}::tests::case_07  test  failed  \
                 reported by its harness  -"
            ),
            format!(
                "delta-fixture  0 of {total} changed since {now}; 0 of {cases} test case(s) \
                 changed: 23 passed, 1 failed, 1 ignored, 0 not concluded {truth}  (now {now})"
            ),
        ]
    );

    // The harness aborts: its row prints, and no case of it is a pass; the
    // cases it never reached are under its row, not rows of their own.
    let crashed = run(UnitHarness::Aborted(Some(7)));
    assert!(
        crashed.contains(&format!(
            "CHANGED     [TEST HARNESS not concluded]  {UNIT_HARNESS}  harness  not concluded: \
             ended by signal 6 (was concluded)  reported by its harness  -"
        )),
        "{crashed:#?}"
    );
    assert!(
        crashed.contains(&format!(
            "STILL       [TEST failed]  {UNIT_HARNESS}::tests::case_07  test  failed  reported by \
             its harness  -"
        )),
        "{crashed:#?}"
    );
    assert!(crashed.iter().all(|line| !line.contains("[TEST passed]")), "{crashed:#?}");
    assert!(crashed.iter().all(|line| !line.contains("case_15")), "{crashed:#?}");
    assert!(crashed.last().unwrap().contains("1 harness(es) not concluded"), "{crashed:#?}");
    // The harness that ran to its end and did not change prints nothing.
    assert!(crashed.iter().all(|line| !line.contains(INTEGRATION_HARNESS)), "{crashed:#?}");
    for line in first.iter().chain(&again).chain(&edited).chain(&still).chain(&crashed) {
        for word in ["PROVED", "proved", "proof", "verified", "certified"] {
            assert!(!line.contains(word), "`{word}` in {line}");
        }
    }
}

#[test]
fn a_record_that_claims_a_test_result_it_cannot_have_is_refused() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    std::fs::create_dir_all(&target).expect("target dir");
    let refuse = |name: &str, record: String, why: &str| {
        let path = root.path().join(name);
        std::fs::write(&path, record).expect("write record");
        let output = command(Some("s"), &target, &target)
            .args(["trust", "delta", "--target-dir"])
            .arg(&target)
            .arg(&path)
            .output()
            .expect("run targo-trust delta");
        let (stdout, stderr) = text(&output);
        assert_eq!(output.status.code(), Some(2), "{name}\n{stdout}\n{stderr}");
        assert!(stderr.contains(why), "{name}: {stderr}");
    };
    let good = test_run_record(UnitHarness::Aborted(None));
    // A case of a harness that did not conclude is never a pass.
    refuse(
        "passed.ndjson",
        good.replacen(
            &format!("\"test\":\"{UNIT_HARNESS}::tests::case_00\",\"outcome\":\"not concluded\""),
            &format!("\"test\":\"{UNIT_HARNESS}::tests::case_00\",\"outcome\":\"passed\""),
            1,
        ),
        "a `passed` case of a harness that did not conclude",
    );
    // A check's record carries no test line.
    refuse(
        "check.ndjson",
        good.replacen(",\"tests\":[]}", "}", 1),
        "in a record that is not a test run's",
    );
    // A harness that did not conclude says why; one that did says nothing.
    refuse(
        "reason.ndjson",
        good.replacen(
            "\"concluded\":false,\"reason\":\"ended by signal 6\"",
            "\"concluded\":false,\"reason\":null",
            1,
        ),
        "whose reason does not match",
    );
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
    // `M` counts the vanished row as well as this run's.
    let compared = rows + 1;
    assert!(
        stdout[3].starts_with(&format!("{package}  2 of {compared} changed since {reformatted}"))
    );
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
/// view's own, printed with it on stdout, and still the only one; the view
/// still lists every row that is not plainly proved, then a summary line that
/// names no token.
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

    let in_session = || {
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
        assert!(!stderr.contains("note:"), "{stderr}");
        let entries: Vec<_> =
            std::fs::read_dir(&dir).unwrap().flatten().map(|e| e.file_name()).collect();
        assert_eq!(entries, [std::ffi::OsString::from("K.lean")], "nothing written beside it");
        (output.status.success(), stdout.lines().map(str::to_string).collect::<Vec<_>>())
    };
    let package = std::fs::canonicalize(&file).expect("canonical").display().to_string();
    let summary = format!("{package}  2 obligation(s)  (now not stored)");
    let (success, stdout) = in_session();
    assert!(success, "{stdout:#?}");
    assert_eq!(
        stdout,
        ["PROVED K.lean — 1 declaration(s) kernel-checked", NO_RECORD_NOTE, &summary, CAPABILITY]
    );

    // A rejected file: the file row and the refused declaration print, as
    // they do with a target directory and no base.
    std::fs::write(&file, "theorem k : 1 = 2 := rfl\n").expect("write");
    let (success, stdout) = in_session();
    assert!(!success, "{stdout:#?}");
    assert_eq!(stdout.len(), 6, "{stdout:#?}");
    assert_eq!(stdout[..2], ["REJECTED K.lean", NO_RECORD_NOTE]);
    let failed = |key: &str| {
        stdout[2..4].iter().any(|line| line.starts_with(&format!("[{FAILED_CLOSED}]  {key}#")))
    };
    assert!(failed("<file>") && failed("k"), "{stdout:#?}");
    assert_eq!(stdout[4..], [summary, CAPABILITY.to_string()]);
}

/// `--all-rows` alone asks a `.lean` check for the changed-only view, as a
/// caller session, `--since` or `--target-dir` does: with no caller session it
/// prints every row and the summary line and writes the record, rather than
/// take the flag and print nothing of it. With nowhere to keep the record, the
/// view still lists every row, after the one note saying why.
#[test]
fn all_rows_alone_asks_a_lean_check_for_the_view() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let dir = root.path().join("bare");
    std::fs::create_dir_all(&dir).expect("dir");
    let file = dir.join("K.lean");
    std::fs::write(&file, "theorem k : 1 = 1 := rfl\n").expect("write");
    let package = std::fs::canonicalize(&file).expect("canonical").display().to_string();
    let verdict = "PROVED K.lean — 1 declaration(s) kernel-checked";
    let rows = |lines: &[&str]| {
        assert!(lines[0].starts_with("[PROVED]  <file>#"), "{lines:#?}");
        assert!(lines[1].starts_with("[PROVED]  k#"), "{lines:#?}");
    };

    let output =
        command(None, &target, &dir).args(["check", "K.lean", "--all-rows"]).output().expect("run");
    let (stdout, stderr) = text(&output);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), 5, "{lines:#?}");
    assert_eq!(lines[0], verdict);
    rows(&lines[1..3]);
    assert!(lines[3].starts_with(&format!("{package}  2 obligation(s)  (now ")), "{lines:#?}");
    assert_eq!(lines[4], CAPABILITY);
    assert!(target.join("trust/snapshots").join(now_token(lines[3])).is_file());
    let records = std::fs::read_dir(target.join("trust/obligations")).expect("records").count();
    assert_eq!(records, 1, "the record is written");

    let output = command(None, &target, &dir)
        .env_remove("CARGO_TARGET_DIR")
        .args(["check", "K.lean", "--all-rows"])
        .output()
        .expect("run");
    let (stdout, stderr) = text(&output);
    assert!(output.status.success(), "{stdout}\n{stderr}");
    assert!(!stderr.contains("note:"), "{stderr}");
    let lines: Vec<&str> = stdout.lines().collect();
    assert_eq!(lines.len(), 6, "{lines:#?}");
    assert_eq!(lines[..2], [verdict, NO_RECORD_NOTE]);
    rows(&lines[2..4]);
    let summary = format!("{package}  2 obligation(s)  (now not stored)");
    assert_eq!(lines[4..], [summary.as_str(), CAPABILITY]);
}

/// A `.lean` declaration's source digest and local ids leave its name out, so
/// one renamed with no other token changed is paired by its source digest (a
/// `MOVED` line) and its rows by their unchanged ids: nothing is `REMOVED` and
/// no row prints as new.
#[test]
fn a_renamed_lean_declaration_is_paired_by_its_source() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let dir = root.path().join("src");
    std::fs::create_dir_all(&dir).expect("source dir");
    let file = dir.join("Fixture.lean");
    std::fs::write(&file, lean_source(None)).expect("write fixture");
    let package = std::fs::canonicalize(&file).expect("canonical").display().to_string();
    let proved =
        format!("PROVED {} — {DECLARATIONS} declaration(s) kernel-checked", file.display());
    let rows = DECLARATIONS + 1;
    let (_, stdout) = lean_check("rename", &target, &dir, &file);
    let base = now_token(&stdout[1]);

    std::fs::write(&file, lean_source(Some("theorem t08r : 8 = 8 := rfl"))).expect("rename");
    let (output, stdout) = lean_check("rename", &target, &dir, &file);
    assert!(output.status.success(), "{stdout:#?}");
    assert_eq!(stdout.len(), 4, "{stdout:#?}");
    let now = now_token(&stdout[2]);
    assert_ne!(now, base, "the record names the new name");
    assert_eq!(
        stdout,
        whole(
            &proved,
            &[
                "MOVED       Fixture.t08 -> Fixture.t08r  (paired by source)".to_string(),
                format!("{package}  0 of {rows} changed since {base}  (now {now})"),
            ]
        )
    );
}

/// A Rust `check` that writes no obligation records (a standalone audit, the
/// rewrite loop, a single `.rs` file) prints no changed-only view, so it
/// refuses `--since` and `--all-rows` (exit 2) before it reads a manifest or
/// looks for a compiler, rather than run without the view and say nothing.
#[test]
fn a_check_that_prints_no_view_refuses_the_view_flags() {
    let root = tempfile::tempdir().expect("tempdir");
    let target = root.path().join("target");
    let since = "0123456789abcdef";
    for (args, refusal) in [
        (
            vec!["check", "--standalone", "--since", since],
            "targo trust: --since does not combine with --standalone: a standalone audit \
             writes no obligation records and prints no changed-only view",
        ),
        (
            vec!["check", "--rewrite", "--all-rows"],
            "targo trust: --all-rows does not combine with --rewrite: the rewrite loop writes \
             no obligation records and prints no changed-only view",
        ),
        (
            vec!["check", "lib.rs", "--since", since, "--all-rows"],
            "targo trust: --since and --all-rows do not combine with a single `.rs` file: a \
             single-file check writes no obligation records and prints no changed-only view",
        ),
        // Focused too: refused, not noted as ignored.
        (
            vec!["check", "--function", "midpoint", "lib.rs", "--all-rows"],
            "targo trust: --all-rows does not combine with a single `.rs` file: a single-file \
             check writes no obligation records and prints no changed-only view",
        ),
    ] {
        let output = command(Some("refusing-session"), &target, root.path())
            .args(&args)
            .output()
            .expect("run");
        let (stdout, stderr) = text(&output);
        assert_eq!(output.status.code(), Some(2), "{args:?}\n{stdout}\n{stderr}");
        assert_eq!(stderr.lines().collect::<Vec<_>>(), [refusal], "{args:?}");
        assert!(stdout.is_empty(), "{args:?}: {stdout}");
    }
    assert!(!target.exists(), "a refused check writes nothing");
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

/// `targo trust help` names `delta` with `delta --help`'s own synopsis, and
/// both state the base as the code chooses it: one measured on the same lane,
/// policy and selection, never "this agent session's last run" (a run measured
/// another way neither reads nor moves that base).
#[test]
fn the_help_index_carries_the_deltas_own_synopsis_and_base() {
    let run = |args: &[&str]| {
        let output = Command::new(binary()).arg("trust").args(args).output().expect("run");
        let (stdout, stderr) = text(&output);
        assert!(output.status.success(), "{args:?}: {stderr}");
        stdout
    };
    let own = run(&["delta", "--help"]);
    let synopsis = own.lines().next().and_then(|line| line.strip_prefix("usage: "));
    let synopsis = synopsis.expect("delta's help opens with its usage");
    let index = run(&["help"]);
    let line = index
        .lines()
        .map(str::trim_start)
        .find(|line| line.starts_with("targo trust delta "))
        .expect("the help index names delta");
    let (named, summary) = line.split_once("  ").expect("a synopsis, then the summary");
    assert_eq!(named, synopsis);
    for text in [own.as_str(), summary] {
        assert!(text.contains("on the same lane, policy and selection"), "{text}");
        assert!(!text.contains("last run"), "{text}");
    }
    // A pointer nobody wrote for 30 days is not read, and it is kept under
    // the target directory, so `--help` names both.
    assert!(own.contains("within 30 days"), "{own}");
    assert!(own.contains("session pointers are kept under --target-dir"), "{own}");
}
