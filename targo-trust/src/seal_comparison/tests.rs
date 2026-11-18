//! Controls for `targo trust gate compare-seal`, all through the command's own
//! path over a state directory on disk.

use std::fs;
use std::path::{Path, PathBuf};

use serde_json::{Value, json};

use super::cli::run_to_string;

const DEPLOYED: &str = "29ebb403de7a102850d6cb10a62d5cc3baf723ed";
const CANDIDATE: &str = "82bb867eddb94599f68194f701c766f2b6f5a02f";
const TREE: &str = "77e892ce9b51a3af75eefc815f01668430fab57c";

/// One obligation row: function, kind, file, line, status, stop.
type Obligation<'a> = (&'a str, &'a str, &'a str, u64, &'a str, &'a str);

struct State {
    root: tempfile::TempDir,
}

impl State {
    fn new() -> Self {
        Self { root: tempfile::tempdir().unwrap() }
    }

    fn path(&self) -> &Path {
        self.root.path()
    }

    fn run_dir(&self, consumer: &str, side: &str) -> PathBuf {
        let directory = self.path().join(consumer).join(side);
        fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// Write one side's run, with the fields `edit` changes.
    fn run(&self, consumer: &str, side: &str, exit: i32, edit: impl FnOnce(&mut Value)) {
        let mut record = json!({
            "schema": "trust.seal-consumer-run.v1",
            "consumer": consumer,
            "tree": TREE,
            "command": "rustup run trust targo trust check --allow-l0-gaps --locked -p tla-cli",
            "seal": if side == "deployed" { DEPLOYED } else { CANDIDATE },
            "cpus": 12,
            "memory_gib": 48,
            "finished": true,
            "exit": exit,
        });
        edit(&mut record);
        let directory = self.run_dir(consumer, side);
        fs::write(directory.join("run.json"), serde_json::to_vec_pretty(&record).unwrap()).unwrap();
    }

    /// Write one side's run with published obligations. `salt` stands for the
    /// compiler's own per-obligation hash, which differs between seals.
    fn verified(&self, consumer: &str, side: &str, exit: i32, rows: &[Obligation<'_>]) {
        let directory = self.run_dir(consumer, side);
        let salt = if side == "deployed" { "d" } else { "c" };
        let mut text = format!(
            "{}\n",
            json!({"schema": "trust.obligations.v1", "package": "tla-cli", "lane": "advisory"})
        );
        for (index, (function, kind, file, line, status, stop)) in rows.iter().enumerate() {
            text.push_str(&format!("{}\n", json!({"fn": function, "source": null})));
            text.push_str(&format!(
                "{}\n",
                json!({
                    "key": format!("{function}#{salt}{index:015x}"),
                    "kind": kind,
                    "status": status,
                    "stop": stop,
                    "file": file,
                    "line": line,
                    "col": 9,
                })
            ));
        }
        fs::create_dir_all(directory.join("obligations")).unwrap();
        fs::write(directory.join("obligations/tla-cli.ndjson"), text).unwrap();
        self.run(consumer, side, exit, |record| record["obligations"] = json!("obligations"));
    }

    fn tested(&self, side: &str, exit: i32, arguments: Value, observations: &[Value]) {
        self.verified("ty", side, exit, &[at("f", "src/lib.rs", 10, PROVED)]);
        let path = self.run_dir("ty", side).join("obligations/tla-cli.ndjson");
        let text = fs::read_to_string(&path).unwrap();
        let (header, proofs) = text.split_once('\n').unwrap();
        let mut header: Value = serde_json::from_str(header).unwrap();
        header["concluded"] = json!(true);
        header["tests"] = arguments;
        let mut text = format!("{header}\n");
        for observation in observations {
            text.push_str(&format!("{observation}\n"));
        }
        text.push_str(proofs);
        fs::write(path, text).unwrap();
        self.run("ty", side, exit, |record| {
            record["obligations"] = json!("obligations");
            record["command"] = json!("rustup run trust targo trust test --locked -p tla-cli");
        });
    }

    fn compare(&self, extra: &[&str]) -> (u8, String) {
        let mut args = vec!["--state".to_string(), self.path().display().to_string()];
        args.extend(extra.iter().map(|argument| (*argument).to_string()));
        run_to_string(&args)
    }

    fn verdict(&self, consumer: &str) -> Option<Value> {
        let bytes = fs::read(self.path().join(consumer).join("verdict.json")).ok()?;
        Some(serde_json::from_slice(&bytes).unwrap())
    }
}

fn line<'a>(text: &'a str, consumer: &str) -> &'a str {
    text.lines()
        .find(|line| line.split('\t').nth(1) == Some(consumer))
        .unwrap_or_else(|| panic!("no line for {consumer} in:\n{text}"))
}

const PROVED: (&str, &str) = ("proved", "solved");
const UNDECIDED: (&str, &str) = ("unknown", "unclassified");
const RUNTIME: (&str, &str) = ("runtime_checked", "unclassified");

fn at<'a>(
    function: &'a str,
    file: &'a str,
    line: u64,
    verdict: (&'a str, &'a str),
) -> Obligation<'a> {
    (function, "assert", file, line, verdict.0, verdict.1)
}

#[test]
fn green_runs_with_the_same_proofs_pass_and_record_the_verdict() {
    let state = State::new();
    let rows = [at("ty::a", "src/a.rs", 3, PROVED), at("ty::b", "src/b.rs", 7, UNDECIDED)];
    state.verified("ty", "deployed", 0, &rows);
    state.verified("ty", "candidate", 0, &rows);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "ty").starts_with("PASS\t"), "{text}");
    let verdict = state.verdict("ty").unwrap();
    assert_eq!(verdict["verdict"], "PASS");
    assert_eq!(verdict["candidate"]["seal"], CANDIDATE);
    assert_eq!(verdict["budget"], json!({"cpus": 12, "memory_gib": 48}));
}

#[test]
fn a_red_candidate_that_only_decides_more_is_a_shared_red() {
    let state = State::new();
    state.verified(
        "ty",
        "deployed",
        1,
        &[
            at("ty::a", "src/a.rs", 3, PROVED),
            at("ty::b", "src/b.rs", 7, ("failed", "solved")),
            at("ty::c", "src/c.rs", 9, ("unknown", "rss-backstop")),
            at("ty::d", "src/d.rs", 2, UNDECIDED),
        ],
    );
    state.verified(
        "ty",
        "candidate",
        1,
        &[
            at("ty::a", "src/a.rs", 3, PROVED),
            at("ty::b", "src/b.rs", 7, ("failed", "solved")),
            // Refuted now, undecided before: disclosed, not a lost proof.
            at("ty::c", "src/c.rs", 9, ("failed", "solved")),
            at("ty::d", "src/d.rs", 2, PROVED),
        ],
    );
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    let row = line(&text, "ty");
    assert!(row.starts_with("SHARED_RED\t"), "{text}");
    assert!(row.contains("proved 1 -> 2"), "{text}");
    assert!(row.contains("candidate-only failed rows 1"), "{text}");
    let verdict = state.verdict("ty").unwrap();
    assert_eq!(verdict["disclosures"]["candidate_only_failed"], json!({"unknown/rss-backstop": 1}));
    assert_eq!(verdict["new_reds"], json!([]));
}

#[test]
fn a_proof_the_deployed_seal_had_is_a_new_red_even_when_others_are_gained() {
    let state = State::new();
    state.verified(
        "ty",
        "deployed",
        1,
        &[
            at("<ty::S as core::default::Default>::default", "src/s.rs", 517, PROVED),
            at("<ty::S as core::default::Default>::default", "src/s.rs", 520, RUNTIME),
            at("ty::other", "src/o.rs", 1, UNDECIDED),
        ],
    );
    state.verified(
        "ty",
        "candidate",
        1,
        &[
            // The same function and kind: one proof lost, one gained. The gain
            // at another site does not stand in for the loss.
            at("<ty::S as core::default::Default>::default", "src/s.rs", 517, RUNTIME),
            at("<ty::S as core::default::Default>::default", "src/s.rs", 520, PROVED),
            at("ty::other", "src/o.rs", 1, PROVED),
        ],
    );
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(line(&text, "ty").starts_with("NEW_RED\t"), "{text}");
    let lost = text.lines().filter(|line| line.starts_with("  NEW\t")).collect::<Vec<_>>();
    assert_eq!(lost.len(), 1, "{text}");
    assert!(lost[0].contains("lost proof\t"), "{text}");
    assert!(lost[0].contains("<ty::S as core::default::Default>::default"), "{text}");
    assert!(lost[0].contains("src/s.rs:517:9"), "{text}");
    assert!(lost[0].contains("now runtime_checked/unclassified"), "{text}");
    assert!(text.ends_with("COMPARE-SEAL: NEW_RED in 1 of 1 consumer(s)\n"), "{text}");
}

#[test]
fn a_refuted_row_the_deployed_seal_proved_is_a_lost_proof_not_a_disclosure() {
    let state = State::new();
    state.verified("ty", "deployed", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    state.verified("ty", "candidate", 1, &[at("ty::a", "src/a.rs", 3, ("failed", "solved"))]);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("now failed/solved"), "{text}");
    assert_eq!(state.verdict("ty").unwrap()["disclosures"]["candidate_only_failed"], json!({}));
}

#[test]
fn a_clock_stopped_loss_is_a_new_red_and_says_so() {
    let state = State::new();
    state.verified("ty", "deployed", 1, &[at("ty::expr_to_json", "src/c.rs", 606, PROVED)]);
    state.verified(
        "ty",
        "candidate",
        1,
        &[at("ty::expr_to_json", "src/c.rs", 606, ("runtime_checked", "wall-backstop"))],
    );
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("  NEW\tlost proof (clock-stopped)\t"), "{text}");
    assert_eq!(state.verdict("ty").unwrap()["disclosures"]["lost_clock_stopped"], 1);
}

#[test]
fn a_site_that_only_moved_is_not_a_lost_proof() {
    // The sysroot's source lines differ between two compilers: the same
    // obligation of the same function sits at another line and is still proved.
    let state = State::new();
    state.verified(
        "ty",
        "deployed",
        1,
        &[("ty::flatten", "overflow:sub", "library/alloc/src/macros.rs", 60, "proved", "solved")],
    );
    state.verified(
        "ty",
        "candidate",
        1,
        &[("ty::flatten", "overflow:sub", "library/alloc/src/macros.rs", 72, "proved", "solved")],
    );
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "ty").starts_with("SHARED_RED\t"), "{text}");
    assert_eq!(state.verdict("ty").unwrap()["disclosures"]["vanished"], 0);
}

#[test]
fn a_moved_site_that_is_no_longer_proved_is_a_new_red() {
    let state = State::new();
    state.verified(
        "ty",
        "deployed",
        1,
        &[("ty::flatten", "overflow:sub", "library/alloc/src/macros.rs", 60, "proved", "solved")],
    );
    state.verified(
        "ty",
        "candidate",
        1,
        &[(
            "ty::flatten",
            "overflow:sub",
            "library/alloc/src/macros.rs",
            72,
            "unknown",
            "unclassified",
        )],
    );
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(
        text.contains(
            "  NEW\tlost proof (site moved)\ttla-cli\tty::flatten\toverflow:sub\t1 row(s)"
        ),
        "{text}"
    );
}

#[test]
fn an_obligation_the_candidate_no_longer_has_is_disclosed_not_red() {
    let state = State::new();
    state.verified(
        "ty",
        "deployed",
        1,
        &[
            ("ty::flatten", "overflow:sub", "library/alloc/src/macros.rs", 60, "proved", "solved"),
            at("ty::flatten", "src/f.rs", 4, UNDECIDED),
        ],
    );
    // No `overflow:sub` obligation of this function exists under the candidate.
    state.verified("ty", "candidate", 1, &[at("ty::flatten", "src/f.rs", 4, UNDECIDED)]);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "ty").contains("vanished 1"), "{text}");
    assert_eq!(state.verdict("ty").unwrap()["verdict"], "SHARED_RED");
}

#[test]
fn a_failing_test_only_the_candidate_names_is_a_new_red() {
    let state = State::new();
    let shared = "-p aterm-containment --lib -- actuator::tests::shell_compat";
    let new = "-p aterm-lab-clock --test live -- a_step_moves_the_wall";
    state.run("aterm", "deployed", 1, |record| record["reds"] = json!([shared]));
    state.run("aterm", "candidate", 1, |record| record["reds"] = json!([shared]));
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "aterm").starts_with("SHARED_RED\t"), "{text}");

    state.run("aterm", "candidate", 1, |record| record["reds"] = json!([shared, new]));
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains(&format!("  NEW\tnamed red\t{new}\n")), "{text}");
    assert!(!text.contains(&format!("named red\t{shared}")), "{text}");
}

fn libtest_case(outcome: &str) -> [Value; 2] {
    [
        json!({"test_harness": "test/tla-cli", "concluded": true, "reason": null}),
        json!({"test": "test/tla-cli::cases::smoke", "outcome": outcome}),
    ]
}

#[test]
fn concluded_native_test_rows_are_compared_alongside_proofs() {
    let state = State::new();
    state.tested("deployed", 101, json!([]), &libtest_case("failed"));
    state.tested("candidate", 101, json!([]), &libtest_case("failed"));
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 0, "{out}");
    assert!(line(&out, "ty").contains("SHARED_RED"), "{out}");

    // Both commands still exit red. The test case regressed independently.
    state.tested("deployed", 101, json!([]), &libtest_case("passed"));
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 1, "{out}");
    let verdict = state.verdict("ty").unwrap();
    assert_eq!(verdict["new_reds"], json!(["failed test\ttla-cli\ttest/tla-cli::cases::smoke"]));
    assert_eq!(verdict["disclosures"]["proved_candidate"], json!(1));

    // A later step can leave the enclosing shell command successful.
    state.tested("candidate", 0, json!([]), &libtest_case("failed"));
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 1, "{out}");
    assert_eq!(state.verdict("ty").unwrap()["new_reds"], verdict["new_reds"]);
}

#[test]
fn test_measurement_must_conclude_for_the_same_population() {
    let state = State::new();
    state.tested("deployed", 0, json!([]), &libtest_case("passed"));
    let mut incomplete = libtest_case("passed");
    incomplete[0]["concluded"] = json!(false);
    incomplete[0]["reason"] = json!("interrupted");
    for (exit, arguments, observations, reason) in [
        (0, json!([]), incomplete.as_slice(), "did not report clean completion"),
        (0, json!([]), libtest_case("not concluded").as_slice(), "has not concluded"),
        (0, json!([]), libtest_case("ignored").as_slice(), "different test populations"),
        (0, json!([]), &libtest_case("passed")[..1], "different test populations"),
        (0, json!(["--ignored"]), libtest_case("passed").as_slice(), "different test populations"),
    ] {
        state.tested("candidate", exit, arguments, observations);
        let (code, out) = state.compare(&[]);
        assert_eq!(code, 3, "{out}");
        assert!(out.contains(reason), "wanted {reason:?} in {out}");
        assert!(state.verdict("ty").is_none());
    }
}

#[test]
fn empty_test_populations_can_accompany_measured_obligations() {
    let state = State::new();
    for side in ["deployed", "candidate"] {
        state.tested(side, 0, json!([]), &[]);
    }
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(state.verdict("ty").unwrap()["verdict"], "PASS");

    let path = state.run_dir("ty", "candidate").join("obligations/tla-cli.ndjson");
    let text = fs::read_to_string(&path).unwrap();
    let (header, _) = text.split_once('\n').unwrap();
    let mut header: Value = serde_json::from_str(header).unwrap();
    let mut text = format!("{header}\n");
    for observation in libtest_case("passed") {
        text.push_str(&format!("{observation}\n"));
    }
    fs::write(&path, text).unwrap();
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 3, "{out}");
    assert!(out.contains("hold no trust.obligations.v1 obligation row"), "{out}");

    // Keep valid proofs, but omit evidence present under the other seal.
    state.tested("candidate", 0, json!([]), &[]);
    let text = fs::read_to_string(&path).unwrap();
    let (_, proofs) = text.split_once('\n').unwrap();
    header.as_object_mut().unwrap().remove("tests");
    fs::write(path, format!("{header}\n{proofs}")).unwrap();
    let (code, out) = state.compare(&[]);
    assert_eq!(code, 3, "{out}");
    assert!(out.contains("report test evidence for different packages"), "{out}");
}

#[test]
fn a_worse_ending_is_a_new_red_and_the_same_ending_is_shared() {
    let stopped = |record: &mut Value| record["stopped_at_bound"] = json!(true);
    // Green before, red now.
    let state = State::new();
    state.run("aterm", "deployed", 0, |_| {});
    state.run("aterm", "candidate", 101, |_| {});
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("  NEW\tending\tdeployed exit 0\tcandidate exit 101\n"), "{text}");

    // Both ended by the bound: neither has a verdict, and that is shared.
    let state = State::new();
    state.run("clean", "deployed", 3, stopped);
    state.run("clean", "candidate", 3, stopped);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "clean").starts_with("SHARED_RED\t"), "{text}");

    // The deployed seal finished red; the candidate did not finish.
    let state = State::new();
    state.run("clean", "deployed", 1, |_| {});
    state.run("clean", "candidate", 3, stopped);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(text.contains("candidate stopped at its bound (exit 3)"), "{text}");

    // A candidate that goes green where the deployed seal was red passes.
    let state = State::new();
    state.run("ay", "deployed", 2, |_| {});
    state.run("ay", "candidate", 0, |_| {});
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "ay").starts_with("PASS\t"), "{text}");
}

#[test]
fn runs_of_unequal_budget_tree_or_command_are_not_compared() {
    for (field, value, reason) in [
        (
            "cpus",
            json!(4),
            "not under the same budget: deployed 4 CPU/48 GiB, candidate 12 CPU/48 GiB",
        ),
        ("memory_gib", json!(32), "not under the same budget"),
        ("tree", json!("6439f3cc"), "not of the same tree"),
        ("command", json!("targo trust check"), "not of the same command"),
        ("seal", json!(CANDIDATE), "both runs are of one seal"),
    ] {
        let state = State::new();
        state.run("ty", "deployed", 1, |record| record[field] = value.clone());
        state.run("ty", "candidate", 1, |_| {});
        let (code, text) = state.compare(&[]);
        assert_eq!(code, 3, "{field}: {text}");
        let row = line(&text, "ty");
        assert!(row.starts_with("INCOMPARABLE\t") && row.contains(reason), "{field}: {text}");
        assert!(state.verdict("ty").is_none(), "{field}: an incomparable pair records no verdict");
    }
}

#[test]
fn an_unfinished_consumer_is_pending_and_a_later_run_resumes_the_table() {
    let state = State::new();
    state.run("aterm", "deployed", 0, |_| {});
    state.run("aterm", "candidate", 0, |_| {});
    state.run("ty", "deployed", 1, |_| {});
    state.run("ty", "candidate", 1, |record| record["finished"] = json!(false));
    let (code, text) = state.compare(&["--require", "aterm,ty,clean"]);
    assert_eq!(code, 3, "{text}");
    assert!(line(&text, "aterm").starts_with("PASS\t"), "{text}");
    assert!(line(&text, "ty").starts_with("PENDING\t"), "{text}");
    assert!(line(&text, "ty").contains("has not finished"), "{text}");
    // A required consumer with no directory is pending, not skipped.
    assert!(line(&text, "clean").starts_with("PENDING\t"), "{text}");
    assert!(
        text.ends_with("COMPARE-SEAL: COULD NOT RUN — 2 of 3 consumer(s) not decided\n"),
        "{text}"
    );
    assert!(state.verdict("aterm").is_some() && state.verdict("ty").is_none());

    // The runs finish; the same command completes the table and keeps what it
    // had already decided.
    let stopped = |record: &mut Value| record["stopped_at_bound"] = json!(true);
    state.run("ty", "candidate", 1, |_| {});
    state.run("clean", "deployed", 3, stopped);
    state.run("clean", "candidate", 3, stopped);
    let (code, text) = state.compare(&["--require", "aterm,ty,clean"]);
    assert_eq!(code, 0, "{text}");
    assert!(line(&text, "aterm").contains("(recorded verdict kept)"), "{text}");
    assert!(!line(&text, "ty").contains("(recorded verdict kept)"), "{text}");
    assert!(text.ends_with("COMPARE-SEAL: no new red in 3 consumer(s)\n"), "{text}");
}

#[test]
fn a_recorded_verdict_is_not_kept_once_a_run_changes() {
    let state = State::new();
    state.verified("ty", "deployed", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    state.verified("ty", "candidate", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    assert_eq!(state.compare(&[]).0, 0);
    // The candidate is run again and no longer proves the row: the obligations
    // changed, `run.json` did not.
    state.verified("ty", "candidate", 1, &[at("ty::a", "src/a.rs", 3, RUNTIME)]);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(!text.contains("(recorded verdict kept)"), "{text}");
    assert_eq!(state.verdict("ty").unwrap()["verdict"], "NEW_RED");
}

#[test]
fn a_recorded_verdict_cannot_override_the_same_runs() {
    let state = State::new();
    state.verified("ty", "deployed", 0, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    state.verified("ty", "candidate", 0, &[at("ty::a", "src/a.rs", 3, RUNTIME)]);
    assert_eq!(state.compare(&[]).0, 1);
    let path = state.path().join("ty/verdict.json");
    let original = fs::read(&path).unwrap();

    // Leave the input digests untouched while changing the recorded result.
    for (field, replacement) in [("verdict", json!("PASS")), ("new_reds", json!([]))] {
        let mut recorded: Value = serde_json::from_slice(&original).unwrap();
        recorded[field] = replacement;
        fs::write(&path, serde_json::to_vec_pretty(&recorded).unwrap()).unwrap();

        let (code, text) = state.compare(&[]);
        assert_eq!(code, 1, "{field}: {text}");
        assert!(line(&text, "ty").starts_with("NEW_RED\t"), "{field}: {text}");
        assert!(!text.contains("(recorded verdict kept)"), "{field}: {text}");
        assert_eq!(fs::read(&path).unwrap(), original, "{field}");
    }
}

#[test]
fn a_new_red_decides_the_exit_while_another_consumer_is_pending() {
    let state = State::new();
    state.run("aterm", "deployed", 0, |_| {});
    state.run("aterm", "candidate", 1, |_| {});
    state.run("ty", "deployed", 1, |_| {});
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 1, "{text}");
    assert!(line(&text, "ty").starts_with("PENDING\t"), "{text}");
}

#[test]
fn explicit_incomplete_coverage_refuses_an_otherwise_green_comparison() {
    for side in ["deployed", "candidate"] {
        for (coverage, reason) in [
            (None, None),
            (Some(json!(true)), None),
            (Some(json!(false)), Some("obligation coverage is incomplete")),
            (Some(json!("true")), Some("coverage_complete must be a boolean")),
            (Some(Value::Null), Some("coverage_complete must be a boolean")),
        ] {
            let state = State::new();
            let measured = [at("ty::a", "src/a.rs", 3, PROVED)];
            for measured_side in ["deployed", "candidate"] {
                state.verified("ty", measured_side, 0, &measured);
                let path = state.run_dir("ty", measured_side).join("obligations/tla-cli.ndjson");
                let text = fs::read_to_string(&path).unwrap();
                let (header, rows) = text.split_once('\n').unwrap();
                let mut header: Value = serde_json::from_str(header).unwrap();
                header["concluded"] = json!(true);
                if measured_side != side {
                    header["coverage_complete"] = json!(true);
                } else if let Some(coverage) = &coverage {
                    header["coverage_complete"] = coverage.clone();
                }
                fs::write(path, format!("{header}\n{rows}")).unwrap();
            }
            let (code, text) = state.compare(&["--require", "ty"]);
            if let Some(reason) = reason {
                assert_eq!(code, 3, "{side}: {coverage:?}: {text}");
                assert!(line(&text, "ty").contains("tla-cli.ndjson"), "{text}");
                assert!(line(&text, "ty").contains(reason), "{text}");
                assert!(state.verdict("ty").is_none());
            } else {
                assert_eq!(code, 0, "{side}: {coverage:?}: {text}");
                assert_eq!(state.verdict("ty").unwrap()["verdict"], "PASS");
            }
        }
    }
}

#[test]
fn an_unconcluded_package_is_never_compared_as_empty() {
    for side in ["deployed", "candidate"] {
        for concluded in [json!(false), json!("true"), Value::Null] {
            let state = State::new();
            let measured = [at("ty::a", "src/a.rs", 3, PROVED)];
            state.verified("ty", "deployed", 1, &measured);
            state.verified("ty", "candidate", 1, &measured);

            // The command ended and another package measured its obligations,
            // but this package never reached verification.
            let record = state.run_dir("ty", side).join("obligations/other-package.ndjson");
            let mut header = json!({
                "schema": "trust.obligations.v1",
                "package": "other-package",
                "concluded": concluded,
            });
            fs::write(&record, format!("{header}\n")).unwrap();
            let (code, text) = state.compare(&["--require", "ty"]);
            assert_eq!(code, 3, "{side}: {header}: {text}");
            assert!(line(&text, "ty").contains("other-package.ndjson"), "{text}");
            assert!(line(&text, "ty").contains("concluded"), "{text}");
            assert!(state.verdict("ty").is_none());

            // A measured package can have zero obligations. The declared
            // completion and the measured sibling make the runs comparable.
            header["concluded"] = json!(true);
            fs::write(&record, format!("{header}\n")).unwrap();
            let (code, text) = state.compare(&["--require", "ty"]);
            assert_eq!(code, 0, "{text}");
            assert!(line(&text, "ty").starts_with("SHARED_RED\t"), "{text}");
        }
    }
}

#[test]
fn malformed_evidence_is_refused_not_read_as_empty() {
    // Obligations are named and hold no row.
    let state = State::new();
    state.verified("ty", "deployed", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    state.verified("ty", "candidate", 1, &[]);
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 3, "{text}");
    assert!(line(&text, "ty").contains("hold no trust.obligations.v1 obligation row"), "{text}");

    // A row without a status.
    let state = State::new();
    state.verified("ty", "deployed", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    state.verified("ty", "candidate", 1, &[at("ty::a", "src/a.rs", 3, PROVED)]);
    let records = state.path().join("ty/candidate/obligations/tla-cli.ndjson");
    let text = fs::read_to_string(&records).unwrap().replace("\"status\":\"proved\",", "");
    fs::write(&records, text).unwrap();
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 3, "{text}");
    assert!(line(&text, "ty").contains("an obligation without status"), "{text}");

    // A run that says it was stopped at its bound and exited 0, an unknown
    // field, and a directory that holds another consumer's runs.
    for (edit, reason) in [
        (
            (|record: &mut Value| record["stopped_at_bound"] = json!(true)) as fn(&mut Value),
            "cannot have exited 0",
        ),
        (|record: &mut Value| record["waived"] = json!(true), "unknown field `waived`"),
        (|record: &mut Value| record["schema"] = json!("v0"), "schema is \"v0\""),
    ] {
        let state = State::new();
        state.run("ty", "deployed", 0, |_| {});
        state.run("ty", "candidate", 0, edit);
        let (code, text) = state.compare(&[]);
        assert_eq!(code, 3, "{text}");
        assert!(line(&text, "ty").contains(reason), "{reason}: {text}");
    }
    let state = State::new();
    state.run("ty", "deployed", 0, |record| record["consumer"] = json!("clean"));
    state.run("ty", "candidate", 0, |record| record["consumer"] = json!("clean"));
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 3, "{text}");
    assert!(line(&text, "ty").contains("holds runs of consumer \"clean\""), "{text}");
}

#[test]
fn usage_errors_and_an_empty_state_are_not_verdicts() {
    let (code, text) = run_to_string(&[]);
    assert_eq!(code, 2);
    assert!(text.contains("--state is required"), "{text}");
    let (code, text) = run_to_string(&["--state".into(), "x".into(), "--waive".into()]);
    assert_eq!(code, 2);
    assert!(text.contains("unknown argument \"--waive\""), "{text}");
    let (code, _) =
        run_to_string(&["--state".into(), "x".into(), "--require".into(), "../y".into()]);
    assert_eq!(code, 2);
    let (code, text) = run_to_string(&["--help".into()]);
    assert_eq!(code, 0);
    assert!(text.starts_with("Usage: targo trust gate compare-seal"), "{text}");

    let state = State::new();
    let (code, text) = state.compare(&[]);
    assert_eq!(code, 3, "{text}");
    assert!(text.contains("holds no consumer"), "{text}");
    let missing = state.path().join("absent");
    let (code, _) = run_to_string(&["--state".into(), missing.display().to_string()]);
    assert_eq!(code, 3);
}
