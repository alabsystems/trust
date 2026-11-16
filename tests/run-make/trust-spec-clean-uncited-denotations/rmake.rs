//! Pins `trust-spec-clean` schema v2 at the compiler boundary. The artifact
//! must inventory every uncited function `requires`/`ensures` clause as a
//! zero-authority denotation, keep cited clauses exclusively on the graded
//! goal lane, and seal the two populations with independent exact counts.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const CRATE_NAME: &str = "spec_clean_uncited_denotations";
const SESSION: &str = "run-make-spec-clean-v2";
const DUMP_DIRECTORY: &str = "spec-clean";
const TAINTED_CRATE_NAME: &str = "spec_clean_deferred_tainted";
const TAINTED_SESSION: &str = "run-make-spec-clean-v2-tainted";
const TAINTED_DUMP_DIRECTORY: &str = "tainted-spec-clean";
const PRE_TAINTED_CRATE_NAME: &str = "spec_clean_pre_tainted";
const PRE_TAINTED_SESSION: &str = "run-make-spec-clean-v2-pre-tainted";
const PRE_TAINTED_DUMP_DIRECTORY: &str = "pre-tainted-spec-clean";
const FEEDBACK_CRATE_NAME: &str = "spec_clean_feedback_selected_carrier";
const FEEDBACK_SESSION: &str = "run-make-spec-clean-v2-feedback";
const FEEDBACK_DUMP_DIRECTORY: &str = "feedback-spec-clean";

const TAINTED_DEFERRED_SOURCE: &str = r#"
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

// This suffix is deferred because it names the Rust import, then rejected.
// The earlier theorem must not retain its in-walk Certified authority.
clean {
    theorem broken_thm : forall (a : UInt64),
        Nat.le
            (UInt64.toNat (trust_import_spec_clean_deferred_tainted__min2 a a))
            (UInt64.toNat a) :=
        this_constant_does_not_exist
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

pub fn caller(x: u64) -> u64
    ensures x >= x by u64_ge_refl
{
    x
}
"#;

const PRE_TAINTED_DEFERRED_SOURCE: &str = r#"
// This batch is checked before the deferred partition and taints the session
// before any MIR body can enter the citation-discharge lane.
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)

    theorem broken_early : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        this_constant_does_not_exist
}

// Merely carrying a deferred suffix is enough to require final adjudication.
clean {
    theorem deferred_marker : forall (a : UInt64),
        Eq (trust_import_spec_clean_pre_tainted__id a) a :=
        fun a => Eq.refl a
}

pub fn id(x: u64) -> u64 {
    x
}

pub fn caller(x: u64) -> u64
    ensures x >= x by u64_ge_refl
{
    x
}
"#;

const FEEDBACK_DEFERRED_SOURCE: &str = r#"
clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

// A valid import-bearing island forces the citation below through deferred
// post-walk adjudication, without tainting the session.
clean {
    theorem min2_import_marker : forall (a : UInt64) (b : UInt64),
        Nat.le
            (UInt64.toNat (trust_import_spec_clean_feedback_selected_carrier__min2 a b))
            (UInt64.toNat a) :=
        fun a b => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt a b)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => b) (fun _ => a))) (UInt64.toNat a))
            (instDecidableUInt64Lt a b)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat a) (UInt64.toNat b)) h)
            (fun h => @Nat.le.refl (UInt64.toNat a))
}

pub fn min2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}

// On the first full/native pass, the decreases row cannot exclude
// `phase > 0 && remaining == 0`. Both kernel-certified E4 legs admit the
// invariant as feedback; the regenerated E5 row then proves on pass two.
// The deferred citation is deliberately in the same body, so its discharge
// index must be rebound against that finally selected carrier.
pub fn feedback_cited(mut phase: u32, witness: u64) -> u64
    requires phase <= 1
    ensures witness >= witness by u64_ge_refl
{
    let mut remaining = 1u32;
    while phase > 0 invariant remaining >= phase decreases remaining {
        remaining = 0;
        phase = 0;
    }
    witness
}
"#;

fn assert_exact_keys(row: &serde_json::Value, expected: &[&str]) {
    let object = row.as_object().unwrap_or_else(|| panic!("artifact row is not an object: {row}"));
    let actual = object.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(actual, expected, "artifact row has the wrong schema: {row}");
}

fn assert_expected_clean_rejection(stderr: &str, expected: &str) {
    assert!(
        stderr.contains(expected),
        "compiler failed without the intended Clean-declaration rejection `{expected}`:\n{stderr}"
    );
    let lowercase = stderr.to_ascii_lowercase();
    for forbidden in [
        "internal compiler error",
        "the compiler unexpectedly panicked",
        "panicked at",
        "thread 'rustc' panicked",
    ] {
        assert!(
            !lowercase.contains(forbidden),
            "expected Clean rejection reached a compiler panic/ICE (`{forbidden}`):\n{stderr}"
        );
    }
}

fn read_artifact(directory: &Path) -> Vec<serde_json::Value> {
    let mut artifacts = rfs::read_dir(directory)
        .map(|entry| entry.expect("read spec-clean dump directory entry").path())
        .filter(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().ends_with(".spec-clean.jsonl"))
        })
        .collect::<Vec<_>>();
    artifacts.sort();
    assert_eq!(
        artifacts.len(),
        1,
        "one compilation unit must publish exactly one spec-clean artifact: {artifacts:?}"
    );

    let contents = rfs::read_to_string(&artifacts[0]);
    assert!(!contents.is_empty(), "spec-clean artifact is empty");
    contents
        .lines()
        .enumerate()
        .map(|(line_index, line)| {
            assert!(!line.trim().is_empty(), "blank JSONL row at line {}", line_index + 1);
            serde_json::from_str(line).unwrap_or_else(|error| {
                panic!("invalid spec-clean JSON at line {}: {error}: {line}", line_index + 1)
            })
        })
        .collect()
}

/// Semantic verifier transport, intentionally excluding timing/detail fields.
/// The spec-clean sink is observational, so enabling it must not change any
/// function's obligation kind or outcome.
fn transport_outcome_ledger(stderr: &str) -> BTreeMap<(String, String, String), usize> {
    let mut ledger = BTreeMap::new();
    for line in stderr.lines() {
        let Some(payload) = line.strip_prefix("TRUST_JSON:") else { continue };
        let Ok(value) = serde_json::from_str::<serde_json::Value>(payload) else { continue };
        if value["type"] != "function_result" {
            continue;
        }
        let function = value["function"]
            .as_str()
            .unwrap_or_else(|| panic!("function_result has no function identity: {value}"));
        *ledger
            .entry((function.to_string(), "<function-result>".to_string(), "<present>".to_string()))
            .or_default() += 1;
        for result in value["results"]
            .as_array()
            .unwrap_or_else(|| panic!("function_result has no obligation array: {value}"))
        {
            let kind = serde_json::to_string(&result["typed_kind"])
                .expect("typed obligation kind serializes");
            let outcome = result["outcome"]
                .as_str()
                .unwrap_or_else(|| panic!("obligation has no outcome: {result}"));
            *ledger.entry((function.to_string(), kind, outcome.to_string())).or_default() += 1;
        }
    }
    assert!(!ledger.is_empty(), "compiler emitted no semantic verifier transport:\n{stderr}");
    ledger
}

fn function_result(stderr: &str, expected_function: &str) -> serde_json::Value {
    let mut matches = stderr
        .lines()
        .filter_map(|line| line.strip_prefix("TRUST_JSON:"))
        .filter_map(|payload| serde_json::from_str::<serde_json::Value>(payload).ok())
        .filter(|value| {
            value["type"] == "function_result" && value["function"] == expected_function
        })
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "expected one transport result for `{expected_function}`:\n{stderr}"
    );
    matches.pop().unwrap()
}

fn main() {
    // Stock-rustc replay has neither Trust's clause grammar nor its verifier.
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        return;
    }

    let baseline = rustc()
        .input("foo.rs")
        .crate_name(CRATE_NAME)
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        // This fixture observes the compiler-authored artifact rather than
        // claiming full-program verification. Advisory keeps an unrelated
        // solver coverage gap from truncating that observational session;
        // the cited clause still has to kernel-grade `certified` below.
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=both")
        .arg(format!("-Ztrust-verify-session={SESSION}"))
        // Bootstrap can deauthorize nested compiler processes through this
        // inherited override. This fixture's explicit tracked flag owns the
        // subject compilation.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run()
        .stderr_utf8();

    let emitted = rustc()
        .input("foo.rs")
        .crate_name(CRATE_NAME)
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=both")
        .arg(format!("-Ztrust-dump=spec-clean:{DUMP_DIRECTORY}"))
        .arg(format!("-Ztrust-verify-session={SESSION}"))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run()
        .stderr_utf8();

    assert_eq!(
        transport_outcome_ledger(&baseline),
        transport_outcome_ledger(&emitted),
        "enabling the observational spec-clean sink changed verifier outcomes"
    );

    let rows = read_artifact(Path::new(DUMP_DIRECTORY));
    assert_eq!(rows.len(), 10, "expected 7 denotations, 2 goals, and 1 seal: {rows:#?}");
    assert_eq!(
        rows.last().expect("non-empty artifact")["row"],
        "session",
        "the completion seal must be the final JSONL row"
    );
    for row in &rows {
        assert_eq!(row["format"], "trust-spec-clean", "wrong format tag: {row}");
        assert_eq!(row["v"], 2, "every schema-v2 row must say v=2: {row}");
        assert_eq!(row["crate"], CRATE_NAME, "row escaped this compilation unit: {row}");
        assert_eq!(row["session"], SESSION, "row escaped this verification session: {row}");
        assert!(
            matches!(row["row"].as_str(), Some("denotation" | "goal" | "session")),
            "unknown spec-clean row kind: {row}"
        );
    }

    let denotations = rows.iter().filter(|row| row["row"] == "denotation").collect::<Vec<_>>();
    let goals = rows.iter().filter(|row| row["row"] == "goal").collect::<Vec<_>>();
    let sessions = rows.iter().filter(|row| row["row"] == "session").collect::<Vec<_>>();
    assert_eq!(denotations.len(), 7, "uncited clause inventory drifted: {rows:#?}");
    assert_eq!(goals.len(), 2, "cited goal inventory drifted: {rows:#?}");
    assert_eq!(sessions.len(), 1, "artifact must carry exactly one completion seal: {rows:#?}");

    for row in &denotations {
        assert_exact_keys(
            row,
            &[
                "format",
                "v",
                "row",
                "crate",
                "session",
                "def_path",
                "contract_index",
                "kind",
                "source",
                "clause",
                "goal_clean",
                "elab_error",
                "authority",
                "verdict",
                // Trust (ref-self I1): this zero-authority population discloses
                // a borrow-erased parameter view too — `null` unless the
                // clause's binders name a frozen shared pointee's field values.
                "view",
            ],
        );
        assert!(row["view"].is_null(), "no denotation here rests on a parameter view: {row}");
        assert_eq!(row["authority"], "none", "a denotation minted authority: {row}");
        assert_eq!(row["verdict"], "ungraded", "a denotation minted a grade: {row}");
        assert_eq!(row["source"], "native", "fixture clauses must retain native origin: {row}");
    }

    let uncited_path = format!("{CRATE_NAME}::uncited");
    let mut uncited = denotations
        .iter()
        .copied()
        .filter(|row| row["def_path"] == uncited_path)
        .collect::<Vec<_>>();
    uncited.sort_by_key(|row| row["contract_index"].as_u64().expect("numeric contract index"));
    assert_eq!(uncited.len(), 6, "every authored uncited clause must be present: {rows:#?}");
    assert_eq!(
        uncited
            .iter()
            .map(|row| row["contract_index"].as_u64().expect("numeric contract index"))
            .collect::<Vec<_>>(),
        [0, 1, 2, 3, 4, 5],
        "contract indices must be dense and stay in authored order"
    );
    assert_eq!(
        uncited.iter().map(|row| row["kind"].as_str().unwrap()).collect::<Vec<_>>(),
        ["requires", "requires", "requires", "ensures", "ensures", "ensures"]
    );

    // Ordinary typed comparisons produce inspectable canonical Clean terms.
    for index in [0usize, 1, 3, 4] {
        let row = uncited[index];
        assert!(
            row["clause"].as_str().is_some_and(|clause| !clause.is_empty()),
            "typed clause lost its canonical query spelling: {row}"
        );
        assert!(
            row["goal_clean"].as_str().is_some_and(|goal| !goal.is_empty()),
            "typed clause lost its canonical Clean denotation: {row}"
        );
        assert!(row["elab_error"].is_null(), "positive denotation carried a refusal: {row}");
    }
    // Identical authored clauses remain distinct rows while denoting the same
    // canonical proposition.
    for (left, right) in [(0usize, 1usize), (3, 4)] {
        assert_eq!(uncited[left]["clause"], uncited[right]["clause"]);
        assert_eq!(uncited[left]["goal_clean"], uncited[right]["goal_clean"]);
    }

    // Variable division stays in the query-owned typed tree, so the authored
    // clause remains inspectable. Clean has no admitted variable-divisor term,
    // however, and the producer must count an explicit elaboration refusal
    // instead of dropping the clause or guessing a proposition.
    for index in [2usize, 5] {
        let row = uncited[index];
        assert!(
            row["clause"].as_str().is_some_and(|clause| !clause.is_empty()),
            "refusal row lost its typed clause text: {row}"
        );
        assert!(row["goal_clean"].is_null(), "refusal row guessed a Clean proposition: {row}");
        assert!(
            row["elab_error"].as_str().is_some_and(|error| !error.is_empty()),
            "refusal row must say why no denotation was admitted: {row}"
        );
    }

    // The mixed bundle has one uncited requires at dense index 0 and one cited
    // ensures at dense indices 1 and 2. Only the former may enter this
    // zero-authority population.
    let mixed_path = format!("{CRATE_NAME}::cited_and_uncited");
    let mixed =
        denotations.iter().copied().filter(|row| row["def_path"] == mixed_path).collect::<Vec<_>>();
    assert_eq!(mixed.len(), 1, "cited clause was duplicated or uncited clause was dropped");
    assert_eq!(mixed[0]["contract_index"], 0);
    assert_eq!(mixed[0]["kind"], "requires");
    assert!(mixed[0]["goal_clean"].as_str().is_some_and(|goal| !goal.is_empty()));
    assert!(mixed[0]["elab_error"].is_null());

    let mut goals = goals;
    goals.sort_by_key(|row| row["contract_index"].as_u64().expect("numeric contract index"));
    for goal in &goals {
        assert_exact_keys(
            goal,
            &[
                "format",
                "v",
                "row",
                "crate",
                "session",
                "def_path",
                "contract_index",
                "origin",
                "clause",
                "theorem",
                "goal_clean",
                "elab_error",
                "verdict",
                "detail",
                // Trust (ref-self I1): written on EVERY goal row, `null` unless
                // the goal's binders name a frozen shared pointee's field
                // values through the borrow-erased E6 parameter view. Its
                // PRESENCE is what distinguishes a post-increment artifact from
                // one written before it; the schema version does not move.
                "view",
                // Trust (OR-A1): the rung `goal_clean` was graded on, the
                // requires-link of a conditional credit, and its hypotheses —
                // written on every goal row, like `view`.
                "rung",
                "requires_link",
                "hypotheses",
            ],
        );
        assert!(goal["view"].is_null(), "no goal here rests on a parameter view: {goal}");
        // Trust (OR-A1): these cited clauses certified UNCONDITIONALLY.
        assert_eq!(goal["rung"], "unconditional", "{goal}");
        assert!(goal["requires_link"].is_null(), "{goal}");
        assert!(goal["hypotheses"].is_null(), "{goal}");
        assert_eq!(goal["def_path"], mixed_path);
        assert_eq!(goal["origin"], "ensures-citation-deferred");
        assert_eq!(goal["verdict"], "certified");
        assert!(goal["goal_clean"].as_str().is_some_and(|value| !value.is_empty()));
        assert!(goal["elab_error"].is_null());
        assert!(goal["detail"].is_null());
    }
    assert_eq!(goals[0]["contract_index"], 1);
    assert_eq!(goals[0]["clause"], "x >= x");
    assert_eq!(goals[0]["theorem"], "u64_ge_refl");
    assert_eq!(
        goals[0]["goal_clean"], "(u : UInt64) -> Nat.le (UInt64.toNat u) (UInt64.toNat u)",
        "the first citation must quantify only the used `x` parameter"
    );
    assert_eq!(goals[1]["contract_index"], 2);
    assert_eq!(goals[1]["clause"], "min2(x, y) <= x");
    assert_eq!(goals[1]["theorem"], "min2_import_thm");
    assert_eq!(
        goals[1]["goal_clean"],
        "(u : UInt64) -> (u1 : UInt64) -> Nat.le (UInt64.toNat \
         (trust_import_spec_clean_uncited_denotations__min2 u u1)) (UInt64.toNat u)",
        "the second citation must quantify `x`, then `y`, and preserve their argument order"
    );

    let session = sessions[0];
    assert_exact_keys(session, &["format", "v", "row", "crate", "session", "goals", "denotations"]);
    assert_eq!(session["goals"], 2, "seal must count the graded goal population separately");
    assert_eq!(
        session["denotations"], 7,
        "seal must count positive and refused denotations without conflating them with goals"
    );

    // No denotation belonging to an unexpected function may hide in the
    // independently sealed count.
    assert!(
        denotations
            .iter()
            .all(|row| row["def_path"] == uncited_path || row["def_path"] == mixed_path),
        "unexpected function contributed a denotation: {denotations:#?}"
    );

    // Exercise the selected-carrier binding seam directly. This native loop's
    // decreases row closes only after its two certified invariant rows feed a
    // complete second verifier pass. A deferred citation in the same body must
    // therefore bind to the postcondition in the selected second-pass result
    // carrier, never to a provisional first-pass row position.
    rfs::write("feedback_selected_carrier.rs", FEEDBACK_DEFERRED_SOURCE);
    let feedback_stderr = rustc()
        .input("feedback_selected_carrier.rs")
        .crate_name(FEEDBACK_CRATE_NAME)
        .crate_type("lib")
        .emit("metadata")
        .arg("-Cstrip=none")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=strict")
        .arg("-Ztrust-verify-output=both")
        .arg(format!("-Ztrust-dump=spec-clean:{FEEDBACK_DUMP_DIRECTORY}"))
        .arg(format!("-Ztrust-verify-session={FEEDBACK_SESSION}"))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run()
        .stderr_utf8();

    let feedback_path = format!("{FEEDBACK_CRATE_NAME}::feedback_cited");
    let feedback_transport = function_result(&feedback_stderr, &feedback_path);
    let feedback_results = feedback_transport["results"]
        .as_array()
        .unwrap_or_else(|| panic!("feedback transport has no result array: {feedback_transport}"));
    assert_eq!(
        feedback_results.len(),
        6,
        "feedback carrier must contain requires, E5, both E4 legs, and both exact cited-clause \
         representations: {feedback_transport}"
    );
    for typed_kind in ["NonTermination", "LoopInvariantInitiation", "LoopInvariantConsecution"] {
        let matching = feedback_results
            .iter()
            .filter(|result| result["typed_kind"].get(typed_kind).is_some())
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1, "selected carrier lost or duplicated `{typed_kind}`");
        assert_eq!(matching[0]["outcome"], "proved", "selected `{typed_kind}` row did not close");
        assert_ne!(
            matching[0]["solver"], "clean-kernel-citation",
            "citation authority was attached to `{typed_kind}` instead of its postcondition"
        );
    }
    let cited_results = feedback_results
        .iter()
        .filter(|result| result["solver"] == "clean-kernel-citation")
        .collect::<Vec<_>>();
    assert_eq!(
        cited_results.len(),
        2,
        "one deferred citation must discharge both selected-carrier postcondition representations"
    );
    for cited_result in cited_results {
        assert_eq!(cited_result["typed_kind"], "Postcondition");
        assert_eq!(cited_result["outcome"], "proved");
    }

    let feedback_rows = read_artifact(Path::new(FEEDBACK_DUMP_DIRECTORY));
    assert_eq!(
        feedback_rows.len(),
        3,
        "feedback crate must publish one denotation, one goal, and one seal: {feedback_rows:#?}"
    );
    for row in &feedback_rows {
        assert_eq!(row["format"], "trust-spec-clean");
        assert_eq!(row["v"], 2);
        assert_eq!(row["crate"], FEEDBACK_CRATE_NAME);
        assert_eq!(row["session"], FEEDBACK_SESSION);
    }
    let feedback_denotations =
        feedback_rows.iter().filter(|row| row["row"] == "denotation").collect::<Vec<_>>();
    let feedback_goals =
        feedback_rows.iter().filter(|row| row["row"] == "goal").collect::<Vec<_>>();
    let feedback_sessions =
        feedback_rows.iter().filter(|row| row["row"] == "session").collect::<Vec<_>>();
    assert_eq!(feedback_denotations.len(), 1);
    assert_eq!(feedback_goals.len(), 1);
    assert_eq!(feedback_sessions.len(), 1);
    assert_eq!(feedback_denotations[0]["def_path"], feedback_path);
    assert_eq!(feedback_denotations[0]["contract_index"], 0);
    assert_eq!(feedback_denotations[0]["kind"], "requires");
    assert_eq!(feedback_denotations[0]["authority"], "none");
    assert_eq!(feedback_denotations[0]["verdict"], "ungraded");
    assert_eq!(feedback_goals[0]["def_path"], feedback_path);
    assert_eq!(feedback_goals[0]["contract_index"], 1);
    assert_eq!(feedback_goals[0]["origin"], "ensures-citation-deferred");
    assert_eq!(feedback_goals[0]["clause"], "witness >= witness");
    assert_eq!(feedback_goals[0]["theorem"], "u64_ge_refl");
    assert_eq!(feedback_goals[0]["verdict"], "certified");
    assert_eq!(feedback_sessions[0]["goals"], 1);
    assert_eq!(feedback_sessions[0]["denotations"], 1);

    // A later rejected deferred island. Until f563f55d64e (TG14) it tainted the
    // whole session, and the citation of the earlier theorem was quarantined as
    // `session-tainted`. TG14 isolates an ORDINARY deferred-island failure: the
    // refused unit is removed, every survivor is rechecked together from the
    // restored checkpoint, and only whole-index/environment failures keep the
    // global taint (DECISION_QUEUE "TG14 forward-reference repair"). So the
    // compile still fails and names the rejection, but `u64_ge_refl`, checked in
    // its own earlier batch, keeps its meaning and the citation is graded against
    // it. Its obligation must still be disclosed exactly once before the terminal
    // seal. This catches row loss at the post-walk seam.
    rfs::write("deferred_tainted.rs", TAINTED_DEFERRED_SOURCE);
    let tainted_failure = rustc()
        .input("deferred_tainted.rs")
        .crate_name(TAINTED_CRATE_NAME)
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg(format!("-Ztrust-dump=spec-clean:{TAINTED_DUMP_DIRECTORY}"))
        .arg(format!("-Ztrust-verify-session={TAINTED_SESSION}"))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    let tainted_stderr = tainted_failure.stderr_utf8();
    // Trust: TG14 reports the refused deferred unit through Clean's batch renderer.
    assert_expected_clean_rejection(
        &tainted_stderr,
        "`broken_thm` did not elaborate: Unknown identifier: this_constant_does_not_exist",
    );
    assert!(
        !tainted_stderr.contains("cannot be validated because an earlier Clean island was rejected"),
        "an ordinary deferred-island failure no longer taints the session (TG14):\n{tainted_stderr}"
    );

    let tainted_rows = read_artifact(Path::new(TAINTED_DUMP_DIRECTORY));
    assert_eq!(
        tainted_rows.len(),
        2,
        "tainted cited-only crate must publish one goal and one terminal seal: {tainted_rows:#?}"
    );
    for row in &tainted_rows {
        assert_eq!(row["format"], "trust-spec-clean", "wrong tainted-row format: {row}");
        assert_eq!(row["v"], 2, "tainted row escaped schema v2: {row}");
    }
    let tainted_goal = &tainted_rows[0];
    assert_exact_keys(
        tainted_goal,
        &[
            "format",
            "v",
            "row",
            "crate",
            "session",
            "def_path",
            "contract_index",
            "origin",
            "clause",
            "theorem",
            "goal_clean",
            "elab_error",
            "verdict",
            "detail",
            // Trust (ref-self I1): see the deferred-goal rows above.
            "view",
            // Trust (OR-A1): see the deferred-goal rows above.
            "rung",
            "requires_link",
            "hypotheses",
        ],
    );
    assert!(tainted_goal["view"].is_null(), "an uncited-view-free citation row rests on no view");
    // Trust (OR-A1): the grade is recorded against the unconditional goal, and
    // this session climbs no conditional rung.
    assert_eq!(tainted_goal["rung"], "unconditional", "{tainted_goal}");
    assert!(tainted_goal["requires_link"].is_null(), "{tainted_goal}");
    assert_eq!(tainted_goal["row"], "goal");
    assert_eq!(tainted_goal["crate"], TAINTED_CRATE_NAME);
    assert_eq!(tainted_goal["session"], TAINTED_SESSION);
    assert_eq!(tainted_goal["def_path"], format!("{TAINTED_CRATE_NAME}::caller"));
    assert_eq!(tainted_goal["contract_index"], 0);
    assert_eq!(tainted_goal["origin"], "ensures-citation-deferred");
    assert_eq!(tainted_goal["clause"], "x >= x");
    assert_eq!(tainted_goal["theorem"], "u64_ge_refl");
    // Trust (TG14): graded against the surviving, independently checked theorem.
    assert_eq!(tainted_goal["verdict"], "certified");
    assert_eq!(tainted_goal["goal_clean"], "(u : UInt64) -> Nat.le (UInt64.toNat u) (UInt64.toNat u)");
    assert!(tainted_goal["clause"].as_str().is_some_and(|value| !value.is_empty()));
    assert!(tainted_goal["goal_clean"].as_str().is_some_and(|value| !value.is_empty()));
    assert!(tainted_goal["elab_error"].is_null());

    let tainted_seal = &tainted_rows[1];
    assert_exact_keys(
        tainted_seal,
        &["format", "v", "row", "crate", "session", "goals", "denotations"],
    );
    assert_eq!(tainted_seal["row"], "session");
    assert_eq!(tainted_seal["crate"], TAINTED_CRATE_NAME);
    assert_eq!(tainted_seal["session"], TAINTED_SESSION);
    assert_eq!(tainted_seal["goals"], 1);
    assert_eq!(tainted_seal["denotations"], 0);

    // A session can also be tainted before the MIR walk. Until ab2e44cf84 the
    // verify pass still ran over such a unit: it quarantined the cited body
    // ("citation `u64_ge_refl` cannot be validated because an earlier Clean
    // island was rejected"), published its query identity as one explicit
    // `session-tainted` goal row, and sealed the session — and this block
    // pinned exactly that. ab2e44cf84 ("a rejected batch is reported at the
    // seam instead of vanishing") renders the rejection as a RESOLVE-TIME hard
    // error, so rustc aborts before the MIR walk and the spec-clean writer —
    // which lives in the verify pass — never runs. Measured on both drivers:
    // the pre-change toolchain prints the quarantine note and writes two rows;
    // this one prints only the rejection and writes nothing. The contract this
    // block now pins is the stricter one: a unit whose island batch is
    // rejected fails, names the rejection without an ICE, publishes NO
    // spec-clean artifact (a rejected compile must leave nothing a downstream
    // consumer could mistake for a graded artifact — `targo trust spec` drives
    // a fresh emission dir and refuses a missing artifact fail-closed, v6/D1),
    // and carries no positive citation evidence anywhere. If island rejection
    // ever becomes non-fatal at resolve time again, the taint rows must return
    // with it, and this block must be re-pinned to them deliberately.
    rfs::write("pre_tainted.rs", PRE_TAINTED_DEFERRED_SOURCE);
    let pre_tainted_failure = rustc()
        .input("pre_tainted.rs")
        .crate_name(PRE_TAINTED_CRATE_NAME)
        .crate_type("lib")
        .emit("metadata")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg(format!("-Ztrust-dump=spec-clean:{PRE_TAINTED_DUMP_DIRECTORY}"))
        .arg(format!("-Ztrust-verify-session={PRE_TAINTED_SESSION}"))
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    let pre_tainted_stderr = pre_tainted_failure.stderr_utf8();
    assert_expected_clean_rejection(
        &pre_tainted_stderr,
        "`broken_early` did not elaborate: Unknown identifier: this_constant_does_not_exist",
    );
    // No positive citation evidence may survive a rejected batch, in any form.
    assert!(
        !pre_tainted_stderr.contains("citation `u64_ge_refl` kernel-discharges"),
        "a rejected batch must not leave positive citation evidence for `u64_ge_refl`:\n\
         {pre_tainted_stderr}"
    );
    // And no artifact: the writer never ran, so the dump directory is absent or
    // holds no `.spec-clean.jsonl` — never a partial or stale one.
    let pre_tainted_dir = Path::new(PRE_TAINTED_DUMP_DIRECTORY);
    let stray = if pre_tainted_dir.exists() {
        rfs::read_dir(pre_tainted_dir)
            .map(|entry| entry.expect("read pre-tainted dump directory entry").path())
            .filter(|path| {
                path.file_name()
                    .is_some_and(|name| name.to_string_lossy().ends_with(".spec-clean.jsonl"))
            })
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    assert!(
        stray.is_empty(),
        "a unit rejected at the resolve seam must publish no spec-clean artifact: {stray:?}"
    );
}
