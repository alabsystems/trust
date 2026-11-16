//! Trust (OR-A1, owner ruling 2026-09-27 — increment 1a): the MACHINE surfaces
//! of a citation credited only UNDER the function's own `requires`.
//!
//! The UI fixtures (`tests/ui/trust/e9_requires_hypothesis_*.rs`) pin the human
//! notes; this recipe pins what they cannot see — the JSON wire row and the
//! spec-clean goal row — because that is where the ruling's marker and the two
//! soundness holes the 2026-09-27 critique found would show:
//!
//!  * **kernel-canonical** (`canonical.rs`, probe r1's shape): the one row only
//!    the citation proves (the `SpecEnsuresUnparseable` sentinel) is `proved`
//!    under `clean-kernel-requires-canonical-citation`, retired to
//!    `postcond`, and ships NO `proof_evidence` — the authenticated boundary
//!    withholds it. Its spec-clean goal row says `rung: under-requires`,
//!    `requires_link: kernel-canonical`, and lists the carried hypothesis with
//!    its LIFTED graded spelling.
//!  * **H2** (`allowlisted.rs::eqk`, probe r5/c3's shape): the solver already
//!    proved the postcondition row `Certified` with `clean-cic` evidence
//!    (measured on c3, 2026-09-27: `vc:…:postcondition:0`, solver
//!    `trust-full-verifier`, `trust-certify`/`clean-kernel`, `Certified`). A
//!    conditional credit must NOT demote it: that row keeps its solver, its
//!    evidence and its assurance, and no row of `eqk` carries a
//!    `clean-kernel-requires-*` label.
//!  * **allow-listed** (`allowlisted.rs::eqk_five`): the sentinel row is proved
//!    under `clean-kernel-requires-allowlist-citation`, no evidence.
//!  * **H1** (`mixed.rs`, in-walk, and `mixed_deferred.rs`, post-walk): on a
//!    MIXED surface the uncited lane seals the rows the citation lanes own; with
//!    an allow-listed cited half every one of them carries the allow-list label
//!    — never `clean-kernel-citation`, never evidence.
//!
//! MEASURED on stage 1 (ora1-land, 2026-09-28): every assertion below passes; the
//! native-envelope assertion was corrected to what the publication predicate
//! actually reads (see `assert_conditional_rows`).

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const CANONICAL_LABEL: &str = "clean-kernel-requires-canonical-citation";
const ALLOWLIST_LABEL: &str = "clean-kernel-requires-allowlist-citation";

fn function_result(stderr: &str, function: &str) -> serde_json::Value {
    let function_token = format!("\"function\":\"{function}\"");
    let rows: Vec<serde_json::Value> = stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:") && line.contains(&function_token))
        .map(|line| {
            serde_json::from_str(&line["TRUST_JSON:".len()..])
                .expect("every TRUST_JSON line must be a JSON object")
        })
        .filter(|row: &serde_json::Value| row["type"] == "function_result")
        .collect();
    assert_eq!(rows.len(), 1, "exactly one function_result row for {function}:\n{stderr}");
    rows.into_iter().next().expect("checked")
}

fn results(row: &serde_json::Value) -> &Vec<serde_json::Value> {
    row["results"].as_array().expect("results array")
}

fn solver(result: &serde_json::Value) -> &str {
    result["solver"].as_str().unwrap_or_default()
}

/// Every row carrying `label` is a proved postcondition with NO proof evidence,
/// and at least one row carries it; no row of the function carries the
/// `Certified` citation label.
fn assert_conditional_rows(row: &serde_json::Value, label: &str) {
    let labelled: Vec<&serde_json::Value> =
        results(row).iter().filter(|result| solver(result) == label).collect();
    assert!(!labelled.is_empty(), "some row must carry `{label}`: {row}");
    for result in labelled {
        assert_eq!(result["outcome"], "proved", "a credited row counts as proved: {result}");
        assert_eq!(result["kind"], "postcond", "the sentinel is retired: {result}");
        assert!(
            result["proof_evidence"].is_null(),
            "a conditional row hands out no kernel proof term, so the authenticated \
             boundary withholds it: {result}"
        );
        // "Withheld" means neither publication path can fire:
        // `authenticated_proved_row_has_publication_evidence` accepts a native
        // proof (which needs `proof_evidence` AND a native TrustIr envelope) or
        // a clean-CIC kernel proof (which needs `proof_evidence`). The row may
        // still carry the native run's DIAGNOSTIC envelope — measured
        // 2026-09-28 on stage 1: `{"suite":"trust-full-verifier",
        // "present":false, "diagnostics":[bundle indexing]}`, the same shape
        // every row of a bundle-indexed function carries — but never a native
        // TrustIr that was present for this obligation, nor a native identity.
        let native = &result["native_trust_ir"];
        assert!(
            native.is_null()
                || (native["present"] == false
                    && native["request_id"].is_null()
                    && native["native_id"].is_null()),
            "a conditional row ships no native TrustIr for its obligation: {result}"
        );
    }
    for result in results(row) {
        assert_ne!(
            solver(result),
            "clean-kernel-citation",
            "a conditional credit must never be sealed under the Certified label: {result}"
        );
    }
}

fn compile(source: &str, spec_dir: Option<&str>) -> String {
    let mut command = rustc();
    command
        .input(source)
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-output=json")
        .env_remove(TRUST_NO_VERIFY_ENV);
    if let Some(dir) = spec_dir {
        rfs::create_dir(dir);
        command.arg(format!("-Ztrust-dump=spec-clean:{dir}"));
    }
    command.run().stderr_utf8()
}

fn spec_goal_rows(dir: &str) -> Vec<serde_json::Value> {
    let artifact = rfs::read_dir(dir)
        .map(|entry| entry.expect("dir entry").path())
        .find(|path| path.to_string_lossy().ends_with(".spec-clean.jsonl"))
        .expect("one spec-clean artifact");
    rfs::read_to_string(&artifact)
        .lines()
        .map(|line| serde_json::from_str(line).expect("spec-clean rows are JSON"))
        .filter(|row: &serde_json::Value| row["row"] == "goal")
        .collect()
}

fn main() {
    // ── kernel-canonical ────────────────────────────────────────────────────
    rfs::write(
        "canonical.rs",
        r#"
#![allow(dead_code)]
clean {
    def spec (n : Nat) : Nat := n
    theorem keep_spec : forall (k : UInt64),
        Nat.lt 0 (UInt64.toNat k) ->
        Eq (UInt64.toNat k) (spec (UInt64.toNat k)) :=
        fun k h => Eq.refl (UInt64.toNat k)
}

pub fn keep(k: u64) -> u64
    requires k > 0
    ensures (result as nat) == spec(k as nat) by keep_spec
{
    k
}
"#,
    );
    let stderr = compile("canonical.rs", Some("canonical-spec-clean"));
    assert_conditional_rows(&function_result(&stderr, "canonical::keep"), CANONICAL_LABEL);
    let goals = spec_goal_rows("canonical-spec-clean");
    assert_eq!(goals.len(), 1, "one graded goal for keep: {goals:#?}");
    let goal = &goals[0];
    assert_eq!(goal["verdict"], "certified", "{goal}");
    assert_eq!(goal["rung"], "under-requires", "{goal}");
    assert_eq!(goal["requires_link"], "kernel-canonical", "{goal}");
    let hypotheses = goal["hypotheses"].as_array().expect("hypotheses list");
    assert_eq!(hypotheses.len(), 1, "{goal}");
    assert_eq!(hypotheses[0]["canonical"], "k > 0", "{goal}");
    assert_eq!(hypotheses[0]["binder"], 0, "{goal}");
    assert!(
        hypotheses[0]["graded"].as_str().is_some_and(|text| text.contains("as nat")),
        "the kernel-canonical link grades the LIFTED reading: {goal}"
    );
    // Every Pi binder already prints `->` (`(k : UInt64) -> …`), so a bare
    // arrow proves nothing. The unconditional goal for this clause is an `Eq`
    // over `spec`; only the conditional one carries the lifted hypothesis
    // `k > 0`, a `Nat.lt`, as a SECOND arrow after the binder's.
    let goal_clean = goal["goal_clean"].as_str().expect("a graded goal prints its goal");
    assert!(
        goal_clean.contains("Nat.lt") && goal_clean.matches("->").count() >= 2,
        "the row prints the CONDITIONAL goal it graded, hypothesis included: {goal}"
    );

    // ── allow-listed, and H2 ────────────────────────────────────────────────
    rfs::write(
        "allowlisted.rs",
        r#"
#![allow(dead_code)]
clean {
    def five (n : Nat) : Nat := n
    theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b :=
        fun a b h => h
    theorem eq_five : forall (a : UInt64) (b : UInt64),
        Eq a b -> Eq (UInt64.toNat a) (five (UInt64.toNat b)) :=
        fun a b h => congrArg UInt64.toNat h
}

pub fn eqk(a: u64, b: u64) -> u64
    requires a == b
    ensures result == b by eq_keep
{
    a
}

pub fn eqk_five(a: u64, b: u64) -> u64
    requires a == b
    ensures (result as nat) == five(b as nat) by eq_five
{
    a
}
"#,
    );
    let stderr = compile("allowlisted.rs", None);
    // H2: the solver's `Certified` row keeps its authority and its evidence.
    let eqk = function_result(&stderr, "allowlisted::eqk");
    let certified: Vec<&serde_json::Value> = results(&eqk)
        .iter()
        .filter(|result| {
            result["proof_evidence"]["backend"] == "clean-kernel"
                && result["proof_evidence"]["strength"]["assurance"] == "Certified"
        })
        .collect();
    assert!(
        !certified.is_empty(),
        "the solver-proved postcondition row must STAY Certified with its clean-kernel \
         evidence (H2): {eqk}"
    );
    for result in &certified {
        assert_eq!(result["outcome"], "proved", "{result}");
        assert!(
            result["proof_evidence"]["artifacts"]
                .as_array()
                .is_some_and(|artifacts| artifacts.iter().any(|a| a["kind"] == "clean_cic")),
            "the publishable clean_cic artifact survives: {result}"
        );
    }
    for result in results(&eqk) {
        assert!(
            !solver(result).starts_with("clean-kernel-requires-"),
            "no row of `eqk` needed the conditional credit, so none carries it: {result}"
        );
    }
    assert_conditional_rows(&function_result(&stderr, "allowlisted::eqk_five"), ALLOWLIST_LABEL);

    // ── H1: the MIXED surface, in-walk and deferred ─────────────────────────
    for (file, function, defer) in [
        ("mixed.rs", "mixed::eqm", ""),
        (
            "mixed_deferred.rs",
            "mixed_deferred::eqm",
            "    -- naming trust_import_ here defers the whole island suffix past the walk\n",
        ),
    ] {
        rfs::write(
            file,
            format!(
                r#"
#![allow(dead_code)]
clean {{
{defer}    def five (n : Nat) : Nat := n
    theorem eq_keep : forall (a : UInt64) (b : UInt64), Eq a b -> Eq a b :=
        fun a b h => h
}}

pub fn eqm(a: u64, b: u64) -> u64
    requires a == b
    ensures result == b by eq_keep
    ensures (result as nat) == five(a as nat)
{{
    a
}}
"#
            ),
        );
        let stderr = compile(file, None);
        assert_conditional_rows(&function_result(&stderr, function), ALLOWLIST_LABEL);
    }
}
