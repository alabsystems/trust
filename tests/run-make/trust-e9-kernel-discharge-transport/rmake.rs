//! Trust (2026-09-12): the MACHINE report must agree with the TEXT report on an
//! E9 kernel discharge.
//!
//! `reports/2026-09-11-island-probe-level-is-zero.md` §6 measured, on the
//! probe's variant E (`defeq.rs` here): bare `trustc -Ztrust-verify=on` prints
//! "2 proved … 2 kernel-certified" and exits 0, while the same run with
//! `-Ztrust-verify-output=json` carried both rows as `"outcome":"unknown"`,
//! `"kind":"unknown"`, typed `UnsupportedMir` — the sentinel rows the E9
//! discharge exists to retire — so `targo trust check` (which reads the JSON)
//! failed a crate the compiler had certified. The cited lane (`cited.rs`) had
//! the same defect: `"solver":"clean-kernel-citation"` rows transported
//! `unknown`.
//!
//! Pins, for both lanes:
//!  * every `TRUST_JSON` result row of the discharged function is
//!    `"outcome":"proved"` under the kernel solver label, and is presented as
//!    `"kind":"postcond"` (`VcKind::Postcondition::transport_tag`) with a typed
//!    `Postcondition` kind and the `postcondition` description — the sentinel is
//!    RETIRED, not merely relabelled: no row still carries an `UnsupportedMir`
//!    typed kind (the compact tag a surviving sentinel prints is `unknown`, as
//!    the CONTROL below measures, so it is the typed kind that discriminates);
//!  * the function_result tally reads `proved == total`, `unknown == 0`;
//!
//! What the discharge deliberately does NOT rewrite, measured 2026-09-12 on
//! `defeq::min2` and asserted below so that a future rewrite is a decision
//! rather than an accident:
//!  * `obligation_id` keeps its `unsupported:<fn>:<contract index>` minting
//!    spelling. That id is not a label, it is the compiler-sealed KEY: the
//!    monitor binding validator requires it byte-for-byte
//!    (`trust_verify.rs`'s `canonical_monitor_contract_id_matches_record`
//!    compares against `format!("unsupported:{}:{}", ..)`), and
//!    `unsupported_monitor_obligation_source_index` recovers the clause's dense
//!    source index by stripping exactly that prefix. Rewriting it on the wire
//!    would break the row's binding to its own sealed bundle entry.
//!  * `monitor` keeps `"status":"unmonitored"` with the unsupported-predicate
//!    reason. That is a statement about RUNTIME monitoring — no native runtime
//!    check exists for this predicate — and it stays true after a kernel
//!    discharge. Rewriting it would advertise a monitor that was never emitted.
//!  * Neither field is read as a verdict by the authenticated reader: `targo
//!    trust check` grades `outcome`/`kind`/`typed_kind`, and neither
//!    `unmonitored` nor an `unsupported:` id prefix appears anywhere in
//!    `targo-trust/src` as a grading input.
//!  * `-Ztrust-dump=spec-clean:<dir>` publishes a kernel-graded goal row for
//!    the defeq clause (`origin: ensures-island-defeq`, `theorem: defeq:min_isl`,
//!    `verdict: certified`) — `targo trust spec --emit clean` used to print
//!    "0 kernel-graded goal(s)" for the very clause the text report called
//!    kernel-certified;
//!  * CONTROL: an ensures sentinel that NO kernel lane discharged still
//!    transports `unknown` under `unsupported_mir` — the fail-closed demotion
//!    is untouched for solver-labelled rows.

use std::path::Path;

use run_make_support::{rfs, rustc, serde_json};

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";

fn json_rows<'a>(stderr: &'a str, function: &str) -> Vec<serde_json::Value> {
    let function_token = format!("\"function\":\"{function}\"");
    stderr
        .lines()
        .filter(|line| line.starts_with("TRUST_JSON:") && line.contains(&function_token))
        .map(|line| {
            serde_json::from_str(&line["TRUST_JSON:".len()..])
                .expect("every TRUST_JSON line must be a JSON object")
        })
        .collect()
}

/// Self-identifying prefix of the E9 `CleanCic` `context` binding record
/// (`trust_certify::clean_island::ensures_evidence::CONTEXT_MAGIC`).
const E9_CONTEXT_MAGIC: &[u8] = b"trust-certify.e9-ensures-discharge.context.v1\0";

/// Trust (E9 evidence; `wf1-probe-package` a2): a `proved` kernel row that ships
/// no `proof_evidence` is WITHHELD at the authenticated publication boundary —
/// `targo trust check` graded every Lean-discharged contract `unknown` while
/// this recipe, which looked only at `outcome`, stayed green. Pin what the
/// boundary actually demands of the row, on the REAL discharge lanes (the
/// in-crate unit test builds the authority by hand; only this recipe proves the
/// production lanes mint a payload, with `self` bound to the E6-imported Rust
/// body rather than to a stand-in island definition):
///
///  * one `clean_cic` artifact under the `trust-certify` / `clean-kernel`
///    envelope, whose artifact id IS the proof id (a content address);
///  * a typed `CleanCic` payload with a non-empty proof term, a lineage, and a
///    `context` that is THIS lane's binding record — not the violation-refutation
///    lanes' `ReducedContext`, which can never begin with the magic.
///
/// It deliberately does not recompute the content address: that framing is the
/// consumer's contract and is pinned where the consumer lives
/// (`targo-trust`'s `e9_ensures_discharge_rows_publish_only_with_their_clean_cic_artifact`).
fn assert_row_carries_e9_clean_cic_artifact(result: &serde_json::Value) {
    let proof = &result["proof_evidence"];
    assert!(proof.is_object(), "a kernel-discharged row must ship proof_evidence: {result}");
    assert_eq!(proof["suite"], "trust-certify", "{result}");
    assert_eq!(proof["backend"], "clean-kernel", "{result}");
    let artifacts = proof["artifacts"].as_array().expect("artifacts array");
    assert_eq!(artifacts.len(), 1, "exactly one CleanCic payload artifact: {result}");
    let artifact = &artifacts[0];
    assert_eq!(artifact["kind"], "clean_cic", "{result}");
    assert_eq!(artifact["format"], "trust-ir-cleancic-v2", "{result}");
    let proof_id = proof["proof_id"].as_str().expect("content-addressed proof id");
    assert!(proof_id.starts_with("clean-cic:v2:"), "{result}");
    assert_eq!(artifact["artifact_id"].as_str(), Some(proof_id), "{result}");
    let payload = &artifact["metadata"]["CleanCic"];
    assert!(payload.is_object(), "the artifact carries the typed CleanCic payload: {result}");
    assert!(
        payload["term"].as_array().is_some_and(|term| !term.is_empty()),
        "the kernel-judged proof term travels with the row: {result}"
    );
    assert!(!payload["lineage"].is_null(), "the payload is lineage-bound to its row: {result}");
    let context: Vec<u8> = payload["context"]
        .as_array()
        .expect("context bytes")
        .iter()
        .map(|byte| byte.as_u64().and_then(|b| u8::try_from(b).ok()).expect("context byte"))
        .collect();
    assert!(
        context.starts_with(E9_CONTEXT_MAGIC),
        "the context must be the E9 binding record (goal, referents, environment digest), \
         never another lane's context: {result}"
    );
}

/// `monitor_bound_key_rows` is how many of the function's rows are expected to
/// keep the sentinel's `unsupported:<fn>:<index>` obligation id. It is 1 for a
/// clause the VC lane cannot represent (`result == min_isl(a, b)`) and 0 for a
/// clause that IS in the solver fragment (`result >= x`), so it is a parameter
/// rather than a constant — the minting provenance below is what is pinned, not
/// the count itself.
fn assert_kernel_discharged_function(
    stderr: &str,
    function: &str,
    solver: &str,
    monitor_bound_key_expected: u64,
) {
    let rows = json_rows(stderr, function);
    assert_eq!(rows.len(), 1, "exactly one function_result row for {function}:\n{stderr}");
    let row = &rows[0];
    let total = row["total"].as_u64().expect("total");
    assert!(total >= 1, "{function} must carry at least one obligation: {row}");
    assert_eq!(row["proved"].as_u64(), Some(total), "proved == total for {function}: {row}");
    assert_eq!(row["unknown"].as_u64(), Some(0), "unknown == 0 for {function}: {row}");
    let results = row["results"].as_array().expect("results array");
    assert_eq!(results.len() as u64, total);
    let mut monitor_bound_key_rows = 0;
    for result in results {
        assert_eq!(result["outcome"], "proved", "every row proved: {result}");
        assert_eq!(result["solver"], solver, "the kernel solver label: {result}");
        // The compact transport tag of `VcKind::Postcondition`. An undischarged
        // sentinel prints `"kind":"unknown"` here — see the CONTROL in `main`.
        assert_eq!(result["kind"], "postcond", "the sentinel is retired: {result}");
        assert_eq!(result["typed_kind"], "Postcondition", "typed kind follows: {result}");
        // The typed kind is the discriminator: a surviving sentinel transports
        // `"typed_kind":{"UnsupportedMir":{..}}`, an object, never this string.
        assert!(
            result["typed_kind"].as_object().is_none(),
            "no row may still carry a parameterized sentinel kind: {result}"
        );
        assert_eq!(result["description"], "postcondition", "{result}");
        assert!(
            !result["description"].as_str().unwrap_or("").contains("unsupported MIR"),
            "the description must not still read as a sentinel: {result}"
        );
        assert_row_carries_e9_clean_cic_artifact(result);
        // The minting provenance the discharge deliberately leaves alone; see
        // the module comment for why each of these is load-bearing as written.
        if let Some(id) = result["obligation_id"].as_str()
            && id.starts_with("unsupported:")
        {
            monitor_bound_key_rows += 1;
            assert_eq!(
                result["monitor"]["status"], "unmonitored",
                "the monitor states a RUNTIME fact and is untouched by a kernel discharge: {result}"
            );
        }
    }
    assert_eq!(
        monitor_bound_key_rows, monitor_bound_key_expected,
        "the monitor-bound `unsupported:<fn>:<index>` keys are unchanged by the discharge: {row}"
    );
    assert!(
        !stderr.contains("\"UnsupportedMir\""),
        "no sentinel typed kind may survive a kernel discharge:\n{stderr}"
    );
}

fn main() {
    // ── the defeq lane (probe variant E) ────────────────────────────────────
    let defeq_dir = Path::new("defeq-spec-clean");
    rfs::create_dir(defeq_dir);
    let defeq = rustc()
        .input("defeq.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-output=json")
        .arg("-Ztrust-verify-session=run-make-e9-transport")
        .arg(format!("-Ztrust-dump=spec-clean:{}", defeq_dir.display()))
        // Bootstrap may deauthorize its own nested compiler processes through
        // this inherited override. A run-make recipe is a new policy boundary.
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    let defeq_stderr = defeq.stderr_utf8();
    assert_kernel_discharged_function(&defeq_stderr, "defeq::min2", "clean-kernel-defeq", 1);

    // The spec-clean artifact carries the kernel-graded defeq goal.
    let artifact = rfs::read_dir(defeq_dir)
        .map(|entry| entry.expect("dir entry").path())
        .find(|path| path.to_string_lossy().ends_with(".spec-clean.jsonl"))
        .expect("one spec-clean artifact");
    let contents = rfs::read_to_string(&artifact);
    let goals: Vec<serde_json::Value> = contents
        .lines()
        .map(|line| serde_json::from_str(line).expect("spec-clean rows are JSON"))
        .filter(|row: &serde_json::Value| row["row"] == "goal")
        .collect();
    assert_eq!(goals.len(), 1, "exactly one graded goal for min2:\n{contents}");
    let goal = &goals[0];
    assert_eq!(goal["origin"], "ensures-island-defeq", "{goal}");
    assert_eq!(goal["theorem"], "defeq:min_isl", "{goal}");
    assert_eq!(goal["verdict"], "certified", "{goal}");
    assert_eq!(goal["def_path"], "defeq::min2", "{goal}");
    assert!(
        goal["goal_clean"].as_str().is_some_and(|g| g.contains("min_isl")),
        "the goal names the island definition the kernel judged: {goal}"
    );
    let session = contents
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("row"))
        .find(|row| row["row"] == "session")
        .expect("the session seal");
    assert_eq!(session["goals"], 1, "the seal counts the goal: {session}");

    // ── the cited lane ──────────────────────────────────────────────────────
    let cited = rustc()
        .input("cited.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-output=json")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    assert_kernel_discharged_function(
        &cited.stderr_utf8(),
        "cited::keep",
        "clean-kernel-citation",
        1,
    );

    // ── the DEFERRED post-walk lane ─────────────────────────────────────────
    // Trust (E9 evidence): the third mint site. An island whose text mentions
    // `trust_import_` defers the whole authored suffix past the body walk
    // (`defer_island_suffix`), so this citation is graded and discharged by
    // `finalize_pending_import_citations` / `grade_pending_import_citation_goals`
    // rather than by the in-walk lane — a different environment (the session's
    // own, untainted) and a different install site. Both lanes above go through
    // the in-walk one, so without this the deferred site would mint unobserved.
    rfs::write(
        "deferred.rs",
        r#"
#![allow(dead_code)]
clean {
    -- naming trust_import_ here defers the whole island suffix past the walk
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
}

pub fn keep(x: u64) -> u64
    ensures result >= x by u64_ge_refl
{
    x
}
"#,
    );
    let deferred = rustc()
        .input("deferred.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-output=json")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run();
    // `result >= x` IS in the solver fragment, so this function's rows are real
    // `Postcondition` VCs and none keeps a sentinel `unsupported:` key.
    assert_kernel_discharged_function(
        &deferred.stderr_utf8(),
        "deferred::keep",
        "clean-kernel-citation",
        0,
    );

    // ── CONTROL: an undischarged sentinel keeps the fail-closed demotion ─────
    rfs::write(
        "undischarged.rs",
        r#"
#![allow(dead_code)]
clean {
    def min_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
}
// The body is NOT definitionally equal to the island definition, so the defeq
// lane refuses (a hard error under E9's say-so rule) and nothing else can
// close the clause: the sentinel must stay a sentinel on the wire.
pub fn not_min(a: u64, b: u64) -> u64
    ensures result == min_isl(a, b)
{
    if a < b { b } else { a }
}
"#,
    );
    let control = rustc()
        .input("undischarged.rs")
        .crate_type("lib")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-verify-output=json")
        .env_remove(TRUST_NO_VERIFY_ENV)
        .run_fail();
    let control_stderr = control.stderr_utf8();
    let rows = json_rows(&control_stderr, "undischarged::not_min");
    assert_eq!(rows.len(), 1, "exactly one control function_result row:\n{control_stderr}");
    let control_row = &rows[0];
    assert_eq!(control_row["proved"].as_u64(), Some(0), "{control_row}");
    let control_results = control_row["results"].as_array().expect("results array");
    assert!(!control_results.is_empty(), "{control_row}");
    for result in control_results {
        assert_eq!(result["outcome"], "unknown", "the demotion is still live: {result}");
        // The sentinel's own presentation, unchanged: the compact tag is
        // `unknown` and the typed kind is the parameterized `UnsupportedMir`
        // object. These are exactly the two fields the discharged lane above
        // requires to have MOVED, so that lane cannot pass by the demotion
        // having been switched off globally.
        assert_eq!(result["kind"], "unknown", "{result}");
        assert!(
            result["typed_kind"]["UnsupportedMir"].is_object(),
            "an undischarged ensures keeps its sentinel typed kind: {result}"
        );
        // Trust (E9 evidence): the close negative twin of the artifact pin
        // above. A payload is minted only after the whole surface re-certifies,
        // so a clause the kernel refused must carry NO kernel certificate.
        //
        // The row is NOT evidence-free — measured: it ships the native full
        // verifier's own `status: unsupported` `proof_evidence`, which is the
        // honest report of a lane that proved nothing. What must be absent is
        // the `trust-certify` / `clean-kernel` envelope and its `clean_cic`
        // artifact, which is exactly what the publication boundary looks for.
        let evidence = &result["proof_evidence"];
        assert_ne!(evidence["suite"], "trust-certify", "{result}");
        assert_ne!(evidence["backend"], "clean-kernel", "{result}");
        assert!(
            !evidence["artifacts"]
                .as_array()
                .is_some_and(|artifacts| artifacts.iter().any(|a| a["kind"] == "clean_cic")),
            "a refused discharge must not carry a kernel certificate: {result}"
        );
    }
}
