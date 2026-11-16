//@ only-unix (the private proof artifact root is a 0700 directory)

//! Trust (TRANSPORT-LINE-BUDGET-1, 2026-11-01): every `TRUST_JSON` transport line fits
//! the transport line budget, and a function whose report does not fit loses at most
//! its OWN optional evidence, disclosed, with no verdict raised.
//!
//! The defect: trustc wrote each function's report as one stderr line of unbounded
//! size. Targo caps a line at 128 MiB (`VERIFIED_TARGO_MAX_CHILD_LINE_BYTES`), closes
//! the pipe when the cap fires, and trustc died of SIGPIPE on its next write, so EVERY
//! function of the crate lost its rows (ay-sat's `reset_search_state_incremental`).
//! Half of each JSON-format line was the payload written twice: once as the
//! diagnostic's `message`, once more as its `rendered` text.
//!
//! The recipe compiles one crate under the JSON error format and the private proof
//! artifact root targo uses, first at the
//! default budget (the baseline, and the positive control that nothing is disclosed),
//! then under budgets LOWERED with the test-only knob `TRUST_TRANSPORT_LINE_BUDGET_BYTES`
//! (it can only lower the bound) and chosen from the baseline's own sizes so that
//! `big` needs each step of the ladder in turn:
//!  * step 1 withholds original-VC snapshots; step 2 proof evidence, demoting what loses
//!    a favorable label's evidence; step 3 replaces the rows by one fail-closed row;
//!  * every stderr line is at most the budget;
//!  * `big`'s envelope states the step, and its rows survive steps 1 and 2 (same count,
//!    same kinds, no outcome raised: each row ranks no higher than its baseline twin);
//!  * every function whose line fit is byte-for-byte its baseline (timings aside);
//!  * the crate summary sums the envelopes as emitted, and a warning names `big` alone.
//! NEGATIVE CONTROLS: a request ABOVE the default, and an unparseable one, change
//! nothing. The raw-stderr framing (`--error-format=human`) is bounded too.
//!
//! Review F4 (2026-11-02): the JSON line's one span names the crate root, after
//! `--remap-path-prefix`, so its length is the compile's choice. A compile whose root is
//! remapped to a 12 KB name (three times the fixed frame) must still price every line
//! exactly: the disclosure's unbounded size is at least the real unfitted line, and every
//! line fits.

use std::collections::BTreeMap;

use run_make_support::{rfs, rustc, serde_json};
use serde_json::Value;

const TRUST_NO_VERIFY_ENV: &str = "TRUST_NO_VERIFY";
const TRUST_VANILLA_REAL_RUSTC_ENV: &str = "__COMPILETEST_TRUST_VANILLA_REAL_RUSTC";
const BUDGET_ENV: &str = "TRUST_TRANSPORT_LINE_BUDGET_BYTES";
const PREFIX: &str = "TRUST_JSON:";
/// `trust_types::transport_budget::JSON_DIAGNOSTIC_FRAMING_OVERHEAD_BYTES`.
const FRAMING: u64 = 4 * 1024;
/// `trust_types::transport_budget::MIN_TRANSPORT_LINE_BUDGET_BYTES`.
const MIN_BUDGET: u64 = 16 * 1024;
/// `rustc_errors::json::TRUST_TRANSPORT_RENDERED`.
const RENDERED: &str = concat!(
    "note: Trust verification transport ",
    "(its machine-readable payload is this diagnostic's `message`)\n\n",
);

struct Run {
    stderr: String,
    /// The `file_name` of the transport notes' one span (JSON format; empty for human).
    span_file_name: String,
    /// function path -> (its function_result payload, the bytes of its stderr line)
    functions: BTreeMap<String, (Value, u64)>,
    crate_summary: Value,
    /// The messages of the compiler's warnings.
    warnings: Vec<String>,
    /// function path -> per row, whether a second baseline compile gave the row the same
    /// outcome (filled by `stable_against`; empty for runs that are not the baseline).
    stable: BTreeMap<String, Vec<bool>>,
    /// The second baseline compile's envelopes, untimed.
    again: BTreeMap<String, Value>,
}

impl Run {
    fn stable_against(&mut self, again: &Run) {
        for (name, (envelope, _)) in &self.functions {
            let (other, _) = &again.functions[name];
            let rows = envelope["results"].as_array().unwrap();
            let other_rows = other["results"].as_array().unwrap();
            assert_eq!(rows.len(), other_rows.len(), "{name}: the obligations are the same");
            let stable = rows
                .iter()
                .zip(other_rows)
                .map(|(row, other)| {
                    assert_eq!(row["kind"], other["kind"]);
                    row["outcome"] == other["outcome"]
                })
                .collect();
            self.stable.insert(name.clone(), stable);
            self.again.insert(name.clone(), untimed(other));
        }
    }
}

fn json_body_bytes(text: &str) -> u64 {
    serde_json::to_string(text).unwrap().len() as u64 - 2
}

/// What `TransportLineFraming::JsonDiagnostic` charges for a payload whose note's span
/// names `span_file_name`.
fn json_line_bytes(payload: &Value, span_file_name: &str) -> u64 {
    json_body_bytes(&format!("{PREFIX}{payload}")) + json_body_bytes(span_file_name) + FRAMING
}

/// The private, canonical proof artifact root targo hands every verifying compile, so
/// native materializations are stored by digest rather than carried inline, as in a
/// real `targo trust` run.
fn proof_artifact_root() -> std::path::PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let root = std::env::current_dir().unwrap().join("proof-artifacts");
    if !root.exists() {
        rfs::create_dir(&root);
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
    }
    std::fs::canonicalize(root).unwrap()
}

fn compile(budget: Option<&str>, human: bool) -> Run {
    compile_named(budget, human, None)
}

/// `compile`, with the crate root given by its absolute path and that directory remapped
/// to `remap` when it is set.
fn compile_named(budget: Option<&str>, human: bool, remap: Option<&str>) -> Run {
    let mut cmd = rustc();
    if let Some(remap) = remap {
        let dir = std::fs::canonicalize(std::env::current_dir().unwrap()).unwrap();
        cmd.input(dir.join("budget.rs"))
            .arg(format!("--remap-path-prefix={}={remap}", dir.display()));
    } else {
        cmd.input("budget.rs");
    }
    cmd.crate_type("lib")
        .edition("2021")
        .arg("-Ztrust-verify=on")
        .arg("-Ztrust-policy=advisory")
        .arg("-Ztrust-verify-output=json")
        .arg(format!("-Ztrust-proof-artifact-root={}", proof_artifact_root().display()))
        .arg(if human { "--error-format=human" } else { "--error-format=json" })
        .env_remove(TRUST_NO_VERIFY_ENV)
        .env_remove(BUDGET_ENV);
    if let Some(budget) = budget {
        cmd.env(BUDGET_ENV, budget);
    }
    let stderr = cmd.run().stderr_utf8();
    let mut functions = BTreeMap::new();
    let mut crate_summary = Value::Null;
    let mut warnings = Vec::new();
    let mut span_file_name: Option<String> = None;
    for line in stderr.lines() {
        let message = if human {
            match line.strip_prefix(PREFIX) {
                Some(_) => line.to_string(),
                None => continue,
            }
        } else {
            let Ok(diagnostic) = serde_json::from_str::<Value>(line) else { continue };
            let message = diagnostic["message"].as_str().unwrap_or("").to_string();
            if diagnostic["level"] == "warning" {
                warnings.push(message.clone());
            }
            if message.starts_with(PREFIX) {
                // The payload travels once: `rendered` is the fixed statement.
                assert_eq!(diagnostic["rendered"], RENDERED, "{line:.300}");
                assert_eq!(diagnostic["code"]["code"], "trust_verification_transport_v1");
                let spans = diagnostic["spans"].as_array().unwrap();
                assert_eq!(spans.len(), 1, "a transport note has one span: {line:.300}");
                let name = spans[0]["file_name"].as_str().unwrap().to_string();
                let frame = json_body_bytes(&message) + json_body_bytes(&name) + FRAMING;
                assert!(
                    line.len() as u64 <= frame,
                    "a transport line is its message and span file name plus a bounded frame: \
                     {} bytes",
                    line.len()
                );
                assert!(
                    span_file_name.as_ref().is_none_or(|seen| *seen == name),
                    "every transport note names one file"
                );
                span_file_name = Some(name);
            }
            message
        };
        let Some(payload) = message.strip_prefix(PREFIX) else { continue };
        let payload: Value = serde_json::from_str(payload).expect("transport payload is JSON");
        match payload["type"].as_str() {
            Some("function_result") => {
                let name = payload["function"].as_str().unwrap().to_string();
                let previous = functions.insert(name.clone(), (payload, line.len() as u64 + 1));
                assert!(previous.is_none(), "one envelope per function: {name}");
            }
            Some("crate_summary") => crate_summary = payload,
            _ => {}
        }
    }
    for name in ["budget::tiny", "budget::small", "budget::big"] {
        assert!(functions.contains_key(name), "{name} has an envelope:\n{stderr:.2000}");
    }
    if let Some(remap) = remap {
        // Positive control: the remap reached the span the line budget prices.
        let expected = format!("{remap}/budget.rs");
        assert_eq!(span_file_name.as_deref(), Some(expected.as_str()), "the span names the remap");
    }
    Run {
        stderr,
        span_file_name: span_file_name.unwrap_or_default(),
        functions,
        crate_summary,
        warnings,
        stable: BTreeMap::new(),
        again: BTreeMap::new(),
    }
}

/// A function envelope with the run-to-run timings zeroed.
fn untimed(envelope: &Value) -> Value {
    let mut envelope = envelope.clone();
    for row in envelope["results"].as_array_mut().unwrap() {
        row["time_ms"] = Value::from(0);
    }
    envelope
}

fn rank(outcome: &str) -> u8 {
    match outcome {
        "failed" => 0,
        "runtime_checked" => 2,
        "proved" => 3,
        _ => 1,
    }
}

fn strip(envelope: &Value, fields: &[&str]) -> Value {
    let mut envelope = envelope.clone();
    for row in envelope["results"].as_array_mut().unwrap() {
        for field in fields {
            row.as_object_mut().unwrap().remove(*field);
        }
    }
    envelope
}

/// The envelope with every evidence record's artifact payloads removed, as step 2
/// leaves a row it selects (less the diagnostic it adds).
fn hollow(envelope: &Value) -> Value {
    let mut envelope = envelope.clone();
    for row in envelope["results"].as_array_mut().unwrap() {
        for record in ["proof_evidence", "native_trust_ir"] {
            if let Some(artifacts) = row.get_mut(record).and_then(|r| r.get_mut("artifacts")) {
                for artifact in artifacts.as_array_mut().unwrap() {
                    let artifact = artifact.as_object_mut().unwrap();
                    artifact.remove("materialization");
                    artifact.remove("metadata");
                }
            }
        }
    }
    envelope
}

fn check_lowered(baseline: &Run, run: &Run, budget: u64, step: &str) {
    for line in run.stderr.lines() {
        assert!(
            line.len() as u64 + 1 <= budget,
            "a {}-byte line over the {budget}-byte budget",
            line.len()
        );
    }
    let (big, _) = &run.functions["budget::big"];
    let (base_big, _) = &baseline.functions["budget::big"];
    let disclosure = &big["transport_budget"];
    assert_eq!(disclosure["step"], step, "{disclosure}");
    assert_eq!(disclosure["line_budget_bytes"], budget);
    assert_eq!(disclosure["minted_rows"], base_big["results"].as_array().unwrap().len());
    let rows = big["results"].as_array().unwrap();
    let base_rows = base_big["results"].as_array().unwrap();
    if step == "report_replaced" {
        assert_eq!(rows.len(), 1, "{big}");
        assert_eq!(rows[0]["kind"], "transport_line_budget");
        let refuted = base_rows.iter().any(|row| row["outcome"] == "failed");
        assert_eq!(rows[0]["outcome"], if refuted { "failed" } else { "unknown" });
        assert_eq!(big["proved"], 0);
        assert_eq!(disclosure["replaced"]["total"], base_rows.len());
    } else {
        // The rows survive, in order, with no outcome raised.
        assert_eq!(rows.len(), base_rows.len());
        let stable = &baseline.stable["budget::big"];
        for ((row, base), stable) in rows.iter().zip(base_rows).zip(stable) {
            assert_eq!(row["kind"], base["kind"]);
            assert_eq!(row["description"], base["description"]);
            let (outcome, was) =
                (row["outcome"].as_str().unwrap(), base["outcome"].as_str().unwrap());
            if *stable {
                assert!(
                    rank(outcome) <= rank(was),
                    "`{was}` row published as `{outcome}`: {row:.400}"
                );
            }
        }
        for entry in disclosure["withheld"].as_array().unwrap() {
            let field = entry["field"].as_str().unwrap();
            for index in entry["rows"].as_array().unwrap() {
                let row = &rows[index.as_u64().unwrap() as usize];
                let base = &base_rows[index.as_u64().unwrap() as usize];
                match field {
                    "original_vc_snapshot" => {
                        assert!(row.get(field).is_none(), "withheld `{field}` still on row {index}")
                    }
                    "proof_evidence_payloads" | "native_trust_ir_payloads" => {
                        // The record stays, with its status; its artifacts lose their
                        // payloads, and an Error diagnostic says so.
                        let record = field.trim_end_matches("_payloads");
                        let (now, was) = (&row[record], &base[record]);
                        assert!(now.is_object(), "the `{record}` record of row {index} stays");
                        assert_eq!(now.get("status"), was.get("status"));
                        assert_eq!(now.get("suite"), was.get("suite"));
                        for artifact in now["artifacts"].as_array().unwrap() {
                            assert!(artifact.get("materialization").is_none(), "{artifact:.300}");
                            assert!(artifact.get("metadata").is_none(), "{artifact:.300}");
                        }
                        assert!(now["diagnostics"].as_array().unwrap().iter().any(|d| {
                            d["code"] == "transport_line_budget_payload_withheld"
                                && d["severity"] == "error"
                        }));
                        assert!(row.get("grade").is_none());
                        assert!(!matches!(
                            row["outcome"].as_str(),
                            Some("proved" | "runtime_checked")
                        ));
                    }
                    other => panic!("unknown withheld field `{other}`"),
                }
            }
        }
        for index in disclosure["demoted_rows"].as_array().into_iter().flatten() {
            let row = &rows[index.as_u64().unwrap() as usize];
            assert!(
                row["reason"].as_str().unwrap().starts_with("transport line budget:"),
                "{row:.400}"
            );
        }
        if step == "withheld_diagnostic_payloads" {
            assert!(disclosure.get("demoted_rows").is_none());
            for ((row, base), stable) in rows.iter().zip(base_rows).zip(stable) {
                if *stable {
                    assert_eq!(row["outcome"], base["outcome"], "step 1 changes no outcome");
                    assert_eq!(row.get("proof_evidence"), base.get("proof_evidence"));
                }
            }
        } else if base_rows.iter().all(|row| {
            (row.get("proof_evidence").is_none() && row.get("native_trust_ir").is_none())
                || matches!(row["outcome"].as_str(), Some("proved" | "runtime_checked"))
        }) {
            // Every row with evidence to withhold claimed a proof: step 2 had to demote.
            assert!(
                !disclosure["demoted_rows"].as_array().unwrap().is_empty(),
                "step 2 had to demote a proved row: {disclosure}"
            );
        }
    }
    // Every function whose baseline line fit is untouched; none other is disclosed.
    for (name, (envelope, _)) in &run.functions {
        if name == "budget::big" {
            continue;
        }
        let (base, _) = &baseline.functions[name];
        if json_line_bytes(base, &baseline.span_file_name) <= budget {
            let envelope = untimed(envelope);
            assert!(
                envelope == untimed(base) || envelope == baseline.again[name],
                "{name} fit, so it is untouched"
            );
        } else {
            assert!(envelope.get("transport_budget").is_some(), "{name} did not fit");
        }
    }
    // The crate summary sums the envelopes as emitted.
    for (summary_key, envelope_key) in [
        ("total_obligations", "total"),
        ("total_proved", "proved"),
        ("total_failed", "failed"),
        ("total_unknown", "unknown"),
        ("total_runtime_checked", "runtime_checked"),
    ] {
        let sum: u64 = run
            .functions
            .values()
            .map(|(envelope, _)| envelope[envelope_key].as_u64().unwrap())
            .sum();
        assert_eq!(run.crate_summary[summary_key], sum, "{summary_key}: {}", run.crate_summary);
    }
    // One warning, naming `big`.
    let budget_warnings: Vec<_> =
        run.warnings.iter().filter(|w| w.contains("transport line budget")).collect();
    assert_eq!(
        budget_warnings.len(),
        1 + run
            .functions
            .iter()
            .filter(|(name, (envelope, _))| {
                name.as_str() != "budget::big" && envelope.get("transport_budget").is_some()
            })
            .count(),
        "{budget_warnings:?}"
    );
    assert!(budget_warnings.iter().any(|w| w.contains("`budget::big`")), "{budget_warnings:?}");
}

fn main() {
    if std::env::var_os(TRUST_VANILLA_REAL_RUSTC_ENV).is_some() {
        // The upstream compiler has no Trust transport.
        return;
    }
    // Guarded divisions and constant indices: every row is decided in milliseconds, so
    // the verdicts do not depend on machine load, and each carries an original-VC
    // snapshot, proof evidence, native evidence and a grade for the ladder to withhold.
    let mut big = String::from(
        "pub fn big(x: &[u64; 8], k: u64) -> u64 {\n    if k == 0 {\n        return 0;\n    }\n\
         \x20   let mut acc = 0u64;\n",
    );
    for i in 0..8 {
        let op = if i % 2 == 0 { '/' } else { '%' };
        big.push_str(&format!("    acc = acc.wrapping_add(x[{i}] {op} k);\n"));
    }
    big.push_str("    acc\n}\n");
    rfs::write(
        "budget.rs",
        format!(
            "pub fn tiny() {{}}\n\n\
             pub fn small(a: u64, k: u64) -> u64 {{\n    if k == 0 {{\n        return 0;\n    }}\n\
             \x20   a / k\n}}\n\n{big}"
        ),
    );

    // BASELINE, and the positive control: at the default budget nothing is disclosed.
    // It is compiled twice: a row whose verdict the verifier does not reproduce cannot
    // pin what the ladder did to it, so the cross-run outcome checks below read only the
    // rows both baselines agree on (`Run::stable`).
    let mut baseline = compile(None, false);
    let again = compile(None, false);
    baseline.stable_against(&again);
    let (base_big, _) = &baseline.functions["budget::big"];
    let big_rows = base_big["results"].as_array().unwrap().len();
    assert!(
        baseline.stable["budget::big"].iter().filter(|stable| **stable).count() * 2 >= big_rows,
        "big's verdicts reproduce, so the outcome checks have rows to read: {:?}",
        baseline.stable["budget::big"]
    );
    for (name, (envelope, _)) in &baseline.functions {
        assert!(envelope.get("transport_budget").is_none(), "{name} fit the default budget");
    }
    assert!(baseline.warnings.iter().all(|w| !w.contains("transport line budget")));
    let name = baseline.span_file_name.as_str();
    assert_eq!(name, "budget.rs", "the unremapped root is named as given");
    let full = json_line_bytes(base_big, name);
    let no_snapshots = json_line_bytes(&strip(base_big, &["original_vc_snapshot"]), name);
    let bare = json_line_bytes(&hollow(&strip(base_big, &["original_vc_snapshot"])), name);
    // The fixture must exercise every step: snapshots and proof evidence to withhold,
    // proved rows to demote, and enough rows that even bare they pass the minimum.
    assert!(full - no_snapshots > 8 * 1024, "big carries snapshots: {full} vs {no_snapshots}");
    assert!(no_snapshots - bare > 64 * 1024, "big carries evidence: {no_snapshots} vs {bare}");
    assert!(bare > MIN_BUDGET + 2 * 1024, "big has enough rows to outgrow the minimum: {bare}");
    assert!(base_big["proved"].as_u64().unwrap() > 0, "big has proved rows to demote");

    // Step 1: between the full line and the line without snapshots.
    let step1 = (full + no_snapshots) / 2;
    check_lowered(
        &baseline,
        &compile(Some(&step1.to_string()), false),
        step1,
        "withheld_diagnostic_payloads",
    );
    // Step 2: far below the line without snapshots, above the hollowed rows.
    // (A demoted row's reason grows by under 600 bytes, each hollowed record gains a
    // diagnostic of under 400, and the disclosure lists the row.)
    let rows = base_big["results"].as_array().unwrap().len() as u64;
    let step2 = bare + 1_400 * rows + (no_snapshots - bare) / 8;
    assert!(step2 < no_snapshots, "the step-2 budget needs step 2: {step2} vs {no_snapshots}");
    check_lowered(
        &baseline,
        &compile(Some(&step2.to_string()), false),
        step2,
        "withheld_proof_evidence",
    );
    // Step 3: the minimum budget, below even the bare rows.
    check_lowered(&baseline, &compile(Some("0"), false), MIN_BUDGET, "report_replaced");

    // The raw-stderr framing is bounded the same way.
    let human = compile(Some(&step2.to_string()), true);
    for line in human.stderr.lines().filter(|line| line.starts_with(PREFIX)) {
        assert!(line.len() as u64 + 1 <= step2, "a {}-byte raw line", line.len());
    }
    assert!(human.functions["budget::big"].0.get("transport_budget").is_some());

    // Review F4: a crate root remapped to a name over three times the fixed frame. The
    // ladder must price the span's file name exactly: at the default budget each line is
    // the long-name baseline; lowered so that `big` needs step 1, the disclosure's unbounded
    // size is at least `big`'s real unfitted line, and every line fits (`check_lowered`).
    // Each component is 200 bytes and each join adds one, so the count is derived from the
    // frame: a fixed 60 made 12,060 bytes, under 3 * 4 KiB = 12,288, and this test's own
    // precondition below refused before it checked anything (land gate 2026-11-08).
    let parts = (3 * FRAMING as usize).div_ceil(201) + 1;
    let components: Vec<String> =
        (0..parts).map(|i| format!("checkout-{i:02}-{}", "r".repeat(188))).collect();
    let long_name = format!("/{}", components.join("/"));
    assert!(long_name.len() as u64 > 3 * FRAMING, "the name outgrows the fixed frame");
    let mut long_base = compile_named(None, false, Some(&long_name));
    let long_again = compile_named(None, false, Some(&long_name));
    long_base.stable_against(&long_again);
    for (name, (envelope, _)) in &long_base.functions {
        assert!(envelope.get("transport_budget").is_none(), "{name} fit the default budget");
    }
    let (long_big, long_big_line) = &long_base.functions["budget::big"];
    let long_full = json_line_bytes(long_big, &long_base.span_file_name);
    assert!(long_full >= *long_big_line, "the frame prices the real line: {long_full}");
    let long_step1 = (long_full
        + json_line_bytes(&strip(long_big, &["original_vc_snapshot"]), &long_base.span_file_name))
        / 2;
    let long_run = compile_named(Some(&long_step1.to_string()), false, Some(&long_name));
    let (fitted_big, _) = &long_run.functions["budget::big"];
    let unbounded = fitted_big["transport_budget"]["unbounded_line_bytes"].as_u64().unwrap();
    assert!(
        unbounded >= *long_big_line,
        "the ladder priced big's unfitted line at {unbounded} bytes, under its real \
         {long_big_line}: the span's file name was not counted"
    );
    check_lowered(&long_base, &long_run, long_step1, "withheld_diagnostic_payloads");

    // A crate-level row cannot be fitted: one over the budget is not written, and the
    // compile FAILS (its consumer would read a missing coverage row as coverage-unknown,
    // which drives no gate, so the failure is what keeps it from passing). Four hundred
    // trivial functions give a coverage inventory over the 16 KiB minimum while every
    // function line stays far under it.
    let mut many = String::new();
    for i in 0..400 {
        many.push_str(&format!("pub fn function_number_{i}() {{}}\n"));
    }
    rfs::write("many.rs", many);
    let many_compile = |budget: Option<&str>| {
        let mut cmd = rustc();
        cmd.input("many.rs")
            .crate_type("lib")
            .edition("2021")
            .arg("-Ztrust-verify=on")
            .arg("-Ztrust-policy=advisory")
            .arg("-Ztrust-verify-output=json")
            .arg(format!("-Ztrust-proof-artifact-root={}", proof_artifact_root().display()))
            .arg("--error-format=json")
            .env_remove(TRUST_NO_VERIFY_ENV)
            .env_remove(BUDGET_ENV);
        if let Some(budget) = budget {
            cmd.env(BUDGET_ENV, budget);
        }
        cmd
    };
    let types_of = |stderr: &str| -> Vec<String> {
        stderr
            .lines()
            .filter_map(|line| serde_json::from_str::<Value>(line).ok())
            .filter_map(|d| {
                d["message"].as_str().and_then(|m| m.strip_prefix(PREFIX)).map(str::to_string)
            })
            .filter_map(|p| serde_json::from_str::<Value>(&p).ok())
            .map(|p| p["type"].as_str().unwrap_or("").to_string())
            .collect()
    };
    // Control: at the default budget the coverage row is written and the compile passes.
    let control = many_compile(None).run().stderr_utf8();
    let control_types = types_of(&control);
    assert_eq!(control_types.iter().filter(|t| *t == "coverage_summary").count(), 1);
    let coverage_line = control
        .lines()
        .find(|line| line.contains("coverage_summary"))
        .expect("the control's coverage line");
    assert!(
        coverage_line.len() as u64 > MIN_BUDGET,
        "the inventory outgrows the minimum: {}",
        coverage_line.len()
    );
    let refused = many_compile(Some("0")).run_fail().stderr_utf8();
    for line in refused.lines() {
        assert!(line.len() as u64 + 1 <= MIN_BUDGET, "a {}-byte line", line.len());
    }
    let refused_types = types_of(&refused);
    assert_eq!(refused_types.iter().filter(|t| *t == "coverage_summary").count(), 0);
    assert_eq!(
        refused_types.iter().filter(|t| *t == "function_result").count(),
        control_types.iter().filter(|t| *t == "function_result").count(),
        "every function line is still written"
    );
    assert!(
        refused.contains("a `coverage_summary` transport line would take"),
        "the refusal says which row: {refused:.3000}"
    );

    // NEGATIVE CONTROLS: the knob cannot raise the bound or switch it off.
    for request in ["999999999999999", "unbounded"] {
        let run = compile(Some(request), false);
        for (name, (envelope, _)) in &run.functions {
            assert!(envelope.get("transport_budget").is_none(), "{request}: {name}");
            assert_eq!(
                untimed(envelope),
                untimed(&baseline.functions[name].0),
                "{request}: {name} as at the default"
            );
        }
    }
}
