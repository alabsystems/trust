// The M1 D1 parse-verdict differential lane (D3 plumbing seed): every S0
// case × mandated mode through trust_js_parse::parse_script AND the node
// --check oracle, compared at verdict level only (accept/reject; reasons are
// never compared):
//   Script     <-> oracle accept  => agree
//   EarlyError <-> oracle reject  => agree
//   Script     <-> oracle reject, EarlyError <-> accept => DISAGREE
//   Unsupported                   => no-coverage (counted, never a disagreement)
//   oracle spawn/classify failure => oracle_error (tool failure)
// Body-only: the lane judges the pristine test file itself — includes never
// participate; strict mode is the exact '"use strict";\n' prefix on BOTH
// sides, so parser and oracle always see identical source bytes. Raw-flag
// cases SKIP this lane (counted raw_skipped). Disagreements are audited
// against ACTIVE head="parse" divergence-audit entries matched by
// path+fingerprint, fingerprint = sha256(path|mode|direction)[..16].
// Artifacts: parse-scorecard.json (trust.js262.parse-verdict.v1),
// parse-verdicts-divergent.jsonl, parse-dashboard.md. Exit 1 on any
// oracle_error or unwaived disagreement.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::BTreeMap;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use trust_js_parse::{parse_module, parse_script, ParseOutcome};

use crate::cases::{prepare_case, PreparedCase};
use crate::heads::{spawn_engine, RunMode, SpawnOutput};
use crate::model::{
    Js262AuditEntry, Js262AuditHead, Js262Classification, ParseDivergenceRow, ParseGate,
    ParseScorecard, ParseTotals, ScorecardEngine, PARSE_SCORECARD_SCHEMA,
};
use crate::slice::{derive, load_slice, verify_derived, SliceKind};

/// The mode label for a module-goal run (modules are always strict — a single
/// run per case, no bare/strict split).
const MODULE_MODE: &str = "module";
use crate::util::{contains_subslice, git_head, now_utc_iso, probe_engine, validation_date, Engine};
use crate::validate::{audit_entry_is_active, load_audit};

/// Per-oracle-spawn timeout. `node --check` parses without executing, so a
/// fixed generous bound suffices; expiry is an oracle_error (fail-closed).
pub const ORACLE_TIMEOUT: Duration = Duration::from_secs(30);

pub const DIR_PARSER_ACCEPTS: &str = "parser-accepts-oracle-rejects";
pub const DIR_PARSER_REJECTS: &str = "parser-rejects-oracle-accepts";

pub struct ParseVerdictOpts {
    pub corpus: PathBuf,
    pub slice: PathBuf,
    /// Which slice/goal to judge: `S0` (script goal) or `S-module` (module goal).
    pub slice_kind: SliceKind,
    pub node: PathBuf,
    pub jobs: usize,
    pub limit: Option<usize>,
    pub out_dir: PathBuf,
    pub ledgers: PathBuf,
}

// ---------------------------------------------------------------------------
// Oracle classification (M1 contract): exit 0 = parse-accept; nonzero with
// "SyntaxError" in stderr = parse-reject; anything else = tool failure.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OracleVerdict {
    Accept,
    Reject,
    Error(String),
}

fn stderr_tail(stderr: &[u8], max: usize) -> String {
    let text = String::from_utf8_lossy(stderr);
    let mut start = text.len().saturating_sub(max);
    while !text.is_char_boundary(start) {
        start += 1;
    }
    text[start..].to_string()
}

/// Classify one `node --check` spawn output per the parse-verdict oracle
/// semantics.
pub fn classify_oracle_output(out: &SpawnOutput) -> OracleVerdict {
    if out.timed_out {
        return OracleVerdict::Error("oracle timeout".to_string());
    }
    if out.success {
        return OracleVerdict::Accept;
    }
    if contains_subslice(&out.stderr, b"SyntaxError") {
        OracleVerdict::Reject
    } else {
        OracleVerdict::Error(format!(
            "oracle exited nonzero without SyntaxError (stderr tail: {:?})",
            stderr_tail(&out.stderr, 300)
        ))
    }
}

// ---------------------------------------------------------------------------
// Verdict comparison
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerdictComparison {
    Agree,
    Disagree { direction: &'static str, parser_reason: Option<String> },
    /// Sound parser refusal — counted, never a disagreement.
    NoCoverage { reason: String },
    /// Oracle tool failure — takes precedence over everything (fail-closed).
    OracleError { detail: String },
}

/// The verdict comparison matrix. Verdict level ONLY: reasons are carried for
/// reporting, never compared. An oracle failure wins over every parser
/// outcome (a tool failure must surface even where the parser has no
/// coverage).
pub fn compare_verdicts(parse: &ParseOutcome, oracle: &OracleVerdict) -> VerdictComparison {
    if let OracleVerdict::Error(detail) = oracle {
        return VerdictComparison::OracleError { detail: detail.clone() };
    }
    match (parse, oracle) {
        (ParseOutcome::Unsupported { reason }, _) => {
            VerdictComparison::NoCoverage { reason: reason.clone() }
        }
        (ParseOutcome::Script(_), OracleVerdict::Accept) => VerdictComparison::Agree,
        (ParseOutcome::EarlyError { .. }, OracleVerdict::Reject) => VerdictComparison::Agree,
        (ParseOutcome::Script(_), OracleVerdict::Reject) => VerdictComparison::Disagree {
            direction: DIR_PARSER_ACCEPTS,
            parser_reason: None,
        },
        (ParseOutcome::EarlyError { reason }, OracleVerdict::Accept) => {
            VerdictComparison::Disagree {
                direction: DIR_PARSER_REJECTS,
                parser_reason: Some(reason.clone()),
            }
        }
        (_, OracleVerdict::Error(_)) => unreachable!("handled above"),
    }
}

/// Divergence fingerprint: first 16 hex of sha256(path|mode|direction).
pub fn parse_fingerprint(path: &str, mode: &str, direction: &str) -> String {
    trust_js_trace::sha256_hex(format!("{path}|{mode}|{direction}").as_bytes())[..16].to_string()
}

/// The strict-mode contract: the EXACT '"use strict";\n' prefix. Both the
/// parser and the oracle judge this identical source text.
pub fn mode_source(body: &str, mode: RunMode) -> String {
    match mode {
        RunMode::Strict => format!("\"use strict\";\n{body}"),
        _ => body.to_string(),
    }
}

/// ACTIVE head="parse" audit entries — the only entries this lane consumes.
/// Same activity rules as the trace lane; projection_too_strong is never a
/// waiver in any lane.
pub fn active_parse_waivers<'a>(
    entries: &'a [Js262AuditEntry],
    date: &str,
) -> Vec<&'a Js262AuditEntry> {
    entries
        .iter()
        .filter(|e| {
            e.head == Js262AuditHead::Parse
                && audit_entry_is_active(e, date)
                && e.classification != Js262Classification::ProjectionTooStrong
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------

struct ParseRunRecord {
    path: String,
    /// The run's mode label: "bare"/"strict" (script goal) or "module".
    mode: String,
    cmp: VerdictComparison,
}

/// One worker's oracle probe: write the mode source to the reusable slot file
/// and `node --check` it.
fn run_oracle(node: &Path, slot_file: &Path, source: &str) -> OracleVerdict {
    if let Err(e) = std::fs::write(slot_file, source) {
        return OracleVerdict::Error(format!("write {}: {e}", slot_file.display()));
    }
    match spawn_engine(node, &[Path::new("--check"), slot_file], ORACLE_TIMEOUT) {
        Ok(out) => classify_oracle_output(&out),
        Err(e) => OracleVerdict::Error(e),
    }
}

pub fn run_parse_verdict(opts: &ParseVerdictOpts) -> anyhow::Result<i32> {
    let vdate = validation_date();

    // --- identities ---
    let oracle_id = probe_engine(Engine::Node, &opts.node)?;
    let corpus_revision = git_head(&opts.corpus).unwrap_or_else(|| "unknown".to_string());

    // --- slice (same fail-closed discipline as calibrate) ---
    let loaded = load_slice(&opts.slice)?;
    // The manifest's self-declared kind must match the requested goal, so a
    // module run can never silently judge the script slice (or vice versa).
    if loaded.kind != opts.slice_kind {
        anyhow::bail!(
            "slice manifest {} is {} but --slice-kind selects {} — fail closed",
            opts.slice.display(),
            loaded.kind.id(),
            opts.slice_kind.id()
        );
    }
    if !loaded.findings.is_empty() {
        for f in &loaded.findings {
            eprintln!("parse-verdict: slice manifest finding: {}", f.render());
        }
        anyhow::bail!(
            "slice manifest {} failed its internal consistency check",
            opts.slice.display()
        );
    }
    let tests: Vec<String> = match &loaded.tests {
        Some(tests) => tests.clone(),
        None => {
            let derived = derive(&opts.corpus, opts.slice_kind)?;
            let findings = verify_derived(&loaded, &derived);
            if !findings.is_empty() {
                for f in &findings {
                    eprintln!("parse-verdict: slice drift finding: {}", f.render());
                }
                anyhow::bail!(
                    "re-derived S0 slice does not match committed manifest {} — fail closed",
                    opts.slice.display()
                );
            }
            derived.paths
        }
    };
    let slice_sha256 = loaded.list_sha256.clone();
    let partial = opts.limit.map(|n| n < tests.len()).unwrap_or(false);
    let selected: Vec<String> = match opts.limit {
        Some(n) => tests.iter().take(n).cloned().collect(),
        None => tests,
    };

    // --- head="parse" waivers ---
    let audit = load_audit(&opts.ledgers);
    let waivers = active_parse_waivers(&audit.entries, &vdate);
    let exceptions = crate::validate::load_test_exceptions(&opts.ledgers);
    let active_exceptions: Vec<&crate::model::Js262TestException> = exceptions
        .exceptions
        .iter()
        .filter(|e| crate::validate::test_exception_is_active(e, &vdate))
        .collect();

    // --- prepare cases (fail-closed on unreadable/unparseable frontmatter) ---
    let mut raw_cases = 0u64;
    let mut queue_cases: Vec<PreparedCase> = Vec::new();
    let mut case_faults: Vec<(String, String)> = Vec::new();
    for rel in &selected {
        match prepare_case(&opts.corpus, rel) {
            Ok(c) => {
                if c.modes == [RunMode::Raw] {
                    raw_cases += 1;
                } else {
                    queue_cases.push(c);
                }
            }
            Err(e) => case_faults.push((rel.clone(), e)),
        }
    }

    // --- worker pool over a locked queue (per-worker slot files) ---
    std::fs::create_dir_all(&opts.out_dir)?;
    let tmp = opts.out_dir.join("tmp");
    let jobs = opts.jobs.max(1);
    let next = Arc::new(Mutex::new(0usize));
    let records: Arc<Mutex<Vec<ParseRunRecord>>> = Arc::new(Mutex::new(Vec::new()));
    let queue_cases = Arc::new(queue_cases);

    std::thread::scope(|scope| -> anyhow::Result<()> {
        let mut handles = Vec::new();
        for worker in 0..jobs {
            let next = Arc::clone(&next);
            let records = Arc::clone(&records);
            let queue_cases = Arc::clone(&queue_cases);
            let node = opts.node.clone();
            let slice_kind = opts.slice_kind;
            let slot_dir = tmp.join(format!("parse-worker-{worker}"));
            handles.push(scope.spawn(move || -> Result<(), String> {
                std::fs::create_dir_all(&slot_dir)
                    .map_err(|e| format!("worker {worker}: slot dir: {e}"))?;
                // Script goal writes a `.js` slot; module goal MUST write a
                // `.mjs` slot so `node --check` reaches the module goal (a `.js`
                // slot would reject top-level import/export).
                let slot_file = slot_dir.join("check.js");
                let module_slot_file = slot_dir.join("check.mjs");
                loop {
                    let idx = {
                        let mut guard = next.lock().map_err(|_| "queue poisoned")?;
                        let idx = *guard;
                        *guard += 1;
                        idx
                    };
                    let Some(case) = queue_cases.get(idx) else { break };
                    let mut runs: Vec<(String, VerdictComparison)> = Vec::new();
                    if slice_kind == SliceKind::SModule {
                        // Module goal: one run per case (modules are always
                        // strict — no bare/strict split), the pristine body
                        // through parse_module and `node --check` a .mjs slot.
                        let source = case.body.clone();
                        let parse = parse_module(&source);
                        let oracle = run_oracle(&node, &module_slot_file, &source);
                        runs.push((MODULE_MODE.to_string(), compare_verdicts(&parse, &oracle)));
                    } else {
                        for &mode in &case.modes {
                            let source = mode_source(&case.body, mode);
                            let parse = parse_script(&source, mode == RunMode::Strict);
                            let oracle = run_oracle(&node, &slot_file, &source);
                            runs.push((mode.as_str().to_string(), compare_verdicts(&parse, &oracle)));
                        }
                    }
                    let mut guard = records.lock().map_err(|_| "records poisoned")?;
                    for (mode, cmp) in runs {
                        guard.push(ParseRunRecord {
                            path: case.rel_path.clone(),
                            mode,
                            cmp,
                        });
                    }
                }
                Ok(())
            }));
        }
        for h in handles {
            h.join()
                .map_err(|_| anyhow::anyhow!("worker panicked"))?
                .map_err(|e| anyhow::anyhow!("{e}"))?;
        }
        Ok(())
    })?;

    let mut records = Arc::try_unwrap(records)
        .map_err(|_| anyhow::anyhow!("records still shared"))?
        .into_inner()
        .map_err(|_| anyhow::anyhow!("records poisoned"))?;
    records.sort_by(|a, b| {
        (a.path.as_str(), a.mode.as_str()).cmp(&(b.path.as_str(), b.mode.as_str()))
    });

    // --- aggregate ---
    let mut totals = ParseTotals::default();
    totals.cases = selected.len() as u64;
    totals.raw_skipped = raw_cases;
    let mut divergent: Vec<ParseDivergenceRow> = Vec::new();
    let mut unwaived_disagree = 0u64;
    let mut oracle_error_notes: Vec<String> = Vec::new();
    let mut no_coverage_reasons: BTreeMap<String, u64> = BTreeMap::new();

    for (rel, err) in &case_faults {
        totals.runs += 1;
        totals.oracle_errors += 1;
        oracle_error_notes.push(format!("{rel}: case preparation failed: {err}"));
    }

    for rec in &records {
        totals.runs += 1;
        match &rec.cmp {
            VerdictComparison::Agree => totals.agree += 1,
            VerdictComparison::NoCoverage { reason } => {
                totals.unsupported += 1;
                *no_coverage_reasons.entry(reason.clone()).or_default() += 1;
            }
            VerdictComparison::OracleError { detail } => {
                // An active tests/js262 test exception (e.g. node --check
                // aborting on a corpus case) accounts the fault visibly;
                // anything unexcepted stays a tool failure.
                if let Some(exc) = active_exceptions.iter().find(|e| e.path == rec.path) {
                    totals.excepted_oracle_errors += 1;
                    oracle_error_notes.push(format!(
                        "{} [{}]: oracle error (excepted: {}): {detail}",
                        rec.path,
                        rec.mode.as_str(),
                        exc.id
                    ));
                    continue;
                }
                totals.oracle_errors += 1;
                oracle_error_notes.push(format!(
                    "{} [{}]: {detail}",
                    rec.path,
                    rec.mode.as_str()
                ));
            }
            VerdictComparison::Disagree { direction, parser_reason } => {
                totals.disagree += 1;
                let fingerprint = parse_fingerprint(&rec.path, rec.mode.as_str(), direction);
                let waiver = waivers
                    .iter()
                    .find(|e| e.path == rec.path && e.fingerprint == fingerprint);
                if waiver.is_none() {
                    unwaived_disagree += 1;
                }
                divergent.push(ParseDivergenceRow {
                    path: rec.path.clone(),
                    mode: rec.mode.as_str().to_string(),
                    direction: direction.to_string(),
                    fingerprint,
                    parser_reason: parser_reason.clone(),
                    classification: waiver.map(|e| e.classification),
                });
            }
        }
    }

    // --- gate ---
    let coverage_ratio = if totals.runs > 0 {
        (totals.agree + totals.disagree) as f64 / totals.runs as f64
    } else {
        1.0
    };
    let disagree_ok = unwaived_disagree == 0;
    let pass = disagree_ok && totals.oracle_errors == 0 && !partial;
    let gate = ParseGate {
        disagree_ok,
        unwaived_disagree,
        coverage_ratio,
        pass,
        reason: if partial {
            Some("partial scorecard (--limit) never claims the gate".to_string())
        } else {
            None
        },
    };

    let scorecard = ParseScorecard {
        schema: PARSE_SCORECARD_SCHEMA.to_string(),
        generated_at: now_utc_iso(),
        partial: if partial { Some(true) } else { None },
        corpus: corpus_revision,
        slice_sha256,
        parser: "trust-js-parse".to_string(),
        oracle: ScorecardEngine {
            path: oracle_id.path.display().to_string(),
            version: oracle_id.version.clone(),
            sha256: oracle_id.sha256.clone(),
        },
        totals,
        gate,
    };

    // --- artifacts ---
    let scorecard_path = opts.out_dir.join("parse-scorecard.json");
    std::fs::write(&scorecard_path, serde_json::to_string_pretty(&scorecard)?)?;
    {
        let mut f = std::fs::File::create(opts.out_dir.join("parse-verdicts-divergent.jsonl"))?;
        for row in &divergent {
            writeln!(f, "{}", serde_json::to_string(row)?)?;
        }
    }
    std::fs::write(
        opts.out_dir.join("parse-dashboard.md"),
        render_dashboard(&scorecard, &divergent, &oracle_error_notes, &no_coverage_reasons),
    )?;

    println!(
        "parse-verdict: cases={} runs={} agree={} disagree={} (unwaived {}) unsupported={} raw_skipped={} oracle_errors={}",
        scorecard.totals.cases,
        scorecard.totals.runs,
        scorecard.totals.agree,
        scorecard.totals.disagree,
        scorecard.gate.unwaived_disagree,
        scorecard.totals.unsupported,
        scorecard.totals.raw_skipped,
        scorecard.totals.oracle_errors,
    );
    println!(
        "parse-verdict: coverage_ratio={:.6} gate.pass={}{} — artifacts in {}",
        scorecard.gate.coverage_ratio,
        scorecard.gate.pass,
        if partial { " (partial)" } else { "" },
        opts.out_dir.display()
    );

    Ok(parse_scorecard_exit_code(&scorecard))
}

/// Exit 1 on any oracle_error or unwaived disagreement (and only those: a
/// clean partial run exits 0 without claiming the gate).
pub fn parse_scorecard_exit_code(s: &ParseScorecard) -> i32 {
    if s.totals.oracle_errors != 0 || s.gate.unwaived_disagree != 0 {
        1
    } else {
        0
    }
}

fn render_dashboard(
    s: &ParseScorecard,
    divergent: &[ParseDivergenceRow],
    oracle_errors: &[String],
    no_coverage_reasons: &BTreeMap<String, u64>,
) -> String {
    let mut out = String::new();
    let t = &s.totals;
    out.push_str("## Parse-verdict differential (M1 D1) — trust-js-parse vs node --check\n\n");
    if s.partial == Some(true) {
        out.push_str("**PARTIAL RUN (`--limit`): this scorecard never claims the gate.**\n\n");
    }
    out.push_str(&format!("- Generated: {}\n", s.generated_at));
    out.push_str(&format!("- Corpus: `{}` (slice sha256 `{}`)\n", s.corpus, s.slice_sha256));
    out.push_str(&format!("- Parser: `{}`\n", s.parser));
    out.push_str(&format!("- Oracle: `{}` ({})\n\n", s.oracle.path, s.oracle.version));
    out.push_str("| metric | value |\n|---|---|\n");
    for (k, v) in [
        ("cases", t.cases),
        ("runs", t.runs),
        ("agree", t.agree),
        ("disagree", t.disagree),
        ("unwaived disagree", s.gate.unwaived_disagree),
        ("unsupported (no-coverage)", t.unsupported),
        ("raw skipped", t.raw_skipped),
        ("oracle errors (tool failures)", t.oracle_errors),
    ] {
        out.push_str(&format!("| {k} | {v} |\n"));
    }
    out.push_str(&format!(
        "\n**Gate**: disagree_ok {} (unwaived {}), coverage_ratio {:.6} => **pass: {}**\n",
        s.gate.disagree_ok, s.gate.unwaived_disagree, s.gate.coverage_ratio, s.gate.pass
    ));
    if let Some(r) = &s.gate.reason {
        out.push_str(&format!("\nReason: {r}\n"));
    }
    if !no_coverage_reasons.is_empty() {
        out.push_str("\nTop no-coverage reasons:\n\n");
        let mut reasons: Vec<(&String, &u64)> = no_coverage_reasons.iter().collect();
        reasons.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        for (reason, n) in reasons.iter().take(10) {
            out.push_str(&format!("- {n} × {reason}\n"));
        }
    }
    let unwaived: Vec<&ParseDivergenceRow> =
        divergent.iter().filter(|d| d.classification.is_none()).collect();
    out.push_str(&format!(
        "\n### Disagreements\n\n{} disagreements ({} unwaived). Full list: parse-verdicts-divergent.jsonl.\n",
        divergent.len(),
        unwaived.len()
    ));
    if !unwaived.is_empty() {
        out.push_str("\nTop unwaived disagreements:\n\n");
        for d in unwaived.iter().take(25) {
            out.push_str(&format!("- `{}` [{}] fp `{}`: {}\n", d.path, d.mode, d.fingerprint, d.direction));
        }
    }
    if !oracle_errors.is_empty() {
        out.push_str(&format!("\n### Oracle errors ({})\n\n", oracle_errors.len()));
        for line in oracle_errors.iter().take(25) {
            out.push_str(&format!("- {line}\n"));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_parse::Program;

    fn spawn_out(success: bool, stderr: &[u8], timed_out: bool) -> SpawnOutput {
        SpawnOutput {
            success,
            stdout: vec![],
            stderr: stderr.to_vec(),
            timed_out,
            stdout_capped: false,
        }
    }

    #[test]
    fn oracle_output_classification() {
        // exit 0 => accept, whatever stderr says.
        assert_eq!(classify_oracle_output(&spawn_out(true, b"", false)), OracleVerdict::Accept);
        assert_eq!(
            classify_oracle_output(&spawn_out(true, b"warning: noise", false)),
            OracleVerdict::Accept
        );
        // nonzero + SyntaxError in stderr => reject.
        assert_eq!(
            classify_oracle_output(&spawn_out(
                false,
                b"/tmp/x.js:1\nlet let = 1;\nSyntaxError: let is disallowed\n",
                false
            )),
            OracleVerdict::Reject
        );
        // nonzero without SyntaxError => tool failure.
        assert!(matches!(
            classify_oracle_output(&spawn_out(false, b"Error: cannot open file", false)),
            OracleVerdict::Error(_)
        ));
        assert!(matches!(
            classify_oracle_output(&spawn_out(false, b"", false)),
            OracleVerdict::Error(_)
        ));
        // Timeout wins over everything.
        assert!(matches!(
            classify_oracle_output(&spawn_out(true, b"SyntaxError", true)),
            OracleVerdict::Error(_)
        ));
    }

    #[test]
    fn verdict_comparison_matrix() {
        let script = ParseOutcome::Script(Program::default());
        let early = ParseOutcome::EarlyError { reason: "let let".to_string() };
        let unsup = ParseOutcome::Unsupported { reason: "stub".to_string() };
        let accept = OracleVerdict::Accept;
        let reject = OracleVerdict::Reject;
        let err = OracleVerdict::Error("boom".to_string());

        assert_eq!(compare_verdicts(&script, &accept), VerdictComparison::Agree);
        assert_eq!(compare_verdicts(&early, &reject), VerdictComparison::Agree);
        assert_eq!(
            compare_verdicts(&script, &reject),
            VerdictComparison::Disagree { direction: DIR_PARSER_ACCEPTS, parser_reason: None }
        );
        assert_eq!(
            compare_verdicts(&early, &accept),
            VerdictComparison::Disagree {
                direction: DIR_PARSER_REJECTS,
                parser_reason: Some("let let".to_string())
            }
        );
        // Unsupported is no-coverage against either verdict — never a
        // disagreement.
        assert!(matches!(
            compare_verdicts(&unsup, &accept),
            VerdictComparison::NoCoverage { .. }
        ));
        assert!(matches!(
            compare_verdicts(&unsup, &reject),
            VerdictComparison::NoCoverage { .. }
        ));
        // An oracle failure wins over every parser outcome (fail-closed).
        for parse in [&script, &early, &unsup] {
            assert!(matches!(
                compare_verdicts(parse, &err),
                VerdictComparison::OracleError { .. }
            ));
        }
    }

    #[test]
    fn fingerprint_contract() {
        let fp = parse_fingerprint("test/language/x.js", "bare", DIR_PARSER_ACCEPTS);
        assert_eq!(fp.len(), 16);
        assert!(fp.chars().all(|c| c.is_ascii_hexdigit()));
        // Exactly sha256(path|mode|direction)[..16].
        let manual = trust_js_trace::sha256_hex(
            format!("test/language/x.js|bare|{DIR_PARSER_ACCEPTS}").as_bytes(),
        )[..16]
            .to_string();
        assert_eq!(fp, manual);
        // Every component binds the fingerprint.
        assert_ne!(fp, parse_fingerprint("test/language/y.js", "bare", DIR_PARSER_ACCEPTS));
        assert_ne!(fp, parse_fingerprint("test/language/x.js", "strict", DIR_PARSER_ACCEPTS));
        assert_ne!(fp, parse_fingerprint("test/language/x.js", "bare", DIR_PARSER_REJECTS));
    }

    #[test]
    fn strict_mode_source_prefix() {
        assert_eq!(mode_source("var x;", RunMode::Bare), "var x;");
        assert_eq!(mode_source("var x;", RunMode::Strict), "\"use strict\";\nvar x;");
    }

    fn audit_entry(head: &str, status: &str, expires: &str, fp: &str) -> Js262AuditEntry {
        let head_line = if head.is_empty() { String::new() } else { format!("head = \"{head}\"\n") };
        let toml = format!(
            r#"
schema_version = "1"
[[entries]]
id = "e"
path = "test/language/x.js"
mode = "bare"
{head_line}fingerprint = "{fp}"
classification = "node_bug"
status = "{status}"
owner = "ayates"
reason = "r"
issue = "https://example.invalid/1"
reviewed_on = "2026-07-01"
expires_on = "{expires}"
"#
        );
        toml::from_str::<crate::model::Js262DivergenceAudit>(&toml)
            .expect("audit entry toml")
            .entries
            .remove(0)
    }

    #[test]
    fn parse_waiver_filtering() {
        let date = "2026-07-21";
        let entries = vec![
            // Default head => trace lane: NEVER consumed by the parse lane.
            audit_entry("", "active", "2026-09-01", "aaaaaaaaaaaaaaaa"),
            audit_entry("trace", "active", "2026-09-01", "bbbbbbbbbbbbbbbb"),
            // head=parse, active, unexpired: consumed.
            audit_entry("parse", "active", "2026-09-01", "cccccccccccccccc"),
            // head=parse but expired / resolved: not consumed.
            audit_entry("parse", "active", "2026-07-01", "dddddddddddddddd"),
            audit_entry("parse", "resolved", "2026-09-01", "eeeeeeeeeeeeeeee"),
        ];
        let active = active_parse_waivers(&entries, date);
        assert_eq!(active.len(), 1);
        assert_eq!(active[0].fingerprint, "cccccccccccccccc");
        assert_eq!(active[0].head, Js262AuditHead::Parse);
    }

    #[test]
    fn exit_code_contract() {
        fn card(oracle_errors: u64, unwaived: u64, pass: bool) -> ParseScorecard {
            ParseScorecard {
                schema: PARSE_SCORECARD_SCHEMA.to_string(),
                generated_at: "2026-07-21T00:00:00Z".to_string(),
                partial: None,
                corpus: "cafe".to_string(),
                slice_sha256: "00".to_string(),
                parser: "trust-js-parse".to_string(),
                oracle: ScorecardEngine {
                    path: "n".into(),
                    version: "v".into(),
                    sha256: "0".into(),
                },
                totals: ParseTotals { oracle_errors, ..Default::default() },
                gate: ParseGate {
                    disagree_ok: unwaived == 0,
                    unwaived_disagree: unwaived,
                    coverage_ratio: 0.0,
                    pass,
                    reason: None,
                },
            }
        }
        assert_eq!(parse_scorecard_exit_code(&card(0, 0, true)), 0);
        assert_eq!(parse_scorecard_exit_code(&card(1, 0, true)), 1);
        assert_eq!(parse_scorecard_exit_code(&card(0, 1, false)), 1);
        // A clean partial run exits 0 even though pass=false.
        assert_eq!(parse_scorecard_exit_code(&card(0, 0, false)), 0);
    }

    /// Env-gated smoke against the real pinned corpus: TRUST_JS_NODE set =>
    /// run --limit 50 and expect the fail-closed invariants — 0
    /// disagreements, 0 oracle errors, the run-accounting identity, exit 0.
    /// Parser-version-agnostic: written against the D1 stub (100%
    /// no-coverage), it must keep holding as trust-js-parse grows real
    /// coverage — only the zero-disagreement bar is pinned.
    #[test]
    fn env_gated_corpus_smoke() {
        let Ok(node) = std::env::var("TRUST_JS_NODE") else {
            eprintln!("env_gated_corpus_smoke: TRUST_JS_NODE unset — skipped");
            return;
        };
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let corpus = std::env::var("TRUST_JS_CORPUS").map(PathBuf::from).unwrap_or_else(|_| {
            repo.join("build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4")
        });
        assert!(
            corpus.is_dir(),
            "TRUST_JS_NODE is set but the pinned corpus is missing at {}",
            corpus.display()
        );
        let out_dir = tempfile::tempdir().expect("tempdir");
        let opts = ParseVerdictOpts {
            corpus,
            slice: repo.join("tests/js262/S0.toml"),
            slice_kind: SliceKind::S0,
            node: PathBuf::from(node),
            jobs: 4,
            limit: Some(50),
            out_dir: out_dir.path().to_path_buf(),
            ledgers: repo.join("tests/js262"),
        };
        let code = run_parse_verdict(&opts).expect("parse-verdict run");
        assert_eq!(code, 0, "clean partial run must exit 0");
        let scorecard: ParseScorecard = serde_json::from_str(
            &std::fs::read_to_string(out_dir.path().join("parse-scorecard.json"))
                .expect("read parse-scorecard.json"),
        )
        .expect("parse scorecard json");
        let t = &scorecard.totals;
        assert_eq!(t.cases, 50);
        assert_eq!(t.disagree, 0);
        assert_eq!(t.oracle_errors, 0);
        // Every executed run is judged or soundly refused, never lost.
        assert_eq!(t.agree + t.disagree + t.unsupported + t.oracle_errors, t.runs);
        assert_eq!(
            scorecard.gate.coverage_ratio,
            (t.agree + t.disagree) as f64 / t.runs as f64
        );
        assert_eq!(scorecard.gate.unwaived_disagree, 0);
        assert!(scorecard.gate.disagree_ok);
        assert_eq!(scorecard.partial, Some(true));
        assert!(!scorecard.gate.pass, "a --limit run never claims the gate");
        // Divergent jsonl exists and is empty; dashboard section exists.
        let jsonl = std::fs::read_to_string(out_dir.path().join("parse-verdicts-divergent.jsonl"))
            .expect("read jsonl");
        assert!(jsonl.is_empty());
        let dash = std::fs::read_to_string(out_dir.path().join("parse-dashboard.md"))
            .expect("read dashboard");
        assert!(dash.contains("## Parse-verdict differential"));
        eprintln!(
            "env_gated_corpus_smoke: cases={} runs={} unsupported={} raw_skipped={} oracle_errors={}",
            t.cases, t.runs, t.unsupported, t.raw_skipped, t.oracle_errors
        );
    }
}
