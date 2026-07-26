// The M0 calibration gate run: every S0 case × mandated mode through Node +
// Bun (+ trust-js-sem with --sem, + the trust-js-interp faithful tier with
// --trustjs — the M1 D3 fourth head, same audit discipline), trace-diffed
// with trust-js-trace, audited against the divergence ledger, and reported as
// a fail-closed scorecard (trust.js262.scorecard.v1) + dashboard.md +
// divergences.jsonl (+ sem_divergences.jsonl / trustjs_divergences.jsonl).
// The published dashboard is the only permitted conformance claim. A --limit
// run is marked partial and NEVER claims the gate.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use trust_js_trace::{
    explain_divergence, normalize_async_completion_markers, trace_driver_sha256, traces_equal,
    ObservableTrace,
};

use crate::cases::{prepare_case, PreparedCase};
use crate::heads::{
    write_driver, BunHead, EngineHead, HeadResult, NodeHead, RunMode, SemHead, TrustJsHead,
};
use crate::model::{
    DivergenceRow, Js262AuditEntry, Js262Classification, Scorecard, ScorecardCorpus,
    ScorecardEngine, ScorecardEngines, ScorecardGate, ScorecardTotals, SCORECARD_SCHEMA,
};
use crate::slice::{derive, load_slice, verify_derived, SliceKind};
use crate::util::{git_head, now_utc_iso, probe_engine, validation_date, Engine, ProbedEngine};
use crate::validate::{audit_entry_is_active, load_audit, load_test_exceptions, test_exception_is_active, validate_ledgers};

pub struct CalibrateOpts {
    pub corpus: PathBuf,
    pub slice: PathBuf,
    pub node: PathBuf,
    pub bun: PathBuf,
    pub sem: bool,
    /// The M1 D3 fourth head (trust-js-interp), composable with --sem.
    pub trustjs: bool,
    pub jobs: usize,
    pub timeout: Duration,
    pub limit: Option<usize>,
    pub out_dir: PathBuf,
    pub ledgers: PathBuf,
}

struct RunRecord {
    path: String,
    mode: RunMode,
    node: HeadResult,
    bun: HeadResult,
    sem: Option<HeadResult>,
    trustjs: Option<HeadResult>,
}

/// The auxiliary-head (sem / trustjs) audit accumulator — one discipline for
/// both heads. Every judged run is covered (trace), a sound refusal
/// (no-coverage), or a harness error; a harness error is neither, so it
/// breaks the audit equation covered + no_coverage == cases (fail-closed).
/// Equality is trace-equality against EITHER engine trace; anything else is
/// a gate-fatal divergence (zero-wrong-traces discipline).
pub(crate) struct HeadAudit {
    head: &'static str,
    pub cases: u64,
    pub covered: u64,
    pub equal: u64,
    pub divergent: u64,
    pub no_coverage: u64,
    pub divergence_notes: Vec<String>,
    pub divergence_rows: Vec<serde_json::Value>,
    pub no_coverage_reasons: BTreeMap<String, u64>,
}

impl HeadAudit {
    pub fn new(head: &'static str) -> Self {
        Self {
            head,
            cases: 0,
            covered: 0,
            equal: 0,
            divergent: 0,
            no_coverage: 0,
            divergence_notes: Vec::new(),
            divergence_rows: Vec::new(),
            no_coverage_reasons: BTreeMap::new(),
        }
    }

    pub fn observe(
        &mut self,
        path: &str,
        mode: RunMode,
        res: &HeadResult,
        node: &ObservableTrace,
        bun: &ObservableTrace,
    ) {
        self.cases += 1;
        match res {
            HeadResult::Trace(t) => {
                self.covered += 1;
                if traces_equal(t, node) || traces_equal(t, bun) {
                    self.equal += 1;
                } else {
                    self.divergent += 1;
                    let explain = explain_divergence(t, node)
                        .unwrap_or_else(|| format!("{} trace differs", self.head));
                    self.divergence_notes.push(format!(
                        "{path} [{}]: {} vs node: {explain}",
                        mode.as_str(),
                        self.head
                    ));
                    self.divergence_rows.push(serde_json::json!({
                        "path": path,
                        "mode": mode.as_str(),
                        "explain": explain,
                    }));
                }
            }
            HeadResult::NoCoverage(reason) => {
                self.no_coverage += 1;
                *self.no_coverage_reasons.entry(reason.clone()).or_default() += 1;
            }
            HeadResult::HarnessError(e) => {
                // Neither covered nor a sound refusal: breaks the audit
                // (covered + no_coverage < cases).
                self.divergence_notes.push(format!(
                    "{path} [{}]: {} harness error: {e}",
                    mode.as_str(),
                    self.head
                ));
            }
        }
    }

    /// The audit equation + zero-wrong-traces bar (vacuously true when the
    /// head never ran).
    pub fn audit_ok(&self) -> bool {
        self.covered + self.no_coverage == self.cases && self.divergent == 0
    }
}

pub fn run_calibrate(opts: &CalibrateOpts) -> anyhow::Result<i32> {
    let vdate = validation_date();

    // --- identities ---
    let node_id = probe_engine(Engine::Node, &opts.node)?;
    let bun_id = probe_engine(Engine::Bun, &opts.bun)?;
    let driver_sha = trace_driver_sha256();
    let corpus_revision = git_head(&opts.corpus).unwrap_or_else(|| "unknown".to_string());

    // --- slice ---
    let loaded = load_slice(&opts.slice)?;
    if !loaded.findings.is_empty() {
        for f in &loaded.findings {
            eprintln!("calibrate: slice manifest finding: {}", f.render());
        }
        anyhow::bail!("slice manifest {} failed its internal consistency check", opts.slice.display());
    }
    // The slice self-declares its kind (S0 vs S-async); re-derivation and the
    // dashboard label both follow it.
    let slice_kind = loaded.kind;
    // Embedded manifests carry the list; payload-external manifests are
    // re-derived from the pinned corpus and checked against [derived].
    let tests: Vec<String> = match &loaded.tests {
        Some(tests) => tests.clone(),
        None => {
            let derived = derive(&opts.corpus, slice_kind)?;
            let findings = verify_derived(&loaded, &derived);
            if !findings.is_empty() {
                for f in &findings {
                    eprintln!("calibrate: slice drift finding: {}", f.render());
                }
                anyhow::bail!(
                    "re-derived {} slice does not match committed manifest {} — fail closed",
                    slice_kind.id(),
                    opts.slice.display()
                );
            }
            derived.paths
        }
    };
    let slice_sha256 = loaded.list_sha256.clone();

    // Corpus module-goal configuration (fail-closed, self-configuring per run).
    // The module-goal driver imports the REAL corpus test file so relative
    // imports (siblings, self-imports, _FIXTURE) resolve. But a `.js` file that
    // lacks import/export/top-level-await triggers Node's CommonJS-first source
    // detection (there is no package.json at the pinned corpus root), so a
    // `flags: [module]` test that relies purely on module SEMANTICS (top-level
    // `return`/`this`/`new.target`, module early errors) is spuriously run in
    // the Script goal by Node while Bun uses the Module goal — a harness-induced
    // divergence, not an engine one. `package.json {"type":"module"}` at the
    // corpus root forces BOTH engines to the Module goal for every `.js` under
    // it, matching `flags:[module]`; importing the real file preserves
    // self-import identity (same URL → same module instance). It must be ABSENT
    // for S0 / S-async, whose raw lane runs corpus `.js` script tests directly
    // and would be mis-run as modules. So each calibration self-configures the
    // corpus goal from its slice kind (do not run a module and a script
    // calibration against the same corpus concurrently).
    let corpus_pkg = opts.corpus.join("package.json");
    match slice_kind {
        SliceKind::SModule => {
            std::fs::write(&corpus_pkg, "{\"type\":\"module\"}\n").map_err(|e| {
                anyhow::anyhow!("module goal needs {}: {e}", corpus_pkg.display())
            })?;
        }
        SliceKind::S0 | SliceKind::SAsync => {
            if corpus_pkg.exists() {
                std::fs::remove_file(&corpus_pkg).map_err(|e| {
                    anyhow::anyhow!("script goal needs {} absent: {e}", corpus_pkg.display())
                })?;
            }
        }
    }

    let partial = opts.limit.map(|n| n < tests.len()).unwrap_or(false);
    let selected: Vec<String> = match opts.limit {
        Some(n) => tests.iter().take(n).cloned().collect(),
        None => tests,
    };

    // --- ledgers ---
    let (ledger_findings, _summary) = validate_ledgers(&opts.ledgers, &vdate);
    let audit = load_audit(&opts.ledgers);
    let exceptions = load_test_exceptions(&opts.ledgers);
    let active_exceptions: Vec<&crate::model::Js262TestException> = exceptions
        .exceptions
        .iter()
        .filter(|e| test_exception_is_active(e, &vdate))
        .collect();
    let active_waivers: Vec<&Js262AuditEntry> = audit
        .entries
        .iter()
        .filter(|e| {
            // The trace lane consumes only head="trace" entries (the default);
            // a head="parse" entry can never waive a trace divergence.
            e.head == crate::model::Js262AuditHead::Trace
                && audit_entry_is_active(e, &vdate)
                && e.classification != Js262Classification::ProjectionTooStrong
        })
        .collect();
    let pts_entries: Vec<&Js262AuditEntry> = audit
        .entries
        .iter()
        .filter(|e| {
            e.classification == Js262Classification::ProjectionTooStrong
                && e.status == crate::model::Js262AuditStatus::Active
        })
        .collect();

    // --- prepare cases (fail-closed on unparseable frontmatter) ---
    let mut prepared: Vec<PreparedCase> = Vec::with_capacity(selected.len());
    let mut case_faults: Vec<(String, String)> = Vec::new();
    for rel in &selected {
        match prepare_case(&opts.corpus, rel) {
            Ok(c) => prepared.push(c),
            Err(e) => case_faults.push((rel.clone(), e)),
        }
    }

    // --- run dir + driver ---
    std::fs::create_dir_all(&opts.out_dir)?;
    let tmp = opts.out_dir.join("tmp");
    let driver = write_driver(&tmp)?;

    // --- auxiliary-head include cache (shared by sem + trustjs) ---
    let aux_cache = if opts.sem || opts.trustjs {
        Some(SemHead::build_cache(prepared.iter().flat_map(|c| c.includes.iter())))
    } else {
        None
    };

    // --- worker pool over a locked queue ---
    let jobs = opts.jobs.max(1);
    let next = Arc::new(Mutex::new(0usize));
    let records: Arc<Mutex<Vec<RunRecord>>> = Arc::new(Mutex::new(Vec::new()));
    let prepared = Arc::new(prepared);
    let timeout = opts.timeout;

    std::thread::scope(|scope| -> anyhow::Result<()> {
        let mut handles = Vec::new();
        for worker in 0..jobs {
            let next = Arc::clone(&next);
            let records = Arc::clone(&records);
            let prepared = Arc::clone(&prepared);
            let aux_cache = aux_cache.clone();
            let sem_on = opts.sem;
            let trustjs_on = opts.trustjs;
            let node_path = opts.node.clone();
            let bun_path = opts.bun.clone();
            let driver = driver.clone();
            let slot_root = tmp.join(format!("worker-{worker}"));
            handles.push(scope.spawn(move || -> Result<(), String> {
                let node_head = NodeHead::new(node_path, driver.clone(), slot_root.join("node"))
                    .map_err(|e| format!("worker {worker}: node slot: {e}"))?;
                let bun_head = BunHead::new(bun_path, driver.clone(), slot_root.join("bun"))
                    .map_err(|e| format!("worker {worker}: bun slot: {e}"))?;
                let sem_head = aux_cache
                    .as_ref()
                    .filter(|_| sem_on)
                    .map(|c| SemHead::new(Arc::clone(c)));
                let trustjs_head = aux_cache
                    .as_ref()
                    .filter(|_| trustjs_on)
                    .map(|c| TrustJsHead::new(Arc::clone(c)));
                loop {
                    let idx = {
                        let mut guard = next.lock().map_err(|_| "queue poisoned")?;
                        let idx = *guard;
                        *guard += 1;
                        idx
                    };
                    let Some(case) = prepared.get(idx) else { break };
                    for &mode in &case.modes {
                        let assembled = case.assemble(mode, timeout);
                        let node_res = node_head.run(&assembled);
                        let bun_res = bun_head.run(&assembled);
                        // The sem/trustjs audits only cover runs the engine
                        // pair can judge; a pair harness error already fails
                        // the run.
                        let (sem_res, trustjs_res) = match (&node_res, &bun_res) {
                            (HeadResult::Trace(_), HeadResult::Trace(_)) => (
                                sem_head.as_ref().map(|h| h.run(&assembled)),
                                trustjs_head.as_ref().map(|h| h.run(&assembled)),
                            ),
                            _ => (None, None),
                        };
                        records
                            .lock()
                            .map_err(|_| "records poisoned")?
                            .push(RunRecord {
                                path: case.rel_path.clone(),
                                mode,
                                node: node_res,
                                bun: bun_res,
                                sem: sem_res,
                                trustjs: trustjs_res,
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

    // --- deterministic collection ---
    let mut records = Arc::try_unwrap(records)
        .map_err(|_| anyhow::anyhow!("records still shared"))?
        .into_inner()
        .map_err(|_| anyhow::anyhow!("records poisoned"))?;
    records.sort_by(|a, b| (a.path.as_str(), a.mode.as_str()).cmp(&(b.path.as_str(), b.mode.as_str())));

    // --- async-failure-marker normalization ---
    // The test262 async harness reports a failure by printing
    // `Test262:AsyncTestFailure:<name>: <message>`; the <message> tail is
    // engine-divergent, unspecified text — the same class the thrown-completion
    // projection already strips to error identity. Apply the normalization to
    // EVERY head's trace uniformly BEFORE any traces_equal comparison so the
    // async failure observable is message-free and comparable across all four
    // heads (a no-op on markerless slices such as S0).
    let normalize = |res: &mut HeadResult| {
        if let HeadResult::Trace(t) = res {
            normalize_async_completion_markers(t);
        }
    };
    for rec in &mut records {
        normalize(&mut rec.node);
        normalize(&mut rec.bun);
        if let Some(sem) = rec.sem.as_mut() {
            normalize(sem);
        }
        if let Some(trustjs) = rec.trustjs.as_mut() {
            normalize(trustjs);
        }
    }

    // --- aggregate ---
    let mut totals = ScorecardTotals::default();
    totals.cases = (prepared.len() + case_faults.len()) as u64;
    let mut divergences: Vec<DivergenceRow> = Vec::new();
    let mut harness_error_notes: Vec<String> = Vec::new();
    let mut sem_audit = HeadAudit::new("sem");
    let mut trustjs_audit = HeadAudit::new("trustjs");
    let mut divergent_paths: BTreeSet<String> = BTreeSet::new();
    let mut unclassified_paths: BTreeSet<String> = BTreeSet::new();

    for (rel, err) in &case_faults {
        totals.runs += 1;
        totals.harness_errors += 1;
        harness_error_notes.push(format!("{rel}: case preparation failed: {err}"));
    }

    for rec in &records {
        totals.runs += 1;
        match (&rec.node, &rec.bun) {
            (HeadResult::Trace(a), HeadResult::Trace(b)) => {
                if traces_equal(a, b) {
                    totals.trace_equal_runs += 1;
                } else {
                    totals.divergent_runs += 1;
                    divergent_paths.insert(rec.path.clone());
                    let explain = explain_divergence(a, b)
                        .unwrap_or_else(|| "traces differ (unlocalized)".to_string());
                    let fp_input = format!("{}|{}|{}", rec.path, rec.mode.as_str(), explain);
                    let fingerprint =
                        trust_js_trace::sha256_hex(fp_input.as_bytes())[..16].to_string();
                    let waiver = active_waivers
                        .iter()
                        .find(|e| e.path == rec.path && e.fingerprint == fingerprint);
                    if waiver.is_none() {
                        unclassified_paths.insert(rec.path.clone());
                    }
                    divergences.push(DivergenceRow {
                        path: rec.path.clone(),
                        mode: rec.mode.as_str().to_string(),
                        explain,
                        fingerprint,
                        classification: waiver.map(|e| e.classification),
                    });
                }
                if let Some(sem) = &rec.sem {
                    sem_audit.observe(&rec.path, rec.mode, sem, a, b);
                }
                if let Some(trustjs) = &rec.trustjs {
                    trustjs_audit.observe(&rec.path, rec.mode, trustjs, a, b);
                }
            }
            _ => {
                let describe = |r: &HeadResult, name: &str| match r {
                    HeadResult::Trace(_) => None,
                    HeadResult::NoCoverage(m) => Some(format!("{name}: no-coverage: {m}")),
                    HeadResult::HarnessError(m) => Some(format!("{name}: {m}")),
                };
                let parts: Vec<String> = [describe(&rec.node, "node"), describe(&rec.bun, "bun")]
                    .into_iter()
                    .flatten()
                    .collect();
                // An active test exception (e.g. an engine's pathological
                // slowdown on one generated test) accounts the fault without
                // hiding it; anything unexcepted is a tool failure.
                if let Some(exc) = active_exceptions.iter().find(|e| e.path == rec.path) {
                    totals.excepted_harness_errors += 1;
                    harness_error_notes.push(format!(
                        "{} [{}]: {} (excepted: {})",
                        rec.path,
                        rec.mode.as_str(),
                        parts.join("; "),
                        exc.id
                    ));
                } else {
                    totals.harness_errors += 1;
                    harness_error_notes.push(format!(
                        "{} [{}]: {}",
                        rec.path,
                        rec.mode.as_str(),
                        parts.join("; ")
                    ));
                }
            }
        }
    }

    totals.divergent_cases = divergent_paths.len() as u64;
    totals.unclassified_divergent_cases = unclassified_paths.len() as u64;
    totals.classified_divergent_cases = totals.divergent_cases - totals.unclassified_divergent_cases;
    totals.tool_failures = totals.harness_errors;
    totals.sem_cases = sem_audit.cases;
    totals.sem_covered = sem_audit.covered;
    totals.sem_equal = sem_audit.equal;
    totals.sem_divergent = sem_audit.divergent;
    totals.sem_no_coverage = sem_audit.no_coverage;
    totals.trustjs_cases = trustjs_audit.cases;
    totals.trustjs_covered = trustjs_audit.covered;
    totals.trustjs_equal = trustjs_audit.equal;
    totals.trustjs_divergent = trustjs_audit.divergent;
    totals.trustjs_no_coverage = trustjs_audit.no_coverage;
    totals.failed =
        totals.unclassified_divergent_cases + totals.sem_divergent + totals.trustjs_divergent;

    // --- gate ---
    let ratio = if totals.runs > 0 {
        totals.trace_equal_runs as f64 / totals.runs as f64
    } else {
        1.0
    };
    // The design doc's >=99.9% Node==Bun agreement figure is a HYPOTHESIS the
    // calibration measures and reports — it is not a pass condition. The gate
    // passes when the apparatus is calibrated: every divergence classified
    // (none of them projection_too_strong), the sem and trustjs audit
    // equations hold, the ledgers validate, and the run is complete.
    let ratio_ok = ratio >= 0.999;
    let unclassified_ok = totals.unclassified_divergent_cases == 0;
    let sem_audit_ok = sem_audit.audit_ok();
    let trustjs_audit_ok = trustjs_audit.audit_ok();
    let ledger_ok = ledger_findings.is_empty() && pts_entries.is_empty();
    let pass = unclassified_ok && sem_audit_ok && trustjs_audit_ok && ledger_ok && !partial;
    let gate = ScorecardGate {
        trace_equal_ratio: ratio,
        ratio_ok,
        unclassified_ok,
        sem_audit_ok,
        trustjs_audit_ok,
        ledger_ok,
        pass,
        reason: if partial {
            Some("partial scorecard (--limit) never claims the gate".to_string())
        } else {
            None
        },
    };

    let scorecard = Scorecard {
        schema: SCORECARD_SCHEMA.to_string(),
        generated_at: now_utc_iso(),
        partial: if partial { Some(true) } else { None },
        corpus: ScorecardCorpus { revision: corpus_revision, slice_sha256 },
        engines: ScorecardEngines { node: engine_json(&node_id), bun: engine_json(&bun_id) },
        driver_sha256: driver_sha,
        totals,
        gate,
    };

    // --- artifacts ---
    let scorecard_path = opts.out_dir.join("scorecard.json");
    std::fs::write(&scorecard_path, serde_json::to_string_pretty(&scorecard)?)?;
    let jsonl_path = opts.out_dir.join("divergences.jsonl");
    {
        let mut f = std::fs::File::create(&jsonl_path)?;
        for row in &divergences {
            writeln!(f, "{}", serde_json::to_string(row)?)?;
        }
    }
    {
        let mut f = std::fs::File::create(opts.out_dir.join("sem_divergences.jsonl"))?;
        for row in &sem_audit.divergence_rows {
            writeln!(f, "{row}")?;
        }
    }
    {
        let mut f = std::fs::File::create(opts.out_dir.join("trustjs_divergences.jsonl"))?;
        for row in &trustjs_audit.divergence_rows {
            writeln!(f, "{row}")?;
        }
    }
    let dashboard_path = opts.out_dir.join("dashboard.md");
    std::fs::write(
        &dashboard_path,
        render_dashboard(
            slice_kind,
            &scorecard,
            &divergences,
            &harness_error_notes,
            &sem_audit,
            &trustjs_audit,
        ),
    )?;

    for f in &ledger_findings {
        eprintln!("calibrate: ledger finding: {}", f.render());
    }
    for e in &pts_entries {
        eprintln!(
            "calibrate: audit entry {} is projection_too_strong — never a waiver; fix trust-js-trace instead",
            e.id
        );
    }
    println!(
        "calibrate: cases={} runs={} trace_equal={} divergent_runs={} unclassified_cases={} harness_errors={} sem: {}/{} covered, {} no-coverage, {} divergent — trustjs: {}/{} covered, {} no-coverage, {} divergent",
        scorecard.totals.cases,
        scorecard.totals.runs,
        scorecard.totals.trace_equal_runs,
        scorecard.totals.divergent_runs,
        scorecard.totals.unclassified_divergent_cases,
        scorecard.totals.harness_errors,
        scorecard.totals.sem_covered,
        scorecard.totals.sem_cases,
        scorecard.totals.sem_no_coverage,
        scorecard.totals.sem_divergent,
        scorecard.totals.trustjs_covered,
        scorecard.totals.trustjs_cases,
        scorecard.totals.trustjs_no_coverage,
        scorecard.totals.trustjs_divergent,
    );
    println!(
        "calibrate: ratio={:.6} gate.pass={}{} — artifacts in {}",
        scorecard.gate.trace_equal_ratio,
        scorecard.gate.pass,
        if partial { " (partial)" } else { "" },
        opts.out_dir.display()
    );

    Ok(scorecard_exit_code(&scorecard))
}

fn engine_json(p: &ProbedEngine) -> ScorecardEngine {
    ScorecardEngine {
        path: p.path.display().to_string(),
        version: p.version.clone(),
        sha256: p.sha256.clone(),
    }
}

/// Exit 1 if tool_failures != 0 or failed != 0 or !gate.pass.
pub fn scorecard_exit_code(s: &Scorecard) -> i32 {
    if s.totals.tool_failures != 0 || s.totals.failed != 0 || !s.gate.pass {
        1
    } else {
        0
    }
}

fn render_dashboard(
    kind: SliceKind,
    s: &Scorecard,
    divergences: &[DivergenceRow],
    harness_errors: &[String],
    sem_audit: &HeadAudit,
    trustjs_audit: &HeadAudit,
) -> String {
    let mut out = String::new();
    let t = &s.totals;
    out.push_str(&format!("# TrustJS {} calibration dashboard\n\n", kind.id()));
    out.push_str("The published dashboard is the only permitted conformance claim.\n\n");
    if s.partial == Some(true) {
        out.push_str("**PARTIAL RUN (`--limit`): this scorecard never claims the gate.**\n\n");
    }
    out.push_str(&format!("- Generated: {}\n", s.generated_at));
    out.push_str(&format!("- Corpus: `{}` (slice sha256 `{}`)\n", s.corpus.revision, s.corpus.slice_sha256));
    // Version + binary digest, never the install path: the dashboard is the
    // published conformance record, and a reader on another box has to be able
    // to check they are running the same engine, which an absolute path from
    // the producing machine cannot tell them.
    out.push_str(&format!(
        "- Node: {} (sha256 `{}`)\n",
        s.engines.node.version, s.engines.node.sha256
    ));
    out.push_str(&format!(
        "- Bun: {} (sha256 `{}`)\n",
        s.engines.bun.version, s.engines.bun.sha256
    ));
    out.push_str(&format!("- Driver sha256: `{}`\n\n", s.driver_sha256));
    out.push_str("| metric | value |\n|---|---|\n");
    for (k, v) in [
        ("cases", t.cases),
        ("runs", t.runs),
        ("trace-equal runs", t.trace_equal_runs),
        ("divergent runs", t.divergent_runs),
        ("divergent cases", t.divergent_cases),
        ("classified divergent cases", t.classified_divergent_cases),
        ("unclassified divergent cases", t.unclassified_divergent_cases),
        ("harness errors (= tool failures)", t.harness_errors),
        ("failed", t.failed),
    ] {
        out.push_str(&format!("| {k} | {v} |\n"));
    }
    out.push_str(&format!(
        "\n**Gate**: unclassified_ok {1}, sem_audit_ok {2}, trustjs_audit_ok {3}, ledger_ok {4} => **pass: {5}** — Node==Bun agreement measured {0:.6} (the design doc's >=99.9% hypothesis is reported, not gated: hypothesis_met={6})\n",
        s.gate.trace_equal_ratio, s.gate.unclassified_ok, s.gate.sem_audit_ok,
        s.gate.trustjs_audit_ok, s.gate.ledger_ok, s.gate.pass, s.gate.ratio_ok
    ));
    if let Some(r) = &s.gate.reason {
        out.push_str(&format!("\nReason: {r}\n"));
    }

    render_head_section(
        &mut out,
        "Sem coverage",
        "sem",
        (t.sem_cases, t.sem_covered, t.sem_equal, t.sem_divergent, t.sem_no_coverage),
        sem_audit,
        10,
    );
    render_head_section(
        &mut out,
        "TrustJS coverage (faithful tier)",
        "trustjs",
        (
            t.trustjs_cases,
            t.trustjs_covered,
            t.trustjs_equal,
            t.trustjs_divergent,
            t.trustjs_no_coverage,
        ),
        trustjs_audit,
        20,
    );

    render_divergence_section(&mut out, divergences, harness_errors);
    out
}

/// One auxiliary-head dashboard section: the counters plus a no-coverage
/// -reason histogram (top `histogram_top`) and the gate-fatal divergences.
fn render_head_section(
    out: &mut String,
    title: &str,
    head: &str,
    (cases, covered, equal, divergent, no_coverage): (u64, u64, u64, u64, u64),
    audit: &HeadAudit,
    histogram_top: usize,
) {
    out.push_str(&format!(
        "\n## {title}\n\n- {head} cases: {cases} — covered {covered}, equal {equal}, divergent {divergent}, no-coverage {no_coverage}\n",
    ));
    if !audit.no_coverage_reasons.is_empty() {
        out.push_str(&format!("\nTop no-coverage reasons (top {histogram_top}):\n\n"));
        let mut reasons: Vec<(&String, &u64)> = audit.no_coverage_reasons.iter().collect();
        reasons.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        for (reason, n) in reasons.iter().take(histogram_top) {
            out.push_str(&format!("- {n} × {reason}\n"));
        }
    }
    if !audit.divergence_notes.is_empty() {
        out.push_str(&format!(
            "\n{} divergences (gate-fatal):\n\n",
            capitalize(head)
        ));
        for line in audit.divergence_notes.iter().take(25) {
            out.push_str(&format!("- {line}\n"));
        }
    }
}

fn capitalize(s: &str) -> String {
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().collect::<String>() + c.as_str(),
        None => String::new(),
    }
}

fn render_divergence_section(
    out: &mut String,
    divergences: &[DivergenceRow],
    harness_errors: &[String],
) {
    let unclassified: Vec<&DivergenceRow> =
        divergences.iter().filter(|d| d.classification.is_none()).collect();
    out.push_str(&format!(
        "\n## Divergences\n\n{} divergent runs ({} unclassified). Full list: divergences.jsonl.\n",
        divergences.len(),
        unclassified.len()
    ));
    if !unclassified.is_empty() {
        out.push_str("\nTop unclassified divergences:\n\n");
        for d in unclassified.iter().take(25) {
            out.push_str(&format!("- `{}` [{}] fp `{}`: {}\n", d.path, d.mode, d.fingerprint, d.explain));
        }
    }
    if !harness_errors.is_empty() {
        out.push_str(&format!("\n## Harness errors ({})\n\n", harness_errors.len()));
        for line in harness_errors.iter().take(25) {
            out.push_str(&format!("- {line}\n"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{ScorecardCorpus, ScorecardEngine, ScorecardEngines};

    fn scorecard(tool_failures: u64, failed: u64, pass: bool) -> Scorecard {
        Scorecard {
            schema: SCORECARD_SCHEMA.to_string(),
            generated_at: "2026-07-21T00:00:00Z".to_string(),
            partial: None,
            corpus: ScorecardCorpus { revision: "cafe".into(), slice_sha256: "00".into() },
            engines: ScorecardEngines {
                node: ScorecardEngine { path: "n".into(), version: "v".into(), sha256: "0".into() },
                bun: ScorecardEngine { path: "b".into(), version: "v".into(), sha256: "0".into() },
            },
            driver_sha256: "d".into(),
            totals: ScorecardTotals {
                tool_failures,
                harness_errors: tool_failures,
                failed,
                ..Default::default()
            },
            gate: ScorecardGate {
                trace_equal_ratio: 1.0,
                ratio_ok: true,
                unclassified_ok: true,
                sem_audit_ok: true,
                trustjs_audit_ok: true,
                ledger_ok: true,
                pass,
                reason: None,
            },
        }
    }

    #[test]
    fn exit_code_contract() {
        assert_eq!(scorecard_exit_code(&scorecard(0, 0, true)), 0);
        assert_eq!(scorecard_exit_code(&scorecard(1, 0, true)), 1);
        assert_eq!(scorecard_exit_code(&scorecard(0, 1, true)), 1);
        assert_eq!(scorecard_exit_code(&scorecard(0, 0, false)), 1);
    }

    #[test]
    fn scorecard_json_round_trip() {
        let s = scorecard(0, 0, true);
        let json = serde_json::to_string_pretty(&s).unwrap();
        let back: Scorecard = serde_json::from_str(&json).unwrap();
        assert_eq!(back.schema, SCORECARD_SCHEMA);
        assert_eq!(back.totals, s.totals);
        // deny_unknown_fields keeps the scorecard schema honest.
        let mut v: serde_json::Value = serde_json::from_str(&json).unwrap();
        v.as_object_mut().unwrap().insert("surprise".into(), serde_json::json!(1));
        assert!(serde_json::from_value::<Scorecard>(v).is_err());
    }

    // --- HeadAudit: the trustjs/sem totals audit equation ---

    use trust_js_trace::{Completion, ThrownProjection, SCHEMA_VERSION};

    fn normal_trace() -> ObservableTrace {
        ObservableTrace {
            schema: SCHEMA_VERSION.to_string(),
            caps: None,
            events: vec![],
            completion: Completion::Normal { v: None },
        }
    }

    fn throw_trace() -> ObservableTrace {
        ObservableTrace {
            schema: SCHEMA_VERSION.to_string(),
            caps: None,
            events: vec![],
            completion: Completion::Throw {
                v: ThrownProjection::Error {
                    ctor: Some("Error:TypeError".into()),
                    name: Some("TypeError".into()),
                    ctor_name: Some("TypeError".into()),
                },
                phase: None,
            },
        }
    }

    #[test]
    fn head_audit_equation_holds_over_traces_and_refusals() {
        let node = normal_trace();
        let bun = normal_trace();
        let mut audit = HeadAudit::new("trustjs");
        // Covered + equal (matches node AND bun).
        audit.observe("a.js", RunMode::Bare, &HeadResult::Trace(normal_trace()), &node, &bun);
        // Covered + equal against EITHER engine: matches bun only.
        audit.observe(
            "b.js",
            RunMode::Strict,
            &HeadResult::Trace(throw_trace()),
            &node,
            &throw_trace(),
        );
        // Sound refusals: counted, never divergences.
        audit.observe(
            "c.js",
            RunMode::Bare,
            &HeadResult::NoCoverage("body parse: class".into()),
            &node,
            &bun,
        );
        audit.observe(
            "d.js",
            RunMode::Bare,
            &HeadResult::NoCoverage("body parse: class".into()),
            &node,
            &bun,
        );
        assert_eq!(
            (audit.cases, audit.covered, audit.equal, audit.divergent, audit.no_coverage),
            (4, 2, 2, 0, 2)
        );
        assert_eq!(audit.covered + audit.no_coverage, audit.cases, "audit equation");
        assert!(audit.audit_ok());
        assert_eq!(audit.no_coverage_reasons.get("body parse: class"), Some(&2));
        assert!(audit.divergence_rows.is_empty());
    }

    #[test]
    fn head_audit_divergence_is_gate_fatal_and_recorded() {
        let node = normal_trace();
        let bun = normal_trace();
        let mut audit = HeadAudit::new("trustjs");
        // A wrong trace (differs from BOTH engines) is a divergence.
        audit.observe("x.js", RunMode::Bare, &HeadResult::Trace(throw_trace()), &node, &bun);
        assert_eq!((audit.cases, audit.covered, audit.equal, audit.divergent), (1, 1, 0, 1));
        // The equation still holds (covered counts the wrong trace) but the
        // zero-wrong-traces bar fails the audit.
        assert_eq!(audit.covered + audit.no_coverage, audit.cases);
        assert!(!audit.audit_ok());
        // The jsonl row carries path/mode/explain.
        assert_eq!(audit.divergence_rows.len(), 1);
        let row = &audit.divergence_rows[0];
        assert_eq!(row.get("path").and_then(|v| v.as_str()), Some("x.js"));
        assert_eq!(row.get("mode").and_then(|v| v.as_str()), Some("bare"));
        assert!(row.get("explain").and_then(|v| v.as_str()).is_some());
        assert_eq!(audit.divergence_notes.len(), 1);
        assert!(audit.divergence_notes[0].contains("trustjs vs node"));
    }

    #[test]
    fn head_audit_harness_error_breaks_the_equation() {
        let node = normal_trace();
        let bun = normal_trace();
        let mut audit = HeadAudit::new("sem");
        audit.observe("a.js", RunMode::Bare, &HeadResult::Trace(normal_trace()), &node, &bun);
        audit.observe(
            "b.js",
            RunMode::Bare,
            &HeadResult::HarnessError("include source unavailable".into()),
            &node,
            &bun,
        );
        // Neither covered nor a sound refusal: covered + no_coverage < cases.
        assert_eq!((audit.cases, audit.covered, audit.no_coverage), (2, 1, 0));
        assert!(audit.covered + audit.no_coverage != audit.cases);
        assert!(!audit.audit_ok());
    }

    #[test]
    fn head_audit_vacuously_ok_when_never_run() {
        assert!(HeadAudit::new("trustjs").audit_ok());
    }

    /// Env-gated smoke against the real pinned corpus: TRUST_JS_NODE and
    /// TRUST_JS_BUN set => calibrate --trustjs --limit 100. Expect zero
    /// trustjs_divergent (zero-wrong-traces discipline), a plausible covered
    /// count, and the audit equation to hold.
    #[test]
    fn env_gated_trustjs_calibrate_smoke() {
        let Ok(node) = std::env::var("TRUST_JS_NODE") else {
            eprintln!("env_gated_trustjs_calibrate_smoke: TRUST_JS_NODE unset — skipped");
            return;
        };
        let Ok(bun) = std::env::var("TRUST_JS_BUN") else {
            eprintln!("env_gated_trustjs_calibrate_smoke: TRUST_JS_BUN unset — skipped");
            return;
        };
        let repo = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let corpus = std::env::var("TRUST_JS_CORPUS").map(PathBuf::from).unwrap_or_else(|_| {
            repo.join("build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4")
        });
        assert!(
            corpus.is_dir(),
            "TRUST_JS_NODE is set but the pinned corpus is missing at {}",
            corpus.display()
        );
        let out_dir = tempfile::tempdir().expect("tempdir");
        let opts = CalibrateOpts {
            corpus,
            slice: repo.join("tests/js262/S0.toml"),
            node: PathBuf::from(node),
            bun: PathBuf::from(bun),
            sem: false,
            trustjs: true,
            jobs: 4,
            timeout: Duration::from_secs(30),
            limit: Some(100),
            out_dir: out_dir.path().to_path_buf(),
            ledgers: repo.join("tests/js262"),
        };
        let code = run_calibrate(&opts).expect("calibrate run");
        let scorecard: Scorecard = serde_json::from_str(
            &std::fs::read_to_string(out_dir.path().join("scorecard.json"))
                .expect("read scorecard.json"),
        )
        .expect("parse scorecard json");
        let t = &scorecard.totals;
        eprintln!(
            "env_gated_trustjs_calibrate_smoke: trustjs cases={} covered={} equal={} divergent={} no_coverage={}",
            t.trustjs_cases, t.trustjs_covered, t.trustjs_equal, t.trustjs_divergent,
            t.trustjs_no_coverage
        );
        assert_eq!(t.cases, 100);
        // Zero wrong traces: gate-fatal if violated.
        assert_eq!(t.trustjs_divergent, 0, "trustjs produced a wrong trace");
        assert_eq!(t.trustjs_equal, t.trustjs_covered);
        // The audit equation must hold exactly.
        assert_eq!(t.trustjs_covered + t.trustjs_no_coverage, t.trustjs_cases);
        assert!(scorecard.gate.trustjs_audit_ok);
        // Plausibility: the head judged runs, and the faithful tier covers a
        // nonzero share of the sample.
        assert!(t.trustjs_cases > 0, "no runs reached the trustjs head");
        assert!(t.trustjs_covered > 0, "implausible: zero covered on 100 S0 cases");
        // --sem was off: the sem lane must be untouched and vacuously OK.
        assert_eq!(t.sem_cases, 0);
        assert!(scorecard.gate.sem_audit_ok);
        // A --limit run never claims the gate, so the exit code is 1.
        assert!(!scorecard.gate.pass, "a --limit run never claims the gate");
        assert_eq!(code, 1);
        assert_eq!(t.failed, t.unclassified_divergent_cases, "aux heads contributed to failed");
        // The trustjs divergences artifact exists and is empty.
        let jsonl = std::fs::read_to_string(out_dir.path().join("trustjs_divergences.jsonl"))
            .expect("read trustjs_divergences.jsonl");
        assert!(jsonl.is_empty(), "unexpected trustjs divergences:\n{jsonl}");
        // The dashboard has the TrustJS section with the histogram.
        let dash =
            std::fs::read_to_string(out_dir.path().join("dashboard.md")).expect("read dashboard");
        assert!(dash.contains("## TrustJS coverage (faithful tier)"));
        // The fresh scorecard passes the ratchet check vacuously (no ledger).
        let findings = crate::ratchet::check_findings(t, None);
        assert!(findings.is_empty(), "ratchet findings on a clean run: {findings:?}");
    }
}
