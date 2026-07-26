// ts-calibrate: the TrustTS differential lane — the erasable-TypeScript
// front-end (trust-ts-strip → trust-js-interp) judged end-to-end against the
// Node and Bun oracles, both of which run `.ts` natively (type-strip + module
// evaluation) when the driver `import()`s the corpus file.
//
// For each corpus `.ts`: the Node ProcessHead and Bun ProcessHead run it in the
// module goal (they strip-and-run), and the TrustTsHead strips it to JS and
// evaluates the stripped module. The TrustTS head COVERS a case only if its
// trace equals Node OR Bun; a covered trace matching NEITHER is `divergent` —
// the zero-wrong-traces bar, a hard failure. A sound refusal (`NoCoverage`, from
// the stripper or the interp) is always safe.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use trust_js_trace::traces_equal;

use crate::calibrate::HeadAudit;
use crate::heads::{
    write_driver, AssembledCase, BunHead, EngineHead, HeadResult, NodeHead, RunMode, TrustTsHead,
};
use crate::util::{probe_engine, Engine};

pub struct TsCalibrateOpts {
    /// Directory of `.ts` corpus programs (tests/ts-corpus for the erasable
    /// lane, tests/ts-transform-corpus for the non-erasable transform lane).
    pub corpus: PathBuf,
    pub node: PathBuf,
    pub bun: PathBuf,
    pub timeout: Duration,
    pub limit: Option<usize>,
    /// Optional JSON scorecard sink.
    pub out: Option<PathBuf>,
    /// The non-erasable transform tier: the TrustTS head lowers enum/namespace
    /// via `trust_ts_strip::transform`, and the Node oracle runs the `.ts` with
    /// `--experimental-transform-types` (so it transpiles rather than only
    /// strips). Bun transpiles natively either way.
    pub transform: bool,
}

/// The TrustTS differential scorecard.
#[derive(Default, Debug)]
pub struct TsScorecard {
    pub cases: u64,
    /// Cases where BOTH engines produced a trace and those traces are equal.
    pub node_bun_equal: u64,
    /// Cases where both engines produced a trace but the traces differ.
    pub node_bun_divergent: u64,
    /// Cases an engine could not judge (spawn/timeout/throw-in-harness). Such a
    /// case has no oracle, so the TrustTS head is not audited on it.
    pub engine_errors: u64,
    /// TrustTS head, audited over the engine-judged cases only.
    pub trustts_covered: u64,
    pub trustts_equal: u64,
    pub trustts_divergent: u64,
    pub trustts_no_coverage: u64,
    pub divergence_notes: Vec<String>,
    pub engine_error_notes: Vec<String>,
    pub no_coverage_reasons: BTreeMap<String, u64>,
}

/// Enumerate the corpus `.ts` files, sorted by corpus-relative path.
fn list_corpus(dir: &Path) -> anyhow::Result<Vec<(String, PathBuf)>> {
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir)
        .map_err(|e| anyhow::anyhow!("read corpus dir {}: {e}", dir.display()))?
    {
        let path = entry.map_err(|e| anyhow::anyhow!("corpus entry: {e}"))?.path();
        if path.extension().and_then(|s| s.to_str()) == Some("ts") {
            let name = path
                .file_name()
                .and_then(|s| s.to_str())
                .ok_or_else(|| anyhow::anyhow!("non-utf8 corpus file name"))?
                .to_string();
            out.push((name, path));
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Run the TrustTS differential over the corpus and return the scorecard.
/// Fail-closed: an unprobeable engine is an error, never a silent skip.
pub fn run_ts_calibrate(opts: &TsCalibrateOpts) -> anyhow::Result<TsScorecard> {
    // Probe engine identities (records nothing but proves both are runnable).
    let _node_id = probe_engine(Engine::Node, &opts.node)?;
    let _bun_id = probe_engine(Engine::Bun, &opts.bun)?;

    let mut files = list_corpus(&opts.corpus)?;
    if let Some(limit) = opts.limit {
        files.truncate(limit);
    }
    if files.is_empty() {
        anyhow::bail!("no .ts corpus files under {}", opts.corpus.display());
    }

    // The Node/Bun oracle imports the REAL `.ts` file as an ES MODULE. Node
    // decides `.ts`'s module format from the nearest package.json `type`, so a
    // work dir carrying `{"type":"module"}` forces the module goal (matching the
    // interp's evaluate_module) for both engines; Bun runs `.ts` natively either
    // way. The committed corpus tree is never mutated: each program is copied
    // into a throwaway work dir alongside that package.json.
    let tmp = tempfile::tempdir().map_err(|e| anyhow::anyhow!("tempdir: {e}"))?;
    let work = tmp.path().join("work");
    std::fs::create_dir_all(&work).map_err(|e| anyhow::anyhow!("mkdir work: {e}"))?;
    std::fs::write(work.join("package.json"), "{\"type\":\"module\"}\n")
        .map_err(|e| anyhow::anyhow!("write package.json: {e}"))?;

    let driver = write_driver(&tmp.path().join("driver"))
        .map_err(|e| anyhow::anyhow!("write driver: {e}"))?;
    // The Node oracle transpiles (not just strips) the non-erasable `.ts` under
    // the transform tier; Bun transpiles natively in both lanes.
    let node_head = if opts.transform {
        NodeHead::new_with_flags(
            opts.node.clone(),
            driver.clone(),
            tmp.path().join("slots/node"),
            vec!["--experimental-transform-types".to_string()],
        )
    } else {
        NodeHead::new(opts.node.clone(), driver.clone(), tmp.path().join("slots/node"))
    }
    .map_err(|e| anyhow::anyhow!("node slot: {e}"))?;
    let bun_head = BunHead::new(opts.bun.clone(), driver.clone(), tmp.path().join("slots/bun"))
        .map_err(|e| anyhow::anyhow!("bun slot: {e}"))?;
    // The TrustTS head lowers in-process; it needs no include cache (the corpus
    // is import-free). Transform tier lowers enum/namespace; else erasure only.
    let trustts_head = if opts.transform {
        TrustTsHead::new_transform(Arc::new(HashMap::new()))
    } else {
        TrustTsHead::new(Arc::new(HashMap::new()))
    };

    let mut audit = HeadAudit::new("trustts");
    let mut card = TsScorecard::default();

    for (name, src_path) in &files {
        card.cases += 1;
        let body = std::fs::read_to_string(src_path)
            .map_err(|e| anyhow::anyhow!("read {}: {e}", src_path.display()))?;
        // The engine oracle runs this pristine `.ts` copy in the module goal.
        let work_copy = work.join(name);
        std::fs::write(&work_copy, &body)
            .map_err(|e| anyhow::anyhow!("write work copy {}: {e}", work_copy.display()))?;

        let case = AssembledCase {
            rel_path: name.clone(),
            source_path: work_copy,
            body,
            includes: vec![],
            mode: RunMode::Module,
            is_async: false,
            timeout: opts.timeout,
        };

        let node_res = node_head.run(&case);
        let bun_res = bun_head.run(&case);
        let trustts_res = trustts_head.run(&case);

        match (&node_res, &bun_res) {
            (HeadResult::Trace(nt), HeadResult::Trace(bt)) => {
                if traces_equal(nt, bt) {
                    card.node_bun_equal += 1;
                } else {
                    card.node_bun_divergent += 1;
                }
                // Audit the TrustTS head against the two engine oracles.
                audit.observe(name, RunMode::Module, &trustts_res, nt, bt);
            }
            _ => {
                // No usable oracle: the TrustTS head is not audited on this case.
                card.engine_errors += 1;
                card.engine_error_notes.push(format!(
                    "{name}: node={} bun={}",
                    describe(&node_res),
                    describe(&bun_res)
                ));
            }
        }
    }

    card.trustts_covered = audit.covered;
    card.trustts_equal = audit.equal;
    card.trustts_divergent = audit.divergent;
    card.trustts_no_coverage = audit.no_coverage;
    card.divergence_notes = audit.divergence_notes.clone();
    card.no_coverage_reasons = audit.no_coverage_reasons.clone();

    if let Some(out) = &opts.out {
        let json = serde_json::json!({
            "cases": card.cases,
            "node_bun_equal": card.node_bun_equal,
            "node_bun_divergent": card.node_bun_divergent,
            "engine_errors": card.engine_errors,
            "trustts_covered": card.trustts_covered,
            "trustts_equal": card.trustts_equal,
            "trustts_divergent": card.trustts_divergent,
            "trustts_no_coverage": card.trustts_no_coverage,
            "divergence_notes": card.divergence_notes,
            "engine_error_notes": card.engine_error_notes,
        });
        if let Some(parent) = out.parent() {
            if !parent.as_os_str().is_empty() {
                std::fs::create_dir_all(parent)
                    .map_err(|e| anyhow::anyhow!("mkdir {}: {e}", parent.display()))?;
            }
        }
        std::fs::write(out, serde_json::to_string_pretty(&json).unwrap_or_default())
            .map_err(|e| anyhow::anyhow!("write scorecard {}: {e}", out.display()))?;
    }

    Ok(card)
}

fn describe(res: &HeadResult) -> String {
    match res {
        HeadResult::Trace(_) => "trace".to_string(),
        HeadResult::NoCoverage(r) => format!("no-coverage({r})"),
        HeadResult::HarnessError(e) => format!("harness-error({e})"),
    }
}

/// Render the scorecard to stdout.
pub fn print_scorecard(card: &TsScorecard) {
    println!("--- TrustTS differential scorecard ---");
    println!("corpus cases:            {}", card.cases);
    println!(
        "node-vs-bun equal:       {} / {} judged (divergent {})",
        card.node_bun_equal,
        card.node_bun_equal + card.node_bun_divergent,
        card.node_bun_divergent
    );
    println!("engine-unjudged cases:   {}", card.engine_errors);
    println!(
        "trustts covered:         {} (equal {}, DIVERGENT {})",
        card.trustts_covered, card.trustts_equal, card.trustts_divergent
    );
    println!("trustts no-coverage:     {}", card.trustts_no_coverage);
    if !card.no_coverage_reasons.is_empty() {
        println!("  no-coverage reasons:");
        for (reason, n) in &card.no_coverage_reasons {
            println!("    {n:>3}  {reason}");
        }
    }
    if !card.engine_error_notes.is_empty() {
        println!("  engine-unjudged notes:");
        for note in &card.engine_error_notes {
            println!("    {note}");
        }
    }
    if !card.divergence_notes.is_empty() {
        println!("  DIVERGENCES (zero-wrong-traces violation):");
        for note in &card.divergence_notes {
            println!("    {note}");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn corpus_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/ts-corpus")
    }

    /// Recompute the committed S-ts manifest digests from the on-disk corpus:
    /// sorted `.ts` file names, `list_sha256` over the sorted "path\n"
    /// concatenation, `content_sha256` over the sorted-path concatenation of
    /// file bytes.
    fn compute_digests(dir: &Path) -> (usize, String, String) {
        use sha2::{Digest, Sha256};
        let mut names: Vec<String> = std::fs::read_dir(dir)
            .expect("read corpus dir")
            .filter_map(|e| e.ok())
            .map(|e| e.path())
            .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("ts"))
            .map(|p| p.file_name().unwrap().to_str().unwrap().to_string())
            .collect();
        names.sort();
        let mut list_h = Sha256::new();
        let mut content_h = Sha256::new();
        for n in &names {
            list_h.update(n.as_bytes());
            list_h.update(b"\n");
            content_h.update(std::fs::read(dir.join(n)).expect("read corpus file"));
        }
        let hex = |d: &[u8]| d.iter().map(|b| format!("{b:02x}")).collect::<String>();
        (names.len(), hex(&list_h.finalize()), hex(&content_h.finalize()))
    }

    /// The committed S-ts.toml manifest must match the corpus on disk (drift
    /// detection; engine-free, so it always runs).
    #[test]
    fn s_ts_manifest_matches_corpus() {
        let (count, list_sha, content_sha) = compute_digests(&corpus_dir());
        let manifest_path =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/js262/S-ts.toml");
        let text = std::fs::read_to_string(&manifest_path).expect("read S-ts.toml");
        let doc: toml::Value = toml::from_str(&text).expect("parse S-ts.toml");
        let m = doc.get("manifest").expect("[manifest] table");
        assert_eq!(
            m.get("count").and_then(|v| v.as_integer()),
            Some(count as i64),
            "S-ts.toml count drift"
        );
        assert_eq!(
            m.get("list_sha256").and_then(|v| v.as_str()),
            Some(list_sha.as_str()),
            "S-ts.toml list_sha256 drift"
        );
        assert_eq!(
            m.get("content_sha256").and_then(|v| v.as_str()),
            Some(content_sha.as_str()),
            "S-ts.toml content_sha256 drift"
        );
    }

    /// The pair of pinned engines, or None when either is unresolvable or
    /// off-pin on this box — the gate then skips rather than measuring against
    /// an engine no ledger describes.
    fn pinned_engines() -> Option<(PathBuf, PathBuf)> {
        let node = crate::util::resolve_engine(Engine::Node, None).ok()?;
        let bun = crate::util::resolve_engine(Engine::Bun, None).ok()?;
        probe_engine(Engine::Node, &node).ok()?;
        probe_engine(Engine::Bun, &bun).ok()?;
        Some((node, bun))
    }

    /// The acceptance gate: the TrustTS front-end covers a meaningful share of
    /// the erasable-TS corpus with ZERO wrong traces. Skips (green) when the
    /// pinned engines are absent — this box has them, and the gate is real.
    #[test]
    fn ts_differential_zero_wrong_traces() {
        let Some((node, bun)) = pinned_engines() else {
            eprintln!("ts_differential: pinned engines not present, skipping");
            return;
        };
        let opts = TsCalibrateOpts {
            corpus: corpus_dir(),
            node,
            bun,
            timeout: Duration::from_secs(30),
            limit: None,
            out: None,
            transform: false,
        };
        let card = run_ts_calibrate(&opts).expect("ts-calibrate run");
        print_scorecard(&card);

        // THE BAR: zero wrong traces.
        assert_eq!(
            card.trustts_divergent, 0,
            "TrustTS produced {} divergent trace(s): {:?}",
            card.trustts_divergent, card.divergence_notes
        );
        // Meaningful coverage: the head must actually cover a real share, not
        // vacuously refuse everything.
        assert!(
            card.trustts_covered >= 10,
            "TrustTS covered only {} cases (expected a meaningful share of {})",
            card.trustts_covered,
            card.cases
        );
    }

    fn transform_corpus_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/ts-transform-corpus")
    }

    /// The transform-tier acceptance gate: the non-erasable TS front-end
    /// (enum/namespace lowering + erasure → interp) covers a meaningful share of
    /// the non-erasable corpus with ZERO wrong traces, judged against Node
    /// (`--experimental-transform-types`) and Bun (both transpile, and must
    /// agree). Skips (green) when the pinned engines are absent.
    #[test]
    fn ts_transform_differential_zero_wrong_traces() {
        let Some((node, bun)) = pinned_engines() else {
            eprintln!("ts_transform_differential: pinned engines not present, skipping");
            return;
        };
        let opts = TsCalibrateOpts {
            corpus: transform_corpus_dir(),
            node,
            bun,
            timeout: Duration::from_secs(30),
            limit: None,
            out: None,
            transform: true,
        };
        let card = run_ts_calibrate(&opts).expect("ts-transform-calibrate run");
        print_scorecard(&card);

        // THE BAR: zero wrong traces. (A covered trace equals Node OR Bun; the
        // 30 lowerable programs all have Node==Bun oracles. The corpus's refuse
        // fixtures — decorators, parameter properties — legitimately diverge
        // Node-vs-Bun, but the transform tier refuses them: NoCoverage, never a
        // wrong trace. So the ONLY invariant that matters is `trustts_divergent`.)
        assert_eq!(
            card.trustts_divergent, 0,
            "transform tier produced {} divergent trace(s): {:?}",
            card.trustts_divergent, card.divergence_notes
        );
        // Meaningful coverage of the non-erasable corpus.
        assert!(
            card.trustts_covered >= 15,
            "transform tier covered only {} cases (expected a meaningful share of {})",
            card.trustts_covered,
            card.cases
        );
    }
}
