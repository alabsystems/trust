// The M1 D4 coverage-ratchet check: per auxiliary head (sem / trustjs) the
// covered-case count may only grow and wrong traces stay at zero, judged
// against the append-only tests/js262/coverage.toml ledger (the LAST entry
// per head is the ratchet floor). `--check` (default) fails closed on a
// ratchet regression, any divergence, or equal != covered; `--propose`
// prints the TOML entry block(s) for the scorecard and NEVER writes the
// ledger — its content is the coordinator's.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::model::{CoverageEntry, CoverageHead, CoverageLedger, Scorecard, ScorecardTotals};
use crate::util::validation_date;

pub struct RatchetOpts {
    pub scorecard: PathBuf,
    pub ledger: PathBuf,
    /// `--propose` prints entry blocks instead of checking.
    pub propose: bool,
    /// `--allow-soundness-decrease`: a covered count BELOW the floor is a
    /// documented soundness improvement (previously-fabricated coverage
    /// converted to a sound refusal), not a regression — so it is downgraded
    /// from a hard finding to a warning. The correctness invariants
    /// (divergent == 0, equal == covered) are NEVER waived: a decrease is
    /// only acceptable because the covered set that remains is still exact.
    pub allow_soundness_decrease: bool,
}

/// The per-head counters a scorecard claims.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct HeadCounts {
    cases: u64,
    covered: u64,
    equal: u64,
    divergent: u64,
    no_coverage: u64,
}

fn head_counts(t: &ScorecardTotals, head: CoverageHead) -> HeadCounts {
    match head {
        CoverageHead::Sem => HeadCounts {
            cases: t.sem_cases,
            covered: t.sem_covered,
            equal: t.sem_equal,
            divergent: t.sem_divergent,
            no_coverage: t.sem_no_coverage,
        },
        CoverageHead::Trustjs => HeadCounts {
            cases: t.trustjs_cases,
            covered: t.trustjs_covered,
            equal: t.trustjs_equal,
            divergent: t.trustjs_divergent,
            no_coverage: t.trustjs_no_coverage,
        },
    }
}

/// The `--check` verdict: findings against the ratchet contract. Empty =
/// pass. `ledger` is `None` when the ledger file does not exist yet (first
/// landing): the ratchet-floor comparison passes vacuously, but the
/// scorecard-internal conditions (divergent == 0, equal == covered) still
/// hold fail-closed.
pub fn check_findings(totals: &ScorecardTotals, ledger: Option<&CoverageLedger>) -> Vec<String> {
    check_findings_opts(totals, ledger, false)
}

/// `allow_soundness_decrease`: when true, a covered count below the floor is
/// a warning (printed) rather than a hard finding — for a documented
/// soundness fix that converts fabricated coverage into a sound refusal. The
/// divergent == 0 and equal == covered invariants are enforced regardless.
pub fn check_findings_opts(
    totals: &ScorecardTotals,
    ledger: Option<&CoverageLedger>,
    allow_soundness_decrease: bool,
) -> Vec<String> {
    let mut findings = Vec::new();
    for head in [CoverageHead::Sem, CoverageHead::Trustjs] {
        let c = head_counts(totals, head);
        let name = head.as_str();
        if c.divergent != 0 {
            findings.push(format!(
                "head {name}: divergent = {} != 0 (zero-wrong-traces discipline)",
                c.divergent
            ));
        }
        if c.equal != c.covered {
            findings.push(format!(
                "head {name}: equal {} != covered {} (every covered trace must match an engine)",
                c.equal, c.covered
            ));
        }
        if let Some(ledger) = ledger {
            // The LAST entry per head is the ratchet floor.
            if let Some(last) = ledger.entries.iter().filter(|e| e.head == head).next_back() {
                if c.covered < last.covered {
                    if allow_soundness_decrease {
                        eprintln!(
                            "ratchet: head {name}: covered {} < floor {} (entry {}) — ALLOWED as a documented soundness decrease (divergent == 0, equal == covered hold)",
                            c.covered, last.covered, last.id
                        );
                    } else {
                        findings.push(format!(
                            "head {name}: ratchet regression — scorecard covered {} < ledger covered {} (entry {}, {})",
                            c.covered, last.covered, last.id, last.date
                        ));
                    }
                }
            }
        }
    }
    findings
}

/// The `--propose` entries: one per auxiliary head the scorecard actually
/// ran (cases > 0). Never written to disk here — printed for the
/// coordinator to append.
pub fn propose_entries(
    totals: &ScorecardTotals,
    scorecard_ref: &str,
    date: &str,
) -> Vec<CoverageEntry> {
    let mut out = Vec::new();
    for head in [CoverageHead::Sem, CoverageHead::Trustjs] {
        let c = head_counts(totals, head);
        if c.cases == 0 {
            continue;
        }
        out.push(CoverageEntry {
            id: format!("cov-{}-{date}", head.as_str()),
            date: date.to_string(),
            scorecard: scorecard_ref.to_string(),
            head,
            cases: c.cases,
            covered: c.covered,
            equal: c.equal,
            divergent: c.divergent,
            no_coverage: c.no_coverage,
        });
    }
    out
}

/// Render proposal entries as appendable `[[entries]]` TOML blocks.
pub fn render_proposal(entries: &[CoverageEntry]) -> Result<String, String> {
    #[derive(Serialize)]
    struct Proposal<'a> {
        entries: &'a [CoverageEntry],
    }
    toml::to_string(&Proposal { entries }).map_err(|e| format!("serialize proposal: {e}"))
}

fn load_ledger(path: &Path) -> anyhow::Result<Option<CoverageLedger>> {
    if !path.exists() {
        return Ok(None);
    }
    let text = std::fs::read_to_string(path)
        .map_err(|e| anyhow::anyhow!("read {}: {e}", path.display()))?;
    let ledger: CoverageLedger = toml::from_str(&text)
        .map_err(|e| anyhow::anyhow!("parse {}: {e}", path.display()))?;
    Ok(Some(ledger))
}

pub fn run_ratchet(opts: &RatchetOpts) -> anyhow::Result<i32> {
    let text = std::fs::read_to_string(&opts.scorecard)
        .map_err(|e| anyhow::anyhow!("read {}: {e}", opts.scorecard.display()))?;
    let scorecard: Scorecard = serde_json::from_str(&text)
        .map_err(|e| anyhow::anyhow!("parse {}: {e}", opts.scorecard.display()))?;
    let totals = &scorecard.totals;

    if opts.propose {
        let entries =
            propose_entries(totals, &opts.scorecard.display().to_string(), &validation_date());
        if entries.is_empty() {
            eprintln!(
                "ratchet: nothing to propose — {} has no sem or trustjs runs",
                opts.scorecard.display()
            );
            return Ok(1);
        }
        // Print only: the ledger content is the coordinator's to append.
        print!("{}", render_proposal(&entries).map_err(|e| anyhow::anyhow!("{e}"))?);
        return Ok(0);
    }

    let ledger = load_ledger(&opts.ledger)?;
    if ledger.is_none() {
        println!(
            "ratchet: ledger {} does not exist — first landing, floor check passes vacuously",
            opts.ledger.display()
        );
    }
    let findings = check_findings_opts(totals, ledger.as_ref(), opts.allow_soundness_decrease);
    if findings.is_empty() {
        for head in [CoverageHead::Sem, CoverageHead::Trustjs] {
            let c = head_counts(totals, head);
            println!(
                "ratchet: head {}: cases={} covered={} equal={} divergent={} no_coverage={} — OK",
                head.as_str(),
                c.cases,
                c.covered,
                c.equal,
                c.divergent,
                c.no_coverage
            );
        }
        println!("ratchet: OK");
        Ok(0)
    } else {
        for f in &findings {
            eprintln!("ratchet finding: {f}");
        }
        Ok(1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;

    fn totals(head: CoverageHead, counts: (u64, u64, u64, u64, u64)) -> ScorecardTotals {
        let (cases, covered, equal, divergent, no_coverage) = counts;
        let mut t = ScorecardTotals::default();
        match head {
            CoverageHead::Sem => {
                t.sem_cases = cases;
                t.sem_covered = covered;
                t.sem_equal = equal;
                t.sem_divergent = divergent;
                t.sem_no_coverage = no_coverage;
            }
            CoverageHead::Trustjs => {
                t.trustjs_cases = cases;
                t.trustjs_covered = covered;
                t.trustjs_equal = equal;
                t.trustjs_divergent = divergent;
                t.trustjs_no_coverage = no_coverage;
            }
        }
        t
    }

    fn ledger(entries: Vec<CoverageEntry>) -> CoverageLedger {
        CoverageLedger { schema_version: "1".to_string(), entries }
    }

    fn entry(id: &str, head: CoverageHead, covered: u64) -> CoverageEntry {
        CoverageEntry {
            id: id.to_string(),
            date: "2026-07-21".to_string(),
            scorecard: "run-1".to_string(),
            head,
            cases: covered + 10,
            covered,
            equal: covered,
            divergent: 0,
            no_coverage: 10,
        }
    }

    #[test]
    fn ratchet_regression_detected() {
        let t = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        let l = ledger(vec![entry("cov-1", CoverageHead::Trustjs, 50)]);
        let findings = check_findings(&t, Some(&l));
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert!(findings[0].contains("ratchet regression"), "{}", findings[0]);
        assert!(findings[0].contains("40 < ledger covered 50"), "{}", findings[0]);
        // Meeting the floor passes; exceeding it passes.
        let ok = totals(CoverageHead::Trustjs, (100, 50, 50, 0, 50));
        assert!(check_findings(&ok, Some(&l)).is_empty());
        let up = totals(CoverageHead::Trustjs, (100, 60, 60, 0, 40));
        assert!(check_findings(&up, Some(&l)).is_empty());
    }

    #[test]
    fn last_entry_per_head_is_the_floor() {
        let l = ledger(vec![
            entry("cov-1", CoverageHead::Trustjs, 30),
            entry("cov-sem-1", CoverageHead::Sem, 90),
            entry("cov-2", CoverageHead::Trustjs, 45),
        ]);
        // 40 beats the FIRST trustjs entry (30) but not the LAST (45).
        let t = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        let findings = check_findings(&t, Some(&l));
        assert_eq!(findings.len(), 2, "{findings:?}");
        assert!(findings.iter().any(|f| f.contains("head trustjs") && f.contains("40 < ledger covered 45")));
        // The sem head is checked independently: a scorecard that never ran
        // sem (covered 0) regresses against its floor — fail-closed.
        assert!(findings.iter().any(|f| f.contains("head sem") && f.contains("0 < ledger covered 90")));
    }

    #[test]
    fn first_landing_is_vacuous() {
        // No ledger at all: the floor check passes vacuously.
        let t = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        assert!(check_findings(&t, None).is_empty());
        // A ledger with no entry for the head is also a first landing.
        let l = ledger(vec![entry("cov-sem-1", CoverageHead::Sem, 5)]);
        let mut t2 = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        t2.sem_cases = 20;
        t2.sem_covered = 5;
        t2.sem_equal = 5;
        t2.sem_no_coverage = 15;
        assert!(check_findings(&t2, Some(&l)).is_empty());
    }

    #[test]
    fn divergent_and_equal_mismatch_fail_even_without_a_ledger() {
        let t = totals(CoverageHead::Trustjs, (100, 40, 40, 1, 59));
        let findings = check_findings(&t, None);
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert!(findings[0].contains("divergent = 1 != 0"));

        let t = totals(CoverageHead::Sem, (100, 40, 39, 0, 60));
        let findings = check_findings(&t, None);
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert!(findings[0].contains("equal 39 != covered 40"));
    }

    #[test]
    fn propose_output_shape() {
        let mut t = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        t.sem_cases = 100;
        t.sem_covered = 90;
        t.sem_equal = 90;
        t.sem_no_coverage = 10;
        let entries = propose_entries(&t, "build/js262/calibration/scorecard.json", "2026-07-21");
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].head, CoverageHead::Sem);
        assert_eq!(entries[0].id, "cov-sem-2026-07-21");
        assert_eq!(entries[1].head, CoverageHead::Trustjs);
        assert_eq!(entries[1].id, "cov-trustjs-2026-07-21");
        assert_eq!(entries[1].covered, 40);
        assert_eq!(entries[1].no_coverage, 60);
        assert_eq!(entries[1].scorecard, "build/js262/calibration/scorecard.json");

        let text = render_proposal(&entries).expect("render");
        assert!(text.contains("[[entries]]"));
        assert!(text.contains("head = \"trustjs\""));
        assert!(text.contains("head = \"sem\""));
        // The block parses back as entries...
        #[derive(Deserialize)]
        struct JustEntries {
            entries: Vec<CoverageEntry>,
        }
        let back: JustEntries = toml::from_str(&text).expect("proposal parses");
        assert_eq!(back.entries, entries);
        // ...and appending it under the ledger header yields a valid ledger.
        let full = format!("schema_version = \"1\"\n\n{text}");
        let l: CoverageLedger = toml::from_str(&full).expect("appended ledger parses");
        assert_eq!(l.entries, entries);

        // A head that never ran (cases == 0) is never proposed.
        let only_trustjs = totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60));
        let entries = propose_entries(&only_trustjs, "run-2", "2026-07-21");
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].head, CoverageHead::Trustjs);
        // A scorecard with neither head proposes nothing.
        assert!(propose_entries(&ScorecardTotals::default(), "run-3", "2026-07-21").is_empty());
    }

    #[test]
    fn run_ratchet_end_to_end_check_and_propose() {
        let dir = tempfile::tempdir().expect("tempdir");
        // A minimal-but-valid scorecard file.
        let scorecard = crate::model::Scorecard {
            schema: crate::model::SCORECARD_SCHEMA.to_string(),
            generated_at: "2026-07-21T00:00:00Z".to_string(),
            partial: None,
            corpus: crate::model::ScorecardCorpus {
                revision: "cafe".into(),
                slice_sha256: "00".into(),
            },
            engines: crate::model::ScorecardEngines {
                node: crate::model::ScorecardEngine {
                    path: "n".into(),
                    version: "v".into(),
                    sha256: "0".into(),
                },
                bun: crate::model::ScorecardEngine {
                    path: "b".into(),
                    version: "v".into(),
                    sha256: "0".into(),
                },
            },
            driver_sha256: "d".into(),
            totals: totals(CoverageHead::Trustjs, (100, 40, 40, 0, 60)),
            gate: crate::model::ScorecardGate {
                trace_equal_ratio: 1.0,
                ratio_ok: true,
                unclassified_ok: true,
                sem_audit_ok: true,
                trustjs_audit_ok: true,
                ledger_ok: true,
                pass: true,
                reason: None,
            },
        };
        let sc_path = dir.path().join("scorecard.json");
        std::fs::write(&sc_path, serde_json::to_string_pretty(&scorecard).unwrap()).unwrap();

        // First landing: no ledger file — check passes vacuously.
        let missing_ledger = dir.path().join("coverage.toml");
        let opts = RatchetOpts {
            scorecard: sc_path.clone(),
            ledger: missing_ledger.clone(),
            propose: false,
            allow_soundness_decrease: false,
        };
        assert_eq!(run_ratchet(&opts).expect("check"), 0);

        // Propose still prints (exit 0) with the ledger missing.
        let opts = RatchetOpts { scorecard: sc_path.clone(), ledger: missing_ledger, propose: true, allow_soundness_decrease: false };
        assert_eq!(run_ratchet(&opts).expect("propose"), 0);

        // With a higher floor on record the check fails (exit 1).
        let ledger_path = dir.path().join("coverage2.toml");
        std::fs::write(
            &ledger_path,
            toml::to_string(&ledger(vec![entry("cov-1", CoverageHead::Trustjs, 50)])).unwrap(),
        )
        .unwrap();
        let opts =
            RatchetOpts { scorecard: sc_path.clone(), ledger: ledger_path.clone(), propose: false, allow_soundness_decrease: false };
        assert_eq!(run_ratchet(&opts).expect("check"), 1);

        // A corrupt ledger is a hard error, never a silent pass.
        std::fs::write(&ledger_path, "schema_version = \"1\"\nnot toml [").unwrap();
        let opts = RatchetOpts { scorecard: sc_path, ledger: ledger_path, propose: false, allow_soundness_decrease: false };
        assert!(run_ratchet(&opts).is_err());
    }
}
