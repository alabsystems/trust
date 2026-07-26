// Line-granular ddmin of a divergent (case, mode) — honest naming: LINE
// granularity, not AST-granular yet. A candidate body is kept iff both
// engines still run (no HarnessError) and the traces are still UNEQUAL with
// the same divergence kind (the explain string's prefix up to the first ':'
// is the invariant). Capped at 200 engine-pair invocations.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use trust_js_trace::{explain_divergence, traces_equal};

use crate::cases::prepare_case;
use crate::heads::{write_driver, AssembledCase, BunHead, EngineHead, HeadResult, NodeHead, RunMode};

pub struct MinimizeOpts {
    pub corpus: PathBuf,
    pub test: String,
    pub node: PathBuf,
    pub bun: PathBuf,
    pub mode: Option<RunMode>,
    pub timeout: Duration,
}

pub const PAIR_BUDGET: usize = 200;

/// The divergence-kind invariant: the explain string up to the first ':'.
pub fn explain_kind(explain: &str) -> &str {
    explain.split(':').next().unwrap_or(explain)
}

/// Classic ddmin over items. `interesting` must be true for the full input;
/// the returned subset is 1-minimal modulo the invocation budget enforced
/// inside the predicate (a budget-exhausted predicate returns false, which
/// soundly stops refinement and keeps the best-so-far).
pub fn ddmin<T: Clone, F: FnMut(&[T]) -> bool>(items: Vec<T>, mut interesting: F) -> Vec<T> {
    let mut current = items;
    let mut n = 2usize;
    while current.len() >= 2 {
        let chunk_len = current.len().div_ceil(n);
        let mut reduced = false;
        let mut start = 0;
        while start < current.len() {
            let end = (start + chunk_len).min(current.len());
            let mut candidate = Vec::with_capacity(current.len() - (end - start));
            candidate.extend_from_slice(&current[..start]);
            candidate.extend_from_slice(&current[end..]);
            if !candidate.is_empty() && interesting(&candidate) {
                current = candidate;
                n = n.saturating_sub(1).max(2);
                reduced = true;
                break;
            }
            start = end;
        }
        if !reduced {
            if n >= current.len() {
                break;
            }
            n = (n * 2).min(current.len());
        }
    }
    current
}

pub fn run_minimize(opts: &MinimizeOpts) -> anyhow::Result<i32> {
    let prepared = prepare_case(&opts.corpus, &opts.test)
        .map_err(|e| anyhow::anyhow!("cannot prepare case: {e}"))?;

    let dir = tempfile::tempdir()?;
    let driver = write_driver(dir.path())?;
    let node = NodeHead::new(opts.node.clone(), driver.clone(), dir.path().join("node"))?;
    let bun = BunHead::new(opts.bun.clone(), driver, dir.path().join("bun"))?;
    // The candidate body evolves; for the RAW lane the head spawns
    // source_path directly, so candidates are staged through a slot file.
    let raw_slot = dir.path().join("raw-candidate.js");

    let invocations = std::cell::Cell::new(0usize);
    let run_pair = |body: &str, mode: RunMode| -> anyhow::Result<Option<String>> {
        invocations.set(invocations.get() + 1);
        let source_path = if mode == RunMode::Raw {
            std::fs::write(&raw_slot, body)?;
            raw_slot.clone()
        } else {
            prepared.abs_path.clone()
        };
        let case = AssembledCase {
            rel_path: prepared.rel_path.clone(),
            source_path,
            body: body.to_string(),
            includes: if mode == RunMode::Raw { vec![] } else { prepared.includes.clone() },
            mode,
            is_async: prepared.frontmatter.flags.iter().any(|f| f == "async"),
            timeout: opts.timeout,
        };
        let (n, b) = (node.run(&case), bun.run(&case));
        match (n, b) {
            (HeadResult::Trace(a), HeadResult::Trace(b)) if !traces_equal(&a, &b) => {
                Ok(explain_divergence(&a, &b))
            }
            _ => Ok(None),
        }
    };

    // Pick the mode: explicit, else the first mandated mode that diverges.
    let mut chosen: Option<(RunMode, String)> = None;
    let probe_modes: Vec<RunMode> = match opts.mode {
        Some(m) => vec![m],
        None => prepared.modes.clone(),
    };
    for mode in probe_modes {
        if let Some(explain) = run_pair(&prepared.body, mode)? {
            chosen = Some((mode, explain));
            break;
        }
    }
    let Some((mode, baseline_explain)) = chosen else {
        eprintln!(
            "minimize: {} does not diverge under its mandated mode(s) — nothing to minimize",
            opts.test
        );
        return Ok(1);
    };
    let invariant = explain_kind(&baseline_explain).to_string();
    println!("minimize: {} [{}] diverges: {baseline_explain}", opts.test, mode.as_str());
    println!("minimize: invariant divergence kind: {invariant:?}");

    let lines: Vec<String> = prepared.body.lines().map(|l| l.to_string()).collect();
    let original_len = lines.len();
    let mut budget_exhausted = false;
    let minimized = ddmin(lines, |candidate| {
        if invocations.get() >= PAIR_BUDGET {
            budget_exhausted = true;
            return false;
        }
        let body = candidate.join("\n");
        match run_pair(&body, mode) {
            Ok(Some(explain)) => explain_kind(&explain) == invariant,
            _ => false,
        }
    });

    println!(
        "minimize: {original_len} -> {} lines in {} engine-pair invocations{}",
        minimized.len(),
        invocations.get(),
        if budget_exhausted { " (budget of 200 exhausted; best-so-far)" } else { "" }
    );
    println!("---- minimized body ----");
    println!("{}", minimized.join("\n"));
    Ok(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kind_prefix() {
        assert_eq!(explain_kind("completion: normal vs throw"), "completion");
        assert_eq!(explain_kind("event[3]: stdout vs host"), "event[3]");
        assert_eq!(explain_kind("no colon"), "no colon");
    }

    #[test]
    fn ddmin_finds_minimal_pair() {
        // Interesting iff both "A" and "B" survive.
        let items: Vec<String> =
            ["x", "A", "y", "z", "B", "w", "v", "u"].iter().map(|s| s.to_string()).collect();
        let out = ddmin(items, |c| {
            c.iter().any(|s| s == "A") && c.iter().any(|s| s == "B")
        });
        assert_eq!(out, ["A", "B"]);
    }

    #[test]
    fn ddmin_single_culprit() {
        let items: Vec<u32> = (0..37).collect();
        let mut calls = 0;
        let out = ddmin(items, |c| {
            calls += 1;
            c.contains(&23)
        });
        assert_eq!(out, [23]);
        assert!(calls < 200, "ddmin used {calls} probes");
    }

    #[test]
    fn ddmin_keeps_full_set_when_all_needed() {
        let items: Vec<u32> = (0..5).collect();
        let out = ddmin(items.clone(), |c| c.len() == 5);
        assert_eq!(out, items);
    }

    #[test]
    fn ddmin_respects_predicate_shutoff() {
        // A predicate that goes dead (budget model) keeps best-so-far.
        let items: Vec<u32> = (0..16).collect();
        let mut budget = 3;
        let out = ddmin(items, |c| {
            if budget == 0 {
                return false;
            }
            budget -= 1;
            c.contains(&7)
        });
        assert!(out.contains(&7));
    }
}
