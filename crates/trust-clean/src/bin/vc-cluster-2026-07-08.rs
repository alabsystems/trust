// vc-cluster-2026-07-08: per-VC-kind diagnostic harness for the M6 rung-2
// SAFETY_GAP cluster diagnosis (reports/m6-rung1-cleankernel-census-2026-07-08.md
// §3.3/§3.4's 44/60 undischarged-safety-VC functions).
//
// SCRATCH TOOL — census-only, additive (new file, does not touch prove.rs /
// mirsem.rs / vc_refute.rs / any pipeline source). Uses ONLY the public API
// mirrored EXACTLY from `trust_clean::prove::prove_one_function`'s own safety-VC
// loop (`trust_vcgen::generate_vcs`, `augment_with_type_bounds_pub`,
// `vc_refute::check_refute_vc_with`, `vc_refute::StructParams::from_function`) —
// this is NOT a reimplementation of discharge, it is the exact same call
// sequence the production `prove_dump_dir` driver makes, just with per-VC
// reporting instead of aggregate counting.
//
// Usage: vc-cluster-2026-07-08 <dump_dir> [<dump_dir2> ...]
// Output: one line per UNDISCHARGED safety VC to stdout:
//   def_path\tvc_kind_tag\tdescription\tsource_path
// plus a cluster summary (count per vc_kind_tag) to stderr at the end.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use trust_clean::prove::augment_with_type_bounds_pub;
use trust_clean::{RefuteOutcome, StructParams, check_refute_vc_with};
use trust_types::{Formula, VcKind, VerifiableFunction};

/// Per-VC wall-clock budget (seconds). A single pathological VC (case-split
/// search) can hang indefinitely (documented precedent: `rustc_version`'s
/// `version_meta_for`, prove.rs's `prove_dump_dir_with_budget` docs) — this
/// diagnostic must never hang on one VC. Fail-closed: a timeout is reported as
/// DECLINED, never counted discharged.
fn vc_budget_secs() -> u64 {
    std::env::var("VC_CLUSTER_BUDGET_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(10)
}

/// Run `check_refute_vc_with` on a worker thread with a wall-clock budget.
/// `None` return means DECLINED (timed out) — distinct from `Some(None)`
/// (ran to completion, undischarged).
fn check_refute_budgeted(
    formula: &Formula,
    params: &StructParams,
    budget: Duration,
) -> Option<Option<RefuteOutcome>> {
    let (tx, rx) = std::sync::mpsc::channel();
    let formula = formula.clone();
    let params = params.clone();
    std::thread::spawn(move || {
        let outcome = check_refute_vc_with(&formula, &params);
        let _ = tx.send(outcome);
    });
    match rx.recv_timeout(budget) {
        Ok(outcome) => Some(outcome),
        Err(_) => None, // timed out — worker thread is leaked (short-lived scratch process)
    }
}

fn vc_tag(kind: &VcKind) -> String {
    // Coarse tag: enum variant name only (strip fields), for clustering.
    let full = format!("{kind:?}");
    match full.find(|c| c == '{' || c == '(') {
        Some(idx) => full[..idx].trim().to_string(),
        None => full,
    }
}

fn read_all_functions(dir: &Path) -> std::io::Result<Vec<(VerifiableFunction, PathBuf)>> {
    let mut out = Vec::new();
    let mut entries: Vec<_> =
        std::fs::read_dir(dir)?.filter_map(Result::ok).map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let bytes = std::fs::read(&path)?;
        if let Ok(func) =
            trust_clean::prove::decode_verifiable_function_with_authenticated_legacy_metadata(
                &bytes,
            )
        {
            out.push((func, path));
        }
    }
    Ok(out)
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: vc-cluster-2026-07-08 <dump_dir> [<dump_dir2> ...]");
        std::process::exit(2);
    }
    // Optional debug mode: `vc-cluster-2026-07-08 <dump_dir> --formula-filter <substr>`
    // prints the FULL augmented formula (Debug) for every safety VC of any
    // function whose def_path contains <substr>, then exits — for drilling into
    // exactly what hypotheses reach `vc_refute` for a specific target.
    let mut formula_filter: Option<String> = None;
    let mut dirs: Vec<&str> = Vec::new();
    {
        let mut it = args[1..].iter();
        while let Some(a) = it.next() {
            if a == "--formula-filter" {
                formula_filter = it.next().cloned();
            } else {
                dirs.push(a.as_str());
            }
        }
    }

    let budget = Duration::from_secs(vc_budget_secs());
    if let Some(filter) = &formula_filter {
        for dir in &dirs {
            let funcs = read_all_functions(Path::new(dir))?;
            for (func, path) in funcs {
                if !func.def_path.contains(filter.as_str()) {
                    continue;
                }
                eprintln!("=== {} ({}) ===", func.def_path, path.display());
                let carriers = trust_clean::clean_ground::reachable_adt_carriers(&func);
                let mut adt_env = clean_kernel::Environment::with_prelude();
                let registry =
                    trust_clean::clean_ground::register_adt_carriers(&mut adt_env, &carriers);
                let struct_params = StructParams::from_function(&func, &registry);
                for (i, vc) in trust_vcgen::generate_vcs(&func).into_iter().enumerate() {
                    if matches!(vc.kind, VcKind::Postcondition) {
                        continue;
                    }
                    let augmented = augment_with_type_bounds_pub(&vc.formula, &func);
                    eprintln!("--- VC[{i}] kind={:?} ---", vc.kind);
                    eprintln!("RAW:       {:?}", vc.formula);
                    eprintln!("AUGMENTED: {augmented:?}");
                    match check_refute_budgeted(&augmented, &struct_params, budget) {
                        None => eprintln!("OUTCOME: DECLINED (budget {budget:?})"),
                        Some(outcome) => eprintln!("OUTCOME: {outcome:?}"),
                    }
                }
            }
        }
        return Ok(());
    }
    let mut cluster_undischarged: BTreeMap<String, usize> = BTreeMap::new();
    let mut cluster_discharged: BTreeMap<String, usize> = BTreeMap::new();
    let mut cluster_declined: BTreeMap<String, usize> = BTreeMap::new();
    let mut fn_undischarged: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut total_funcs = 0usize;
    let mut seen_def_paths: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();

    for dir in dirs {
        let funcs = match read_all_functions(Path::new(dir)) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("skip {dir}: {e}");
                continue;
            }
        };
        for (func, path) in funcs {
            if !seen_def_paths.insert(func.def_path.clone()) {
                continue; // avoid double-counting the same def_path across dirs
            }
            total_funcs += 1;
            eprintln!("[{total_funcs}] {} ({})", func.def_path, path.display());
            let carriers = trust_clean::clean_ground::reachable_adt_carriers(&func);
            let mut adt_env = clean_kernel::Environment::with_prelude();
            let registry =
                trust_clean::clean_ground::register_adt_carriers(&mut adt_env, &carriers);
            let struct_params = StructParams::from_function(&func, &registry);
            for vc in trust_vcgen::generate_vcs(&func) {
                if matches!(vc.kind, VcKind::Postcondition) {
                    continue; // only safety obligations, matching prove_one_function's split
                }
                let augmented = augment_with_type_bounds_pub(&vc.formula, &func);
                let tag = vc_tag(&vc.kind);
                match check_refute_budgeted(&augmented, &struct_params, budget) {
                    None => {
                        *cluster_declined.entry(tag.clone()).or_default() += 1;
                        eprintln!("  DECLINED (budget {budget:?}) kind={tag}");
                    }
                    Some(outcome) => {
                        let discharged = matches!(outcome, Some(RefuteOutcome::RefutedModulo3));
                        if discharged {
                            *cluster_discharged.entry(tag).or_default() += 1;
                        } else {
                            *cluster_undischarged.entry(tag.clone()).or_default() += 1;
                            println!("{}\t{}\t{}\t{}", func.def_path, tag, vc.kind, path.display());
                            fn_undischarged.entry(func.def_path.clone()).or_default().push(tag);
                        }
                    }
                }
            }
        }
    }

    eprintln!("\n=== VC cluster summary ({total_funcs} functions scanned) ===");
    eprintln!(
        "{:<40} {:>12} {:>12} {:>10}",
        "vc_kind_tag", "discharged", "undischarged", "declined"
    );
    let all_tags_sorted: Vec<&String> = {
        let set: std::collections::BTreeSet<&String> = cluster_discharged
            .keys()
            .chain(cluster_undischarged.keys())
            .chain(cluster_declined.keys())
            .collect();
        let mut v: Vec<&String> = set.into_iter().collect();
        v.sort_by_key(|t| std::cmp::Reverse(*cluster_undischarged.get(*t).unwrap_or(&0)));
        v
    };
    for tag in all_tags_sorted {
        eprintln!(
            "{:<40} {:>12} {:>12} {:>10}",
            tag,
            cluster_discharged.get(tag).unwrap_or(&0),
            cluster_undischarged.get(tag).unwrap_or(&0),
            cluster_declined.get(tag).unwrap_or(&0)
        );
    }
    eprintln!("\n=== functions with >=1 undischarged safety VC: {} ===", fn_undischarged.len());
    for (def_path, tags) in &fn_undischarged {
        eprintln!("  {def_path}: {tags:?}");
    }
    Ok(())
}
