//! Census of the generic refutation scope's S1-S3 holds (2026-10-16) over a
//! directory of extracted MIR (default: this crate's `tests/fixtures`).
//!
//! For every function fixture it generates the VCs WITH the hardened twins
//! (`targo trust check`'s profile), asks in-process ay for each row, and for
//! every row ay REFUTES prints which screen of
//! [`GenericRefutationScope::rejection_reason`] holds it. The S1-S3 screens run
//! after every older screen, so a row whose reason is an S1-S3 reason is exactly
//! a row that was a FAILED refutation before them: the movement the change
//! makes. Measurement aid only.
//!
//! `CENSUS_DUMP=1` also prints each refuted row's query on stderr.
//!
//! ```text
//! targo --unverified run -p trust-vcgen --example refutation_hold_census -- [dir] [ms]
//! ```
use std::collections::BTreeMap;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_types::{VerifiableFunction, VerificationResult};
use trust_vcgen::{GenericRefutationScope, VcgenContext};

const STACK_BYTES: usize = 256 * 1024 * 1024;

/// `(fixture, kind, line:col, class, reason)` of one refuted row.
type Row = (String, String, String, &'static str, String);

fn class(reason: Option<&str>) -> &'static str {
    let Some(reason) = reason else { return "kept (FAILED)" };
    if reason.contains("path condition collapsed") {
        "S1 collapsed path"
    } else if reason.contains("unmodelled return of a foreign call") {
        "S3 foreign call value"
    } else if reason.contains("loop-carried value at a loop header") {
        "S2 loop-carried join"
    } else if reason.contains("loop-carried join scan of the query exceeds its bound") {
        "S2 query scan bound"
    } else if reason.contains("loop-carried join analysis") {
        "S2 fallback (no exact joins)"
    } else {
        "held before S1-S3"
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args
        .next()
        .unwrap_or_else(|| concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures").to_owned());
    let timeout_ms: u64 = args.next().map_or(5_000, |a| a.parse().expect("timeout ms"));
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .expect("fixture directory must be readable")
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "json"))
        .collect();
    paths.sort();
    let next = AtomicUsize::new(0);
    let rows: Mutex<Vec<Row>> = Mutex::new(Vec::new());
    let skipped = AtomicUsize::new(0);
    let workers = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    std::thread::scope(|scope| {
        for _ in 0..workers {
            std::thread::Builder::new()
                .stack_size(STACK_BYTES)
                .spawn_scoped(scope, || {
                    let router = trust_router::Router::deterministic_in_process_ay(
                        timeout_ms,
                        trust_types::determinism::EffortScale::BUILTIN,
                    );
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        let Some(path) = paths.get(i) else { break };
                        if i.is_multiple_of(50) {
                            eprintln!("[census] {i}/{}", paths.len());
                        }
                        let Ok(text) = std::fs::read_to_string(path) else { continue };
                        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else {
                            skipped.fetch_add(1, Ordering::Relaxed);
                            continue;
                        };
                        let fixture =
                            path.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
                        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            let context = VcgenContext::for_function(func.def_path.clone());
                            let (solver_vcs, discharged) = trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                                &func,
                                &trust_vcgen::SummaryDatabase::new(),
                                true,
                                &context,
                                &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
                            );
                            let scope = GenericRefutationScope::for_function_with_call_dests(
                                &func,
                                &solver_vcs,
                                &discharged,
                                &context,
                            );
                            let mut out = Vec::new();
                            for vc in &solver_vcs {
                                let verdict = router
                                    .verify_all(std::slice::from_ref(vc))
                                    .into_iter()
                                    .next()
                                    .map(|(_, v)| v);
                                if !matches!(verdict, Some(VerificationResult::Failed { .. })) {
                                    continue;
                                }
                                let reason = scope.rejection_reason(vc);
                                if std::env::var_os("CENSUS_DUMP").is_some() {
                                    eprintln!(
                                        "== {fixture} {} {}:{} {:?}\n{}\n",
                                        vc.kind.description(),
                                        vc.location.line_start,
                                        vc.location.col_start,
                                        reason,
                                        vc.formula.to_smtlib()
                                    );
                                }
                                out.push((
                                    fixture.clone(),
                                    vc.kind.description(),
                                    format!("{}:{}", vc.location.line_start, vc.location.col_start),
                                    class(reason.as_deref()),
                                    reason.unwrap_or_default(),
                                ));
                            }
                            out
                        }));
                        match outcome {
                            Ok(out) => rows.lock().expect("rows").extend(out),
                            Err(_) => {
                                eprintln!("{fixture}: generation panicked; skipped");
                                skipped.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                })
                .expect("spawn census worker");
        }
    });
    let mut rows = rows.into_inner().expect("rows");
    rows.sort();
    let mut tally: BTreeMap<&'static str, usize> = BTreeMap::new();
    for (fixture, kind, at, class, reason) in &rows {
        *tally.entry(class).or_default() += 1;
        if class.starts_with('S') {
            println!("{class}\t{fixture}\t{at}\t{kind}\t{reason}");
        }
    }
    println!("---");
    println!(
        "fixtures: {} ({} skipped: not a function or panicked)",
        paths.len(),
        skipped.load(Ordering::Relaxed)
    );
    for (class, n) in &tally {
        println!("{class}\t{n}");
    }
}
