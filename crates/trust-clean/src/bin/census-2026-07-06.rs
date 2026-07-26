// census-2026-07-06: per-function classification harness for the
// flagship-crate census (reports/flagship-crate-census-2026-07-06.md).
//
// SCRATCH TOOL — census-only, additive (new file, does not touch prove.rs /
// mirsem.rs / trustir_*.rs / any pipeline source). Uses ONLY the public API:
// `trust_clean::{prove_dump_dir_with_budget_and_bodies, ProveScorecard}` and
// `trust_types::call_graph::CalleeResolver` (the shared exact/unique resolver
// used by production call-graph scans).
//
// PROBLEM: `prove_dump_dir` returns only an AGGREGATE `ProveScorecard` over a
// whole directory of dumps — never a per-function verdict. But an aggregate
// run over a whole crate honors "callees-first" composition (a caller can
// consume an already-certified callee's `CalleeFact`), so simply running
// each function in a directory BY ITSELF would understate composed callers
// (e.g. `memchr::OneIter::count` calling `One::count_raw`).
//
// SOLUTION (isolation-by-subtraction, exact, no double counting): for a
// target function `t`,
//   1. compute its transitive callee closure C(t) WITHIN the dump directory
//      (via the same `Terminator::Call` edge scan `build_call_graph` uses);
//   2. run `prove_dump_dir` on A = C(t) ∪ {t};
//   3. run `prove_dump_dir` on B = C(t) alone;
//   4. the DELTA (A − B), field by field, is exactly `t`'s own scorecard
//      contribution — because A and B differ by exactly one function (`t`),
//      and nothing in C(t) calls `t` back (fail-closed cycle handling in the
//      production driver means a cyclic member never finds itself certified
//      anyway), so C(t)'s own certification status cannot change between the
//      two runs.
//
// Usage:
//   census-2026-07-06 <dump_dir> [target_def_path ...]
// With no targets given, every function in <dump_dir> is classified.
// Output: one TSV line per target to stdout:
//   def_path\ttotal\tinhabited\ttype_grounded_not_inhabited\tnot_grounded\t
//   kernel_rejected\tsafety_obligations\tsafety_discharged\tfully_faithful\t
//   via_trustir\tmirsem_fallback\tdeclined\texpr_fold_decline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use trust_clean::{ProveScorecard, prove_dump_dir_with_budget_and_bodies};
use trust_types::{Terminator, VerifiableFunction};

fn budget_secs() -> u64 {
    std::env::var("TRUST_CENSUS_BUDGET_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(15)
}

fn read_all_functions(dir: &Path) -> std::io::Result<Vec<(String, VerifiableFunction, PathBuf)>> {
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
            out.push((func.def_path.clone(), func, path));
        }
    }
    Ok(out)
}

/// Transitive callee closure of `root` within `all` (BFS over Call edges),
/// EXCLUDING `root` itself.
fn callee_closure(
    root: &str,
    all: &[(String, VerifiableFunction, PathBuf)],
    resolver: &trust_types::call_graph::CalleeResolver<'_>,
) -> BTreeSet<String> {
    let mut seen: BTreeSet<String> = BTreeSet::new();
    let mut stack = vec![root.to_string()];
    while let Some(cur) = stack.pop() {
        let Some((_, func, _)) = all.iter().find(|(p, _, _)| p == &cur) else { continue };
        for block in &func.body.blocks {
            if let Terminator::Call { func: callee_name, .. } = &block.terminator {
                // Shared production semantics: exact def-path first;
                // shorthand/qualified suffix only when globally unique.
                if let Some(callee_path) = resolver.resolve(callee_name) {
                    if callee_path != root && seen.insert(callee_path.to_string()) {
                        stack.push(callee_path.to_string());
                    }
                }
            }
        }
    }
    seen
}

/// A minimal self-cleaning scratch directory (std-only — no new Cargo
/// dependency for a census-only tool). Unique via pid + a monotonic counter +
/// the current time, under `std::env::temp_dir()`.
struct ScratchDir(PathBuf);

impl ScratchDir {
    fn new() -> std::io::Result<Self> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0);
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir()
            .join(format!("trust-census-2026-07-06-{}-{nanos}-{n}", std::process::id()));
        std::fs::create_dir_all(&dir)?;
        Ok(ScratchDir(dir))
    }
    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn stage_dir(paths: &[&PathBuf]) -> std::io::Result<ScratchDir> {
    let td = ScratchDir::new()?;
    for p in paths {
        let name = p.file_name().unwrap();
        std::fs::copy(p, td.path().join(name))?;
    }
    Ok(td)
}

#[derive(Default)]
struct Fields {
    total: usize,
    inhabited: usize,
    type_grounded_not_inhabited: usize,
    not_grounded: usize,
    kernel_rejected: usize,
    safety_obligations: usize,
    safety_discharged: usize,
    fully_faithful: usize,
    via_trustir: usize,
    mirsem_fallback: usize,
    declined: usize,
}

impl Fields {
    fn of(sc: &ProveScorecard) -> Self {
        Fields {
            total: sc.total,
            inhabited: sc.inhabited,
            type_grounded_not_inhabited: sc.type_grounded_not_inhabited,
            not_grounded: sc.not_grounded,
            kernel_rejected: sc.kernel_rejected,
            safety_obligations: sc.safety_obligations,
            safety_discharged: sc.safety_discharged,
            fully_faithful: sc.fully_faithful,
            via_trustir: sc.fully_faithful_via_trustir,
            mirsem_fallback: sc.fully_faithful_mirsem_fallback,
            declined: sc.declined,
        }
    }
    fn sub(&self, other: &Fields) -> Fields {
        Fields {
            total: self.total.saturating_sub(other.total),
            inhabited: self.inhabited.saturating_sub(other.inhabited),
            type_grounded_not_inhabited: self
                .type_grounded_not_inhabited
                .saturating_sub(other.type_grounded_not_inhabited),
            not_grounded: self.not_grounded.saturating_sub(other.not_grounded),
            kernel_rejected: self.kernel_rejected.saturating_sub(other.kernel_rejected),
            safety_obligations: self.safety_obligations.saturating_sub(other.safety_obligations),
            safety_discharged: self.safety_discharged.saturating_sub(other.safety_discharged),
            fully_faithful: self.fully_faithful.saturating_sub(other.fully_faithful),
            via_trustir: self.via_trustir.saturating_sub(other.via_trustir),
            mirsem_fallback: self.mirsem_fallback.saturating_sub(other.mirsem_fallback),
            declined: self.declined.saturating_sub(other.declined),
        }
    }
    fn tsv(&self, def_path: &str, expr_fold_decline: &str) -> String {
        format!(
            "{def_path}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{expr_fold_decline}",
            self.total,
            self.inhabited,
            self.type_grounded_not_inhabited,
            self.not_grounded,
            self.kernel_rejected,
            self.safety_obligations,
            self.safety_discharged,
            self.fully_faithful,
            self.via_trustir,
            self.mirsem_fallback,
            self.declined,
        )
    }
}

fn main() -> std::io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!(
            "usage: census-2026-07-06 <dump_dir> [target_def_path ...]\n       census-2026-07-06 <dump_dir> --targets-file <path>  (newline-delimited def_paths — \
             use this form; def_paths routinely contain spaces, e.g. `ArrayVec<T, CAP>::len`, \
             which shell word-splitting on positional args would corrupt)\n       census-2026-07-06 <dump_dir> --aggregate --targets-file <path>  (ONE prove_dump_dir \
             call over the whole target set — fast aggregate scorecard, no per-function attribution; \
             use when per-function isolation is too slow, e.g. a shared generic type whose registration \
             cost is repeated on every isolated call)"
        );
        std::process::exit(2);
    }
    let dump_dir = PathBuf::from(&args[1]);
    let all = read_all_functions(&dump_dir)?;
    // Structural-fold rungs C/D need generic dispatch/SCC co-member dumps as
    // fingerprint inputs even when the counted population is staged down to
    // an aggregate target set or one function plus its callee closure. Build
    // this once from the whole source directory and thread it through BOTH
    // census modes; it never contributes rows to a scorecard.
    let mut extra_bodies = trust_clean::trustir_fold::DumpBodies::new();
    for (path, func, _) in &all {
        extra_bodies.entry(path.clone()).or_insert_with(|| func.clone());
    }

    let aggregate_only = args.iter().any(|a| a == "--aggregate");
    let targets: Vec<String> = if let Some(tf_idx) = args.iter().position(|a| a == "--targets-file")
    {
        std::fs::read_to_string(&args[tf_idx + 1])?
            .lines()
            .map(|s| s.to_string())
            .filter(|s| !s.is_empty())
            .collect()
    } else if args.len() > 2 {
        args[2..].iter().filter(|a| a.as_str() != "--aggregate").cloned().collect()
    } else {
        all.iter().map(|(p, _, _)| p.clone()).collect()
    };

    if aggregate_only {
        let paths: Vec<&PathBuf> =
            all.iter().filter(|(p, _, _)| targets.contains(p)).map(|(_, _, path)| path).collect();
        eprintln!(
            "aggregate: {} of {} requested targets found in dump dir",
            paths.len(),
            targets.len()
        );
        let td = stage_dir(&paths)?;
        // Trust: structural-fold rung C — thread the WHOLE dump directory as
        // sibling bodies (design §7 item 6: the staged target subset lacks
        // the generic ExprFolderOpt dispatch co-members the rung-C SCC unit
        // peels). Fingerprint input only; the counted population stays the
        // staged target set.
        let sc = prove_dump_dir_with_budget_and_bodies(td.path(), budget_secs(), &extra_bodies)?;
        println!("{sc:#?}");
        return Ok(());
    }

    println!(
        "def_path\ttotal\tinhabited\ttype_grounded_not_inhabited\tnot_grounded\tkernel_rejected\tsafety_obligations\tsafety_discharged\tfully_faithful\tvia_trustir\tmirsem_fallback\tdeclined\texpr_fold_decline"
    );

    // One O(V) index for the whole census; every call-edge lookup in every
    // target closure is then O(1), with ambiguous shorthand failing closed.
    let callee_resolver = trust_types::call_graph::CalleeResolver::new(
        all.iter().map(|(path, func, _)| (path.as_str(), func.name.as_str())),
    );

    for (idx, t) in targets.iter().enumerate() {
        eprintln!("[{}/{}] {t}", idx + 1, targets.len());
        let Some((_, _, t_path)) = all.iter().find(|(p, _, _)| p == t) else {
            eprintln!("# WARNING: target not found in dump dir: {t}");
            continue;
        };
        let closure = callee_closure(t, &all, &callee_resolver);
        let closure_paths: Vec<&PathBuf> =
            all.iter().filter(|(p, _, _)| closure.contains(p)).map(|(_, _, path)| path).collect();

        // B = closure alone
        let sc_b = if closure_paths.is_empty() {
            ProveScorecard::default()
        } else {
            let td_b = stage_dir(&closure_paths)?;
            prove_dump_dir_with_budget_and_bodies(td_b.path(), budget_secs(), &extra_bodies)?
        };

        // A = closure + target
        let mut a_paths = closure_paths.clone();
        a_paths.push(t_path);
        let td_a = stage_dir(&a_paths)?;
        let sc_a =
            prove_dump_dir_with_budget_and_bodies(td_a.path(), budget_secs(), &extra_bodies)?;

        let fa = Fields::of(&sc_a);
        let fb = Fields::of(&sc_b);
        let delta = fa.sub(&fb);
        if delta.total != 1 {
            eprintln!(
                "# WARNING: {t}: delta.total = {} (expected 1) — closure size {} — verdict may be unreliable",
                delta.total,
                closure.len()
            );
        }
        let expr_fold_decline = all
            .iter()
            .find(|(path, _, _)| path == t)
            .and_then(|(_, func, _)| {
                trust_clean::diagnose_expr_fold_scc_for_function(func, &extra_bodies)
            })
            .and_then(Result::err)
            .map_or("-", |decline| decline.name());
        println!("{}", delta.tsv(t, expr_fold_decline));
    }
    Ok(())
}
