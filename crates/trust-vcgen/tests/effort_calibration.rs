// trust-vcgen/tests/effort_calibration.rs: the measurement behind the one
// effort count's built-in scale, `trust_types::determinism::EffortScale::BUILTIN`.
//
// Plan docs/design/2026-09-29-incremental-deterministic-trust-results.md §3.2a;
// docs/DECISION_QUEUE.md, BUDGET-1 and its amendment BUDGET-1a. T1 lands with
// this provisional fit. `targo trust calibrate` replaces it, and T8 calibrates
// once on the whole corpus in ay's check-wide ticks.
//
// IGNORED: it solves every in-process ay query of the real-MIR corpus several
// times (1,383 s on m3 on 2026-10-08), and it needs the solver built optimized,
// as trustc links it. A debug ay runs an order of magnitude slower per
// conflict, so the 5 s clock would end searches the shipped compiler decides.
// Run it with
//
//   CARGO_TARGET_DIR=<a dir of its own> targo --unverified test -p trust-vcgen \
//     --config 'profile.test.package."*".opt-level=3' \
//     --test effort_calibration -- --ignored --nocapture
//
// on an idle host, and record the load average it prints. It writes one row per
// query to `$CARGO_TARGET_TMPDIR/effort_calibration.tsv`.
//
// What it measures, in order:
//
// 1. The corpus: every VC of every `tests/fixtures/**/*.json` that deserializes
//    as a `VerifiableFunction`, for which the in-process ay backend accepts the
//    VC (`can_handle`). These are compiler-extracted MIR functions, so the
//    queries are the ones trustc's in-process lane solves. Fixtures and VCs run
//    in sorted, generation order.
// 2. The reference: P2's flat count. Every query gets C = 100,000 conflicts
//    (`EffortScale { conflicts_per_node: C }`), behind the shipped 5,000 ms
//    per-query clock (`Backstop::BUILTIN`).
// 3. For each query the reference decides: the smallest grid k at which it is
//    decided, solving at ascending grid values.
// 4. The fit, by BUDGET-1's rule: the k that keeps the most decided queries at
//    no more total projected conflicts than the reference, ties going to the
//    smaller k. A query's projected conflicts under k are at most its count,
//    min(C, k · size). Since C is the reference count, no k projects more than
//    the reference, and the cost side never binds. The rule's k is then taken
//    with a margin: the fitted k is the smallest grid k at least MARGIN times
//    it (DECISION_QUEUE BUDGET-1a says why).
// 5. The check: every query solved again at the fitted k. If that decides
//    fewer queries than step 3 predicted (a search that is not monotone in its
//    count), the next grid value is tried.
// 6. The clock condition: no query that the reference decides or stops on its
//    count (`effort`) may stop on the clock (`wall-backstop`) at the fitted k.
//
// The run fails, as `targo trust calibrate` exits 1, when no k keeps the
// reference's decided count, or when the clock condition fails.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::time::Instant;

use trust_router::VerificationBackend;
use trust_router::in_process_ay_backend::InProcessAyBackend;
use trust_types::determinism::{Backstop, EffortScale, StopCause};
use trust_types::{VerifiableFunction, VerificationCondition, VerificationResult};

/// The k values the fit chooses from: roughly a factor of 1.5 apart, from one
/// conflict per term to the ceiling.
const GRID: [u64; 33] = [
    1, 2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048,
    3072, 4096, 6144, 8192, 12288, 16384, 24576, 32768, 49152, 65536, 100_000,
];

/// The fitted k is at least this many times the least k that keeps every
/// query the reference decides. On the pinned ay the conflicts a query needs
/// are not a pure function of the query: ay's residual clocks (inprocessing,
/// the strict-proof discharge) run on wall time and move the search. At the
/// rule's exact k a query at the edge is decided idle and lost under load
/// (measured 2026-10-08: `cex_grounding_castu_unminable` VC 2, refuted alone at
/// k = 192 and incomplete in 2 of 4 runs of its test file at eight threads;
/// 0 of 5 at 384, 768 and 1536). The margin goes when T2 counts that work.
const MARGIN: u64 = 2;

/// One corpus query: the VC and where it came from.
struct Query {
    fixture: String,
    index: usize,
    kind: String,
    size: u64,
    vc: VerificationCondition,
}

/// One solve: what it answered, why it stopped, and how long it took.
#[derive(Clone, Copy)]
struct Solve {
    decided: bool,
    outcome: &'static str,
    cause: StopCause,
    ms: u128,
}

fn fixtures(dir: &Path, out: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{}: {e}", dir.display()))
        .map(|entry| entry.expect("a directory entry").path())
        .collect();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            fixtures(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "json") {
            out.push(path);
        }
    }
}

fn corpus(root: &Path) -> Vec<Query> {
    let mut paths = Vec::new();
    fixtures(root, &mut paths);
    let accepts = InProcessAyBackend::new();
    let mut queries = Vec::new();
    let mut functions = 0usize;
    for path in &paths {
        let Ok(json) = std::fs::read_to_string(path) else { continue };
        let Ok(function) = serde_json::from_str::<VerifiableFunction>(&json) else { continue };
        let Ok(vcs) = std::panic::catch_unwind(|| trust_vcgen::generate_vcs(&function)) else {
            continue;
        };
        functions += 1;
        let fixture = path.strip_prefix(root).unwrap_or(path).display().to_string();
        for (index, vc) in vcs.into_iter().enumerate() {
            if !accepts.can_handle(&vc) {
                continue;
            }
            let size = accepts.query_effort_for(&vc.formula).size;
            queries.push(Query {
                fixture: fixture.clone(),
                index,
                kind: vc.kind.description(),
                size,
                vc,
            });
        }
    }
    println!(
        "corpus: {} fixture files, {functions} functions, {} queries",
        paths.len(),
        queries.len()
    );
    queries
}

fn solve(query: &Query, k: u64) -> Solve {
    let backend = InProcessAyBackend::new()
        .with_timeout(Backstop::BUILTIN.vc_clock_ms())
        .with_effort_scale(EffortScale { conflicts_per_node: k });
    let start = Instant::now();
    let result =
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| backend.verify(&query.vc)));
    let ms = start.elapsed().as_millis();
    match result {
        Ok(result) => {
            let (decided, outcome) = match &result {
                VerificationResult::Proved { .. } => (true, "proved"),
                VerificationResult::Failed { .. } => (true, "failed"),
                _ => (false, "undecided"),
            };
            Solve { decided, outcome, cause: StopCause::of_result(&result), ms }
        }
        Err(_) => Solve { decided: false, outcome: "panic", cause: StopCause::SolverFault, ms },
    }
}

fn load_average() -> String {
    std::process::Command::new("/usr/sbin/sysctl")
        .args(["-n", "vm.loadavg"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map_or_else(|| "unavailable".to_string(), |text| text.trim().to_string())
}

fn progress(label: &str, done: usize, total: usize) {
    if done.is_multiple_of(500) || done == total {
        println!("  {label}: {done}/{total}");
    }
}

#[test]
#[ignore = "about 25 minutes of optimized solving; run by hand to set EffortScale::BUILTIN"]
fn effort_calibration() {
    let c = EffortScale::CEILING;
    println!("load average at start: {}", load_average());
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let queries = corpus(&root);
    let n = queries.len();
    assert!(n > 0, "no corpus");

    // 2. The reference.
    let mut reference = Vec::with_capacity(n);
    for (done, query) in queries.iter().enumerate() {
        reference.push(solve(query, c));
        progress("reference (flat C)", done + 1, n);
    }
    let reference_decided = reference.iter().filter(|s| s.decided).count();

    // 3. The smallest grid k that decides each reference-decided query.
    let mut least_k: Vec<Option<u64>> = vec![None; n];
    for (i, query) in queries.iter().enumerate() {
        if reference[i].decided {
            least_k[i] =
                Some(GRID.iter().copied().find(|&k| k < c && solve(query, k).decided).unwrap_or(c));
        }
        progress("least k", i + 1, n);
    }

    // 4. The fit.
    let worst = |k: u64| -> u128 {
        queries.iter().map(|q| u128::from(k.saturating_mul(q.size).clamp(1, c))).sum()
    };
    let reference_worst = worst(c);
    let kept = |k: u64| least_k.iter().filter(|least| least.is_some_and(|l| l <= k)).count();
    let mut table = String::new();
    for k in GRID {
        let _ = writeln!(
            table,
            "  k={k:>6}  kept {:>5}/{reference_decided}  projected worst {:.4} of the reference",
            kept(k),
            worst(k) as f64 / reference_worst as f64
        );
    }
    println!("fit (C = {c}, clock {} ms):\n{table}", Backstop::BUILTIN.vc_clock_ms());
    let most = GRID.iter().map(|&k| kept(k)).max().unwrap_or(0);
    assert!(
        GRID.iter().all(|&k| worst(k) <= reference_worst),
        "a k projects more conflicts than the reference: C is not the reference count"
    );
    let least = GRID.iter().copied().find(|&k| kept(k) == most).expect("the grid ends at C");
    let fitted = GRID
        .iter()
        .copied()
        .find(|&k| k >= least.saturating_mul(MARGIN).min(c))
        .expect("the grid ends at C");
    println!(
        "least k keeping every query the reference decides: {least}; with the margin: {fitted}"
    );

    // 5. The check at the fitted k, moving up the grid while a check decides
    // fewer queries than the reference; and 6. the clock condition, below.
    let mut checked = None;
    for k in GRID.iter().copied().filter(|&k| k >= fitted) {
        let mut solves = Vec::with_capacity(n);
        for (done, query) in queries.iter().enumerate() {
            solves.push(solve(query, k));
            progress(&format!("check at k={k}"), done + 1, n);
        }
        let decided = solves.iter().filter(|s| s.decided).count();
        println!("  k={k}: {decided} decided, against {reference_decided} for the reference");
        if decided >= reference_decided {
            checked = Some((k, solves));
            break;
        }
    }
    let Some((chosen, at_chosen)) = checked else {
        panic!("no grid k keeps the reference's {reference_decided} decided queries");
    };

    let mut tsv = String::from(
        "fixture\tvc\tkind\tsize\tref_outcome\tref_cause\tref_ms\tleast_k\tk_outcome\tk_cause\tk_ms\n",
    );
    let mut moved_to_clock = Vec::new();
    let mut tally = std::collections::BTreeMap::<(String, String), usize>::new();
    for (i, query) in queries.iter().enumerate() {
        let (r, s) = (reference[i], at_chosen[i]);
        let _ = writeln!(
            tsv,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            query.fixture,
            query.index,
            query.kind.replace('\t', " "),
            query.size,
            r.outcome,
            r.cause,
            r.ms,
            least_k[i].map_or_else(|| "-".to_string(), |k| k.to_string()),
            s.outcome,
            s.cause,
            s.ms
        );
        *tally.entry((r.cause.to_string(), s.cause.to_string())).or_default() += 1;
        let reference_held = r.decided || r.cause == StopCause::Effort;
        if reference_held && s.cause == StopCause::WallBackstop {
            moved_to_clock.push(format!("{}#{} (size {})", query.fixture, query.index, query.size));
        }
    }
    let out = Path::new(env!("CARGO_TARGET_TMPDIR")).join("effort_calibration.tsv");
    std::fs::write(&out, tsv).expect("write the per-query table");

    println!("stop causes, reference -> k={chosen}:");
    for ((from, to), count) in &tally {
        println!("  {from:>18} -> {to:<18} {count}");
    }
    println!(
        "fitted k = {chosen} (EffortScale::BUILTIN is {}); {} of {n} queries decided at k, \
         {reference_decided} at the reference; table: {}",
        EffortScale::BUILTIN.conflicts_per_node,
        at_chosen.iter().filter(|s| s.decided).count(),
        out.display()
    );
    println!("load average at end: {}", load_average());
    assert!(
        moved_to_clock.is_empty(),
        "{} queries the reference decided or stopped on its count stop on the clock at k={chosen}: {}",
        moved_to_clock.len(),
        moved_to_clock.join(", ")
    );
}
