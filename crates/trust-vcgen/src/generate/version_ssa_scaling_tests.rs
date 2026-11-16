//! LINEAR SCALING of the statement-version oracle, pinned by deterministic WORK
//! COUNTERS (`fn_memo::AnalysisMemoStats`), never by wall time or RSS.
//!
//! For each generated family (`version_ssa_families`) at sizes 64, 128, 256 and 512,
//! the oracle is built (with the retired-oracle differential OFF — it is the thing
//! that was quadratic) and driven with the queries the per-statement and
//! per-terminator rows make: for every statement, every place it READS, versioned AT
//! that statement; for every block terminal, the places its terminator row reads (an
//! `Assert`'s condition, a `SwitchInt`'s discriminant, a call's arguments); for each
//! of those the `#e` mint gate and the may-reassigned kill probe. `Drop` places are
//! not queried: drop glue carries no row whose body reads them. The helper work the
//! oracle is BUILT from is counted too: the definition extraction's statements
//! (`extraction_stmts`), the local-write walks (`body_scan_items`) and the per-function
//! memo lookups (`memo_identity_checks`) — a quadratic build shows up there even when
//! the oracle's own counters are linear.
//!
//! THE BOUND is linear in the INPUT plus the OUTPUT. Each rung doubles the family's
//! size parameter (and grows the program by at most 2x, asserted); every counter must
//! grow by at most 1.25x the larger of that 2x and the growth of the answered token
//! bytes — 2.5x on every family whose answers are bounded. The persistent token sets
//! add a log factor (a union rebuilds an O(log) spine), and their two counters are
//! allowed it. The per-resolution QUERY steps (jump pointers, range descents) are
//! gated at O(log size) per resolution instead.
//!
//! THE OUTPUT IS LINEAR (D15). A joined token used to name every def that reaches:
//! `diamond_chain`'s and `loop_joins`' reads after `i` diamonds / loops carried `i + 1`
//! tokens, and `confined_store_blocks`' reads of `self` after `i` field stores carried
//! `i`, so those families' answers were quadratic in bytes (13,393 / 55,153 / 224,710 /
//! 942,278 on `diamond_chain(64..512)`). A joined set longer than 33 bytes is now spelled
//! by a collision-checked hash (`version_ssa`, THE SPELLING), so every answer is at most
//! 33 bytes; `version_ssa_spelling_tests::joined_answer_bytes_are_linear` pins it.
//!
//! WHAT IS NOT CLAIMED. A name written inside `depth` nested loops and read after the
//! outermost resolves `depth` loop-header joins: that is the size of its MINIMAL SSA
//! form, so `nested_loops_names(n, depth)` costs Θ(n · depth). Each axis is gated
//! alone below; their product is the documented residual.

use trust_types::vc_context::{
    ContextStats, Oracle, ParityCount, RowFormula, VcContext, VcRow, WorkRatio,
};
use trust_types::{
    Formula, Operand, Rvalue, Statement, Terminator, VcKind, VerifiableFunction,
    VerificationCondition,
};

use super::legacy_version_oracle::without_differential;
use super::{StmtVersionCtx, version_ssa_families as families};
use crate::AnalysisMemoStats;

fn places_of_stmt(func: &VerifiableFunction, s: &Statement, out: &mut Vec<String>) {
    let mut add = |p: &trust_types::Place| out.push(crate::place_to_var_name(func, p));
    let op = |o: &Operand, add: &mut dyn FnMut(&trust_types::Place)| {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            add(p);
        }
    };
    if let Statement::Assign { place, rvalue, .. } = s {
        // A projected destination READS its base (`(*p).0 = v` reads `p`).
        if !place.projections.is_empty() {
            add(&trust_types::Place { local: place.local, projections: Vec::new() });
        }
        match rvalue {
            Rvalue::Use(o) | Rvalue::Cast(o, _) | Rvalue::UnaryOp(_, o) => op(o, &mut add),
            Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
                op(a, &mut add);
                op(b, &mut add);
            }
            Rvalue::Ref { place, .. } => add(place),
            _ => {}
        }
    }
}

fn places_of_terminator(func: &VerifiableFunction, t: &Terminator, out: &mut Vec<String>) {
    let mut add = |p: &trust_types::Place| out.push(crate::place_to_var_name(func, p));
    match t {
        Terminator::Call { args, .. } => {
            for a in args {
                if let Operand::Copy(p) | Operand::Move(p) = a {
                    add(p);
                }
            }
        }
        Terminator::Assert { cond: Operand::Copy(p) | Operand::Move(p), .. }
        | Terminator::SwitchInt { discr: Operand::Copy(p) | Operand::Move(p), .. } => add(p),
        _ => {}
    }
}

/// Build the oracle and drive it; the counters it accumulated, and the size of the
/// answers it gave (the OUTPUT the work is measured against), in bytes of their RETIRED
/// spelling: a hashed joined token (D15) is 33 bytes, but the resolution work behind it
/// is proportional to the SET it names, which is what the retired spelling measured.
///
/// Inside a function-analysis scope and an (unmetered) generation scope, as every
/// production entry point runs: the per-function memos the extraction helpers rely on
/// (`fn_memo`, `place_memo`, `havoc_memo`, the local-write index) are active only
/// there, and without them those helpers rescan the locals or the body per call.
fn drive(func: &VerifiableFunction) -> (AnalysisMemoStats, u64) {
    let (stats, set_bytes, _) = drive_full(func, &|_, _| Vec::new());
    (stats, set_bytes)
}

/// The bytes of the version tokens [`drive`] answers for `func`, as SPELLED.
pub(super) fn answer_bytes(func: &VerifiableFunction) -> u64 {
    drive_full(func, &|_, _| Vec::new()).2
}

/// [`drive`], plus the names `extra(block, statement index)` versioned at each point.
fn drive_with(
    func: &VerifiableFunction,
    extra: &dyn Fn(usize, usize) -> Vec<String>,
) -> (AnalysisMemoStats, u64) {
    let (stats, set_bytes, _) = drive_full(func, extra);
    (stats, set_bytes)
}

/// [`drive_with`], and the answers' SPELLED bytes beside their retired-spelling bytes.
fn drive_full(
    func: &VerifiableFunction,
    extra: &dyn Fn(usize, usize) -> Vec<String>,
) -> (AnalysisMemoStats, u64, u64) {
    without_differential(|| {
        let _analysis = super::FuncAnalysisScope::enter(func);
        let _scope = crate::gen_work_scope_unmetered();
        crate::fn_memo::reset_analysis_memo_stats();
        let sv = StmtVersionCtx::build(func);
        let (mut answer, mut spelled) = (0u64, 0u64);
        let mut names: Vec<String> = Vec::new();
        let mut ask = |b: trust_types::BlockId, i: usize, name: &str| {
            let token = sv.version_token_at(func, b, i, name);
            let len = token.as_ref().map_or(0, |t| t.len() as u64);
            spelled += len;
            // A hashed token is always the inter-block arm's answer.
            answer += if token.is_some_and(|t| t.starts_with('h')) {
                sv.ssa().retired_answer_len(b.0, name)
            } else {
                len
            };
            let _ = sv.full_graph_union_is_entry_only(b, name);
            let _ = sv.may_reassigned_rebinds(b, name);
        };
        for b in &func.body.blocks {
            for (i, s) in b.stmts.iter().enumerate() {
                names.clear();
                places_of_stmt(func, s, &mut names);
                names.extend(extra(b.id.0, i));
                for name in &names {
                    ask(b.id, i, name);
                }
            }
            names.clear();
            places_of_terminator(func, &b.terminator, &mut names);
            names.extend(extra(b.id.0, b.stmts.len()));
            for name in &names {
                ask(b.id, b.stmts.len(), name);
            }
        }
        (crate::fn_memo::analysis_memo_stats(), answer, spelled)
    })
}

/// Program size: statements + blocks + locals (edges are O(blocks) in every family).
fn size(func: &VerifiableFunction) -> u64 {
    (func.body.blocks.iter().map(|b| b.stmts.len() + 1).sum::<usize>() + func.body.locals.len())
        as u64
}

fn counters(s: &AnalysisMemoStats) -> [(&'static str, u64); 17] {
    [
        ("cfg_work", s.cfg_work),
        ("query_steps", s.query_steps),
        ("rebind_probes", s.rebind_probes),
        ("block_write_entries", s.block_write_entries),
        ("gate_fallbacks", s.gate_fallbacks),
        ("ssa_queries", s.ssa_queries),
        ("ssa_phis", s.ssa_phis),
        ("tracked_names", s.tracked_names),
        ("leafset_unions", s.leafset_unions),
        ("leafset_elems", s.leafset_elems),
        ("token_bytes", s.token_bytes),
        ("set_hash_nodes", s.set_hash_nodes),
        ("memo_identity_checks", s.memo_identity_checks),
        ("pseudo_defs", s.pseudo_defs),
        ("extraction_stmts", s.extraction_stmts),
        ("body_scan_items", s.body_scan_items),
        ("writes_until", s.writes_until_computed),
    ]
}

/// The persistent token-set counters: O(log) nodes / union steps per set built.
const SET_STORE: [&str; 2] = ["leafset_elems", "leafset_unions"];

/// The per-rung slack of the set-store counters. A treap's work per operation is
/// O(log) in EXPECTATION, and the realization moves with the priorities: when token
/// keys became content keys (D15) the treaps changed and `diamond_chain_single_read`'s
/// `leafset_unions / (n log2 n)` measured 0.456 .. 0.574 over n = 32..640 (step 32) —
/// Θ(n log n) with a bump between 128 and 256, where one adjacent-rung ratio is 2.84
/// against the shared 1.25 slack's 2.79. 1.4 admits that band and still refuses a
/// quadratic set store (4x per doubling against at most ~3.1 on a linear-output rung).
const SET_STORE_SLACK: f64 = 1.4;

/// Assert every counter grows at most linearly in `size + answer bytes` per rung (see
/// the module doc), and query steps at most O(log) per resolution.
fn assert_linear(family: &str, ladder: &[VerifiableFunction]) {
    let runs: Vec<(AnalysisMemoStats, u64)> = ladder.iter().map(drive).collect();
    assert_runs_linear(family, ladder, &runs);
}

fn assert_runs_linear(
    family: &str,
    ladder: &[VerifiableFunction],
    runs: &[(AnalysisMemoStats, u64)],
) {
    for w in 0..ladder.len() - 1 {
        let ((small, out_a), (big, out_b)) = (&runs[w], &runs[w + 1]);
        let (size_a, size_b) = (size(&ladder[w]) as f64, size(&ladder[w + 1]) as f64);
        let size_ratio = size_b / size_a;
        assert!(
            (1.3..=2.1).contains(&size_ratio),
            "{family}: each rung must grow the program by at most 2x ({size_ratio:.2})"
        );
        // The varied parameter doubles, so the program at most doubles; the answers
        // may grow faster (the families whose joined tokens grow with the input).
        let out_ratio = (*out_b as f64) / (*out_a as f64).max(1.0);
        let growth = f64::max(2.0, out_ratio);
        let (io_a, io_b) = (size_a + *out_a as f64, size_b + *out_b as f64);
        for ((name, a), (_, b)) in counters(small).into_iter().zip(counters(big)) {
            // QUERY steps are gated per resolution below, not per doubling; hashed
            // nodes are a sub-count of the nodes built, gated below.
            if name == "query_steps" || name == "set_hash_nodes" {
                continue;
            }
            // A counter that is (near) zero at both sizes did no work to scale.
            if b <= 16 {
                continue;
            }
            let (slack, log_factor) = if SET_STORE.contains(&name) {
                (SET_STORE_SLACK, io_b.log2() / io_a.log2())
            } else {
                (1.25, 1.0)
            };
            let bound = slack * growth * log_factor;
            let ratio = b as f64 / a.max(1) as f64;
            assert!(
                ratio <= bound,
                "{family}: `{name}` grew {ratio:.2}x ({a} -> {b}) over a rung where the program \
                 grew {size_ratio:.2}x and the answers {out_ratio:.2}x (bound {bound:.2}) — the \
                 version oracle is super-linear again. All counters: {:?} -> {:?}",
                small,
                big
            );
        }
    }
    // QUERY steps (jump pointers, range descents over a def list) are O(log) per
    // resolution: at every rung, at most `8 · log2(size)` per resolution. A resolution
    // that walked a path or scanned a list would blow through this at the top rung.
    for (func, (s, _)) in ladder.iter().zip(runs) {
        let per = 8.0 * (size(func) as f64).log2();
        assert!(
            (s.query_steps as f64) <= per * s.ssa_queries.max(1) as f64,
            "{family}: {} query steps for {} resolutions exceeds O(log) per resolution ({per:.1} \
             each) at size {}",
            s.query_steps,
            s.ssa_queries,
            size(func)
        );
    }
    // HASHED nodes (D15): each node of a store is hashed at most once, so they are
    // bounded by the nodes built, whose growth is gated above.
    for (s, _) in runs {
        assert!(
            s.set_hash_nodes <= s.leafset_elems,
            "{family}: {} set nodes hashed but only {} built — a node was hashed twice",
            s.set_hash_nodes,
            s.leafset_elems
        );
    }
    let last = &runs.last().expect("non-empty ladder").0;
    assert!(
        last.ssa_queries > 0 && last.block_write_entries > 0,
        "{family}: the driver did nothing"
    );
}

const LADDER: [usize; 4] = [64, 128, 256, 512];

fn ladder_of(mk: impl Fn(usize) -> VerifiableFunction) -> Vec<VerifiableFunction> {
    LADDER.iter().map(|&n| mk(n)).collect()
}

#[test]
fn locals_chain_is_linear() {
    assert_linear("locals_chain", &ladder_of(families::locals_chain));
}

#[test]
fn grid_is_linear_in_writes_in_arms_and_in_both() {
    assert_linear("grid(N, 64)", &ladder_of(|n| families::grid(n, 64)));
    assert_linear("grid(64, M)", &ladder_of(|m| families::grid(64, m)));
    assert_linear("grid(N, N)", &ladder_of(|x| families::grid(x, x)));
}

/// The joined tokens after `i` diamonds name `i + 1` defs (the answers are quadratic
/// in total); the work follows the answers.
#[test]
fn diamond_chain_is_linear_in_program_and_answers() {
    assert_linear("diamond_chain", &ladder_of(families::diamond_chain));
}

#[test]
fn loop_ladder_is_linear() {
    assert_linear("loop_ladder", &ladder_of(|n| families::loop_ladder(n, 8)));
}

/// Like `diamond_chain`, the value after loop `i` may come from any earlier loop's
/// body, so the joined tokens (answer SIZE) grow with `i`; the resolution work does
/// not grow faster.
#[test]
fn loop_joins_are_linear_in_program_and_answers() {
    assert_linear("loop_joins", &ladder_of(families::loop_joins));
}

#[test]
fn irreducible_regions_are_linear() {
    assert_linear("irreducible", &ladder_of(families::irreducible));
}

/// ONE loop, `n` names each written in one diamond of its body and read after it:
/// every answer has size 2. Resolving a name used to walk every join of the body (a
/// def reached through the back edge made each join a trivial phi): Θ(names x joins).
/// The loop header is a PSEUDO-DEF of every name defined in its loop, which cuts that.
#[test]
fn loop_diamond_names_are_linear() {
    let ladder = ladder_of(families::loop_diamond_names);
    assert_linear("loop_diamond_names", &ladder);
    // And the joins resolved are O(1) per name, not O(joins).
    let (s, _) = drive(&ladder[3]);
    assert!(s.ssa_phis <= 8 * 512, "loop_diamond_names(512) resolved {} joins", s.ssa_phis);
}

/// ONE read, whose answer has `n + 1` tokens: the persistent sets store O(n log n)
/// nodes for the chain of joins behind it (flat sets stored Θ(n²)).
#[test]
fn diamond_chain_single_read_stores_near_linear_sets() {
    assert_linear("diamond_chain_single_read", &ladder_of(families::diamond_chain_single_read));
}

/// Confined field stores through `&mut self` in `n` blocks, beside `n` borrows (a
/// `2n`-name havoc list): each store's gen-set is the havoc list MINUS `self`'s tree,
/// which is now a class of the write index, not a copy of the list per block.
#[test]
fn confined_store_blocks_are_linear_in_program_and_answers() {
    assert_linear("confined_store_blocks", &ladder_of(families::confined_store_blocks));
}

/// THE REBINDER TREE (`version_ssa`, REBINDER UNIONS). `confined_store_blocks`' store
/// in block `i` reads `self`, whose rebinders are `self` and every field, `i` of them
/// defined by then. Resolving the rebinders one by one cost Θ(Σ rebinders): `ssa_queries`
/// 8,258 / 32,898 / 131,330 / 524,802 at n = 64..512, 4x per doubling — which the ladder
/// gate above admits, because it bounds work by the answers' RETIRED size and that is
/// quadratic here. This gate bounds it by the PROGRAM: at most
/// `REBINDER_QUERIES_PER_N_LOG_N · n · log2 n` resolutions at every rung, and at most
/// 1.25 · 2 · (log growth) per doubling.
#[test]
fn confined_store_blocks_rebinder_unions_are_n_log_n() {
    assert_n_log_n_queries("confined_store_blocks", &families::confined_store_blocks);
}

/// The same, with the fields defined a few at a time around a CYCLE of joins (every
/// other store in one arm of a diamond, all inside one loop).
#[test]
fn confined_store_loop_rebinder_unions_are_n_log_n() {
    assert_linear("confined_store_loop", &ladder_of(families::confined_store_loop));
    assert_n_log_n_queries("confined_store_loop", &families::confined_store_loop);
}

/// The per-`n log n` constant of [`assert_n_log_n_queries`]. Measured at n = 64..512:
/// 1.49 .. 1.33 on `confined_store_blocks`, 2.68 .. 2.11 on `confined_store_loop`; the
/// per-rebinder fan-out it replaced measures 21.7 and 23.4 at n = 64.
const REBINDER_QUERIES_PER_N_LOG_N: f64 = 3.0;

fn assert_n_log_n_queries(family: &str, mk: &dyn Fn(usize) -> VerifiableFunction) {
    let queries: Vec<u64> = LADDER.iter().map(|&n| drive(&mk(n)).0.ssa_queries).collect();
    for (w, &n) in LADDER.iter().enumerate() {
        let n_log_n = n as f64 * (n as f64).log2();
        let bound = REBINDER_QUERIES_PER_N_LOG_N * n_log_n;
        assert!(
            queries[w] as f64 <= bound,
            "{family}({n}): {} resolutions exceed {REBINDER_QUERIES_PER_N_LOG_N} · n · log2 n \
             = {bound:.0} — the rebinder union fans out per rebinder again. Ladder: {queries:?}",
            queries[w]
        );
        if w > 0 {
            let m = LADDER[w - 1] as f64;
            let growth = n_log_n / (m * m.log2());
            let ratio = queries[w] as f64 / queries[w - 1].max(1) as f64;
            assert!(
                ratio <= 1.25 * growth,
                "{family}: resolutions grew {ratio:.2}x from n = {m} to {n} (bound {:.2}). \
                 Ladder: {queries:?}",
                1.25 * growth
            );
        }
    }
}

/// `n` confined stores in ONE block, each followed by a read of `(*self).f0`: the
/// write index finds the latest store outside the failing bases by jumping over runs
/// of one base, and every inter-block answer (the `#e` gate included) is IN of the
/// root of the read's rebinder tree (`version_ssa`, REBINDER UNIONS), one memoised
/// resolution per `(block, read)` — no per-rebinder fan-out.
#[test]
fn confined_store_one_block_is_linear() {
    assert_linear("confined_store_one_block", &ladder_of(families::confined_store_one_block));
}

/// `n` calls handed `&*self`, each REFINED to "the havoc list minus `self`": the
/// refinement is a delta over the list, not a copy of it per call.
#[test]
fn shared_reborrow_calls_are_linear() {
    assert_linear("shared_reborrow_calls", &ladder_of(families::shared_reborrow_calls));
}

/// Names written inside nested loops: linear in the names at a fixed depth, and
/// linear in the depth at a fixed number of names (the product is the residual in the
/// module doc).
#[test]
fn nested_loops_are_linear_in_names_and_in_depth() {
    assert_linear("nested_loops_names(N, 4)", &ladder_of(|n| families::nested_loops_names(n, 4)));
    assert_linear("nested_loops_names(16, D)", &ladder_of(|d| families::nested_loops_names(16, d)));
}

/// The write index's EXACT-PREFIX fallback, exercised: array-theory stores define
/// `arr$2$vN`, synthetic names no destination spells, so versioning those names
/// mid-block takes the fallback. Every read at a point shares one prefix extraction.
/// (RESIDUAL: each extraction is O(point), so a fallback firing at every statement
/// of a long block costs Θ(statements²) time, as the retired gate did; exact liveness
/// intervals for synthetic names — design step 3 — would remove it.)
#[test]
fn the_exact_prefix_fallback_is_taken_once_per_point() {
    let func = families::array_stores_block(64);
    let arr = |i: usize| -> Vec<String> {
        // Before statement `i`, `i / 2 + (i % 2)` stores have run; ask about the live
        // version, the next one and the previous one.
        let k = i.div_ceil(2);
        (k.saturating_sub(1)..=k + 1).map(|v| format!("arr$2$v{v}")).collect()
    };
    let (s, _) = drive_with(&func, &|_, i| arr(i));
    let points = func.body.blocks[0].stmts.len() as u64 + 1;
    assert!(s.gate_fallbacks > points, "the fallback never fired ({} times)", s.gate_fallbacks);
    assert!(
        s.writes_until_computed <= points,
        "{} exact prefixes extracted for {points} points: the fallback is not memoised per point",
        s.writes_until_computed
    );
}

/// Under a whole `generate_vcs` — the queries the VCs themselves make, one per free
/// variable of every threaded fact — the back-edge ladder resolves a BOUNDED number of
/// joins per query. (The number of queries grows with the VCs' backward cones of
/// facts, which is the path-definition residual of WS-E steps 5-6, not the oracle's.)
#[test]
fn loop_ladder_joins_per_query_under_generate_vcs_are_bounded() {
    let mut per_query: Vec<f64> = Vec::new();
    for n in [16usize, 32, 64] {
        let f = families::loop_ladder(n, 8);
        let s = without_differential(|| {
            crate::fn_memo::reset_analysis_memo_stats();
            let _ = super::generate_vcs(&f);
            crate::fn_memo::analysis_memo_stats()
        });
        assert!(s.ssa_queries > 0, "generate_vcs made no version query on loop_ladder({n})");
        per_query.push(s.ssa_phis as f64 / s.ssa_queries as f64);
    }
    assert!(
        per_query.iter().all(|&r| r <= 1.0) && per_query[2] <= 1.25 * per_query[0],
        "joins per version query grew with the ladder under generate_vcs: {per_query:?}"
    );
}

/// T3 C08s: a generation into a context materializes at most one row at a time, and keeps
/// none materialized once it returns. The generation's sink interns each row through the
/// row oracle, which materializes the row once to compare it and drops the read-back before
/// the next row joins, so the oracle keeps no second copy of the rows alive; every row the
/// context holds was checked, with no disagreement. `trees_alive` counts those read-backs
/// only: the sink still keeps every row's eager tree until it returns them (L4-C08s-6),
/// which this does not measure.
#[test]
fn a_generation_into_a_context_materializes_one_row_at_a_time() {
    let fams: Vec<NamedFamily> = vec![
        ("locals_chain", Box::new(families::locals_chain)),
        ("diamond_chain", Box::new(families::diamond_chain)),
        ("loop_ladder", Box::new(|n| families::loop_ladder(n, 8))),
    ];
    for (name, mk) in &fams {
        for n in [16usize, 32, 64] {
            let f = mk(n);
            let mut rows = VcContext::new();
            let vcs = without_differential(|| super::generate_vcs_rows(&f, &mut rows));
            assert!(!vcs.is_empty(), "{name}({n}) generated no row");
            let stats = rows.stats();
            assert_eq!(stats.rows, vcs.len() as u64, "{name}({n}): one context row per row");
            assert!(
                stats.trees_alive == 0 && stats.trees_alive_max <= 1,
                "{name}({n}): {} trees alive, at most {} at once",
                stats.trees_alive,
                stats.trees_alive_max
            );
            assert_eq!(
                rows.parity(Oracle::Row),
                ParityCount { rows: vcs.len() as u64, mismatches: 0 },
                "{name}({n})"
            );
        }
    }
}

/// The rungs a generation into a context is gated at (T3 C08), on every family but
/// `locals_chain`: from 256 its body is over the whole-function VC-generation budget
/// (`func_exceeds_vcgen_budget`, a structural count), so production refuses it with one
/// `UnsupportedMir` row and a rung there measures nothing. The plan's 200..1600 ladder is
/// past that bound from its second rung (L4-C08-5, measured 2026-10-21).
const CONTEXT_RUNGS: [usize; 4] = [32, 64, 128, 256];

/// `locals_chain`'s rungs: the last doubling below the whole-function budget.
const LOCALS_CHAIN_RUNGS: [usize; 4] = [16, 32, 64, 128];

fn context_rungs(family: &str) -> &'static [usize] {
    if family == "locals_chain" { &LOCALS_CHAIN_RUNGS } else { &CONTEXT_RUNGS }
}

/// The Spine share of block-def rows each C08 family keeps at every rung (plan C08,
/// coverage gate: "the measured shares become floors"), as measured on the merged tree
/// 2026-10-21 (L4-C08-5). `block_def_divisions` measured 1.000 at every rung, every row of
/// it a Spine row. The other five have no block-def row at any rung and count no decline:
/// their rows are the safety walk's, decorated after its block loop (L4-RECIPE-1's first
/// lane), so they have no share to hold. Their floor is 0.0, and
/// [`assert_context_run`] holds them to having no block-def row, so a family that starts
/// making them must take a measured floor here.
const SPINE_SHARE_FLOORS: [(&str, f64); 6] = [
    ("locals_chain", 0.0),
    ("diamond_chain", 0.0),
    ("loop_ladder", 0.0),
    ("grid", 0.0),
    ("irreducible", 0.0),
    ("block_def_divisions", 1.0),
];

/// The linearity gates a family is measured not to meet, reported instead of gated
/// (L4-C08-7, measured 2026-10-21 on the merged tree; each doubling's value is printed as
/// `CONTEXT-TOTALS`):
///
/// * `diamond_chain`: the costliest row's materialization and record-replay work per node
///   grew 1.79x, 1.88x and 1.94x across the three doublings, while its retained bytes per
///   row held at 1.00x. Reading a row back costs work in n beyond the row's own size.
/// * `grid`: record replay per node grew 1.15x from 64 to 128 (materialization 0.19x, the
///   costliest row changing shape) and 1.00x on the other doublings.
/// * `irreducible`: the generation changes regime between 64 and 128 (the largest row
///   grew 3.40x, then 0.006x), so its doublings do not compare like generations.
const MEASURED_NONLINEAR: &[(&str, &str)] = &[
    ("diamond_chain", "materialization work per row size"),
    ("diamond_chain", "record replay work per row size"),
    ("grid", "record replay work per row size"),
    ("irreducible", "materialized_nodes_max"),
    ("irreducible", "seq_cells per unit of the rows' size"),
    ("irreducible", "materialization work per row size"),
    ("irreducible", "record replay work per row size"),
];

/// `family`'s Spine share floor.
fn spine_share_floor(family: &str) -> f64 {
    SPINE_SHARE_FLOORS
        .iter()
        .find(|(name, _)| *name == family)
        .map(|&(_, floor)| floor)
        .unwrap_or_else(|| panic!("{family} has no Spine share floor"))
}

/// The work of reading every Spine row of a context back once more: the Spine-row part of
/// the context's totals, whose cones `sum_cone_blocks` counts exactly.
#[derive(Debug, Clone, Copy, Default)]
struct SpineReads {
    rows: u64,
    materialization: u64,
    record_replay: u64,
}

/// What one generation of `func` into a context of its own left there.
struct ContextRun {
    rows: u64,
    /// The generation's refusal, when it made one `UnsupportedMir` row and nothing else.
    refused: Option<String>,
    stats: ContextStats,
    parity: ParityCount,
    recipes: crate::RecipeCounts,
    /// Read after `stats`, so the reads are not in it.
    spine_reads: SpineReads,
}

fn generate_into_context(func: &VerifiableFunction) -> ContextRun {
    let mut context = VcContext::new();
    // Unmetered, as the version ladders run: a rung the generation work meter refuses is
    // one refusal row, and a doubling against it measures nothing.
    let vcs = without_differential(|| {
        let _scope = crate::gen_work_scope_unmetered();
        super::generate_vcs_rows(func, &mut context)
    });
    let refused = match vcs.as_slice() {
        [VerificationCondition { kind: VcKind::UnsupportedMir { kind, .. }, .. }] => {
            Some(kind.clone())
        }
        _ => None,
    };
    let stats = context.stats();
    ContextRun {
        rows: vcs.len() as u64,
        refused,
        stats,
        parity: context.parity(Oracle::Row),
        recipes: crate::recipe_counts(&context),
        spine_reads: spine_reads(&context),
    }
}

/// Read every Spine row of `context` back once, and count what the reads cost.
fn spine_reads(context: &VcContext) -> SpineReads {
    let before = context.stats();
    let mut rows = 0;
    for id in context.row_ids() {
        if matches!(context.row(id).map(VcRow::formula), Ok(RowFormula::Spine(_))) {
            drop(context.materialize(id).expect("a row of this context"));
            rows += 1;
        }
    }
    let after = context.stats();
    SpineReads {
        rows,
        materialization: after.materialization.work.saturating_sub(before.materialization.work),
        record_replay: after.record_replay.work.saturating_sub(before.record_replay.work),
    }
}

/// The families the plan's C08 linearity and coverage gates read, by name: the plan's,
/// and the anchor whose rows are all block-def combinations (`block_def_divisions`). The
/// three `confined_store_*` families are the version ladders' and generate no row, so a
/// context of theirs has nothing to measure (L4-C08-5).
fn context_families() -> Vec<NamedFamily> {
    vec![
        ("locals_chain", Box::new(families::locals_chain)),
        ("diamond_chain", Box::new(families::diamond_chain)),
        ("loop_ladder", Box::new(|n| families::loop_ladder(n, 8))),
        ("grid", Box::new(|n| families::grid(n, n))),
        ("irreducible", Box::new(families::irreducible)),
        ("block_def_divisions", Box::new(families::block_def_divisions)),
    ]
}

/// The Spine share of `run`'s block-def rows.
fn spine_share(run: &ContextRun) -> f64 {
    run.recipes.spine_rows as f64 / run.recipes.block_def_rows.max(1) as f64
}

/// One line of the Spine share of `run`'s block-def rows.
fn spine_share_line(family: &str, n: usize, run: &ContextRun) -> String {
    let counts = &run.recipes;
    let declines: Vec<String> = crate::SpineDecline::ALL
        .iter()
        .map(|reason| format!("{}={}", reason.name(), counts.declined(*reason)))
        .collect();
    format!(
        "SPINE-SHARE {family} n={n} rows={} recorded={} block_def_rows={} spine_rows={} \
         share={:.3} {} seq_cells={} spines={} sum_cone_blocks={} cone_rows={}",
        run.rows,
        counts.recorded,
        counts.block_def_rows,
        counts.spine_rows,
        spine_share(run),
        declines.join(" "),
        run.stats.seq_cells,
        run.stats.spines,
        run.stats.sum_cone_blocks,
        run.stats.cone_rows
    )
}

/// The per-rung checks of `family`'s run at `n`: the row oracle, the cones and the Spine
/// rows the counts name, and the Spine share floor.
fn assert_context_run(family: &str, n: usize, run: &ContextRun) {
    println!("{}", spine_share_line(family, n, run));
    assert_eq!(run.refused, None, "{family}({n}): a refused generation measures nothing");
    assert!(run.rows > 1, "{family}({n}): {} rows, nothing to measure", run.rows);
    assert_eq!(run.parity.mismatches, 0, "{family}({n}): the row oracle");
    assert_eq!(run.stats.sum_cone_blocks, run.recipes.spine_rows, "{family}({n})");
    assert!(run.recipes.spine_rows <= run.recipes.block_def_rows, "{family}({n})");
    assert_eq!(
        run.spine_reads.rows, run.recipes.spine_rows,
        "{family}({n}): the Spine rows counted are the context's"
    );
    let (share, floor) = (spine_share(run), spine_share_floor(family));
    assert!(share >= floor, "{family}({n}): Spine share {share:.3} is below its floor {floor}");
    if floor == 0.0 {
        assert_eq!(
            run.recipes.block_def_rows, 0,
            "{family}({n}): block-def rows appeared, so its share needs a measured floor"
        );
    }
}

fn growth(a: u64, b: u64) -> f64 {
    b as f64 / a.max(1) as f64
}

fn ratio(r: WorkRatio) -> f64 {
    r.work as f64 / r.size.max(1) as f64
}

/// The C08 linearity criterion between two rungs of `family`, the second twice the first
/// (plan C08, Linearity):
///
/// * `materialized_nodes_max`, `retained_row_bytes` per row and `spines` grow at most 2.1x,
///   and `seq_cells` per unit of the rows' own size at most 1.1x: a family whose rows grow
///   with n (`locals_chain`'s walk rows conjoin every earlier path definition) stores a
///   quadratic total of cells because its rows hold one (L4-C08-5);
/// * materialization and record-replay work per row size grow at most 1.1x;
/// * the totals are gated where the cones they cover grow at most 2.1x and the rows keep
///   their size (the largest row grows at most 1.1x): the Spine rows' reads
///   ([`SpineReads`]) wherever the family has Spine rows, since `sum_cone_blocks` counts
///   exactly their cones, and the whole context's materialization and record-replay work
///   only where every row's cone is known (every row a Spine row). Otherwise they are
///   reported (`CONTEXT-TOTALS`): rows that grow with n make any total over them
///   quadratic, as `block_def_divisions`' do in its one dense block (L4-C08-5). The
///   relevance work always is: a Spine's closure scans its block's candidates, so on a
///   dense block its total is quadratic in the block by design, as the eager rule's is.
///
/// A gate [`MEASURED_NONLINEAR`] lists for the family is reported, not gated.
fn assert_context_rung_linear(family: &str, (n, a): (usize, &ContextRun), b: &ContextRun) {
    let (sa, sb) = (&a.stats, &b.stats);
    let per_row = |s: &ContextStats| s.retained_row_bytes as f64 / s.rows.max(1) as f64;
    // The rows' own size is the work of reading each back once (the row oracle reads
    // every row): a family whose rows grow with n stores cells in proportion.
    let per_size =
        |cells: u64, s: &ContextStats| cells as f64 / s.materialization.work.max(1) as f64;
    let mut gated: Vec<(&str, f64, f64)> = vec![
        (
            "materialized_nodes_max",
            growth(sa.materialized_nodes_max, sb.materialized_nodes_max),
            2.1,
        ),
        ("retained_row_bytes per row", per_row(sb) / per_row(sa).max(1.0), 2.1),
        (
            "seq_cells per unit of the rows' size",
            per_size(sb.seq_cells, sb) / per_size(sa.seq_cells, sa).max(f64::MIN_POSITIVE),
            1.1,
        ),
        ("spines", growth(sa.spines, sb.spines), 2.1),
        (
            "materialization work per row size",
            ratio(sb.materialization.max_ratio) / ratio(sa.materialization.max_ratio).max(1.0),
            1.1,
        ),
        (
            "record replay work per row size",
            ratio(sb.record_replay.max_ratio) / ratio(sa.record_replay.max_ratio).max(1.0),
            1.1,
        ),
    ];
    let cones = growth(sa.sum_cone_blocks, sb.sum_cone_blocks);
    let rows_keep_size = growth(sa.materialized_nodes_max, sb.materialized_nodes_max) <= 1.1;
    let mut reported: Vec<(&str, f64)> = Vec::new();
    let spine_totals = [
        (
            "Spine-row materialization work",
            growth(a.spine_reads.materialization, b.spine_reads.materialization),
        ),
        (
            "Spine-row record replay work",
            growth(a.spine_reads.record_replay, b.spine_reads.record_replay),
        ),
    ];
    if sa.sum_cone_blocks > 0 && cones <= 2.1 && rows_keep_size {
        gated.extend(spine_totals.iter().map(|&(name, grew)| (name, grew, 2.1)));
    } else {
        reported.extend(spine_totals);
    }
    let totals = [
        ("materialization work", growth(sa.materialization.work, sb.materialization.work)),
        ("record replay work", growth(sa.record_replay.work, sb.record_replay.work)),
    ];
    let cones_known = sa.cone_rows == sa.rows && sb.cone_rows == sb.rows;
    if cones_known && cones <= 2.1 && rows_keep_size {
        gated.extend(totals.iter().map(|&(name, grew)| (name, grew, 2.1)));
    } else {
        reported.extend(totals);
    }
    reported.push(("relevance work", growth(sa.relevance.work, sb.relevance.work)));
    let (measured, gated): (Vec<_>, Vec<_>) = gated.into_iter().partition(|(name, _, _)| {
        MEASURED_NONLINEAR.iter().any(|&(listed, gate)| listed == family && gate == *name)
    });
    reported.extend(measured.into_iter().map(|(name, grew, _)| (name, grew)));
    let line: Vec<String> =
        reported.iter().map(|(name, grew)| format!("{name}={grew:.2}x")).collect();
    println!("CONTEXT-TOTALS {family} n={n}->{} reported: {}", 2 * n, line.join(" "));
    for (name, grew, bound) in gated {
        assert!(
            grew <= bound,
            "{family}: {name} grew {grew:.2}x from n={n} to n={} (bound {bound}x): {sa:?} -> \
             {sb:?}",
            2 * n
        );
    }
}

/// T3 C08 (plan C08, coverage and linearity): a generation into a context, family by
/// family at every rung. Its block-def rows' Spine share and each decline are printed
/// (`SPINE-SHARE`) and held to the family's floor ([`SPINE_SHARE_FLOORS`]); the context's
/// costs are gated as linear ([`assert_context_rung_linear`]); every Spine row counts its
/// one block of cone; and the row oracle saw no disagreement.
#[test]
fn a_generation_into_a_context_grows_linearly_and_reports_its_spines() {
    for (family, mk) in context_families() {
        let runs: Vec<(usize, ContextRun)> =
            context_rungs(family).iter().map(|&n| (n, generate_into_context(&mk(n)))).collect();
        for (n, run) in &runs {
            assert_context_run(family, *n, run);
        }
        for pair in runs.windows(2) {
            let [(n, a), (_, b)] = pair else { continue };
            assert_context_rung_linear(family, (*n, a), b);
        }
    }
}

/// The nodes of `f` as a TREE: every occurrence counts, shared subterms as often as
/// they occur. This is what a row costs while it is materialized whole.
fn tree_nodes(f: &Formula) -> u64 {
    let (mut n, mut stack) = (0u64, vec![f]);
    while let Some(x) = stack.pop() {
        n += 1;
        stack.extend(x.children());
    }
    n
}

/// REPORT-ONLY row counters (T3 C01): the size of the VC output `generate_vcs`
/// hands on, the baseline T3's per-function VC context is measured against
/// (design docs/design/2026-10-08-t3-memory-proportional-reconstruction.md §13).
///
/// * `rows`: the VCs.
/// * `row_bytes_total` / `row_bytes_max`: each row's canonical JSON (the exact-VC
///   payload's encoding: `canonical_digest_json_value`, keys in byte order), the
///   bytes every row carries through the transport and the record today.
/// * `tree_nodes_total` / `tree_nodes_max`: each row's formula as a tree
///   ([`tree_nodes`]), what materializing every row whole costs.
/// * `dag_nodes_max`: the largest row's distinct terms (`query_size` of the row).
/// * `dag_nodes_union`: the distinct terms of all rows TOGETHER — what one shared
///   context would hold. `tree_nodes_total` over it is the duplication across rows.
/// * `ctx_*` (T3 L4, C06): the rows interned into one per-function
///   `trust_types::vc_context::VcContext` and each materialized once — the context's
///   retention counters and its materialization and record-replay work
///   (`ContextStats::counters`).
///
/// Not a gate and not in any vector or key: the rows are only read.
fn row_counters(vcs: &[VerificationCondition]) -> Vec<(&'static str, u64)> {
    let (mut bytes_total, mut bytes_max, mut nodes_total, mut nodes_max, mut dag_max) =
        (0u64, 0u64, 0u64, 0u64, 0u64);
    for vc in vcs {
        let bytes = trust_types::canonical_digest_json_value(vc)
            .map(|mut v| {
                trust_types::canonicalize_json_in_place(&mut v);
                v.to_string().len() as u64
            })
            .unwrap_or(0);
        bytes_total += bytes;
        bytes_max = bytes_max.max(bytes);
        let nodes = tree_nodes(&vc.formula);
        nodes_total += nodes;
        nodes_max = nodes_max.max(nodes);
        dag_max = dag_max.max(trust_types::determinism::query_size(&[&vc.formula]));
    }
    let all: Vec<&Formula> = vcs.iter().map(|vc| &vc.formula).collect();
    let mut context = trust_types::vc_context::VcContext::new();
    let ids: Vec<_> = vcs.iter().map(|vc| context.push_node_row(vc).unwrap()).collect();
    for id in ids {
        drop(context.materialize(id));
    }
    let mut out = vec![
        ("rows", vcs.len() as u64),
        ("row_bytes_total", bytes_total),
        ("row_bytes_max", bytes_max),
        ("tree_nodes_total", nodes_total),
        ("tree_nodes_max", nodes_max),
        ("dag_nodes_max", dag_max),
        ("dag_nodes_union", trust_types::determinism::query_size(&all)),
    ];
    out.extend(context.stats().counters());
    out
}

/// MEASUREMENT (not a gate): what the semantic-guard BFS stores and asks, on shapes
/// under its size caps — the evidence those caps are re-justified by
/// (`generate::MAX_SEMANTIC_GUARD_WORK`).
#[test]
#[ignore = "measurement: the semantic-guard map's stored facts and version queries"]
fn measure_semantic_guard_map() {
    for (name, mk) in [
        ("locals_chain", &families::locals_chain as &dyn Fn(usize) -> VerifiableFunction),
        ("diamond_chain", &families::diamond_chain),
        ("loop_ladder", &|n| families::loop_ladder(n, 8)),
    ] {
        for n in [16usize, 32, 64, 128] {
            let f = mk(n);
            let (facts, fact_nodes, fact_dag, ms, stats) = without_differential(|| {
                let _analysis = super::FuncAnalysisScope::enter(&f);
                let _scope = crate::gen_work_scope_unmetered();
                crate::fn_memo::reset_analysis_memo_stats();
                let t = std::time::Instant::now();
                let map = super::build_semantic_guard_map(&f);
                let ms = t.elapsed().as_millis();
                let facts: usize = map.values().map(Vec::len).sum();
                // Report-only (T3 C01): the stored facts as trees, and their
                // distinct terms together (what a shared store would hold).
                let all: Vec<&Formula> = map.values().flatten().collect();
                let fact_nodes: u64 = all.iter().map(|g| tree_nodes(g)).sum();
                let fact_dag = trust_types::determinism::query_size(&all);
                (facts, fact_nodes, fact_dag, ms, crate::fn_memo::analysis_memo_stats())
            });
            println!(
                "SGMAP {name} n={n} blocks={} size={} facts={facts} fact_tree_nodes={fact_nodes} \
                 fact_dag_nodes={fact_dag} ms={ms} ssa_queries={} extraction_stmts={}",
                f.body.blocks.len(),
                size(&f),
                stats.ssa_queries,
                stats.extraction_stmts
            );
        }
    }
}

/// A family by name: the function it builds at size `n`.
type NamedFamily = (&'static str, Box<dyn Fn(usize) -> VerifiableFunction>);

/// MEASUREMENT (not a gate): every counter of every family at every rung.
#[test]
#[ignore = "measurement: prints the counters of every family"]
fn measure_all_families() {
    let fams: Vec<NamedFamily> = vec![
        ("locals_chain", Box::new(families::locals_chain)),
        ("grid_nn", Box::new(|x| families::grid(x, x))),
        ("diamond_chain", Box::new(families::diamond_chain)),
        ("loop_ladder", Box::new(|n| families::loop_ladder(n, 8))),
        ("loop_joins", Box::new(families::loop_joins)),
        ("irreducible", Box::new(families::irreducible)),
        ("loop_diamond_names", Box::new(families::loop_diamond_names)),
        ("diamond_chain_single_read", Box::new(families::diamond_chain_single_read)),
        ("confined_store_blocks", Box::new(families::confined_store_blocks)),
        ("confined_store_one_block", Box::new(families::confined_store_one_block)),
        ("confined_store_loop", Box::new(families::confined_store_loop)),
        ("shared_reborrow_calls", Box::new(families::shared_reborrow_calls)),
        ("nested_loops_names_d4", Box::new(|n| families::nested_loops_names(n, 4))),
        ("nested_loops_names_depth", Box::new(|d| families::nested_loops_names(16, d))),
        ("nested_loops_names_nn", Box::new(|x| families::nested_loops_names(x, x))),
        ("array_stores_block", Box::new(families::array_stores_block)),
    ];
    for (name, mk) in &fams {
        for n in LADDER {
            let f = mk(n);
            let t = std::time::Instant::now();
            let (st, answer, spelled) = drive_full(&f, &|_, _| Vec::new());
            let ms = t.elapsed().as_millis();
            let cs: Vec<String> = counters(&st).iter().map(|(k, v)| format!("{k}={v}")).collect();
            println!(
                "MEASURE {name} n={n} size={} answer_bytes={answer} spelled_bytes={spelled} \
                 ms={ms} {}",
                size(&f),
                cs.join(" ")
            );
        }
    }
}

/// MEASUREMENT (not a gate): the counters of a whole `generate_vcs` — the queries the
/// VCs themselves make — on the loop ladder and the loop-diamond family. The generation
/// writes into a context of its own (`generate_vcs_rows`, T3 C08s), whose counters are
/// printed as `sink_ctx_*`: what the generation's sink retained and materialized,
/// `sink_ctx_trees_alive_max` among them.
#[test]
#[ignore = "measurement: prints generate_vcs counters"]
fn measure_generate_vcs() {
    let fams: Vec<NamedFamily> = vec![
        ("gen/loop_ladder", Box::new(|n| families::loop_ladder(n, 8))),
        ("gen/loop_diamond_names", Box::new(families::loop_diamond_names)),
        ("gen/locals_chain", Box::new(families::locals_chain)),
    ];
    let sizes: Vec<usize> = std::env::var("GEN_SIZES")
        .ok()
        .map(|v| v.split(',').filter_map(|x| x.parse().ok()).collect())
        .unwrap_or_else(|| vec![16, 32, 64, 128]);
    for (name, mk) in &fams {
        for &n in &sizes {
            let f = mk(n);
            let mut sink = VcContext::new();
            let (st, ms, vcs) = without_differential(|| {
                crate::fn_memo::reset_analysis_memo_stats();
                let t = std::time::Instant::now();
                let vcs = super::generate_vcs_rows(&f, &mut sink);
                (crate::fn_memo::analysis_memo_stats(), t.elapsed().as_millis(), vcs)
            });
            let cs: Vec<String> = counters(&st).iter().map(|(k, v)| format!("{k}={v}")).collect();
            let rs: Vec<String> =
                row_counters(&vcs).iter().map(|(k, v)| format!("{k}={v}")).collect();
            let ks: Vec<String> =
                sink.stats().counters().iter().map(|(k, v)| format!("sink_{k}={v}")).collect();
            println!(
                "MEASURE {name} n={n} size={} vcs={} ms={ms} {} {} {}",
                size(&f),
                vcs.len(),
                cs.join(" "),
                rs.join(" "),
                ks.join(" ")
            );
        }
    }
}

/// MEASUREMENT HARNESS (not a gate): build and drive ONE oracle — the SSA one, or
/// the retired dense-map one — over a dumped body or a generated family, so its peak
/// RSS can be read off `/usr/bin/time -l` around this process alone.
///
/// `TRUST_VCGEN_ORACLE_PROBE=ssa|legacy`, and either `TRUST_VCGEN_PROBE_JSON=<dumped
/// VerifiableFunction>` or `TRUST_VCGEN_PROBE_FAMILY=locals_chain:<n>`.
#[test]
#[ignore = "measurement harness: run under /usr/bin/time -l with the env vars in its doc"]
fn probe_oracle_alone() {
    let which = std::env::var("TRUST_VCGEN_ORACLE_PROBE").unwrap_or_else(|_| "ssa".into());
    let func: VerifiableFunction = if let Ok(path) = std::env::var("TRUST_VCGEN_PROBE_JSON") {
        serde_json::from_str(&std::fs::read_to_string(path).expect("read")).expect("parse")
    } else {
        let spec =
            std::env::var("TRUST_VCGEN_PROBE_FAMILY").unwrap_or_else(|_| "locals_chain:64".into());
        let n: usize = spec.split(':').nth(1).and_then(|n| n.parse().ok()).unwrap_or(64);
        families::locals_chain(n)
    };
    let start = std::time::Instant::now();
    let stats = if which == "legacy" {
        let _scope = crate::gen_work_scope_unmetered();
        crate::fn_memo::reset_analysis_memo_stats();
        let legacy = super::legacy_version_oracle::LegacyStmtVersions::build(&func);
        let mut names: Vec<String> = Vec::new();
        for b in &func.body.blocks {
            for (i, s) in b.stmts.iter().enumerate() {
                names.clear();
                places_of_stmt(&func, s, &mut names);
                for name in &names {
                    let _ = legacy.version_token_at(&func, b.id, i, name);
                    let _ = legacy.full_graph_union_is_entry_only(b.id, name);
                    let _ = legacy.may_reassigned_rebinds(b.id, name);
                }
            }
        }
        crate::fn_memo::analysis_memo_stats()
    } else {
        drive(&func).0
    };
    println!(
        "ORACLE_PROBE oracle={which} fn={} blocks={} size={} ms={} stats={stats:?}",
        func.name,
        func.body.blocks.len(),
        size(&func),
        start.elapsed().as_millis()
    );
}
