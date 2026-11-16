//! T3 L4 (C08s): the generation's row sink (`super::row_sink`) against the whole-list
//! passes it replaces, on the in-tree fixtures.
//!
//! Until C08s `generate_vcs_impl_with_origins` collected every lane's rows into one list,
//! sorted and spliced it, and then ran four passes over the whole list: SSA version-token
//! normalization, term-`Ite` elimination (with its record mirror), the havoc decline, and
//! the self-referential-definition refusal. The sink runs each on a row as the row joins.
//! These tests hold the two to the same rows:
//!
//! * per pass, the sink stopped after pass `k` gives exactly the rows that pass `k`'s
//!   whole-list form gives over the sink stopped after pass `k - 1`
//!   (`row_sink::seam::passes_through`); the whole-list forms are the old code, the havoc
//!   decline's kept verbatim (`havoc_decline::reclassify_havoc_only_refutations`); and the
//!   work meter ends a generation where it ends with no pass run (L4-C08s-3);
//! * the self-reference pass, which no sampled fixture is known to reach, refuses a built
//!   recurrence as its whole-list form does;
//! * a separation-engine row is wrapped by `SepFacts::wrap` exactly as the separation
//!   loop wrapped it (the loop's code, kept here);
//! * a lane that joins the sink out of its phase is caught, keeps its rows, and refuses
//!   the origin table; no real generation joins one;
//! * a generation the work meter refused is its one refusal row, in its context too.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use trust_types::vc_context::{Oracle, ParityCount, VcContext, same_row};

use super::row_sink::seam;
use super::*;

/// Stack for a thread that generates real extracted MIR: deep recursive `Formula` walks
/// overflow the libtest default (the allowance the real-MIR integration tests make).
const STACK_BYTES: usize = 64 * 1024 * 1024;

/// About one fixture in this many is in the per-pass sample ([`in_pass_sample`]), beside
/// the named fixtures below: 61 of the 2961 `tests/**/*.json` files on 2026-10-22.
const PASS_STRIDE: u64 = 49;

/// Fixtures whose generation is known to exercise a pass: a term `Ite` the generation
/// eliminates (`overflow_origins_tests::a_row_rewritten_through_a_term_ite_is_listed_as_emitted`)
/// and rows the havoc decline reclassifies (`tests/havoc_dest_decline_realmir.rs`).
const NAMED: &[&str] = &[
    "data/signed_clamp_cast_c2_add.json",
    "data/signed_clamp_cast_c2_index.json",
    "fixtures/hv_div_cmp_max.json",
    "fixtures/hv_add_cmp_min.json",
    "fixtures/hv_idx_cmp_min.json",
    "fixtures/hv_div_len_utf8.json",
    "fixtures/hv_slice_soft_len_and_call.json",
];

/// How many functions with separation rows the wrapper test reads.
const SEP_SAMPLE: usize = 24;

/// The per-function step budget a compile verifies under (`rustc_session`'s
/// `-Ztrust-verify-function-budget-steps` default). A fixture whose analyses trip it, or
/// trip the generation's work meter, is a function production refuses whole, so the
/// wrapper test skips it and counts it.
const FUNCTION_BUDGET_STEPS: u64 = 64_000_000;

fn tests_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests")
}

fn json_files(root: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(root) else { return };
    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            json_files(&path, out);
        } else if path.extension().is_some_and(|x| x == "json") {
            out.push(path);
        }
    }
}

fn sorted_fixtures() -> Vec<PathBuf> {
    let mut files = Vec::new();
    json_files(&tests_dir(), &mut files);
    files.sort();
    files
}

/// Whether the per-pass sample holds `path`: its path under `tests/`, `/`-separated, hashed
/// by FNV-1a (stable across toolchains, unlike `DefaultHasher`). A fixture's membership
/// depends on its own path alone, so adding one never moves another in or out, and the
/// floors measured over the sample still hold. A stride over the sorted list moved most of
/// the sample when three fixtures were added ahead of it (review of `95449037cd`,
/// 2026-10-22), and its floors failed with no pass changed.
fn in_pass_sample(path: &Path) -> bool {
    let tests = tests_dir();
    let relative = path.strip_prefix(&tests).unwrap_or(path);
    let parts: Vec<_> =
        relative.components().map(|part| part.as_os_str().to_string_lossy()).collect();
    let hash = parts.join("/").bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
    });
    hash % PASS_STRIDE == 0
}

fn parse(path: &Path) -> Option<VerifiableFunction> {
    let text = std::fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

/// Run `work` on a thread with [`STACK_BYTES`] of stack.
fn on_big_stack<R: Send + 'static>(work: impl FnOnce() -> R + Send + 'static) -> R {
    std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(work)
        .expect("spawn the test thread")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

/// The view of `func` the generation's lanes and passes read: the same projections
/// `generate_vcs_impl_with_origins` takes, in its order.
fn sink_view(func: &VerifiableFunction) -> VerifiableFunction {
    let placed = func.with_placed_opaque_values();
    let ranged = with_param_type_range_facts(placed.as_ref());
    let expanded = ranged.as_ref().with_tail_calls_expanded();
    let safe = without_unmodeled_contract_arithmetic(expanded.as_ref());
    safe.as_ref().clone()
}

/// Pass `pass` (1-based, in the sink's order) as it ran over the generation's finished
/// list until C08s.
fn whole_list_pass(pass: usize, func: &VerifiableFunction, vcs: &mut [VerificationCondition]) {
    match pass {
        1 => {
            for vc in vcs.iter_mut() {
                if !v2_is_unsupported_mir_vc(vc) {
                    vc.formula = normalize_ssa_version_tokens(func, &vc.formula);
                }
            }
        }
        2 => {
            for vc in vcs.iter_mut() {
                if !v2_is_unsupported_mir_vc(vc) && formula_contains_ite(&vc.formula) {
                    vc.formula = eliminate_term_ites(&vc.formula, ITE_ELIM_CASE_CAP);
                    ob_record_eliminate_ites(vc, ITE_ELIM_CASE_CAP);
                }
            }
        }
        3 => {
            super::havoc_decline::reclassify_havoc_only_refutations(func, vcs);
        }
        4 => {
            for vc in vcs.iter_mut() {
                if let Some(detail) = super::row_sink::self_referential_definition(&vc.formula) {
                    *vc = unsupported_mir_vc(
                        func,
                        "SelfReferentialDefinition".to_string(),
                        detail,
                        vc.location.clone(),
                    );
                }
            }
        }
        _ => unreachable!("the sink has {} passes", seam::PASSES),
    }
}

/// What the per-pass comparison found over one function.
#[derive(Debug, Default)]
struct PassCounts {
    /// Rows compared, per pass.
    rows: [usize; seam::PASSES],
    /// Rows the pass changed, per pass.
    changed: [usize; seam::PASSES],
}

/// The per-pass comparison over `func`, or `None` when a generation of it panics (the
/// row-parity probe skips such a fixture too).
///
/// Each stage runs inside one outer work-meter scope, read before the scope closes: the
/// passes now run before the generation's trip check (L4-C08s-3), which leaves every
/// outcome as it was only if no pass charges the meter, so the meter must end every stage
/// where it ends the stage with no pass run.
fn compare_passes(name: &str, func: &VerifiableFunction) -> Option<PassCounts> {
    let mut stages = Vec::with_capacity(seam::PASSES + 1);
    let mut work = Vec::with_capacity(seam::PASSES + 1);
    for k in 0..=seam::PASSES {
        let generated = catch_unwind(AssertUnwindSafe(|| {
            let _meter = crate::gen_work_scope();
            let vcs = seam::passes_through(k, || generate_vcs(func));
            (vcs, crate::gen_work_used())
        }));
        let (vcs, used) = generated.ok()?;
        stages.push(vcs);
        work.push(used);
    }
    assert!(
        work.iter().all(|used| *used == work[0]),
        "{name}: the per-row passes charged the work meter (its total by passes run, 0..=4): \
         {work:?}"
    );
    let view = sink_view(func);
    let mut counts = PassCounts::default();
    for pass in 1..=seam::PASSES {
        let mut expected = stages[pass - 1].clone();
        whole_list_pass(pass, &view, &mut expected);
        let got = &stages[pass];
        assert_eq!(got.len(), expected.len(), "{name}: pass {pass} changed the row count");
        for (index, (got, expected)) in got.iter().zip(&expected).enumerate() {
            assert!(
                same_row(got, expected),
                "{name}: pass {pass}, row {index}: the sink gave\n{got:?}\nthe whole-list pass \
                 gives\n{expected:?}"
            );
        }
        counts.rows[pass - 1] += got.len();
        counts.changed[pass - 1] +=
            got.iter().zip(&stages[pass - 1]).filter(|(a, b)| !same_row(a, b)).count();
    }
    Some(counts)
}

#[test]
fn each_pass_at_the_sink_is_its_whole_list_pass() {
    let totals = on_big_stack(|| {
        let files = sorted_fixtures();
        assert!(!files.is_empty(), "no fixture found under tests/");
        let mut chosen: Vec<PathBuf> =
            files.into_iter().filter(|path| in_pass_sample(path)).collect();
        for name in NAMED {
            let path = tests_dir().join(name);
            assert!(path.exists(), "named fixture {name} is missing");
            chosen.push(path);
        }
        let mut totals = PassCounts::default();
        let mut functions = 0usize;
        for path in &chosen {
            let Some(func) = parse(path) else { continue };
            let Some(counts) = compare_passes(&path.display().to_string(), &func) else {
                continue;
            };
            functions += 1;
            for pass in 0..seam::PASSES {
                totals.rows[pass] += counts.rows[pass];
                totals.changed[pass] += counts.changed[pass];
            }
        }
        eprintln!("ROW-SINK passes functions={functions} {totals:?}");
        totals
    });
    // Measured 2026-10-22 over the hashed sample ([`in_pass_sample`]) at `fa054122ff`: 68
    // functions, 216 rows at each pass, and changed [44, 13, 6, 0]. Pass 4 (`changed[3]`)
    // has no floor: no sampled or named fixture reaches it, and
    // `the_self_reference_pass_refuses_a_recurrence_at_the_sink` holds it to a built row.
    assert!(totals.rows[0] >= 216, "{} rows compared, below the 216 measured", totals.rows[0]);
    assert!(
        totals.changed[0] >= 44,
        "{} pass-1 rewrites, below the 44 measured",
        totals.changed[0]
    );
    assert!(
        totals.changed[1] >= 13,
        "{} term `Ite`s eliminated, below the 13 measured",
        totals.changed[1]
    );
    assert!(totals.changed[2] >= 6, "{} havoc declines, below the 6 measured", totals.changed[2]);
}

/// Pass 4 at the sink refuses a recurrence as its whole-list form refuses it. The row is
/// built (`i == i + 100` beside its obligation, the shape the pass exists for) over a
/// function with no call, so the havoc decline has nothing to decline before it.
#[test]
fn the_self_reference_pass_refuses_a_recurrence_at_the_sink() {
    let func = super::version_ssa_families::diamond_chain(1);
    let i = || Formula::Var("i".to_string(), Sort::Int);
    let recurrence = Formula::Eq(
        Box::new(i()),
        Box::new(Formula::Add(Box::new(i()), Box::new(Formula::Int(100)))),
    );
    let obligation = Formula::Lt(Box::new(i()), Box::new(Formula::Int(0)));
    let row = VerificationCondition {
        formula: Formula::And(vec![recurrence, obligation.clone()]),
        ..filler(7)
    };
    // Control: the same obligation without the recurrence is kept.
    let control = VerificationCondition { formula: obligation, ..filler(8) };

    let mut sink = RowSink::new(&func, None);
    sink.lane([row.clone(), control.clone()]);
    sink.sort_by_location();
    let got = sink.finish().vcs;

    let mut expected = vec![row, control];
    for pass in 1..=seam::PASSES {
        whole_list_pass(pass, &func, &mut expected);
    }
    assert_eq!(got.len(), 2);
    for (got, expected) in got.iter().zip(&expected) {
        assert!(
            same_row(got, expected),
            "the sink gave\n{got:?}\nthe whole list gives\n{expected:?}"
        );
    }
    assert!(
        matches!(
            &got[0].kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "SelfReferentialDefinition"
        ),
        "the recurrence was not refused: {:?}",
        got[0].kind
    );
    assert_eq!(got[1].kind, VcKind::DivisionByZero, "control: a row with no recurrence is kept");
}

/// The separation loop's wrappers as `generate_vcs_impl_with_origins` applied them until
/// C08s, over every separation row of `func`.
fn loop_wrapped(
    func: &VerifiableFunction,
) -> Vec<(VerificationCondition, BlockId, crate::unsafe_verify::MirOp)> {
    let sep_guard_paths = guard_map_for(func);
    let sep_sv = stmt_versions_for(func);
    let sep_path_defs = v2_build_path_definition_map(func);
    let sep_sem_guards = build_semantic_guard_map(func);
    let sep_checked_facts = crate::guards::build_checked_arith_facts(func);
    let sep_div_exact = build_division_exact_facts(func);
    let mut out = Vec::new();
    for (mut vc, block_id, sep_op) in crate::sep_engine::check_sep_unsafe_blocked_ops(
        func,
        &FxHashSet::default(),
        &FxHashSet::default(),
    ) {
        if let Some(block) = func.body.blocks.get(block_id.0) {
            let end = match sep_op {
                crate::unsafe_verify::MirOp::Statement(index) => index,
                crate::unsafe_verify::MirOp::Terminator => block.stmts.len(),
            };
            vc.formula = super::block_defs::v2_formula_with_block_defs_at_point(
                func, block, end, vc.formula,
            );
        }
        if let Some(path_defs) = sep_path_defs.get(&block_id)
            && !path_defs.is_empty()
        {
            let live = v2_live_path_defs(func, &func.body.blocks[block_id.0], path_defs);
            if !live.is_empty() {
                let mut conjuncts = live;
                conjuncts.push(vc.formula.clone());
                vc.formula = Formula::And(conjuncts);
            }
        }
        if let Some(paths) = sep_guard_paths.get(&block_id) {
            vc.formula = v2_formula_with_path_guards(func, &sep_sv, block_id, paths, vc.formula);
        }
        if let Some(sem) = sep_sem_guards.get(&block_id)
            && !sem.is_empty()
        {
            let mut conjuncts = sem.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
        if !sep_checked_facts.is_empty() {
            let mut conjuncts = sep_checked_facts.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
        if !sep_div_exact.is_empty() {
            let mut conjuncts = sep_div_exact.clone();
            conjuncts.push(vc.formula.clone());
            vc.formula = Formula::And(conjuncts);
        }
        out.push((vc, block_id, sep_op));
    }
    out
}

#[test]
fn a_separation_row_is_wrapped_as_the_separation_loop_wrapped_it() {
    let (functions, rows, over_budget) = on_big_stack(|| {
        let (mut functions, mut rows, mut over_budget) = (0usize, 0usize, 0usize);
        for path in sorted_fixtures() {
            if functions == SEP_SAMPLE {
                break;
            }
            let Some(func) = parse(&path) else { continue };
            let func = sink_view(&func);
            if !crate::sep_engine::has_unsafe_patterns(&func) {
                continue;
            }
            // A fixture the separation engine panics on is skipped, as the probe skips it.
            // Each side runs as a generation does: in the function's analysis scope and a
            // work-meter scope of its own, whose memos are live only inside it. Without
            // them every lane rebuilt the whole-CFG analyses at every point, and one
            // census fixture ran past an hour.
            let generated = catch_unwind(AssertUnwindSafe(|| {
                let _analysis = super::FuncAnalysisScope::enter(&func);
                let expected = within_function_budget(|| loop_wrapped(&func))?;
                let got = within_function_budget(|| {
                    let facts = SepFacts::for_function(&func);
                    let raw = crate::sep_engine::check_sep_unsafe_blocked_ops(
                        &func,
                        &FxHashSet::default(),
                        &FxHashSet::default(),
                    );
                    raw.into_iter()
                        .map(|(vc, block, op)| (facts.wrap(&func, vc, block, op), block, op))
                        .collect::<Vec<_>>()
                })?;
                Some((expected, got))
            }));
            let Ok(generated) = generated else { continue };
            let Some((expected, got)) = generated else {
                over_budget += 1;
                continue;
            };
            assert_eq!(got.len(), expected.len(), "{}", path.display());
            for ((got, block, op), (wrapped, _, _)) in got.iter().zip(&expected) {
                assert!(
                    same_row(got, wrapped),
                    "{}: bb{} {op:?}: SepFacts::wrap gave\n{got:?}\nthe loop gave\n{wrapped:?}",
                    path.display(),
                    block.0
                );
            }
            if !expected.is_empty() {
                functions += 1;
                rows += expected.len();
            }
        }
        (functions, rows, over_budget)
    });
    eprintln!("ROW-SINK sep functions={functions} rows={rows} over_budget={over_budget}");
    // Measured 2026-10-21 on the merged tree: 24 functions, 105 rows, none over budget.
    assert_eq!(functions, SEP_SAMPLE, "fewer functions with separation rows than the sample");
    assert!(rows >= 105, "{rows} separation rows compared, below the 105 measured");
}

/// `work` as one generation of a function runs it: under the function's step budget and in
/// a work-meter scope of its own; `None` when either tripped.
fn within_function_budget<R>(work: impl FnOnce() -> R) -> Option<R> {
    let _budget =
        trust_types::verify_budget::VerifyBudgetGuard::install(None, FUNCTION_BUDGET_STEPS);
    let _meter = crate::gen_work_scope();
    let out = work();
    let refused = trust_types::verify_budget::exhausted_readonly() || crate::gen_work_tripped();
    (!refused).then_some(out)
}

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

/// An Add-overflow row at `line`, the kind whose origin the sink keeps.
fn add_row(line: u32) -> VerificationCondition {
    VerificationCondition {
        kind: VcKind::ArithmeticOverflow { op: BinOp::Add, operand_tys: (u32_ty(), u32_ty()) },
        function: trust_types::Symbol::intern("f"),
        location: SourceSpan {
            file: "sink.rs".into(),
            line_start: line,
            col_start: 1,
            line_end: line,
            col_end: 9,
        },
        formula: Formula::Bool(true),
        contract_metadata: None,
        obligation: None,
    }
}

/// A walk of two Add rows, each its block's overflow `Assert`'s, out of location order.
fn walk() -> super::safety::SafetyWalk {
    let rows = vec![(BlockId(0), add_row(20)), (BlockId(1), add_row(10))];
    super::safety::SafetyWalk {
        overflow_assert_rows: (0..rows.len()).collect(),
        rows,
        truncated: false,
        row_capped: false,
    }
}

/// A row with no origin.
fn filler(line: u32) -> VerificationCondition {
    VerificationCondition { kind: VcKind::DivisionByZero, ..add_row(line) }
}

/// The table `output` gives, and its rows' lines in order.
fn table_and_lines(output: SinkOutput) -> (bool, Vec<u32>) {
    let lines = output.vcs.iter().map(|vc| vc.location.line_start).collect();
    (!output.origins.finish(&output.vcs).is_truncated(), lines)
}

#[test]
fn a_lane_out_of_its_phase_refuses_the_origin_table() {
    let func = super::version_ssa_families::locals_chain(2);

    // Control: every lane in its phase keeps the table, and the sort moved the walk.
    let mut sink = RowSink::new(&func, None);
    sink.walk(walk(), KeepOrigins::Yes);
    sink.lane([filler(15)]);
    sink.sort_by_location();
    let at = sink.mark();
    sink.append([filler(5)]);
    sink.splice_at(at, vec![filler(1)]);
    assert_eq!(sink.out_of_phase(), 0);
    assert_eq!(table_and_lines(sink.finish()), (true, vec![10, 15, 20, 1, 5]));

    // A sorted lane after the sort: kept where it joined, and no table.
    let mut sink = RowSink::new(&func, None);
    sink.walk(walk(), KeepOrigins::Yes);
    sink.sort_by_location();
    sink.lane([filler(15)]);
    assert_eq!(sink.out_of_phase(), 1);
    assert_eq!(table_and_lines(sink.finish()), (false, vec![10, 20, 15]));

    // An appended lane before the sort, and a splice before it: no table.
    let mut sink = RowSink::new(&func, None);
    sink.walk(walk(), KeepOrigins::Yes);
    sink.append([filler(5)]);
    sink.splice_at(0, vec![filler(1)]);
    assert_eq!(sink.out_of_phase(), 2);
    sink.sort_by_location();
    assert!(!table_and_lines(sink.finish()).0);

    // A walk after another row: its origins would index the wrong rows, so no table.
    let mut sink = RowSink::new(&func, None);
    sink.lane([filler(15)]);
    sink.walk(walk(), KeepOrigins::Yes);
    assert_eq!(sink.out_of_phase(), 1);
    sink.sort_by_location();
    assert_eq!(table_and_lines(sink.finish()), (false, vec![10, 15, 20]));
}

/// A generation into a context returns each row's id, and the id reads back as the row; a
/// generation into none returns no id.
#[test]
fn the_sink_returns_the_id_of_each_row_it_interned() {
    let func = super::version_ssa_families::locals_chain(8);
    let none = FxHashSet::default();
    let context = crate::VcgenContext::for_function(func.def_path.clone());
    let generate = |rows: Option<&mut VcContext>| {
        super::legacy_version_oracle::without_differential(|| {
            crate::with_function_vcgen_context(&func.def_path, &context, || {
                generate_vcs_impl_with_origins(
                    &func,
                    None,
                    false,
                    &none,
                    KeepOrigins::No,
                    rows,
                    super::recipes::Spines::Join,
                )
            })
        })
    };
    let mut rows = VcContext::new();
    let into = generate(Some(&mut rows));
    assert!(!into.vcs.is_empty());
    assert_eq!(into.ids.len(), into.vcs.len());
    for (id, vc) in into.ids.iter().zip(&into.vcs) {
        let id = id.expect("a row of an unfull context has an id");
        let read_back = rows.materialize(id).expect("a row of this context");
        assert!(same_row(read_back.vc(), vc));
    }
    assert_eq!(rows.len(), into.vcs.len());

    let bare = generate(None);
    assert!(bare.ids.iter().all(Option::is_none));
    assert_eq!(bare.vcs.len(), into.vcs.len());
    for (a, b) in bare.vcs.iter().zip(&into.vcs) {
        assert!(same_row(a, b), "a context changed a row");
    }
}

/// No real generation joins its sink out of its phase, and one that keeps its origins keeps
/// its table. The census reads each line of `generate_vcs_impl_with_origins` for its shape,
/// not for the order of its lanes; this reads the order, over three families and the
/// per-pass fixture sample, where the sink counts it (`seam::out_of_phase_joins`).
#[test]
fn no_generation_joins_its_sink_out_of_phase() {
    let (functions, joins) = on_big_stack(|| {
        let none = FxHashSet::default();
        let keep = |func: &VerifiableFunction| {
            let context = crate::VcgenContext::for_function(func.def_path.clone());
            let mut rows = VcContext::new();
            super::legacy_version_oracle::without_differential(|| {
                crate::with_function_vcgen_context(&func.def_path, &context, || {
                    generate_vcs_impl_with_origins(
                        func,
                        None,
                        false,
                        &none,
                        KeepOrigins::Yes,
                        Some(&mut rows),
                        super::recipes::Spines::Join,
                    )
                })
            })
        };
        let before = seam::out_of_phase_joins();
        let mut functions = 0usize;
        for n in [4usize, 8] {
            // locals_chain's overflow checks are what the origin table is for.
            let output = keep(&super::version_ssa_families::locals_chain(n));
            assert!(
                !output.origins.finish(&output.vcs).is_truncated(),
                "locals_chain({n}): the origin table was refused"
            );
            keep(&super::version_ssa_families::diamond_chain(n));
            keep(&super::version_ssa_families::loop_ladder(n, 2));
            functions += 3;
        }
        for path in sorted_fixtures().iter().filter(|path| in_pass_sample(path)) {
            let Some(func) = parse(path) else { continue };
            // A fixture the generation panics on is skipped, as the probe skips it.
            if catch_unwind(AssertUnwindSafe(|| keep(&func))).is_ok() {
                functions += 1;
            }
        }
        (functions, seam::out_of_phase_joins() - before)
    });
    eprintln!("ROW-SINK phases functions={functions} out_of_phase={joins}");
    assert_eq!(joins, 0, "a generation joined its row sink out of its phase");
    assert!(functions > 6, "the fixture sample went vacuous");
}

/// The work budget a test installs on this thread, cleared when the guard drops.
struct TestBudget;

impl TestBudget {
    fn install(budget: usize) -> Self {
        crate::gen_work::set_test_budget(Some(budget));
        TestBudget
    }
}

impl Drop for TestBudget {
    fn drop(&mut self) {
        crate::gen_work::set_test_budget(None);
    }
}

/// A generation the work meter refused is its one refusal row, its id the context's: the
/// rows that joined before the trip stay in the context, named by no id, every one checked
/// with no disagreement, and the rows that joined after it skipped their passes and the
/// oracle (`RowSink::take`). Control: under the production budget the same body keeps
/// every row.
#[test]
fn a_tripped_generation_is_its_one_refusal_row_in_its_context_too() {
    let func = super::version_ssa_families::locals_chain(8);
    let generate = |context: &mut VcContext| {
        super::legacy_version_oracle::without_differential(|| generate_vcs_rows(&func, context))
    };

    let mut whole = VcContext::new();
    let kept = generate(&mut whole);
    assert!(kept.len() > 1, "control: locals_chain(8) has more than one row");

    let _budget = TestBudget::install(1);
    let mut context = VcContext::new();
    let refused = generate(&mut context);
    assert_eq!(refused.len(), 1, "a 1-node work budget leaves one row: {refused:?}");
    assert!(
        matches!(
            &refused[0].kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "TrustVcGenWorkBudgetExceeded"
        ),
        "control: the meter tripped: {:?}",
        refused[0].kind
    );
    let stats = context.stats();
    eprintln!("ROW-SINK tripped context_rows={} whole_rows={}", stats.rows, kept.len());
    assert!(stats.rows >= 1, "the refusal row joined the context");
    assert_eq!(
        context.parity(Oracle::Row),
        ParityCount { rows: stats.rows, mismatches: 0 },
        "every row the refused generation left in its context was checked"
    );
}
