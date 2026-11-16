//! F6B-FIELD-OVERRIDE-UNSTABLE-1 and F6B-TRACE-MEMO-KEY-1 (2026-10-06) on REAL
//! extracted MIR: the F6b callee re-trace may use only facts about the context
//! it traces.
//!
//! ```text
//! fn bump(mut p: P) -> f64 { p.a = 1.0e300; p.a }
//! fn via_mut(mut p: (f64, f64)) -> f64 { set(&mut p.0); p.0 }
//! lie_struct()    = bump(P { a: 0.5 }) * 1.0e300
//! lie_tuple_mut() = via_mut((0.5, 0.5)) * 1.0e300
//! pre_lie()       = scaled(bump(P { a: 0.5 }))    // scaled requires 0 <= x <= 1
//!
//! fn inner(v) { v }   fn outer(w) { inner(w) }
//! twice(x, y)  requires x == 2 { let a = outer(x); let b = outer(y); a * b }
//! caller(x, y) requires x == 2 { let a = inner(x); let b = outer(y); a * b }
//! ```
//!
//! Before the fix the F6b trace bound the leaf `p.0` of a struct or tuple
//! formal to the caller's actual (`0.5`) although the callee writes it first,
//! and one trace memo, keyed in the traced function's own local names, was
//! shared by every nested context, so `outer(y)` reused the `[2, 2]` cached for
//! the same key during `outer(x)` (or during the caller's own `inner(x)`).
//! The `float_overflow_to_infinity` rows of `lie_struct`, `lie_tuple_mut`,
//! `twice` and `caller` were not generated at all, and F5 dropped `pre_lie`'s
//! precondition row for `scaled`. At run time each of them computes infinity
//! (`tests/ui/trust/f6b_float_trace_context_run.rs`).
//!
//! The summary database is the one the a3d harness assembles
//! (`float_range_tests::a3d_geom_whole_crate_residual_diagnosis`): every
//! function, keyed by its def path, with its parameter names, gated
//! preconditions and extracted body. Generation only; no solver runs.
//!
//! Source: one `-Ztrust-dump=mir:<dir>` capture of
//! `tests/ui/trust/f6b_float_trace_context.rs` (the `default` revision's flags:
//! `--edition 2021 -Ztrust-verify=on --crate-type lib --cfg default
//! --emit=metadata`, compiled from the repository root) by the stage 1 of
//! `4ccd862830` at `scratchpad/stage1-w18b`, 2026-10-06, its 22 functions
//! collected into `tests/fixtures/f6b_trace_context_mir.json` in def-path
//! order. The span paths are repository-relative as dumped.

use std::sync::Arc;

use trust_types::{VcKind, VerifiableFunction, VerificationResult};
use trust_vcgen::{FunctionSummary, SummaryDatabase};

/// Real extracted MIR carries deep recursive `Formula` walks.
const GENERATION_STACK_BYTES: usize = 256 * 1024 * 1024;

const CRATE: &str = "f6b_float_trace_context";

fn load_all() -> Vec<VerifiableFunction> {
    let path = format!("{}/tests/fixtures/f6b_trace_context_mir.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{path}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{path}` must deserialize: {e}"))
}

fn summary_db(fns: &[VerifiableFunction]) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    for f in fns {
        let params: Vec<String> = (1..=f.body.arg_count)
            .map(|i| {
                f.body.locals.get(i).and_then(|l| l.name.clone()).unwrap_or_else(|| format!("_{i}"))
            })
            .collect();
        let mut s = FunctionSummary::new(f.def_path.clone())
            .with_param_names(params)
            .with_extracted_body(Arc::new(f.clone()));
        for pre in &f.preconditions {
            s = s.with_precondition(pre.clone());
        }
        db.insert(s);
    }
    db
}

/// What vcgen leaves of function `name`: its `float_overflow_to_infinity` rows
/// (each with whether the structural pass already proved it) and the callees
/// of its call-site `Precondition` rows.
struct Rows {
    float: Vec<bool>,
    precondition_callees: Vec<String>,
}

fn rows(name: &str) -> Rows {
    let name = format!("{CRATE}::{name}");
    std::thread::Builder::new()
        .stack_size(GENERATION_STACK_BYTES)
        .spawn(move || {
            let fns = load_all();
            let db = summary_db(&fns);
            let func = fns
                .iter()
                .find(|f| f.def_path == name)
                .unwrap_or_else(|| panic!("fixture has no `{name}`"));
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::new(),
                );
            let is_float = |kind: &VcKind| matches!(kind, VcKind::FloatOverflowToInfinity { .. });
            let float = solver_vcs
                .iter()
                .filter(|vc| is_float(&vc.kind))
                .map(|_| false)
                .chain(
                    preclassified
                        .iter()
                        .filter(|(vc, _)| is_float(&vc.kind))
                        .map(|(_, r)| matches!(r, VerificationResult::Proved { .. })),
                )
                .collect();
            let precondition_callees = trust_vcgen::generate_callsite_precondition_vcs(func, &db)
                .into_iter()
                .filter_map(|vc| match vc.kind {
                    VcKind::Precondition { callee } => Some(callee),
                    _ => None,
                })
                .collect();
            Rows { float, precondition_callees }
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

fn assert_float_row_unproved(name: &str) {
    let rows = rows(name);
    assert!(
        !rows.float.is_empty(),
        "`{name}`: FALSE PROOF — the float_overflow_to_infinity row was discharged from a fact \
         about another context"
    );
    assert!(rows.float.iter().all(|proved| !proved), "`{name}`: a float row was proved");
}

fn assert_no_float_row(name: &str) {
    let rows = rows(name);
    assert!(rows.float.is_empty(), "`{name}`: control: the float row must stay discharged");
}

/// `bump` writes `p.a` before it reads it: its result is 1e300, not the
/// caller's 0.5.
#[test]
fn a_formal_field_written_by_the_callee_is_not_the_callers_value() {
    assert_float_row_unproved("lie_struct");
}

/// `via_mut` lends `&mut p.0` to `set` before it reads `p.0`.
#[test]
fn a_formal_field_lent_mutably_by_the_callee_is_not_the_callers_value() {
    assert_float_row_unproved("lie_tuple_mut");
}

/// `scaled(bump(p))`: F5 must not discharge `scaled`'s `requires` from the
/// caller's `p.a`.
#[test]
fn the_precondition_row_of_a_call_on_a_written_formal_field_is_kept() {
    let rows = rows("pre_lie");
    assert!(
        rows.precondition_callees.iter().any(|c| c.ends_with("::scaled")),
        "`pre_lie`: FALSE PROOF — `scaled`'s precondition row was dropped: {:?}",
        rows.precondition_callees
    );
}

/// The second trace of `outer`, with `y` unbounded, must not read the first
/// trace's memo entry.
#[test]
fn a_second_trace_of_the_same_callee_does_not_reuse_the_first() {
    assert_float_row_unproved("twice");
}

/// The caller's own `inner(x)` at `bb0` must not answer the `inner(copy _1)` at
/// `bb0` inside `outer`.
#[test]
fn a_callee_query_is_not_answered_by_the_callers_own_entry() {
    assert_float_row_unproved("caller");
}

/// Controls the scout measured keeping the row before the fix.
#[test]
fn the_unbounded_trace_controls_keep_their_row() {
    for name in ["once", "twice_ba", "nocollide"] {
        assert_float_row_unproved(name);
    }
}

/// Controls that stay discharged: a callee that does not write its formal, and
/// a second trace under the same bound.
#[test]
fn unwritten_formals_and_same_bound_traces_stay_discharged() {
    for name in ["keep_struct", "keep_tuple", "twice_same"] {
        assert_no_float_row(name);
    }
    let rows = rows("pre_keep");
    assert!(
        !rows.precondition_callees.iter().any(|c| c.ends_with("::scaled")),
        "`pre_keep`: control: `scaled`'s precondition is established by `keep`'s trace: {:?}",
        rows.precondition_callees
    );
}
