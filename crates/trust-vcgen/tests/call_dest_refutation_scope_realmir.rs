//! REAL-MIR matrix for the D5-A same-crate call-destination refutation screen
//! (`GenericRefutationScope::for_function_with_call_dests`).
//!
//! # What was wrong
//!
//! ```text
//! pub fn guard(bit: u32) -> bool { bit < 64 }
//! pub fn shift_via_guard(x: u64, bit: u32) -> Option<u64> {
//!     if !guard(bit) { return None; }
//!     Some(x >> bit)
//! }
//! ```
//!
//! reported `[shift:right] FAILED (ay-in-process); counterexample: _3 = true,
//! … bit = 64` on stage-1 `a8c853de6f`. `_3` is `guard(bit)`: no summary models
//! a same-crate callee's return, so it is a free variable of the query and ay
//! CHOSE `true` for `bit = 64`. That is a model of the formula, not a run.
//!
//! # What this file pins
//!
//! Every fixture is the compiler's OWN extracted MIR, captured verbatim from
//! `tests/fixtures/d5_call_dest_fx.rs` with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        -Ztrust-dump=mir-only:<dir> d5_call_dest_fx.rs
//! ```
//!
//! and the generation entry is the one the compiler uses
//! (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`).
//! Each HOLD row carries its own positive control: the same row, solved by
//! in-process ay, must really come back `Failed` (so the screen is what turns
//! it into a held Unknown), and the SAME scope built from an EMPTY census must
//! not hold it (so nothing else in the scope does).
//!
//! | row | census | expected |
//! |---|---|---|
//! | `shift_via_guard` (dest in the PATH GUARD) | `guard` | HELD |
//! | `div_nz` (dest is the divisor) | `nz` | HELD |
//! | `unguarded_after_call` (`let _ = guard_bad(bit)`; dest never read) | `guard_bad` | NOT held — genuine refutation |
//! | `div_one_bad` (`x / (one() - 1)`, `one` const-set pinned) | `one` + crate-wide const set | NOT held — genuine refutation |
//! | `div_one_bad` (the const set registered for ANOTHER body) | `one` + another body's const set | HELD |
//! | `div_one_bad` (`one` summarized `ensures result == 1`, injected) | `one` + DB | NOT held |
//! | `div_one_bad` (`one` summarized `ensures result <= 1`, injected) | `one` + DB | HELD — a bound is not a pin |
//! | `div_when_zero` (field-read summary at the call) | `is_zero` + field summary | NOT held |
//! | `shift_via_guard` with a census for ANOTHER `DefIndex` | other | NOT held |
//! | `shift_via_guard` with a context owned by another function | `guard` | NOT held |
//!
//! # Injected is not pinned (2026-09-28)
//!
//! `p_falsefail::dead_else` FAILED on stage 1 (and `dead_else_s` on the pack):
//! `let r = smax(a, 3); if r == a { 0 } else { 3 - r }` under `a > 3`, where
//! `smax` is `requires b <= a ensures result <= a`. ay answered `a = 5, r = 4`:
//! a model of the contract, not a run (`smax(5, 3)` is 5; the else arm is
//! dead). The census had treated every callee whose summary INJECTS a clause as
//! pinning its destination. It now asks whether the injected clause DETERMINES
//! the result (`summary_pins_result`), at a site the injector admits. The rows
//! below are the compiler's own MIR of `tests/fixtures/d5_contract_pin_fx.rs`
//! (`trustc --crate-name fx`, same dump flags as above, trustc `4d9a20e3d`),
//! each generated WITH the summary DB the screen reads:
//!
//! | row | callee summary | expected |
//! |---|---|---|
//! | `dead_else_s` (`3 - r` in the dead arm) | `smax`: `requires b <= a`, `ensures result <= a` | HELD |
//! | `dead_else_u` (same, no guard) | `umax`: `ensures result >= a` | HELD |
//! | `three_bad` (`2 - r`, `r == 3`: really overflows) | `three`: `ensures result == 3` | NOT held |
//! | `four`'s own `ensures result == 4` (body returns `three()`) | `three` | NOT held |
//! | `smax_bad`'s own `ensures result < a` (no call) | — | NOT held |
use trust_types::fx::{FxHashMap, FxHashSet};
use trust_types::{
    Formula, Sort, Terminator, VerifiableFunction, VerificationCondition, VerificationResult,
};
use trust_vcgen::{
    CalleeSummaryContext, FunctionSummary, GENERIC_REFUTATION_HELD_PREFIX, GenericRefutationScope,
    LocalCallDestScreen, SummaryBodyIdentity, SummaryDatabase, VcgenContext,
};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for generation + the in-process solver (same allowance the other
/// real-MIR matrices make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The `(stable_crate_id, def_index)` of the single call in `func`, read off the
/// extractor's own `CalleeIdentity` — the exact key the compiler's census uses.
fn sole_callee(func: &VerifiableFunction) -> (String, (u64, u32)) {
    let calls: Vec<_> = func
        .body
        .blocks
        .iter()
        .filter_map(|block| match &block.terminator {
            Terminator::Call { func: callee, callee_identity: Some(identity), .. } => {
                Some((callee.clone(), (identity.stable_crate_id, identity.def_index)))
            }
            _ => None,
        })
        .collect();
    assert_eq!(calls.len(), 1, "{}: exactly one identified call expected", func.def_path);
    calls.into_iter().next().expect("length checked")
}

/// For every solver row ay REFUTES, the screen's answer. Also returns how many
/// rows ay refuted (the positive control that there is something to screen).
fn refuted_rows(
    func: VerifiableFunction,
    context: VcgenContext,
) -> (usize, Vec<(VerificationCondition, Option<String>)>) {
    refuted_rows_with(func, context, SummaryDatabase::new())
}

/// [`refuted_rows`], generating with `summaries` — the DB the census must be
/// built from too, as the compiler builds both from `vc_summaries`.
fn refuted_rows_with(
    func: VerifiableFunction,
    context: VcgenContext,
    summaries: SummaryDatabase,
) -> (usize, Vec<(VerificationCondition, Option<String>)>) {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let (solver_vcs, discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &summaries,
                    false,
                    &context,
                    &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
                );
            let scope = GenericRefutationScope::for_function_with_call_dests(
                &func,
                &solver_vcs,
                &discharged,
                &context,
            );
            let router = test_router::deterministic_test_router();
            let mut refuted = 0usize;
            let mut rows = Vec::new();
            for vc in &solver_vcs {
                let result =
                    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one").1;
                if matches!(result, VerificationResult::Failed { .. }) {
                    refuted += 1;
                    rows.push((vc.clone(), scope.rejection_reason(vc)));
                }
            }
            (refuted, rows)
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn census(func: &VerifiableFunction, keys: &[(u64, u32)], db: &SummaryDatabase) -> VcgenContext {
    VcgenContext::for_function(func.def_path.clone())
        .with_local_call_dest_screen(LocalCallDestScreen::new(keys.iter().copied(), db))
}

fn assert_held(name: &str, callee_path: &str) {
    let func = load(name);
    let (_, key) = sole_callee(&func);
    // Positive control: an EMPTY census holds nothing, and ay really refutes.
    let (refuted, rows) = refuted_rows(func.clone(), census(&func, &[], &SummaryDatabase::new()));
    assert!(refuted >= 1, "{name}: control — ay must refute the row the screen is about");
    assert!(
        rows.iter().all(|(_, reason)| reason.is_none()),
        "{name}: control — an empty census must hold nothing: {rows:?}"
    );
    let (refuted, rows) =
        refuted_rows(func.clone(), census(&func, &[key], &SummaryDatabase::new()));
    assert!(refuted >= 1, "{name}: the screened row must still be a live ay SAT");
    for (vc, reason) in &rows {
        let reason = reason.as_deref().unwrap_or_else(|| {
            panic!("{name}: a SAT over `{callee_path}`'s free return must be withheld: {vc:?}")
        });
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
        assert!(reason.contains(callee_path), "the reason names the callee: {reason}");
    }
}

// ---------------------------------------------------------------------------
// HELD: the counterexample chose an unmodeled same-crate return value.
// ---------------------------------------------------------------------------

/// The measured defect. The dependency is through the PATH GUARD `_3`, not
/// through the shift's operands — a data-dependence-only screen misses it.
#[test]
fn guard_helper_path_guard_dependence_is_held() {
    assert_held("d5_shift_via_guard", "fx::guard");
}

/// `x / nz(d)`: `nz` never returns 0, but its return is free, so ay picked 0.
#[test]
fn diamond_helper_divisor_is_held() {
    assert_held("d5_div_nz", "fx::nz");
}

// ---------------------------------------------------------------------------
// NOT HELD: the screen must not over-hold a genuine refutation.
// ---------------------------------------------------------------------------

/// `let _ = guard_bad(bit); x >> bit` really overflows at `bit = 64`; the call's
/// result is never read, so the query does not mention it and the witness is
/// genuine. Memo fixture 6, at the vcgen layer.
#[test]
fn unread_call_result_keeps_its_refutation() {
    let func = load("d5_unguarded_after_call");
    let (_, key) = sole_callee(&func);
    let (refuted, rows) =
        refuted_rows(func.clone(), census(&func, &[key], &SummaryDatabase::new()));
    assert!(refuted >= 1, "control: the shift really overflows");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// `x / (one() - 1)` REALLY divides by zero. `one`'s crate-wide constant-set
/// summary pins the destination to `1`, so the witness is genuine and must
/// survive; this is the control that a MODELED local callee is not swept in.
#[test]
fn const_set_pinned_callee_keeps_its_refutation() {
    let func = load("d5_div_one_bad");
    let (callee, key) = sole_callee(&func);
    let pinned_by = |body: SummaryBodyIdentity| {
        let mut const_sets = FxHashMap::default();
        const_sets.insert(callee.clone(), vec![1i128]);
        let mut ids = FxHashMap::default();
        ids.insert(callee.clone(), body);
        census(&func, &[key], &SummaryDatabase::new()).with_callee_summaries(
            CalleeSummaryContext::default()
                .with_return_const_sets(const_sets)
                .with_summary_body_identities(ids),
        )
    };
    let own_body = SummaryBodyIdentity::Item { stable_crate_id: key.0, def_index: key.1 };
    let (refuted, rows) = refuted_rows(func.clone(), pinned_by(own_body));
    assert!(refuted >= 1, "control: `x / 0` really divides by zero");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
    // And WITHOUT the pin the same row is held: the pin is what decides.
    let (_, rows) = refuted_rows(func.clone(), census(&func, &[key], &SummaryDatabase::new()));
    assert!(rows.iter().any(|(_, reason)| reason.is_some()), "{rows:?}");
    // Trust (2026-09-30): a summary of ANOTHER body pins nothing — generation does
    // not read it at this call (`call_reaches_summarized_body`), so the screen must
    // not count it either, and the row is held.
    let other_body = SummaryBodyIdentity::Item { stable_crate_id: key.0, def_index: key.1 + 1 };
    let (_, rows) = refuted_rows(func.clone(), pinned_by(other_body));
    assert!(rows.iter().any(|(_, reason)| reason.is_some()), "{rows:?}");
}

/// `div_one_bad`'s callee summarized with `ensures`, as the compiler's
/// postcondition-composition mint builds it (no `requires`).
fn one_summary(callee: &str, post: Formula) -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(FunctionSummary::new(callee).with_verified_callee_postcondition(post));
    db
}

fn result_int() -> Formula {
    int("_0")
}

/// A callee whose injected `ensures` DETERMINES its destination
/// (`result == 1`, no `requires`): the witness is an execution, the screen
/// leaves it alone, and the genuine division by zero stays refuted.
#[test]
fn contract_summarized_callee_is_not_screened() {
    let func = load("d5_div_one_bad");
    let (callee, key) = sole_callee(&func);
    let db = one_summary(&callee, Formula::Eq(Box::new(result_int()), Box::new(Formula::Int(1))));
    let (refuted, rows) = refuted_rows_with(func.clone(), census(&func, &[key], &db), db);
    assert!(refuted >= 1, "control: `x / (1 - 1)` really divides by zero");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// The COST of the rule, pinned on purpose: the same genuine bug, but `one`'s
/// injected `ensures result <= 1` only BOUNDS the result, so a model over it is
/// not known to be a run and the row is held (a fail-closed `Unknown`, still a
/// strict-build error) rather than reported `Failed`.
#[test]
fn a_bounding_contract_does_not_pin_even_over_a_genuine_bug() {
    let func = load("d5_div_one_bad");
    let (callee, key) = sole_callee(&func);
    let db = one_summary(&callee, Formula::Le(Box::new(result_int()), Box::new(Formula::Int(1))));
    let (refuted, rows) = refuted_rows_with(func.clone(), census(&func, &[key], &db), db);
    assert!(refuted >= 1, "control: ay refutes the row");
    assert!(rows.iter().all(|(_, reason)| reason.is_some()), "{rows:?}");
}

/// The census is keyed by `CalleeIdentity`'s `DefId` half, never by a string:
/// a census naming some OTHER local item screens nothing here.
#[test]
fn census_is_keyed_by_identity_not_by_name() {
    let func = load("d5_shift_via_guard");
    let (_, (krate, index)) = sole_callee(&func);
    let (refuted, rows) = refuted_rows(
        func.clone(),
        census(&func, &[(krate, index.wrapping_add(1))], &SummaryDatabase::new()),
    );
    assert!(refuted >= 1);
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
    let (_, rows) = refuted_rows(
        func.clone(),
        census(&func, &[(krate.wrapping_add(1), index)], &SummaryDatabase::new()),
    );
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// A census on a context owned by ANOTHER function is not this function's
/// census; it must not be lent (the `VcgenContext` owner discipline).
#[test]
fn census_of_another_function_is_not_lent() {
    let func = load("d5_shift_via_guard");
    let (_, key) = sole_callee(&func);
    let foreign = VcgenContext::for_function("fx::some_other_function")
        .with_local_call_dest_screen(LocalCallDestScreen::new([key], &SummaryDatabase::new()));
    let (_, rows) = refuted_rows(func.clone(), foreign);
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// The held row really is the one whose query mentions the call result `_3`
/// (the path guard), and the scope's answer is a function of the row alone:
/// asking twice gives the same answer.
#[test]
fn held_row_mentions_the_call_result() {
    let func = load("d5_shift_via_guard");
    let (_, key) = sole_callee(&func);
    let (_, rows) = refuted_rows(func.clone(), census(&func, &[key], &SummaryDatabase::new()));
    assert!(!rows.is_empty());
    for (vc, reason) in &rows {
        let names: FxHashSet<String> =
            vc.formula.free_variables().iter().map(|v| v.as_str().to_string()).collect();
        assert!(names.contains("_3"), "the held row mentions the call result: {names:?}");
        assert!(reason.is_some());
    }
}

// ---------------------------------------------------------------------------
// Injected is not pinned (2026-09-28): the `p_falsefail` shapes.
// ---------------------------------------------------------------------------

fn int(name: &str) -> Formula {
    Formula::Var(name.into(), Sort::Int)
}

/// The callee's summary as the compiler's postcondition-composition mint builds
/// it for a same-crate callee whose rows all proved: formals in declaration
/// order, the AUTHORED `requires` (spelled here from the fixture source, not
/// read off the extraction's `preconditions`, which also carries the formals'
/// type-range facts), and each `ensures` as a verified, reusable clause.
fn minted_summary(
    callee_fixture: &str,
    requires: &[Formula],
    ensures: &[Formula],
) -> (String, SummaryDatabase) {
    let callee = load(callee_fixture);
    let formals: Vec<String> = (1..=callee.body.arg_count)
        .map(|index| {
            callee.body.locals[index].name.clone().expect("the fixture's formals are named")
        })
        .collect();
    assert_eq!(
        callee.postconditions, ensures,
        "{callee_fixture}: the spelled `ensures` is the extraction's own"
    );
    let mut summary = FunctionSummary::new(callee.def_path.clone()).with_param_names(formals);
    for pre in requires {
        assert!(callee.preconditions.contains(pre), "{callee_fixture}: {pre:?} is authored");
        summary = summary.with_precondition(pre.clone());
    }
    for post in ensures {
        summary = summary.with_verified_callee_postcondition(post.clone());
    }
    let mut db = SummaryDatabase::new();
    db.insert(summary);
    (callee.def_path, db)
}

/// `smax`: `requires b <= a`, `ensures result <= a`.
fn smax_contract() -> (Vec<Formula>, Vec<Formula>) {
    (
        vec![Formula::Le(Box::new(int("b")), Box::new(int("a")))],
        vec![Formula::Le(Box::new(int("_0")), Box::new(int("a")))],
    )
}

/// `umax`: `ensures result >= a` only.
fn umax_contract() -> (Vec<Formula>, Vec<Formula>) {
    (vec![], vec![Formula::Ge(Box::new(int("_0")), Box::new(int("a")))])
}

/// `three`: `ensures result == 3` only.
fn three_contract() -> (Vec<Formula>, Vec<Formula>) {
    (vec![], vec![Formula::Eq(Box::new(int("_0")), Box::new(Formula::Int(3)))])
}

/// Generate `caller` WITH `callee`'s minted summary and the census built from
/// the same DB; return ay's refuted rows and the screen's answer for each.
fn contract_rows(
    caller: &str,
    callee_fixture: &str,
    (requires, ensures): (Vec<Formula>, Vec<Formula>),
) -> (usize, Vec<(VerificationCondition, Option<String>)>) {
    let func = load(caller);
    let (callee, key) = sole_callee(&func);
    let (minted, db) = minted_summary(callee_fixture, &requires, &ensures);
    assert_eq!(callee, minted, "the summary is keyed by the call's own callee string");
    assert!(
        db.postcondition_injecting_names().any(|name| name == callee),
        "{caller}: the premise — `{callee}`'s ensures IS injected at the call"
    );
    refuted_rows_with(func.clone(), census(&func, &[key], &db), db)
}

/// THE MEASURED FALSE REFUTATION. Positive control: ay refutes `3 - r` under the
/// injected `3 <= a -> r <= a` (the model `r < a`). The screen holds every such
/// row, naming `smax`.
#[test]
fn a_guarded_bounding_contract_does_not_pin_dead_else_s() {
    let (refuted, rows) = contract_rows("d5_dead_else_s", "d5_smax", smax_contract());
    assert!(refuted >= 1, "control: the contract-level model exists (`r < a`)");
    for (vc, reason) in &rows {
        let reason = reason.as_deref().unwrap_or_else(|| {
            panic!("a model over `smax`'s bounded result is not an execution: {vc:?}")
        });
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
        assert!(reason.contains("fx::smax"), "{reason}");
    }
}

/// No guard involved: an unguarded bound (`ensures result >= a`) is the same
/// false refutation, so "never treat a GUARDED callee as pinning" alone would
/// not have closed it.
#[test]
fn an_unguarded_bounding_contract_does_not_pin_dead_else_u() {
    let (refuted, rows) = contract_rows("d5_dead_else_u", "d5_umax", umax_contract());
    assert!(refuted >= 1, "control: the contract-level model exists (`r > a`)");
    assert!(rows.iter().all(|(_, reason)| reason.is_some()), "{rows:?}");
}

/// A determining contract (`ensures result == 3`, no `requires`) pins `r`: the
/// genuine `2 - r` overflow keeps its refutation.
#[test]
fn a_determining_contract_keeps_a_genuine_refutation() {
    let (refuted, rows) = contract_rows("d5_three_bad", "d5_three", three_contract());
    assert!(refuted >= 1, "control: `2 - 3` really overflows");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// A genuinely FALSE postcondition still fails: `four`'s own `ensures result ==
/// 4` over a body returning the pinned `three()`.
#[test]
fn a_genuinely_false_caller_postcondition_still_fails() {
    let (refuted, rows) = contract_rows("d5_four", "d5_three", three_contract());
    assert!(refuted >= 1, "control: `result == 4` is false of `three()`");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

/// A genuinely false postcondition with no call at all (`smax_bad`'s own
/// `ensures result < a`, false at `b <= a`): the call-destination screen has
/// nothing to say about it.
#[test]
fn a_genuinely_false_callee_postcondition_still_fails() {
    let func = load("d5_smax_bad");
    let context = census(&func, &[], &SummaryDatabase::new());
    let (refuted, rows) = refuted_rows(func, context);
    assert!(refuted >= 1, "control: `result < a` is false of `smax_bad`");
    assert!(rows.iter().all(|(_, reason)| reason.is_none()), "{rows:?}");
}

// ---------------------------------------------------------------------------
// Mentioned is not depended on (2026-09-29, review blocker 2 of cb/track-b).
// ---------------------------------------------------------------------------
//
// Once a bounding callee stopped pinning its result, the whole-query screen
// held every row whose query CARRIED the call's own injected `pre → post`
// fact, not only the rows that read the result: `let _r = smax(20, 3); a - 10`
// read `[overflow:sub] UNKNOWN` instead of FAILED at `a = 0`. The rows below
// are the compiler's own MIR of `tests/fixtures/d5_dependence_fx.rs` (stage-1
// trustc at cb/track-b's stage-1 bless commit, whose D5-A share main carries
// as `d08ab772554`; `--crate-name fx`, same dump flags as above), each
// generated WITH the callee's minted summary, like the rows above. Both
// directions are pinned: a genuine bug the result cannot reach keeps its
// refutation, and every way a result can reach a row — data, a value chosen
// by a branch, the reachability of the violation itself — still holds it.

/// Every refuted row of `caller` must be a live ay SAT and NOT held.
fn assert_not_held(caller: &str, callee_fixture: &str, contract: (Vec<Formula>, Vec<Formula>)) {
    let (refuted, rows) = contract_rows(caller, callee_fixture, contract);
    assert!(refuted >= 1, "{caller}: control — ay must refute the genuine bug");
    for (vc, reason) in &rows {
        assert!(
            reason.is_none(),
            "{caller}: a refutation the call result cannot reach must stand: {reason:?}\n{vc:?}"
        );
    }
}

/// Every refuted row of `caller` must be held, naming the callee.
fn assert_dependent_held(
    caller: &str,
    callee_fixture: &str,
    contract: (Vec<Formula>, Vec<Formula>),
    callee_path: &str,
) {
    let (refuted, rows) = contract_rows(caller, callee_fixture, contract);
    assert!(refuted >= 1, "{caller}: control — the contract-level model exists");
    for (vc, reason) in &rows {
        let reason = reason.as_deref().unwrap_or_else(|| {
            panic!("{caller}: a model over `{callee_path}`'s bounded result is not an execution: {vc:?}")
        });
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
        assert!(reason.contains(callee_path), "{reason}");
    }
}

/// THE REVIEWER'S COUNTEREXAMPLE (`rvB/mb/m2.rs::unused_result`): the result
/// is never read, and `a - 10` really underflows at `a = 0`.
#[test]
fn an_unread_bounded_result_keeps_a_genuine_refutation() {
    assert_not_held("d5_dep_unused_result", "d5_smax", smax_contract());
}

/// `rvB/mb/m1.rs::indep_after`: the result is read, but only by a branch AFTER
/// the underflow, which it can neither reach nor feed.
#[test]
fn a_result_read_only_after_the_violation_keeps_a_genuine_refutation() {
    assert_not_held("d5_dep_indep_after", "d5_smax", smax_contract());
}

/// The call's bound `r >= a` shares the parameter `a` with the underflow: a
/// fact every run satisfies, not a dependence.
#[test]
fn a_bound_sharing_a_parameter_with_the_violation_keeps_a_genuine_refutation() {
    assert_not_held("d5_dep_indep_after_shared", "d5_umax", umax_contract());
}

/// DATA: `w = r + 1; w - 10`. `smax(20, 3)` is 20, so this never underflows;
/// the bound `r <= 20` lets ay pick `r = 0`.
#[test]
fn a_violation_computed_from_the_result_is_held() {
    assert_dependent_held("d5_dep_data_dep", "d5_smax", smax_contract(), "fx::smax");
}

/// CONTROL of a value: `v = if r > 100 { 10 } else { 0 }; a - v`. `umax(a, 3)`
/// exceeds 100 only when `a` does, so `a - v` never underflows; ay picks
/// `a = 0, r = 101`.
#[test]
fn a_value_chosen_by_a_branch_on_the_result_is_held() {
    assert_dependent_held("d5_dep_ctrl_dep_value", "d5_umax", umax_contract(), "fx::umax");
}

/// CONTROL of reachability: `if r > 100 { a - 10 }`. The violation's own
/// operands never read `r`, but whether it runs does.
#[test]
fn a_violation_reached_only_through_a_branch_on_the_result_is_held() {
    assert_dependent_held("d5_dep_ctrl_dep_reach", "d5_umax", umax_contract(), "fx::umax");
}

// ---------------------------------------------------------------------------
// S1-S3 (2026-10-16): ungrounded generic refutations, held independent of any
// loop contract or call-destination census.
//
// Fixtures are the compiler's own extracted MIR of `fixtures/srh_*_fx.rs`
// (`srh_foreign_value_fx.rs` against `srh_foreign_value_dep.rs` built
// `--crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir`), captured with
//
// ```text
// trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//        -Ztrust-dump=mir-only:<dir> --crate-name fx <file>.rs
// ```
//
// on the sealed `trust-150efe4a` toolchain, and generated here WITH the hardened
// profile (`targo trust check`'s default), so the `HardenedBoundary` twins —
// rows with no obligation record — are in the inventory too. Every HOLD case
// first shows ay really refutes a row; every KEEP case is a genuine bug whose
// refutation must survive (the negative control of the screen beside it).
// ---------------------------------------------------------------------------

/// Every row in-process ay refutes for `name`, generated with the hardened twins,
/// with the generic scope's answer for it.
fn hardened_refuted_rows(name: &str) -> Vec<(VerificationCondition, Option<String>)> {
    let func = load(name);
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = VcgenContext::for_function(func.def_path.clone());
            let (solver_vcs, discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &SummaryDatabase::new(),
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
            let router = test_router::deterministic_test_router();
            solver_vcs
                .iter()
                .filter(|vc| {
                    matches!(
                        router.verify_all(std::slice::from_ref(*vc)).into_iter().next().expect("one").1,
                        VerificationResult::Failed { .. }
                    )
                })
                .map(|vc| (vc.clone(), scope.rejection_reason(vc)))
                .collect()
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn is_kind(vc: &VerificationCondition, kind: &str) -> bool {
    use trust_types::VcKind;
    match kind {
        "shift" => matches!(vc.kind, VcKind::ShiftOverflow { .. }),
        "overflow" => matches!(vc.kind, VcKind::ArithmeticOverflow { .. }),
        "slice" => matches!(vc.kind, VcKind::SliceBoundsCheck),
        "index" => matches!(vc.kind, VcKind::IndexOutOfBounds),
        "rem" => matches!(vc.kind, VcKind::RemainderByZero),
        "hardened" => matches!(vc.kind, VcKind::HardenedBoundary { .. }),
        _ => unreachable!("unknown kind label {kind}"),
    }
}

/// `name` has at least one refuted row of each `kinds`, and EVERY refuted row is
/// held with a reason containing `needle`.
fn assert_all_held(name: &str, kinds: &[&str], needle: &str) {
    let rows = hardened_refuted_rows(name);
    for kind in kinds {
        assert!(
            rows.iter().any(|(vc, _)| is_kind(vc, kind)),
            "{name}: control — ay must refute a `{kind}` row: {rows:?}"
        );
    }
    for (vc, reason) in &rows {
        let reason = reason
            .as_deref()
            .unwrap_or_else(|| panic!("{name}: an ungrounded SAT must be withheld: {vc:?}"));
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
        assert!(reason.contains(needle), "{name}: expected `{needle}` in: {reason}");
    }
}

/// `name` has a refuted row of `kind` and every such row is kept (not held).
fn assert_kind_kept(name: &str, kind: &str) {
    let rows = hardened_refuted_rows(name);
    let of_kind: Vec<_> = rows.iter().filter(|(vc, _)| is_kind(vc, kind)).collect();
    assert!(!of_kind.is_empty(), "{name}: control — ay must refute a `{kind}` row: {rows:?}");
    for (vc, reason) in of_kind {
        assert!(
            reason.is_none(),
            "{name}: a genuine `{kind}` refutation must be kept: {reason:?} {vc:?}"
        );
    }
}

/// S1, carry390's shape: the shift's block has more than 64 root paths, its path
/// list collapses, and both the shift row and its hardened twin were refuted with
/// two early returns firing in the model. Both are held.
#[test]
fn s1_a_collapsed_path_condition_is_held_with_its_twin() {
    assert_all_held("srh_validate_carry", &["shift", "hardened"], "path condition collapsed");
}

/// S1 negative control: `x >> s` with no path at all is a genuine `s = 32` bug.
#[test]
fn s1_an_unconditional_shift_keeps_its_refutation() {
    assert_kind_kept("srh_shift_entry", "shift");
    assert_kind_kept("srh_shift_entry", "hardened");
}

/// S2, utf8simd's shape: `i + 3` reads the loop-header join of `i`, which has no
/// defining equation. Pins the SPELLING too: the symbol the reason names is the
/// oracle's, and it must occur verbatim in the solver query.
#[test]
fn s2_a_loop_carried_join_is_held_and_spelled_as_the_query_spells_it() {
    let rows = hardened_refuted_rows("srh_bulk_3byte");
    assert!(rows.iter().any(|(vc, _)| is_kind(vc, "overflow")), "control: {rows:?}");
    for (vc, reason) in &rows {
        let reason = reason.as_deref().unwrap_or_else(|| panic!("must be withheld: {vc:?}"));
        assert!(reason.contains("loop-carried value at a loop header"), "{reason}");
        let symbol = reason.split('`').nth(1).expect("the reason names the symbol");
        assert!(symbol.starts_with("i#"), "the join is `i`'s: {symbol}");
        let mut named = false;
        vc.formula.visit(&mut |f| {
            if matches!(f, Formula::Var(n, _) if n == symbol) {
                named = true;
            }
        });
        assert!(named, "`{symbol}` must be a variable of the query: {:?}", vc.formula);
    }
}

/// S2 negative control: `x + 1` before the loop never reads the join; `x = 255`
/// is a genuine refutation in a body that HAS loop-carried joins.
#[test]
fn s2_a_query_that_does_not_name_the_join_keeps_its_refutation() {
    assert_kind_kept("srh_pre", "overflow");
}

/// S3, dispatch745's twin: `c.len() + 1` over a foreign `Cap::len`. The L0 row is
/// declined in generation (`UnmodeledCalleeReturn`); the hardened twin has no
/// obligation record and used to be refuted with `len = u64::MAX`.
#[test]
fn s3_a_hardened_twin_over_a_foreign_call_value_is_held() {
    assert_all_held("srh_at_cap", &["hardened"], "unmodelled return of a foreign call");
}

/// S3, dispatch751/752: `position` over a REASSIGNED slice has no length fact, so
/// the payload is free. The L0 pass keeps its `Iterator::next`-only candidate set
/// (it rewrites rows), so the slice rows reach the solver and are refuted; the
/// bridge reads EVERY foreign value call's payload and holds them. Not vacuous:
/// ay must refute at least one slice row, and one must be held on the `position`
/// payload itself (S3); any other refuted row of the body is held too (S2 holds
/// the rows that also read the loop-carried `rest`).
#[test]
fn s3_a_reseated_position_payload_is_held() {
    let rows = hardened_refuted_rows("srh_split_fields");
    let slices: Vec<_> = rows.iter().filter(|(vc, _)| is_kind(vc, "slice")).collect();
    assert!(!slices.is_empty(), "control — ay must refute a `rest[..]` slice row: {rows:?}");
    assert!(
        slices.iter().any(|(_, reason)| reason
            .as_deref()
            .is_some_and(|r| r.contains("unmodelled return of a foreign call (`_6@1.0`)"))),
        "a slice row must be held on the unmodelled `position` payload `_6@1.0`: {slices:?}"
    );
    for (vc, reason) in &rows {
        let reason = reason.as_deref().unwrap_or_else(|| panic!("must be withheld: {vc:?}"));
        assert!(reason.starts_with(GENERIC_REFUTATION_HELD_PREFIX), "{reason}");
    }
}

/// S3 negative controls: `255 + (val() | 1)` overflows for every value, and the
/// NON-reseated `s[k + 1]` after `position` is pinned by the yield fact and really
/// out of bounds at `k = len - 1`.
#[test]
fn s3_genuine_refutations_over_foreign_values_are_kept() {
    assert_kind_kept("srh_always_overflows", "overflow");
    assert_kind_kept("srh_after_semicolon", "slice");
}

/// S3's measured capability cost (falsification gate, 2026-10-20): two mutants
/// main refutes only through a counterexample that is NOT an execution are now
/// held. `checked_arith_match`'s `v + 1` was refuted with `a = 0, b = 0` and the
/// `checked_add` payload `v = u32::MAX`; `charindices_plus_one_boundary_oob`'s
/// `i + 1` with the `char_indices` index `i = usize::MAX` on an EMPTY string.
/// Neither call's payload is modelled, so the solver's value is free; recovery is
/// a model of the call (`Some(v) => v == a + b`; a char index below the length),
/// not a narrower screen. Pinned so the cost stays visible.
#[test]
fn s3_holds_mutant_refutations_whose_model_is_not_an_execution() {
    assert_all_held(
        "srh_mut_checked_arith_match",
        &["overflow"],
        "unmodelled return of a foreign call",
    );
    assert_all_held(
        "srh_mut_charindices_plus_one_boundary_oob",
        &["overflow"],
        "unmodelled return of a foreign call",
    );
}

/// `name` has at least one refuted row of `kind` that the generic scope KEEPS
/// (FAILED, not held): a genuine bug must keep a counterexample.
fn assert_some_kind_kept(name: &str, kind: &str) {
    let rows = hardened_refuted_rows(name);
    assert!(
        rows.iter().any(|(vc, reason)| is_kind(vc, kind) && reason.is_none()),
        "{name}: a genuine `{kind}` refutation must survive the generic scope: {:?}",
        rows.iter()
            .map(|(vc, r)| (vc.kind.description(), vc.location.line_start, r))
            .collect::<Vec<_>>()
    );
}

/// S2 negative control INSIDE a loop (review 2026-10-16): the countdown mutant's
/// `offset -= 4` underflows on the fifth pass (`LEN 19, T = 5: 19 - 20 < 0`, the
/// REAL underflow at `n = u64::MAX`, `countdown_trip_tests`). Its query names the
/// loop-carried join of `offset`, and a value the join takes within the first
/// passes satisfies it, so the refutation is kept. Holding every row that names a
/// join lost all ten of this fixture's refutations.
#[test]
fn s2_a_genuine_in_loop_underflow_keeps_its_refutation() {
    assert_some_kind_kept("countdown_short_buffer_mir", "overflow");
    assert_some_kind_kept("countdown_short_buffer_mir", "hardened");
}

/// S2 negative controls on two more genuine in-loop bugs that name a loop-header
/// join: an escaped-seam index bug in a loop whose borrow is reseated, and the gcd
/// falsification mutant's unguarded `a % b` (`b` loop-carried, zero on a pass).
#[test]
fn s2_genuine_in_loop_bugs_keep_their_refutations() {
    assert_some_kind_kept("escaped_seam_rev13_fs_loop_borrow_reseat_bug_o1_mir", "index");
    assert_some_kind_kept("nat_gcd_unguarded_rem_mutant_mir", "rem");
}

/// S2 negative controls DEEPER than the shallow walk's passes (falsification gate,
/// 2026-10-20): four `tests/trust-falsification/mutant/loop_*` mutants overflow a
/// `u8` counter incremented from 0, which needs 256 passes. With 32 passes and no
/// horizon every one was held and the gate scored it an UNCAUGHT MUTANT; the
/// horizon carries the still-moving counter on, so the refutation is kept.
/// Fixtures: each mutant's MIR from the stage 2 of the land merge,
/// `-Cpanic=abort -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir>`.
#[test]
fn s2_a_u8_counter_past_the_shallow_passes_keeps_its_refutation() {
    for name in [
        "srh_mut_loop_add_on_none_arm",
        "srh_mut_loop_path_skips_next",
        "srh_mut_loop_empty_sibling_zero_trip",
        "srh_mut_loop_iterator_rebuilt_every_iteration",
    ] {
        assert_some_kind_kept(name, "overflow");
    }
}

/// A compiler extraction BUNDLE (a JSON array of bodies), for the rows whose
/// callee summary is derived from other bodies of the same crate.
fn load_bundle(name: &str) -> Vec<VerifiableFunction> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("fixture bundle `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("fixture bundle `{name}` must deserialize: {e}"))
}

/// `if is_zero(s) { x / s.n }` REALLY divides by zero: it divides exactly when
/// `s.n == 0`. `is_zero(s: &S) -> bool { n_of(s) == 0 }` is a same-crate FREE
/// fn, so the census screens its destination `_3` — and the refuted query
/// mentions `_3` through the path guard. What makes the witness genuine is the
/// field-read summary (`generate::return_field_summary`): it models `_3 ⇔
/// ((*s).n == 0)` at THIS call, so `_3 = true` is forced by `s.n = 0`, not
/// chosen.
///
/// The D5-A screen learns that the destination is modeled ONLY through its
/// mirror of the field-read producer (`return_field_call_is_modeled` in
/// `refutation_scope::unpinned_local_call_dests`). Delete that mirror and this
/// genuine refutation is over-held as an Unknown: that is the failure this row
/// pins.
///
/// Fixtures: `tests/fixtures/d5_field_fx.rs`, compiled as `field_fx.rs` with
///
/// ```text
/// trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
///        [-Zmir-opt-level=0] -Ztrust-dump=mir-only:<dir> field_fx.rs
/// ```
///
/// and each directory's bodies collected into one array sorted by `def_path`.
/// The summaries are derived from the PRE-optimization bodies and the caller is
/// verified from the default-level one, as the compiler does (see
/// `return_field_summary_realmir.rs`).
#[test]
fn field_read_summarised_callee_keeps_its_refutation() {
    let preopt = load_bundle("d5_field_fx_preopt");
    let func = load_bundle("d5_field_fx_opt")
        .into_iter()
        .find(|f| f.def_path == "field_fx::div_when_zero")
        .expect("fixture `field_fx::div_when_zero`");
    let (callee, key) = sole_callee(&func);
    assert_eq!(callee, "field_fx::is_zero", "the one identified call is the screened helper");
    let field_summaries = trust_vcgen::compute_return_field_summaries(&preopt);
    assert!(
        field_summaries.contains_key(&callee),
        "control: `is_zero` must carry a field-read summary: {field_summaries:?}"
    );
    let context = census(&func, &[key], &SummaryDatabase::new()).with_callee_summaries(
        CalleeSummaryContext::default().with_return_field_summaries(field_summaries),
    );
    let (refuted, rows) = refuted_rows(func.clone(), context);
    assert!(refuted >= 1, "control: `x / s.n` on the `s.n == 0` branch really divides by zero");
    assert!(
        rows.iter().all(|(_, reason)| reason.is_none()),
        "a SAT over a destination the field-read summary models is a genuine refutation and \
         must not be held (is the D5-A mirror `return_field_call_is_modeled` still consulted?): \
         {rows:?}"
    );
    // And WITHOUT the summaries the same row is held: the model is what decides.
    let (_, rows) = refuted_rows(func.clone(), census(&func, &[key], &SummaryDatabase::new()));
    assert!(rows.iter().any(|(_, reason)| reason.is_some()), "{rows:?}");
}
