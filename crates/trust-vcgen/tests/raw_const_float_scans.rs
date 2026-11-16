// Regression: the FLOAT lane must not bound a float that a `&raw const` pointer
// can have rewritten.
//
// The float lane decides `FloatOverflowToInfinity` by interval tracing
// (`float_range`) and, when it can bound an operation's result below the width's
// overflow margin, emits NO obligation for it. So a stale bound does not prove a
// row — it deletes it, and nothing downstream (no solver, no kernel re-check) ever
// sees the operation. Each body in tests/data/raw_const_float_scans.rs returns
// `inf` natively (-O0 and -O3), and before 2026-09-30 each had no
// `FloatOverflowToInfinity` row on any lane: stage 1 `a7ea88986d` reports none for
// them and one (UNKNOWN) for the `&raw mut` control, and this file measured the
// same on origin/main `8ad8af8ec9` and on the union merge `160b8cc269`.
//
// Cause: the lane's stability scans counted `&mut` / `&raw mut` as write channels
// and missed `&raw const` (a write through `&raw const x as *mut _` is defined
// under Tree Borrows for a `mut` binding or memory behind `&mut`; Trust assumes
// only what Stacked AND Tree Borrows both validate):
//
//   * `float_whole_local_defs` — a local's def set (`v = 2.0` was its only def);
//     also read as the stability of a place BEHIND a parameter by the abs-guard
//     lane (`stable_base` on `(*s)`);
//   * `param_place_is_entry_stable` — a contract bound on a parameter field
//     (`s.0 <= 2.0`) is an ENTRY fact;
//   * the masked-element lane — one Call init and no aliasing store reaching the
//     read.
//
// Closed by routing each through the POINTER rule of the write-channel family
// (`generate::borrow_write_target`: `&mut`, `&raw mut`, `&raw const` of ANY place
// rooted at the local, a `Deref` included, except a `&raw const` through a shared
// reference to pointer-free `Freeze` data — these scans ask about what a parameter
// points to, where the slot rule's `Deref` exclusion is the wrong test). Main's H2
// fix (96db9eb9f0) routed the same three scans through the same rule independently;
// this file is the union lane's real-MIR pin of them.
//
// Fixtures: real MIR dumped by stage 1 `a7ea88986d` from
// tests/data/raw_const_float_scans.rs (the command is in that file's header;
// nothing in the dumps was edited).
use std::sync::Arc;

use trust_types::*;
use trust_vcgen::{FunctionSummary, SummaryDatabase, generate_vcs};

#[path = "support/test_router.rs"]
mod test_router;

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/raw_const_float_scans_{name}_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{name}` must deserialize: {e}"))
}

/// The summary database the compiler hands the entry: every LOCAL callee whose
/// return value the float lane may trace, with its extracted body (the
/// masked-element lane re-traces `make_cols`' body to bound `m.c[0]`).
fn summaries() -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(
        FunctionSummary::new("raw_const_float_scans::make_cols")
            .with_param_names(vec![])
            .with_extracted_body(Arc::new(fixture("make_cols"))),
    );
    db
}

fn is_float_overflow(kind: &VcKind) -> bool {
    matches!(kind, VcKind::FloatOverflowToInfinity { .. })
}

fn is_discharged(vc: &VerificationCondition, res: &VerificationResult) -> bool {
    matches!(res, VerificationResult::Proved { .. }) || trust_certify::certify_vc(vc).is_some()
}

/// Every `FloatOverflowToInfinity` row the COMPILER's entry emits for `func`
/// (`generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops`,
/// hardened ON, the [`summaries`] database), pre-classified rows included, each
/// with "is it discharged" (the interval backend's proof, as the compiler keeps
/// it, else deterministic in-process ay; or a kernel certificate).
fn compiler_float_rows(func: &VerifiableFunction) -> Vec<(String, bool)> {
    let func = func.clone();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let context = trust_vcgen::VcgenContext::for_function(func.def_path.clone());
            let db = summaries();
            let (solver_vcs, preclassified) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &db,
                    true,
                    &context,
                    &std::collections::HashSet::<(BlockId, usize)>::new(),
                );
            let interval = trust_router::Router::with_backends(vec![Box::new(
                trust_router::interval_backend::IntervalBackend,
            )]);
            let ay = test_router::deterministic_test_router();
            let decide = |vc: &VerificationCondition| {
                let one = |r: &trust_router::Router| {
                    let (_, res) = r
                        .verify_all(std::slice::from_ref(vc))
                        .into_iter()
                        .next()
                        .expect("one verdict per VC");
                    res
                };
                let by_interval = one(&interval);
                if matches!(by_interval, VerificationResult::Proved { .. }) {
                    by_interval
                } else {
                    one(&ay)
                }
            };
            let decided = solver_vcs.into_iter().map(|vc| {
                let res = decide(&vc);
                (vc, res)
            });
            preclassified
                .into_iter()
                .chain(decided)
                .filter(|(vc, _)| is_float_overflow(&vc.kind))
                .map(|(vc, res)| (format!("{:?} @{:?}", vc.kind, vc.location), is_discharged(&vc, &res)))
                .collect()
        })
        .expect("spawn")
        .join()
        .expect("generation thread")
}

/// A body whose float op overflows to `inf` when run must KEEP that op's
/// `FloatOverflowToInfinity` obligation, undischarged, on the compiler's entry —
/// and, where the per-statement lane emits the row at all, there too.
fn assert_float_overflow_is_not_bounded_away(name: &str) {
    let func = fixture(name);
    let rows = compiler_float_rows(&func);
    assert!(
        !rows.is_empty(),
        "{name}: the body returns `inf` when run, and the compiler entry emitted NO \
         `FloatOverflowToInfinity` row — the float lane bounded a value a `&raw const` \
         pointer rewrote"
    );
    assert!(
        rows.iter().all(|(_, ok)| !ok),
        "{name}: a float op that overflows at runtime has a DISCHARGED row: {rows:?}"
    );
    let per_statement: Vec<_> =
        generate_vcs(&func).into_iter().filter(|vc| is_float_overflow(&vc.kind)).collect();
    assert!(
        !per_statement.is_empty(),
        "{name}: `generate_vcs` emitted no `FloatOverflowToInfinity` row either"
    );
}

/// `let mut v: f64 = 2.0; let p = &raw const v as *mut f64; *p = f64::MAX; v * 4.0`
/// (the union review's `rc_float_mut_direct`; its `rc_float_local` is the
/// immutable-binding spelling, UB by the Reference, with the same extracted body).
#[test]
fn a_float_local_written_through_raw_const_is_not_bounded_by_its_literal() {
    assert_float_overflow_is_not_bounded_away("float_local_written_directly");
}

/// The review's measured case: the write is done by a callee
/// (`poke_f64(&raw const v as *mut f64)`).
#[test]
fn a_float_local_written_by_a_call_through_raw_const_is_not_bounded() {
    assert_float_overflow_is_not_bounded_away("float_local_written_by_a_call");
}

/// binary32: `v + f32::MAX` after a callee sets `v = f32::MAX`.
#[test]
fn an_f32_local_written_by_a_call_through_raw_const_is_not_bounded() {
    assert_float_overflow_is_not_bounded_away("f32_local_written_by_a_call");
}

/// CONTROL: the same program through `&raw mut`, the channel the scans always
/// named. The row exists before and after the fix.
#[test]
fn a_float_local_written_through_raw_mut_keeps_its_row() {
    assert_float_overflow_is_not_bounded_away("float_local_written_through_raw_mut");
}

/// `param_place_is_entry_stable`: the contract bound `|s.0| <= 2` is an ENTRY
/// fact, and the body rewrites `s` through `&raw const s` before reading `s.0`
/// (the projected read takes `contract_range`, not the def-set path). By-value
/// parameter and by-value `self`.
#[test]
fn a_contract_bounded_parameter_rewritten_through_raw_const_is_not_bounded() {
    assert_float_overflow_is_not_bounded_away("contract_bounded_param_written_through_raw_const");
    assert_float_overflow_is_not_bounded_away("contract_bounded_self_written_through_raw_const");
}

/// The abs-guard lane (`float_abs_guard_magnitude_bounds`' `stable_base`, which
/// asks `float_whole_local_defs` about `(*s)`): `|*s| > 1e-20` floors the divisor
/// of `1.0 / *s`, and a callee then sets `*s = 1e-310` through `&raw const *s` — a
/// `Deref` place, so the SLOT rule rightly does not list it; the pointer rule must.
#[test]
fn an_abs_guarded_pointee_rewritten_through_raw_const_is_not_floored() {
    assert_float_overflow_is_not_bounded_away("abs_guarded_pointee_written_through_raw_const");
}

/// The masked-element lane: `m = make_cols(); m.c[1] = 3.0;` and a callee handed
/// `&raw const m` writes `m.c[0] = f64::MAX`. With `make_cols`' body in the
/// summary database (as the compiler has it) the lane re-traces the init and
/// bounded `m.c[0]` by `1.0`.
#[test]
fn a_masked_element_rewritten_through_raw_const_is_not_bounded_by_its_init() {
    assert_float_overflow_is_not_bounded_away("masked_element_written_by_a_call");
}
