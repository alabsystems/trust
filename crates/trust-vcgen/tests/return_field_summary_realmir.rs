//! REAL-MIR pin: a same-crate `bool` callee that compares a field through a
//! getter is summarised, so bit-vec's `pop` stops being refuted (TRUST-10).
//!
//! # What was wrong
//!
//! bit-vec 0.9.1 (`src/lib.rs:1638`):
//!
//! ```text
//! pub fn len(&self) -> usize { self.nbits }
//! pub fn is_empty(&self) -> bool { self.len() == 0 }
//! pub fn pop(&mut self) -> Option<bool> {
//!     self.ensure_invariant();
//!     if self.is_empty() { None } else { let i = self.nbits - 1; .. }
//! }
//! ```
//!
//! was reported, and the reduced `pop` below still is on the installed toolchain
//! (`trustc 0.10.0+g450403669`, `-Ztrust-policy=advisory`):
//!
//! ```text
//! [overflow:sub] FAILED (ay-in-process); counterexample: _2 = false, …, self*.1#e_s0_t = 0
//! ```
//!
//! `is_empty()` false at `nbits == 0` is not an execution. Nothing modeled the
//! callee's result: the bool-predicate summaries cover enum-TAG predicates only.
//! `generate::return_field_summary` now derives `len: ret == (*self).nbits` and
//! `is_empty: ret ⇔ ((*self).nbits == 0)` from the bodies and states the second
//! over the caller's spelling of the field, pre- and post-call.
//!
//! # Fixtures
//!
//! Both bundles are the compiler's own extraction of the source below, captured
//! with
//!
//! ```text
//! trustc --edition 2021 --crate-type lib -Ztrust-policy=advisory \
//!        [-Zmir-opt-level=0] -Ztrust-dump=mir-only:<dir> field_summary.rs
//! ```
//!
//! `return_field_summary_preopt.json` (`-Zmir-opt-level=0`) carries the
//! PRE-optimization shapes the compiler's crate-wide summary inventory reads
//! (`mir_drops_elaborated_and_const_checked`: `_3 = &(*_1); _2 = len(move _3)`,
//! storage markers); `return_field_summary_opt.json` carries the bodies the
//! compiler VERIFIES at the default level. The summaries are computed from the
//! first and the callers are verified from the second, as the compiler does.
//!
//! ```text
//! pub struct V { storage: Vec<u32>, nbits: usize, cap: usize }
//! impl V {
//!     fn check(&self) { let _ = self.storage.len(); }
//!     pub fn len(&self) -> usize { self.nbits }
//!     pub fn is_empty(&self) -> bool { self.len() == 0 }
//!     pub fn cap_is_zero(&self) -> bool { self.cap == 0 }
//!     pub fn few(&self) -> bool { 3 >= self.len() }
//!     pub fn weird(&self) -> bool { if self.cap > 0 { self.nbits == 0 } else { false } }
//!     pub fn pop(&mut self) -> Option<usize> {
//!         if self.is_empty() { None } else { let i = self.nbits - 1; self.nbits = i; Some(i) }
//!     }
//!     pub fn pop_after_check(&mut self) -> Option<usize> {
//!         self.check();
//!         if self.is_empty() { None } else { let i = self.nbits - 1; self.nbits = i; Some(i) }
//!     }
//!     pub fn last_index(&self) -> Option<usize> {
//!         if self.is_empty() { None } else { Some(self.len() - 1) }
//!     }
//!     pub fn drop_four(&mut self) -> Option<usize> {
//!         if !self.few() { Some(self.nbits - 4) } else { None }
//!     }
//!     pub fn drop_five(&mut self) -> Option<usize> {
//!         if !self.few() { Some(self.nbits - 5) } else { None }
//!     }
//!     pub fn pop_inverted(&mut self) -> Option<usize> {
//!         if self.is_empty() { Some(self.nbits - 1) } else { None }
//!     }
//!     pub fn pop_wrong_field(&mut self) -> Option<usize> {
//!         if self.cap_is_zero() { None } else { Some(self.nbits - 1) }
//!     }
//!     pub fn pop_after_reset(&mut self) -> Option<usize> {
//!         if self.is_empty() { None } else { self.nbits = 0; Some(self.nbits - 1) }
//!     }
//!     pub fn pop_weird(&mut self) -> Option<usize> {
//!         if self.weird() { None } else { Some(self.nbits - 1) }
//!     }
//! }
//! ```
//!
//! # The matrix
//!
//! | caller | why | `[overflow:sub]` |
//! |---|---|---|
//! | `pop` | bit-vec's shape | not REFUTED (was) |
//! | `pop_after_check` | a `&self` call first — bit-vec's `ensure_invariant()` | not REFUTED (was) |
//! | `last_index` | the getter on the caller side too (`self.len() - 1`) | not REFUTED (was) |
//! | `drop_four` | `!few()` = `len > 3`, a swapped and negated comparison | not REFUTED (was) |
//! | `drop_five` | `len > 3` does not cover `- 5` | REFUTED |
//! | `pop_inverted` | the subtraction on the EMPTY branch | REFUTED |
//! | `pop_wrong_field` | the guard compares ANOTHER field | REFUTED |
//! | `pop_after_reset` | `nbits = 0` between the check and the use | REFUTED |
//! | `pop_weird` | a branching callee — no summary, its result stays free | REFUTED |
//!
//! Every REFUTED row is a real panic (each was replayed in the reasoning above:
//! `drop_five` at `nbits == 4`, the rest at `nbits == 0`), so the summary
//! adding a TRUE fact must leave them refuted.
use trust_types::fx::FxHashMap;
use trust_types::{
    BinOp, Projection, Rvalue, Statement, Ty, VcKind, VerifiableFunction, VerificationResult,
};
use trust_vcgen::{ReturnFieldSummary, ReturnFieldValue, SummaryDatabase, VcgenContext};

#[path = "support/test_router.rs"]
mod test_router;

/// Stack for the generation/solver thread; real extracted MIR carries deep
/// recursive `Formula` walks (the same allowance the other realmir files make).
const SOLVER_STACK_BYTES: usize = 64 * 1024 * 1024;

fn bundle(which: &str) -> Vec<VerifiableFunction> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/fixtures/return_field_summary_");
    let text = std::fs::read_to_string(format!("{path}{which}.json"))
        .unwrap_or_else(|e| panic!("fixture bundle `{which}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("fixture bundle `{which}` must deserialize: {e}"))
}

fn pick(funcs: &[VerifiableFunction], name: &str) -> VerifiableFunction {
    funcs
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("fixture `{name}` missing"))
        .clone()
}

fn key(name: &str) -> String {
    format!("field_summary::V::{name}")
}

/// The field-read summaries the compiler would install: derived from the
/// PRE-optimization bodies, as its crate-wide inventory is.
fn summaries() -> FxHashMap<String, ReturnFieldSummary> {
    trust_vcgen::compute_return_field_summaries(&bundle("preopt"))
}

/// The verdict of every `[overflow:sub]` row of the VERIFIED body `name`, under
/// the given field-read summaries, through the compiler's generation entry and
/// the deterministic in-process ay the bridge uses. A row the generator already
/// discharged reports its discharge verdict.
fn sub_rows_of(
    func: VerifiableFunction,
    fields: FxHashMap<String, ReturnFieldSummary>,
) -> Vec<String> {
    std::thread::Builder::new()
        .stack_size(SOLVER_STACK_BYTES)
        .spawn(move || {
            let context = VcgenContext::for_function(func.def_path.clone()).with_callee_summaries(
                trust_vcgen::CalleeSummaryContext::default().with_return_field_summaries(fields),
            );
            let (solver_vcs, discharged) =
                trust_vcgen::generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops(
                    &func,
                    &SummaryDatabase::new(),
                    false,
                    &context,
                    &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
                );
            let is_sub = |kind: &VcKind| {
                matches!(kind, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. })
            };
            let tag = |result: &VerificationResult| match result {
                VerificationResult::Proved { .. } => "PROVED".to_string(),
                VerificationResult::Failed { .. } => "REFUTED".to_string(),
                other => format!("{other:?}").chars().take(24).collect(),
            };
            let router = test_router::deterministic_test_router();
            let mut rows = Vec::new();
            for vc in solver_vcs.iter().filter(|vc| is_sub(&vc.kind)) {
                let verdict = router
                    .verify_all(std::slice::from_ref(vc))
                    .into_iter()
                    .next()
                    .expect("one verdict per VC")
                    .1;
                rows.push(tag(&verdict));
            }
            for (_, verdict) in discharged.iter().filter(|(vc, _)| is_sub(&vc.kind)) {
                rows.push(tag(verdict));
            }
            rows
        })
        .expect("spawn analysis thread")
        .join()
        .expect("analysis thread must not panic")
}

fn sub_rows(name: &str) -> Vec<String> {
    sub_rows_of(pick(&bundle("opt"), name), summaries())
}

fn assert_not_refuted(name: &str) {
    let rows = sub_rows(name);
    assert!(!rows.is_empty(), "{name}: the fixture must produce an `[overflow:sub]` row");
    assert!(
        rows.iter().all(|v| v == "PROVED"),
        "{name}: the subtraction cannot underflow on any execution; a refutation is a \
         counterexample over a free `is_empty()`/`few()` result: {rows:?}"
    );
}

fn assert_refuted(name: &str) {
    let rows = sub_rows(name);
    assert!(
        rows.iter().any(|v| v == "REFUTED"),
        "{name}: the subtraction really underflows and must stay refuted: {rows:?}"
    );
}

// ---------------------------------------------------------------------------
// 1. What is recorded.
// ---------------------------------------------------------------------------

#[test]
fn the_getter_and_the_comparisons_are_summarised_from_the_preopt_bodies() {
    let sums = summaries();
    let field = |field: usize, value: ReturnFieldValue| ReturnFieldSummary {
        param_count: 1,
        subject_param: 1,
        struct_name: "field_summary::V".to_string(),
        field,
        field_ty: (64, false),
        value,
    };
    assert_eq!(sums.get(&key("len")), Some(&field(1, ReturnFieldValue::Field)));
    assert_eq!(
        sums.get(&key("is_empty")),
        Some(&field(1, ReturnFieldValue::Compare { op: BinOp::Eq, rhs: 0 })),
        "`self.len() == 0` composes through `len`'s summary"
    );
    assert_eq!(
        sums.get(&key("few")),
        Some(&field(1, ReturnFieldValue::Compare { op: BinOp::Le, rhs: 3 })),
        "`3 >= self.len()` is recorded with the field on the left: `len <= 3`"
    );
    assert_eq!(
        sums.get(&key("cap_is_zero")),
        Some(&field(2, ReturnFieldValue::Compare { op: BinOp::Eq, rhs: 0 }))
    );
    // A branching body, a unit body and every caller record nothing.
    for name in ["weird", "check", "pop", "last_index", "drop_four"] {
        assert!(!sums.contains_key(&key(name)), "`{name}` must not be summarised: {sums:?}");
    }
    assert_eq!(sums.len(), 4, "exactly the four field readers: {sums:?}");
}

/// The compiler's identity gate (`compute_return_field_summaries_admitting`,
/// fed the interposable bodies): a refused getter records nothing, and nothing
/// composes THROUGH it — `is_empty` and `few` read the field only via `len`.
/// `cap_is_zero` reads its field directly and is unaffected.
#[test]
fn a_refused_getter_lends_nothing_to_its_callers() {
    let sums = trust_vcgen::compute_return_field_summaries_admitting(&bundle("preopt"), |f| {
        f.name != "len"
    });
    for name in ["len", "is_empty", "few"] {
        assert!(!sums.contains_key(&key(name)), "`{name}` rests on the refused `len`: {sums:?}");
    }
    assert!(sums.contains_key(&key("cap_is_zero")), "{sums:?}");
    assert_eq!(sums.len(), 1, "{sums:?}");
}

#[test]
fn the_optimized_bodies_yield_the_same_summaries() {
    assert_eq!(trust_vcgen::compute_return_field_summaries(&bundle("opt")), summaries());
}

// ---------------------------------------------------------------------------
// 2. The callers.
// ---------------------------------------------------------------------------

/// bit-vec's `pop`, reduced.
#[test]
fn bit_vec_pop_shape_is_not_refuted() {
    assert_not_refuted("pop");
}

/// bit-vec's `pop` has `self.ensure_invariant()` (a `&self` call) first, which
/// re-versions `self`'s fields before `is_empty()` is called.
#[test]
fn pop_after_a_shared_self_call_is_not_refuted() {
    assert_not_refuted("pop_after_check");
}

#[test]
fn the_getter_on_the_caller_side_is_not_refuted() {
    assert_not_refuted("last_index");
}

#[test]
fn a_negated_swapped_comparison_is_not_refuted() {
    assert_not_refuted("drop_four");
}

#[test]
fn a_comparison_that_does_not_cover_the_subtraction_stays_refuted() {
    assert_refuted("drop_five");
}

#[test]
fn the_subtraction_on_the_empty_branch_stays_refuted() {
    assert_refuted("pop_inverted");
}

#[test]
fn a_guard_on_another_field_stays_refuted() {
    assert_refuted("pop_wrong_field");
}

#[test]
fn a_write_between_the_check_and_the_use_stays_refuted() {
    assert_refuted("pop_after_reset");
}

#[test]
fn a_branching_callee_is_not_summarised_and_stays_refuted() {
    assert_refuted("pop_weird");
}

/// The control for the whole file: WITHOUT the summaries, `pop` is refuted —
/// the fix is the summary, not some other lane.
#[test]
fn without_the_summaries_pop_is_refuted() {
    let rows = sub_rows_of(pick(&bundle("opt"), "pop"), FxHashMap::default());
    assert!(rows.iter().any(|v| v == "REFUTED"), "control must refute: {rows:?}");
}

// ---------------------------------------------------------------------------
// 3. The gates bite (each a one-edit mutation of a real body).
// ---------------------------------------------------------------------------

/// `is_empty(&mut self)`: a `&mut` subject has no argument protector that
/// freezes the field, so nothing is recorded.
#[test]
fn a_mut_subject_is_not_summarised() {
    let mut funcs = bundle("preopt");
    for func in funcs.iter_mut().filter(|f| f.name == "is_empty" || f.name == "len") {
        for local in func.body.locals.iter_mut().filter(|l| l.index == 1) {
            if let Ty::Ref { mutable, .. } = &mut local.ty {
                *mutable = true;
            }
        }
    }
    let sums = trust_vcgen::compute_return_field_summaries(&funcs);
    assert!(!sums.contains_key(&key("len")) && !sums.contains_key(&key("is_empty")), "{sums:?}");
}

/// A body that writes anything but a whole local (here: through its subject)
/// records nothing.
#[test]
fn a_projected_write_in_the_callee_is_not_summarised() {
    let mut funcs = bundle("preopt");
    let len = funcs.iter_mut().find(|f| f.name == "len").expect("len");
    let Statement::Assign { rvalue, span, .. } = len.body.blocks[0].stmts[0].clone() else {
        panic!("`len`'s first statement is its field read");
    };
    let Rvalue::Use(trust_types::Operand::Copy(field)) = rvalue.clone() else {
        panic!("`len` reads its field by copy: {rvalue:?}");
    };
    // `(*self).nbits = copy (*self).nbits` ahead of the read.
    len.body.blocks[0].stmts.insert(
        0,
        Statement::Assign {
            place: field.clone(),
            rvalue: Rvalue::Use(trust_types::Operand::Copy(field)),
            span: span.clone(),
        },
    );
    let sums = trust_vcgen::compute_return_field_summaries(&funcs);
    assert!(!sums.contains_key(&key("len")), "{sums:?}");
    assert!(!sums.contains_key(&key("is_empty")), "`is_empty` loses its only getter: {sums:?}");
}

/// A caller whose `self` pointer is reseated gets no fact: `self*.1` after the
/// call need not be the field the callee read.
#[test]
fn a_reseated_subject_pointer_gets_no_fact() {
    let mut pop = pick(&bundle("opt"), "pop");
    // `self = copy self` in the success block: a second whole definition of `_1`.
    let reseat = Statement::Assign {
        place: trust_types::Place::local(1),
        rvalue: Rvalue::Use(trust_types::Operand::Copy(trust_types::Place::local(1))),
        span: trust_types::SourceSpan::default(),
    };
    pop.body.blocks[2].stmts.insert(0, reseat);
    let rows = sub_rows_of(pop, summaries());
    assert!(rows.iter().any(|v| v == "REFUTED"), "no fact may fire: {rows:?}");
}

/// The summary is keyed on the struct as well as the field: a caller whose
/// subject is a DIFFERENT struct (here: the same shape under another name)
/// gets no fact.
#[test]
fn a_different_struct_gets_no_fact() {
    let mut sums = summaries();
    for summary in sums.values_mut() {
        summary.struct_name = "field_summary::W".to_string();
    }
    let rows = sub_rows_of(pick(&bundle("opt"), "pop"), sums);
    assert!(rows.iter().any(|v| v == "REFUTED"), "no fact may fire: {rows:?}");
}

/// Only field projections below the pointee are named; the fixture's subject
/// place really is `(*self)` (a guard against a vacuous mutation test above).
#[test]
fn the_pop_fixture_borrows_the_whole_pointee() {
    let pop = pick(&bundle("opt"), "pop");
    assert!(pop.body.blocks[0].stmts.iter().any(|s| matches!(
        s,
        Statement::Assign { rvalue: Rvalue::Ref { mutable: false, place }, .. }
            if place.local == 1 && place.projections == vec![Projection::Deref]
    )));
}
