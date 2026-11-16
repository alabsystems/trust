//! Trust (D2 tier 1, 2026-09-24): the `ADAPTER_YIELD` premise, CLOSURE SIDE, on
//! real compiler MIR.
//!
//! Every fixture is a `-Ztrust-dump=mir-only` capture of a closure body from the
//! stage-1 snapshot of `main` 4e9fe36bf (`-Copt-level=0`, edition 2021, file
//! names relative). The compiler half of D2 (`rustc_mir_transform::
//! trust_adapter_yield`) decides WHETHER a closure gets a premise; these tests
//! pin what vcgen does with one it is handed, through the SAME generation entry
//! the compiler calls (`generate_vcs_with_discharge_and_summaries_configured_
//! with_context_and_box_deref_ops`) and the deterministic in-process `ay` router
//! plus the Clean kernel re-check.
//!
//! BEFORE (snapshot, no premise exists): every closure below is refused on its
//! own root — `windows_all` (= sweep s23 / sample i13) `2 failed`, witness
//! `w__slice_len = 1` and `= 0`; `windows_filter_count` (= s19) `4 failed`,
//! `w*__slice_len = 1`; `range_all` `[bounds] FAILED`, `i = 8`; `chunks_all`
//! `[slice] FAILED`, `c__slice_len = 0`; `chunks_exact_fold` `1 failed`.
//!
//! Each proving row has a NEGATIVE CONTROL in the same file: the same body with
//! no context, with a context owned by another function, or with a premise
//! that does not imply the access — so a green here cannot come from the
//! instrument.

use trust_types::{VcKind, VerifiableFunction, VerificationResult};
// The entry `rustc_mir_transform::trust_verify` calls.
use trust_vcgen::{
    AdapterYieldFact, ClosureAdapterPremise, SummaryDatabase, VcgenContext,
    generate_vcs_with_discharge_and_summaries_configured_with_context_and_box_deref_ops as entry,
};

#[path = "support/test_router.rs"]
mod test_router;

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!(
        "{}/tests/fixtures/adapter_yield_{name}_closure_mir.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

fn premise(item_local: usize, item_deref: bool, fact: AdapterYieldFact) -> ClosureAdapterPremise {
    ClosureAdapterPremise {
        item_local,
        item_deref,
        item_fields: Vec::new(),
        fact,
        adapter: "Iterator::test".to_string(),
        receiver: "test-receiver".to_string(),
    }
}

fn slice_eq(len: u64) -> AdapterYieldFact {
    AdapterYieldFact::SliceLenEq { len }
}

/// `(kind, verdict, kernel-certified)` for every dispatched row plus every row
/// vcgen discharged at generation time.
type Row = (VcKind, VerificationResult, bool);

/// How the context for one run is built.
enum Ctx {
    /// No premise at all — the pre-D2 behaviour.
    Empty,
    /// The premise, owned by THIS function.
    Owned(Vec<ClosureAdapterPremise>),
    /// The premise, owned by a DIFFERENT function.
    Foreign(Vec<ClosureAdapterPremise>),
}

fn verdicts(name: &str, ctx: Ctx) -> Vec<Row> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let context = match ctx {
                Ctx::Empty => VcgenContext::for_function(func.def_path.clone()),
                Ctx::Owned(p) => {
                    VcgenContext::for_function(func.def_path.clone()).with_adapter_yield_premises(p)
                }
                Ctx::Foreign(p) => {
                    VcgenContext::for_function("adapter_yield::someone_else::{closure#0}")
                        .with_adapter_yield_premises(p)
                }
            };
            let summaries = SummaryDatabase::new();
            let (vcs, discharged) = entry(
                &func,
                &summaries,
                false,
                &context,
                &std::collections::HashSet::<(trust_types::BlockId, usize)>::new(),
            );
            let router = test_router::deterministic_test_router();
            let mut rows: Vec<Row> = router
                .verify_all(&vcs)
                .into_iter()
                .map(|(vc, r)| {
                    let certified = trust_certify::certify_vc(&vc).is_some();
                    (vc.kind, r, certified)
                })
                .collect();
            rows.extend(discharged.into_iter().map(|(vc, r)| (vc.kind, r, true)));
            rows
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

/// Every bounds row proves AND is kernel-certified, and there is at least one.
fn assert_bounds_certified(name: &str, ctx: Ctx, expected_bounds_rows: usize) {
    let rows = verdicts(name, ctx);
    let bounds: Vec<&Row> = rows.iter().filter(|(k, _, _)| is_bounds(k)).collect();
    assert_eq!(
        bounds.len(),
        expected_bounds_rows,
        "{name}: bounds-row count drifted; got {rows:?}"
    );
    for (kind, verdict, certified) in &bounds {
        assert!(
            is_proved(verdict),
            "{name}: {kind:?} must prove under the premise; got {verdict:?}"
        );
        assert!(*certified, "{name}: {kind:?} must be kernel-certified under the premise");
    }
    for (kind, verdict, _) in &rows {
        assert!(is_proved(verdict), "{name}: every row must prove; {kind:?} got {verdict:?}");
    }
}

/// At least one bounds row is NOT proved — the fail-closed direction.
fn assert_some_bounds_unproved(name: &str, ctx: Ctx) {
    let rows = verdicts(name, ctx);
    let bounds: Vec<&Row> = rows
        .iter()
        .filter(|(k, _, _)| is_bounds(k) || matches!(k, VcKind::UnsupportedMir { .. }))
        .collect();
    assert!(!bounds.is_empty(), "{name}: the bounds obligation must be generated; got {rows:?}");
    assert!(
        bounds.iter().any(|(_, verdict, _)| !is_proved(verdict)),
        "{name}: a bounds row must stay unproved; got {rows:?}"
    );
}

// ---------------------------------------------------------------------------
// windows(2) + all  (ordinary-rust sweep s23, idiomatic sample i13)
// ---------------------------------------------------------------------------

#[test]
fn windows_all_proves_under_the_premise() {
    assert_bounds_certified("windows_all", Ctx::Owned(vec![premise(2, false, slice_eq(2))]), 2);
}

#[test]
fn windows_all_without_premise_stays_refused() {
    assert_some_bounds_unproved("windows_all", Ctx::Empty);
}

#[test]
fn windows_all_premise_owned_by_another_function_is_ignored() {
    assert_some_bounds_unproved("windows_all", Ctx::Foreign(vec![premise(2, false, slice_eq(2))]));
}

/// A premise that does not imply `w[1]` (length 1) must not prove it: the fact
/// is a constraint on the modeled length, not a blanket discharge.
#[test]
fn windows_all_premise_len1_does_not_prove_index_1() {
    assert_some_bounds_unproved("windows_all", Ctx::Owned(vec![premise(2, false, slice_eq(1))]));
}

/// The premise names `_1` (the environment) or `_0`: refused by the parameter
/// gate, whatever the fact says.
#[test]
fn windows_all_premise_on_environment_is_refused() {
    assert_some_bounds_unproved("windows_all", Ctx::Owned(vec![premise(1, false, slice_eq(2))]));
    assert_some_bounds_unproved("windows_all", Ctx::Owned(vec![premise(0, false, slice_eq(2))]));
}

/// A slice premise on the wrong deref depth (`*w` is `[u32]`, not `&[u32]`)
/// finds no shared sub-slice and adds nothing.
#[test]
fn windows_all_premise_wrong_depth_is_refused() {
    assert_some_bounds_unproved("windows_all", Ctx::Owned(vec![premise(2, true, slice_eq(2))]));
}

/// An integer-range premise on a slice parameter is a type mismatch: nothing.
#[test]
fn windows_all_premise_wrong_family_is_refused() {
    assert_some_bounds_unproved(
        "windows_all",
        Ctx::Owned(vec![premise(2, false, AdapterYieldFact::IntHalfOpen { start: 0, end: 8 })]),
    );
}

// ---------------------------------------------------------------------------
// windows(2) + filter + count  (sweep s19): the item is `&&[u32]`
// ---------------------------------------------------------------------------

#[test]
fn windows_filter_count_proves_under_the_deref_premise() {
    assert_bounds_certified(
        "windows_filter_count",
        Ctx::Owned(vec![premise(2, true, slice_eq(2))]),
        4,
    );
}

#[test]
fn windows_filter_count_without_premise_stays_refused() {
    assert_some_bounds_unproved("windows_filter_count", Ctx::Empty);
}

// ---------------------------------------------------------------------------
// The closure reassigns its item: `|mut w| { w = &[]; w[1] == 0 }` always
// panics. The compiler's scan reads only the PARENT, so it would install the
// premise; the closure-side never-written gate is what must refuse it.
// ---------------------------------------------------------------------------

#[test]
fn item_reassigned_is_refused_by_the_parameter_gate() {
    assert_some_bounds_unproved(
        "item_reassigned",
        Ctx::Owned(vec![premise(2, false, slice_eq(2))]),
    );
}

// ---------------------------------------------------------------------------
// Integer ranges: `(0..8).all(|i| a[i] == 0)` over `&[u8; 8]`, its `rev()` twin,
// and `(0..8usize).filter(|&i| a[i] > 0).count()` (item behind `&`).
// ---------------------------------------------------------------------------

fn half_open(start: i128, end: i128) -> AdapterYieldFact {
    AdapterYieldFact::IntHalfOpen { start, end }
}

#[test]
fn range_all_proves_under_the_premise() {
    assert_bounds_certified("range_all", Ctx::Owned(vec![premise(2, false, half_open(0, 8))]), 1);
}

#[test]
fn range_all_wider_premise_still_refutes() {
    // `0..9` admits `i = 8`, which is out of bounds for `[u8; 8]`.
    assert_some_bounds_unproved("range_all", Ctx::Owned(vec![premise(2, false, half_open(0, 9))]));
}

#[test]
fn range_all_without_premise_stays_refused() {
    assert_some_bounds_unproved("range_all", Ctx::Empty);
}

#[test]
fn range_rev_all_proves_under_the_premise() {
    assert_bounds_certified(
        "range_rev_all",
        Ctx::Owned(vec![premise(2, false, half_open(0, 8))]),
        1,
    );
}

#[test]
fn range_filter_count_proves_under_the_deref_premise() {
    assert_bounds_certified(
        "range_filter_count",
        Ctx::Owned(vec![premise(2, true, half_open(0, 8))]),
        1,
    );
}

#[test]
fn range_filter_count_without_premise_stays_refused() {
    assert_some_bounds_unproved("range_filter_count", Ctx::Empty);
}

// ---------------------------------------------------------------------------
// chunks(3): `c[0]` needs only `len >= 1`; chunks_exact(4) + fold: the item is
// the SECOND parameter (`_3`).
// ---------------------------------------------------------------------------

#[test]
fn chunks_all_proves_under_the_premise() {
    assert_bounds_certified(
        "chunks_all",
        Ctx::Owned(vec![premise(2, false, AdapterYieldFact::SliceLenIn { min: 1, max: 3 })]),
        1,
    );
}

#[test]
fn chunks_all_without_premise_stays_refused() {
    assert_some_bounds_unproved("chunks_all", Ctx::Empty);
}

#[test]
fn chunks_exact_fold_proves_under_the_second_parameter_premise() {
    assert_bounds_certified(
        "chunks_exact_fold",
        Ctx::Owned(vec![premise(3, false, slice_eq(4))]),
        1,
    );
}

/// The `fold` item is `_3`; a premise mis-aimed at the accumulator `_2`
/// (an integer, not a slice) proves nothing.
#[test]
fn chunks_exact_fold_premise_on_accumulator_is_refused() {
    assert_some_bounds_unproved(
        "chunks_exact_fold",
        Ctx::Owned(vec![premise(2, false, slice_eq(4))]),
    );
}

// ---------------------------------------------------------------------------
// Byte-identity: a context with no premise generates exactly what the plain
// entry generates, so every body the compiler admits nothing for is unchanged.
// ---------------------------------------------------------------------------

#[test]
fn empty_context_is_byte_identical_to_no_context() {
    for name in ["windows_all", "range_all", "chunks_exact_fold"] {
        let func = fixture(name);
        let plain = trust_vcgen::generate_vcs(&func);
        let with_empty = trust_vcgen::generate_vcs_with_context(
            &func,
            &VcgenContext::for_function(func.def_path.clone())
                .with_adapter_yield_premises(Vec::new()),
        );
        let render = |vcs: &[trust_types::VerificationCondition]| {
            vcs.iter().map(|vc| format!("{:?}|{:?}", vc.kind, vc.formula)).collect::<Vec<_>>()
        };
        assert_eq!(
            render(&plain),
            render(&with_empty),
            "{name}: an empty premise set changed generation"
        );
    }
}

// ---------------------------------------------------------------------------
// The disclosure names the premise first, so a consumer can key on it.
// ---------------------------------------------------------------------------

#[test]
fn disclosure_names_the_premise() {
    let p = ClosureAdapterPremise {
        item_local: 2,
        item_deref: true,
        item_fields: Vec::new(),
        fact: slice_eq(2),
        adapter: "Iterator::filter".to_string(),
        receiver: "<[T]>::windows(2)".to_string(),
    };
    let text = p.disclosure();
    assert!(text.starts_with("ADAPTER_YIELD: "), "{text}");
    assert!(text.contains("`*_2`") && text.contains("slice length 2"), "{text}");
}

// ---------------------------------------------------------------------------
// The auto-deref COPY channel (`stable_copy_slice_lens`): a copy of the item
// that is written once carries the item's length; one that is reseated does not.
// ---------------------------------------------------------------------------

/// `|w| { let x = w; x[0] <= x[1] }` — `x` is a single-assignment copy of the
/// item: proves under the premise (and is refused without it, snapshot:
/// `2 failed`).
#[test]
fn copy_alias_of_item_proves_under_the_premise() {
    assert_bounds_certified("copy_alias_ok", Ctx::Owned(vec![premise(2, false, slice_eq(2))]), 2);
}

#[test]
fn copy_alias_of_item_without_premise_stays_refused() {
    assert_some_bounds_unproved("copy_alias_ok", Ctx::Empty);
}

/// `|w| { let mut x: &[u32] = *w; if x[0] == 7 { x = &[]; } x[1] == 0 }` panics
/// whenever a window starts with 7. `x` has two writes, so it is not a copy of
/// the item for the whole body and gets NO length fact, premise or not.
#[test]
fn reseated_copy_of_item_gets_no_fact() {
    assert_some_bounds_unproved("copy_reassigned", Ctx::Owned(vec![premise(2, true, slice_eq(2))]));
}

// ---------------------------------------------------------------------------
// `-Copt-level=2` closure bodies (the compiler's scan reads the PARENT's
// pre-inlining MIR, identical at every opt level; the CLOSURE body it annotates
// is the optimized one). These pin what vcgen does with the O2 bodies.
// ---------------------------------------------------------------------------

#[test]
fn o2_windows_all_proves_under_the_premise() {
    // O2 keeps both native asserts and adds the two load rows the O0 body's exact
    // assert binding suppresses: four rows, all proved and certified.
    assert_bounds_certified("windows_all_o2", Ctx::Owned(vec![premise(2, false, slice_eq(2))]), 4);
}

#[test]
fn o2_windows_all_without_premise_stays_refused() {
    assert_some_bounds_unproved("windows_all_o2", Ctx::Empty);
}

#[test]
fn o2_windows_filter_count_proves_under_the_deref_premise() {
    assert_bounds_certified(
        "windows_filter_count_o2",
        Ctx::Owned(vec![premise(2, true, slice_eq(2))]),
        4,
    );
}

#[test]
fn o2_windows_filter_count_without_premise_stays_refused() {
    assert_some_bounds_unproved("windows_filter_count_o2", Ctx::Empty);
}

#[test]
fn o2_range_all_proves_under_the_premise() {
    assert_bounds_certified(
        "range_all_o2",
        Ctx::Owned(vec![premise(2, false, half_open(0, 8))]),
        1,
    );
}

#[test]
fn o2_chunks_exact_fold_proves_under_the_premise() {
    assert_bounds_certified(
        "chunks_exact_fold_o2",
        Ctx::Owned(vec![premise(3, false, slice_eq(4))]),
        2,
    );
}

// ---------------------------------------------------------------------------
// The remaining admitted adapters, each over a `windows`/`chunks_exact`
// receiver, each refused on the snapshot (`[slice] FAILED`).
// ---------------------------------------------------------------------------

#[test]
fn windows_any_proves_under_the_premise() {
    assert_bounds_certified("windows_any", Ctx::Owned(vec![premise(2, false, slice_eq(3))]), 2);
    assert_some_bounds_unproved("windows_any", Ctx::Empty);
}

#[test]
fn windows_position_proves_under_the_premise() {
    assert_bounds_certified(
        "windows_position",
        Ctx::Owned(vec![premise(2, false, slice_eq(3))]),
        1,
    );
    assert_some_bounds_unproved("windows_position", Ctx::Empty);
}

#[test]
fn windows_find_proves_under_the_deref_premise() {
    assert_bounds_certified("windows_find", Ctx::Owned(vec![premise(2, true, slice_eq(2))]), 2);
    assert_some_bounds_unproved("windows_find", Ctx::Empty);
}

#[test]
fn windows_map_proves_under_the_premise() {
    assert_bounds_certified(
        "windows_map_count",
        Ctx::Owned(vec![premise(2, false, slice_eq(2))]),
        2,
    );
    assert_some_bounds_unproved("windows_map_count", Ctx::Empty);
}

#[test]
fn chunks_exact_for_each_proves_under_the_premise() {
    assert_bounds_certified(
        "chunks_exact_for_each",
        Ctx::Owned(vec![premise(2, false, slice_eq(4))]),
        1,
    );
    assert_some_bounds_unproved("chunks_exact_for_each", Ctx::Empty);
}
