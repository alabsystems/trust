// Trust (UTF8-CORE-RANGE-INDEX-1, 2026-10-05): indexing a slice or `str` with the
// new range API's own types — `core::range::{Range, RangeFrom, RangeInclusive,
// RangeToInclusive}` — pinned on REAL extracted MIR (`-Ztrust-dump=mir-only` on the
// stage 1 of `dc15b882f6`, main plus wave 16; `fixtures/core_range_index/*.json`,
// named `<revision>_<fn>` after the revision and function of
// `tests/ui/trust/core_range_index_charged.rs` that produced them).
//
// BEFORE: every `stable_*`, `new_range_*`, `inline_*` and `guarded_loss_*` function
// built rc=0 under the default policy (`stable` at `-O0` and `-O3`, `inline` under
// `-Zinline-mir=yes`) with one runtime-checked row, and the unguarded ones panic at
// run time — the RangeIndex arm did not see a `core::range` ADT as a range and
// emitted NO bounds row. These tests pin the row vcgen now mints for each, and that
// no lane proves or certifies it. (Until the 2026-10-08 merge of the class-10 fix,
// RANGE-DECLINE, that row was the always-violated `SliceBoundsCheck` the in-process
// solver refuted on an all-zero model; an untraceable range is now the declined
// `slice-range-bounds-unresolved` row, Unknown, which the strict policy still counts
// as a fatal gap: `strict_l0_verification_failure`.) The
// `controls_*` functions use the `core::ops` types (including the `core::range`
// re-exports of `RangeTo`/`RangeFull`, which the extractor prints by their
// `core::ops::range::` path) and must keep their behaviour.
use trust_types::*;
use trust_vcgen::generate_vcs;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/core_range_index/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

fn router() -> trust_router::Router {
    test_router::deterministic_test_router()
}

/// The rows of the function that charge its range index: `SliceBoundsCheck` rows,
/// the fail-honest `UnsupportedMir { kind: "SliceBoundsCheck" }` twin the
/// owned-`Vec` soft-length path mints, and the declined range rows of the
/// `RangeIndex` arm (RANGE-DECLINE: an untraceable range, an unmodeled receiver
/// length, an uncredited `str` char boundary).
fn index_rows(vcs: &[VerificationCondition]) -> Vec<&VerificationCondition> {
    vcs.iter()
        .filter(|vc| match &vc.kind {
            VcKind::SliceBoundsCheck => true,
            VcKind::UnsupportedMir { kind, .. } => {
                kind == "SliceBoundsCheck"
                    || kind == DECLINED_BOUNDS
                    || kind == "slice-range-len-unresolved"
                    || kind == "str-range-char-boundary-unmodeled"
            }
            _ => false,
        })
        .collect()
}

/// `panic_calls::RANGE_INDEX_BOUNDS_UNRESOLVED`.
const DECLINED_BOUNDS: &str = "slice-range-bounds-unresolved";

fn verdicts(rows: &[&VerificationCondition]) -> Vec<VerificationResult> {
    let router = router();
    rows.iter()
        .map(|vc| router.verify_all(std::slice::from_ref(*vc)).into_iter().next().unwrap().1)
        .collect()
}

/// The new-range index is charged and the charge cannot be discharged: no tracer
/// reads the new layouts, so the `RangeIndex` arm declines the range — an
/// `UnsupportedMir` row (Unknown), [`DECLINED_BOUNDS`] or its receiver-length twin — and no
/// `SliceBoundsCheck` row is left that an all-zero model could refute. No charging
/// row is proved by the in-process solver or certified by the kernel.
fn assert_charged_fail_closed(name: &str) {
    let func = load(name);
    let vcs = generate_vcs(&func);
    let rows = index_rows(&vcs);
    assert!(!rows.is_empty(), "{name}: the `core::range` index must carry a bounds row");
    // The range is declined by the `RangeIndex` arm (`slice-range-bounds-unresolved`;
    // `slice-range-len-unresolved` when the receiver's length is not modeled either,
    // e.g. a `String`), or charged by the owned-`Vec` soft-length twin.
    assert!(
        rows.iter().any(|vc| matches!(&vc.kind, VcKind::UnsupportedMir { .. })),
        "{name}: expected a declined (`UnsupportedMir`) charging row; got {rows:#?}"
    );
    for vc in rows.iter().filter(|vc| matches!(vc.kind, VcKind::SliceBoundsCheck)) {
        let body = vc.obligation.as_ref().map_or(&vc.formula, |o| &o.body);
        assert_ne!(
            body,
            &Formula::Bool(true),
            "{name}: an untraceable range is declined, never the always-violated row"
        );
    }
    let results = verdicts(&rows);
    assert!(
        !results.iter().any(|r| matches!(r, VerificationResult::Proved { .. })),
        "{name}: no charging row may PROVE; got {results:?}"
    );
    for vc in &rows {
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "{name}: a charging row was kernel-certified: {:?}",
            vc.kind
        );
    }
}

#[test]
fn stable_core_range_slice_and_str_indexes_are_charged() {
    for name in [
        "stable_str_from",
        "stable_slice_range",
        "stable_slice_lit",
        "stable_array_range",
        "stable_string_from",
        "stable_mut_str",
        "stable_vec_incl",
        "stable_vec_mut",
        "stable_slice_to_incl",
        "stable_by_param",
    ] {
        assert_charged_fail_closed(name);
    }
}

#[test]
fn new_range_syntax_indexes_are_charged() {
    // `#![feature(new_range)]`: plain `1..`, `0..5`, `0..=4`, `..=4`, `..=0` build
    // the `core::range` types directly, as aggregates.
    for name in [
        "new_range_str_from",
        "new_range_slice_range",
        "new_range_slice_incl",
        "new_range_slice_to_incl",
        "new_range_str_to_incl",
    ] {
        assert_charged_fail_closed(name);
    }
}

#[test]
fn an_inlined_legacy_str_index_exposes_the_new_type_and_is_charged() {
    // `-Zinline-mir=yes`: core's `SliceIndex<str>` impl for `core::ops::Range`
    // forwards to the `core::range::Range` impl, so `&mut s[0..5]` reaches the
    // verifier as `<core::range::Range<usize> as SliceIndex<str>>::index_mut(r, s)`
    // (range first). It built rc=0 that way and panics on `"ab"`.
    assert_charged_fail_closed("inline_mut_str_inlined");
}

#[test]
fn a_guarded_core_range_index_is_refused_too() {
    // THE CAPABILITY LOSS (docs/DECISION_QUEUE.md, UTF8-CORE-RANGE-1): no tracer
    // reads the new layouts, so the guard cannot reach the row. These two cannot
    // panic and built rc=0 before.
    assert_charged_fail_closed("guarded_loss_guarded");
    assert_charged_fail_closed("guarded_loss_guarded_from");
}

#[test]
fn legacy_ranges_and_reexports_keep_their_rows() {
    // A guarded `core::ops` range and the `core::range::RangeTo` re-export keep
    // their precise row, which the guard discharges.
    for name in ["controls_ops_guarded", "controls_reexport_to"] {
        let func = load(name);
        let vcs = generate_vcs(&func);
        let rows = index_rows(&vcs);
        assert_eq!(rows.len(), 1, "{name}: one bounds row; got {rows:#?}");
        assert!(matches!(rows[0].kind, VcKind::SliceBoundsCheck), "{name}");
        let body = rows[0].obligation.as_ref().map_or(&rows[0].formula, |o| &o.body);
        assert_ne!(body, &Formula::Bool(true), "{name}: the legacy range is traced");
        let results = verdicts(&rows);
        assert!(
            results.iter().all(|r| matches!(r, VerificationResult::Proved { .. })),
            "{name}: the guarded legacy index must PROVE; got {results:?}"
        );
    }
    // `..` (spelled directly, or as the `core::range::RangeFull` re-export) never
    // panics and carries no bounds row; neither does the total `get`.
    for name in ["controls_ops_full", "controls_reexport_full", "controls_checked_get"] {
        let func = load(name);
        let vcs = generate_vcs(&func);
        assert!(index_rows(&vcs).is_empty(), "{name}: no bounds row expected");
    }
}
