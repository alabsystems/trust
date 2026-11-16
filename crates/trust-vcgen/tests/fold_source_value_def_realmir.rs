//! Trust: 2026-10-11 — CL-FOLD-LOCALDEF-1 and CL-FOLD-MAP-FORCED-1, MEASURED ON REAL
//! COMPILER MIR.
//!
//! CL-FOLD-LOCALDEF-1. `alloc_vcs::local_def` INLINES a local's one defining statement
//! (a `Range` aggregate, a `RangeInclusive::new` call, a `Duration` constructor) into a
//! formula, and it asked only the seam's COUNTING question
//! (`local_defs::has_one_explicit_def`), which by design does not count a field store
//! (`LocalWrite::Partial`) or a `&mut` alias (`LocalWrite::Escape`). So
//! `let mut r = 0u8..4; r.end = 200; r.sum::<u8>()` — and the `&mut` callee,
//! `mem::swap`, store-through-`&mut r` and closure-capture twins of it — had its sum
//! row PROVED, kernel-certified, under `-Ztrust-policy=certify` on the stage 1 of
//! `2bf0ad72e3`, while the program panics "attempt to add with overflow". The same
//! resolver fed the slice-index lane's `RangeInclusive::new` arm and the `Duration`
//! literal lane. `local_def` now asks a VALUE question
//! (`local_defs::unique_value_modulo_whole_drops`: `unique_value_def` or
//! `unique_value_call`, with a whole-local `Drop` read as the end of the value), and
//! two upper-bound readers, `fold_source_bound` and `collect_source_live_count`,
//! re-admit a `&mut` alias whose every use is the receiver of core's own
//! `Iterator::next`.
//!
//! CL-FOLD-MAP-FORCED-1. A `sum`/`product` whose source counts are bounded but whose
//! items pass through `map` (`filter_map`, `map_while`, `scan`) has no modelled item
//! range. The lane defaulted each item to the accumulator's MAX and minted an ordinary
//! refutable row, so `(0..4usize).map(|_| 1u32).sum::<u32>()` was REFUTED with a
//! "counterexample" holding only the range's fields, and escalated to a "guaranteed
//! Level 0 safety violation". Such a fold is now the honest `iterator-fold-overflow`
//! Unknown unless its count is a closed constant of at most one.
//!
//! Every fixture is a `-Ztrust-dump=mir-only` capture from the stage 1 of `2bf0ad72e3`
//! (`scratchpad/stage1-w22probe/bin/rustc --edition 2021 -Ztrust-verify=on
//! -Ztrust-policy=advisory --crate-type lib`, `-Copt-level=0`) of the function `f` in
//! a crate named after the fixture. The spans are relative (the capture compiled a
//! relative path), so no path needed rewriting. Each row's source is quoted in its
//! doc, with the stage-1 verdict it had BEFORE this change. The verdict asserted is
//! the one this crate produces through `generate_vcs` (with the 64-bit host's pointer
//! width installed, as the compiler installs it) + the deterministic in-process `ay`
//! router.

use trust_types::{BinOp, VcKind, VerifiableFunction, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn fixture(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("the captured MIR fixture must deserialize")
}

type Row = (VcKind, VerificationResult);

fn verdicts(name: &str) -> Vec<Row> {
    let func = fixture(name);
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            // The captures are 64-bit-host extractions; generate as the compiler does
            // there, with the target's pointer width installed (ALLOC-WIDTH-1).
            let vcs = trust_vcgen::with_target_pointer_bits(Some(64), || {
                trust_vcgen::generate_vcs(&func)
            });
            let router = test_router::deterministic_test_router();
            router.verify_all(&vcs).into_iter().map(|(vc, r)| (vc.kind, r)).collect::<Vec<_>>()
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn is_proved(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Proved { .. })
}

fn is_refuted(r: &VerificationResult) -> bool {
    matches!(r, VerificationResult::Failed { counterexample: Some(_), .. })
}

fn is_fold_row(k: &VcKind) -> bool {
    matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add | BinOp::Mul, .. })
}

fn is_unmodelled_fold(k: &VcKind) -> bool {
    matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "iterator-fold-overflow")
}

fn is_slice_row(k: &VcKind) -> bool {
    matches!(k, VcKind::SliceBoundsCheck | VcKind::IndexOutOfBounds)
}

fn is_duration_add(k: &VcKind) -> bool {
    matches!(k, VcKind::Assertion { message } if message == "Duration Add: overflow")
}

fn is_unmodelled_duration(k: &VcKind) -> bool {
    matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "duration-arith-overflow-unmodeled")
}

/// The sum of a range CHANGED after it was built: no fold overflow row is proved, and
/// the fold is the honest `iterator-fold-overflow` Unknown.
fn assert_rewritten_range_sum_is_not_proved(name: &str) {
    let rows = verdicts(name);
    for (kind, verdict) in &rows {
        assert!(
            !(is_fold_row(kind) && is_proved(verdict)),
            "{name}: the sum of a range rewritten after construction is PROVED again: {rows:?}"
        );
    }
    assert!(
        rows.iter().any(|(k, _)| is_unmodelled_fold(k)),
        "{name}: the fold must be the iterator-fold-overflow Unknown: {rows:?}"
    );
}

/// The fold row of a correct program proves.
fn assert_fold_proved(name: &str) {
    let rows = verdicts(name);
    let fold: Vec<&Row> = rows.iter().filter(|(k, _)| is_fold_row(k)).collect();
    assert_eq!(fold.len(), 1, "{name}: exactly one fold overflow row: {rows:?}");
    assert!(is_proved(&fold[0].1), "{name}: the fold overflow row must prove: {rows:?}");
    assert!(
        !rows.iter().any(|(k, _)| is_unmodelled_fold(k)),
        "{name}: a modelled fold has no iterator-fold-overflow row: {rows:?}"
    );
}

/// The fold row of a program that overflows is refuted with a counterexample.
fn assert_fold_refuted(name: &str) {
    let rows = verdicts(name);
    let fold: Vec<&Row> = rows.iter().filter(|(k, _)| is_fold_row(k)).collect();
    assert_eq!(fold.len(), 1, "{name}: exactly one fold overflow row: {rows:?}");
    assert!(is_refuted(&fold[0].1), "{name}: the fold overflow row must be refuted: {rows:?}");
}

/// A fold whose items are not modelled: NO fold overflow row at all (so nothing can
/// be refuted on a defaulted item), and the `iterator-fold-overflow` Unknown instead.
fn assert_unmodelled_items_are_unknown(name: &str) {
    let rows = verdicts(name);
    assert!(
        !rows.iter().any(|(k, _)| is_fold_row(k)),
        "{name}: an unmodelled-item fold minted a refutable overflow row: {rows:?}"
    );
    assert!(
        rows.iter().any(|(k, _)| is_unmodelled_fold(k)),
        "{name}: the fold must be the iterator-fold-overflow Unknown: {rows:?}"
    );
}

// ── CL-FOLD-LOCALDEF-1: STILL CLOSED ──────────────────────────────────────────

/// `let mut r = 0u8..4; r.end = 200; r.sum::<u8>()` — a field store (`Partial`).
/// BEFORE: certify rc=0, the `overflow:add` row proved and kernel-certified; the
/// program panics.
#[test]
fn field_store_after_construction_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_field");
}

/// `fn f(n: u8) { let mut r = 0u8..4; r.end = n; r.sum::<u8>() }` — BEFORE: certify
/// rc=0, kernel-certified; `f(200)` panics.
#[test]
fn field_store_of_a_parameter_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_param");
}

/// `widen(&mut r)` with `fn widen(q: &mut Range<u8>) { q.end = 200 }` — an `Escape`
/// into a callee. BEFORE: certify rc=0, kernel-certified; panics.
#[test]
fn a_mut_callee_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_fnitem");
}

/// `core::mem::swap(&mut r, &mut big)` with `big = 0u8..200`. BEFORE: certify rc=0,
/// kernel-certified; panics.
#[test]
fn a_swap_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_swap");
}

/// `let p = &mut r; p.end = 200;` — a store through a `&mut` (whose place is `p`).
/// BEFORE: certify rc=0, kernel-certified; panics.
#[test]
fn a_store_through_a_mut_alias_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_mutref");
}

/// `let mut g = || r.end = 200; g();` — a closure capturing `r.end` by unique borrow.
/// BEFORE: default rc=0 with the sum row proved; panics.
#[test]
fn a_closure_capturing_the_end_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_closure_field");
}

/// `let mut g = || r = 0..200; g();` — a closure reseating the whole range.
/// BEFORE: default rc=0 with the sum row proved; panics.
#[test]
fn a_closure_reseating_the_range_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_closure_whole");
}

/// `let mut r = 0u8..=3; let p = &mut r; *p = 0..=200; r.sum::<u8>()` — the
/// `RangeInclusive::new` call-destination arm. BEFORE: default rc=0, sum row proved;
/// panics.
#[test]
fn an_inclusive_range_reseated_through_an_alias_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_incl_escape");
}

/// `r.next(); let p = &mut r; p.end = 200; r.sum::<u8>()` — the precision recovery's
/// own adversary: one conduit feeds `next`, the other is WRITTEN THROUGH, so the
/// recovery's conduit gate refuses and the value question already did.
#[test]
fn a_next_beside_a_store_through_an_alias_is_not_proved() {
    assert_rewritten_range_sum_is_not_proved("fold_localdef_next_then_widen");
}

/// The slice-index lane's `RangeInclusive::new` arm (`collection_range::
/// norm_usize_range`): `let mut r = 0usize..=0; let p = &mut r; *p = 0..=100;
/// if v.len() > 0 { v[r].len() } else { 0 }`. BEFORE: certify rc=0, the slice bounds
/// row proved and kernel-certified; `f(&[1, 2, 3, 4])` panics "range end index 100
/// out of range for slice of length 4".
#[test]
fn a_slice_range_reseated_through_an_alias_is_not_proved() {
    let rows = verdicts("fold_localdef_slice_incl_escape");
    for (kind, verdict) in &rows {
        assert!(
            !(is_slice_row(kind) && is_proved(verdict)),
            "the slice row of a range rewritten after construction is PROVED again: {rows:?}"
        );
    }
    assert!(
        rows.iter().any(|(k, v)| !is_proved(v)
            && (is_slice_row(k) || matches!(k, VcKind::UnsupportedMir { .. }))),
        "the slice range must be charged, not dropped: {rows:?}"
    );
}

/// `numeric_panic::literal_duration_nanos`: `let mut d = Duration::from_secs(1);
/// let mut g = || d = Duration::MAX; g(); d + Duration::from_secs(2)`. BEFORE: default
/// rc=0 with `Duration Add: overflow` proved; panics "overflow when adding durations".
#[test]
fn a_duration_reseated_by_a_closure_is_not_proved() {
    assert_duration_add_not_proved("fold_localdef_dur_closure");
}

/// `let p = &mut d; *p = Duration::MAX;` — the same lane through a store-through.
#[test]
fn a_duration_reseated_through_an_alias_is_not_proved() {
    assert_duration_add_not_proved("fold_localdef_dur_mutref");
}

fn assert_duration_add_not_proved(name: &str) {
    let rows = verdicts(name);
    for (kind, verdict) in &rows {
        assert!(
            !(is_duration_add(kind) && is_proved(verdict)),
            "{name}: the Duration Add row of a rewritten Duration is PROVED again: {rows:?}"
        );
    }
    assert!(
        rows.iter().any(|(k, _)| is_unmodelled_duration(k)),
        "{name}: the Duration Add must be the duration-arith-overflow-unmodeled Unknown: \
         {rows:?}"
    );
}

// ── CL-FOLD-LOCALDEF-1: CONTROLS ────────────────────────────────────────────

/// `let r = 0u8..4; r.sum::<u8>()` — unchanged. Proved before and after.
#[test]
fn an_unmodified_range_sum_still_proves() {
    assert_fold_proved("fold_localdef_ctl_plain");
}

/// `let mut r = 0u8..4; r.next(); r.sum::<u8>()` — the PRECISION RECOVERY. The value
/// question refuses `r` (the `&mut r` that `next` takes is an `Escape`), and
/// `fold_source_bound` re-admits it because that borrow's only use is the receiver of
/// core's `Iterator::next` (by rendered path and compiler-minted key): `next` only
/// moves `start` forward, so `0..4` still bounds the count and every item. Proved
/// before (through the alias-blind resolver) and after (through the recovery).
#[test]
fn next_then_sum_still_proves_through_the_recovery() {
    assert_fold_proved("fold_localdef_ctl_next");
}

/// `let mut r = 0u8..=3; r.next(); r.sum::<u8>()` — the recovery's
/// `RangeInclusive::new` call-destination arm.
#[test]
fn next_then_sum_of_an_inclusive_range_still_proves() {
    assert_fold_proved("fold_localdef_ctl_next_incl");
}

/// `let mut r = 0u8..200; r.next(); r.sum::<u8>()` overflows (`1 + .. + 199`). The
/// recovered bound is an UPPER bound, so a real overflow stays refuted.
#[test]
fn next_then_sum_of_a_long_range_is_still_refuted() {
    assert_fold_refuted("fold_localdef_ctl_next_big");
}

/// `let r = 0u8..200; r.sum::<u8>()` — refuted before and after.
#[test]
fn an_unmodified_long_range_sum_is_still_refuted() {
    assert_fold_refuted("fold_localdef_ctl_big");
}

/// `let r = 0usize..=3; if v.len() > 3 { v[r].len() } else { 0 }` — the slice lane's
/// unchanged inclusive range still proves.
#[test]
fn an_unmodified_inclusive_slice_range_still_proves() {
    let rows = verdicts("fold_localdef_ctl_slice");
    let slice: Vec<&Row> = rows.iter().filter(|(k, _)| is_slice_row(k)).collect();
    assert!(!slice.is_empty(), "the slice row must be generated: {rows:?}");
    assert!(slice.iter().all(|(_, v)| is_proved(v)), "the slice row must prove: {rows:?}");
}

/// `let d = Duration::from_secs(1); d + Duration::from_secs(2)` — still proved.
#[test]
fn an_unmodified_literal_duration_add_still_proves() {
    let rows = verdicts("fold_localdef_ctl_dur");
    let add: Vec<&Row> = rows.iter().filter(|(k, _)| is_duration_add(k)).collect();
    assert_eq!(add.len(), 1, "one Duration Add row: {rows:?}");
    assert!(is_proved(&add[0].1), "the literal Duration Add must prove: {rows:?}");
}

// ── CL-FOLD-LOCALDEF-1: THE `collect` WALK'S RECOVERY ────────────────────────

/// Any `collect` allocation row: the source's count is not derivable, or the
/// destination cannot be shown to hold a bounded source.
fn is_collect_allocation_row(k: &VcKind) -> bool {
    matches!(k, VcKind::UnsupportedMir { kind, .. }
        if kind.starts_with("UnboundedAllocation::Iterator::collect"))
}

/// The row a `collect` gets when the walk found NO bound on its source.
fn is_collect_count_unknown(k: &VcKind) -> bool {
    matches!(k, VcKind::UnsupportedMir { kind, .. }
        if kind == "UnboundedAllocation::Iterator::collect::count-not-derivable")
}

/// `let mut chars = word.chars(); match chars.next() { Some(first) =>
/// first.to_uppercase().chain(chars.flat_map(|c| c.to_lowercase())).collect(), None =>
/// String::new() }` — the `capitalize` idiom (`tests/ui/trust/iter_hof_collect_counts.rs
/// #capitalize_root`, check-pass). `chars` is `&mut`-borrowed by `next`, so the VALUE
/// question refuses it, and `collect_source_live_count` falls back to its ORIGIN
/// because that borrow feeds only core's `Iterator::next`. Without the fallback the
/// collect is `count-not-derivable` and the default lane refuses the function.
#[test]
fn a_hand_advanced_chars_source_is_still_a_bounded_collect_source() {
    for name in ["collect_origin_capitalize", "collect_origin_tail_lower"] {
        let rows = verdicts(name);
        assert!(
            !rows.iter().any(|(k, _)| is_collect_allocation_row(k)),
            "{name}: the hand-advanced source must stay a bounded source that fits: {rows:?}"
        );
    }
}

/// `let _ = chars.by_ref().next(); chars.flat_map(..).collect()` — the alias feeds
/// `by_ref`, not `next`, so the origin gate refuses it and the collect is
/// `count-not-derivable`. A RECORDED COST (DECISION_QUEUE CL-FOLD-LOCALDEF-1): the
/// counting gate admitted it, along with a store through the same alias.
#[test]
fn a_source_advanced_through_by_ref_is_not_recovered() {
    let rows = verdicts("collect_origin_by_ref");
    assert!(
        rows.iter().any(|(k, _)| is_collect_count_unknown(k)),
        "the by_ref alias is not the recovery's: {rows:?}"
    );
}

// ── CL-FOLD-MAP-FORCED-1 ────────────────────────────────────────────────────

/// `(0..4usize).map(|_i| 1u32).sum::<u32>()` (returns 4). BEFORE: default rc=1 with
/// `[overflow:add] FAILED` on a Range-only model and "guaranteed Level 0 safety
/// violation".
#[test]
fn a_mapped_range_sum_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_ones");
}

/// `(0..4u32).map(u32::from).sum::<u32>()` (returns 6) — the fn-item twin.
#[test]
fn a_fn_item_mapped_range_sum_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_fn_item");
}

/// `(0..4usize).map(|_i| 2u32).product::<u32>()` (returns 16). BEFORE:
/// `[overflow:mul] FAILED`, "guaranteed".
#[test]
fn a_mapped_range_product_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_product");
}

/// `(0usize..).map(|_| 1u32).take(4).sum::<u32>()` (returns 4) — the count comes from
/// `take`, the items from `map`.
#[test]
fn take_after_map_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_take");
}

/// `(0..3i32).map(|x| x - 1).sum::<i32>()` (returns 0) — the signed lower half.
#[test]
fn a_signed_mapped_sum_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_signed");
}

/// `if n <= 4 { (0..n).map(|_| 1u32).sum::<u32>() } else { 0 }` — a SYMBOLIC count.
/// BEFORE: refuted with `n = 2`, a value at which the program returns 2. The recorded
/// cost of the rule: a symbolic count a guard bounds at one would have proved, and is
/// now Unknown too.
#[test]
fn a_guarded_symbolic_mapped_sum_is_unknown_not_refuted() {
    assert_unmodelled_items_are_unknown("fold_map_guarded");
}

/// `(0..1usize).map(|_| 7u32).sum::<u32>()` — a closed count of one: a single item
/// cannot overflow a sum, so the row is kept and proves.
#[test]
fn a_one_item_mapped_sum_still_proves() {
    assert_fold_proved("fold_map_one_item");
}

/// `(0..4u32).sum::<u32>()` — a plain range keeps its linear row and proves.
#[test]
fn a_plain_range_sum_keeps_its_linear_row() {
    assert_fold_proved("fold_map_ctl_range");
}

/// `(0..4u32).filter(|x| *x > 1).sum::<u32>()` — `filter` keeps the source's items.
#[test]
fn a_filtered_range_sum_still_proves() {
    assert_fold_proved("fold_map_ctl_filter");
}

/// `fn f(a: u8, b: u8) -> u8 { (a..b).sum::<u8>() }` — a real overflow, refuted.
#[test]
fn an_unguarded_range_sum_is_still_refuted() {
    assert_fold_refuted("fold_map_ctl_unguarded");
}
