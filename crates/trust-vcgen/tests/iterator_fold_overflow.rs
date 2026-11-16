// Trust (iterator sum/product overflow — the SILENT false-accept) regression.
//
// `(1..=n).product::<i32>()` overflows i32 for n >= 13 (debug panic), yet the
// pre-fix verifier emitted ZERO obligations for it — the fold arithmetic lives
// inside the library impl, so `overflow_arith_call` deliberately skipped it (a
// refutable VC would false-FAIL an ordinary bounded `vec.sum()`), which left a
// silent accept. The fix mints an `UnsupportedMir { kind: "iterator-fold-overflow" }`
// obligation instead — which routes to Unknown → runtime-checked in the default
// lane (exactly like the `m[&k]` map-index backstop, verified on a live binary):
// HONESTLY accounted and delegated to the runtime overflow check, never silently
// verified and never false-FAILED.
//
// Pins:
//  * i32 `product` / `sum`  -> the obligation IS minted (no more silent accept).
//  * f64 `sum`              -> NOT minted (a float sum saturates to ±inf, no
//                              overflow panic — the `int_width()` result-type gate).
//
// Fixtures are the REAL MIR extracted with `-Ztrust-dump=mir:<dir>`.
use trust_types::*;
use trust_vcgen::generate_vcs;

// Trust (2026-09-25, F4): a fold whose source COUNT is derivable (a range,
// `take(n)`, `repeat_n`) is now a real `ArithmeticOverflow` row — provable under
// a bounding guard, refutable without one — and only an unbounded-count fold
// keeps the `iterator-fold-overflow` Unknown. Either one is the minted
// obligation this file pins; neither is the silent accept.
fn has_iterator_fold_overflow_vc(json: &str) -> bool {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    generate_vcs(&func).into_iter().any(|vc| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "iterator-fold-overflow")
            || matches!(&vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Add | BinOp::Mul, .. })
    })
}

#[test]
fn integer_product_mints_fold_overflow_obligation() {
    assert!(
        has_iterator_fold_overflow_vc(include_str!("fixtures/iter_product_i32_mir.json")),
        "`(1..=n).product::<i32>()` must mint an iterator-fold-overflow obligation \
         (no more silent 0-obligation accept)"
    );
}

#[test]
fn integer_sum_mints_fold_overflow_obligation() {
    assert!(
        has_iterator_fold_overflow_vc(include_str!("fixtures/iter_sum_i32_mir.json")),
        "`v.iter().sum::<i32>()` must mint an iterator-fold-overflow obligation"
    );
}

#[test]
fn float_sum_is_not_flagged() {
    // A float sum saturates to ±inf — no overflow panic. The `int_width()` gate
    // must leave it untouched (no obligation), or the fix would over-refute all
    // float folds.
    assert!(
        !has_iterator_fold_overflow_vc(include_str!("fixtures/iter_sum_f64_mir.json")),
        "`v.iter().sum::<f64>()` must NOT be flagged — floats do not overflow-panic"
    );
}

// Trust (CL-FOLD-MAP-FORCED-1, 2026-10-11): a fold whose COUNT is bounded but whose
// ITEMS are not modelled (a `map`/`filter_map`/`map_while`/`scan` result) is the
// `iterator-fold-overflow` Unknown, and mints NO `ArithmeticOverflow` row: that row
// used to default every item to the accumulator's MAX, so a constant count of 4 made
// `4 * MAX > MAX` true and `(0..4usize).map(|_| 1u32).sum::<u32>()` was REFUTED as a
// "guaranteed" violation. A closed count of at most one keeps its row, and a plain
// range keeps its linear row. Real MIR, `-Ztrust-dump=mir-only` on the stage 1 of
// `2bf0ad72e3`; the end-to-end verdicts are `fold_source_value_def_realmir.rs`.
fn fold_rows(name: &str) -> Vec<VcKind> {
    let path = format!("{}/tests/fixtures/{name}_mir.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let func: VerifiableFunction =
        serde_json::from_str(&json).expect("fixture MIR must deserialize");
    generate_vcs(&func)
        .into_iter()
        .map(|vc| vc.kind)
        .filter(|k| {
            matches!(k, VcKind::UnsupportedMir { kind, .. } if kind == "iterator-fold-overflow")
                || matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Add | BinOp::Mul, .. })
        })
        .collect()
}

#[test]
fn a_mapped_range_fold_mints_the_unknown_and_no_overflow_row() {
    for name in [
        "fold_map_ones",
        "fold_map_fn_item",
        "fold_map_product",
        "fold_map_take",
        "fold_map_signed",
        "fold_map_guarded",
    ] {
        let rows = fold_rows(name);
        assert!(
            matches!(rows.as_slice(), [VcKind::UnsupportedMir { kind, .. }] if kind == "iterator-fold-overflow"),
            "{name}: exactly the iterator-fold-overflow Unknown, no refutable row: {rows:?}"
        );
    }
}

#[test]
fn a_plain_range_or_one_mapped_item_keeps_its_overflow_row() {
    for name in ["fold_map_ctl_range", "fold_map_one_item", "fold_map_ctl_filter"] {
        let rows = fold_rows(name);
        assert!(
            matches!(rows.as_slice(), [VcKind::ArithmeticOverflow { op: BinOp::Add, .. }]),
            "{name}: exactly the linear overflow row: {rows:?}"
        );
    }
}
