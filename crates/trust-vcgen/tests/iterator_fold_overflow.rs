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

fn has_iterator_fold_overflow_vc(json: &str) -> bool {
    let func: VerifiableFunction =
        serde_json::from_str(json).expect("fixture MIR must deserialize");
    generate_vcs(&func).into_iter().any(|vc| {
        matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. } if kind == "iterator-fold-overflow")
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
