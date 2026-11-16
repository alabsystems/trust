//! REAL-ARTIFACT guard for CAST-SIGNED-CLAMP-UB-1: a `min(v, C)` clamp on a SIGNED
//! local was published as an UNSIGNED bound on its `as uN` cast.
//!
//! Fixtures: the compiler's own extracted input for `tests/data/signed_clamp_cast.rs`
//! (one `signed_clamp_cast_<fn>.json` per function, captured with
//! `-Ztrust-dump=mir:<dir>` on the stage 1 of main + wave 15, before the fix).
//!
//! ```text
//! pub fn c2_index(v: i32, arr: &[u8; 11]) -> u8 {
//!     let l = if v > 10 { 10 } else { v };
//!     arr[l as usize]
//! }
//! ```
//!
//! `l` has two definitions (the two arms of the diamond), so
//! `value_facts::unsigned_upper_bound` took its unstable-local path, where
//! `clamp_upper_bound(l)` is `Some(10)` — true of the signed `l`. The Cast arm of
//! `_5 = l as usize` recursed into `l` with no signedness check and kept that 10, and
//! `build_additive_bound_facts` conjoined the GLOBAL fact `_5 <= 10` into every VC.
//! The bounds violation `_5 >= 11` is then UNSAT although `v = -1` gives
//! `_5 = 18446744073709551615`: the compiler reported `bounds proved (ay-in-process)`,
//! Certified by the clean kernel, while the program panics. `c2_add`'s
//! `(l as u32) + 4294967200` overflow row was Certified the same way.
//!
//! MEASURED 2026-10-05 through this file's own pipeline (`generate_vcs`, the
//! in-process ay, `trust_certify::certify_vc`). BEFORE the fix: the bounds rows of
//! `c2_index`, `m2_lt`, `m3_i8` and `m6_isize` and the `overflow:add` row of `c2_add`
//! were ay-`Proved` and certified; `m8_div`'s bounds row was neither `Proved` nor
//! `Failed` under ay but `certify_vc` certified it (the compiler reported it proved
//! through the kernel lane). `ctl_u32` was `Proved` and certified, `ctl_oneblock`
//! `Failed` and uncertified. AFTER: every liar row above is `Failed` and uncertified;
//! the two controls read as before, and `m8_div`'s division-overflow rows do not move.
use trust_types::{VcKind, VerifiableFunction, VerificationCondition, VerificationResult};

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/data/signed_clamp_cast_{name}.json", env!("CARGO_MANIFEST_DIR"));
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture `{path}` must be readable: {e}"));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("fixture `{path}` must deserialize: {e}"))
}

/// The rows of `func` whose kind `keep` selects.
fn rows(func: &VerifiableFunction, keep: impl Fn(&VcKind) -> bool) -> Vec<VerificationCondition> {
    trust_vcgen::generate_vcs(func).into_iter().filter(|vc| keep(&vc.kind)).collect()
}

fn bounds_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    rows(func, |k| matches!(k, VcKind::IndexOutOfBounds))
}

fn verdict(vc: &VerificationCondition) -> VerificationResult {
    let router = test_router::deterministic_test_router();
    router.verify_all(std::slice::from_ref(vc)).into_iter().next().expect("one verdict per VC").1
}

/// The false row must be REFUTED, and must not mint a kernel certificate.
fn assert_refuted(name: &str, vcs: &[VerificationCondition]) {
    assert!(!vcs.is_empty(), "`{name}`: the row under test must exist");
    for vc in vcs {
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Failed { .. }),
            "`{name}`: a negative `l` wraps to a huge unsigned value, so this row is \
             FALSE and must be refuted.\n  verdict: {result:?}\n  formula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(vc).is_none(),
            "`{name}`: a false row must not kernel-certify; formula: {:?}",
            vc.formula
        );
    }
}

/// WATCHED FAILING before the fix: it stopped at `c2_index`, ay-`Proved` with
/// `Le(Var("_5"), Int(10))` in the formula.
#[test]
fn signed_clamp_index_rows_are_refuted() {
    for name in ["c2_index", "m2_lt", "m3_i8", "m6_isize", "m8_div"] {
        let func = load(name);
        assert_refuted(name, &bounds_rows(&func));
    }
}

/// WATCHED FAILING before the fix: `(l as u32) + 4294967200` read `Proved` and
/// certified, though `l = -1` makes it `4294967295 + 4294967200`.
#[test]
fn signed_clamp_cast_add_overflow_row_is_refuted() {
    let func = load("c2_add");
    let adds = rows(&func, |k| matches!(k, VcKind::ArithmeticOverflow { .. }));
    assert_refuted("c2_add", &adds);
}

/// CONTROL: the same diamond on an unsigned `v` is in bounds. Its bound must still
/// be published, prove, and kernel-certify.
#[test]
fn unsigned_clamp_index_row_still_proves_and_certifies() {
    let func = load("ctl_u32");
    let vcs = bounds_rows(&func);
    assert!(!vcs.is_empty(), "`ctl_u32`: the bounds row must exist");
    for vc in &vcs {
        let result = verdict(vc);
        assert!(
            matches!(result, VerificationResult::Proved { .. }),
            "`ctl_u32`: `min(v, 10) as usize < 11` holds for every `u32`.\n  verdict: \
             {result:?}\n  formula: {:?}",
            vc.formula
        );
        assert!(
            trust_certify::certify_vc(vc).is_some(),
            "`ctl_u32`: the proved row must kernel-certify; formula: {:?}",
            vc.formula
        );
    }
}

/// CONTROL: the one-block spelling of `c2_index` was already refused before the
/// fix; it must stay refused.
#[test]
fn one_block_signed_clamp_stays_refuted() {
    let func = load("ctl_oneblock");
    assert_refuted("ctl_oneblock", &bounds_rows(&func));
}
