// Trust (2026-10-10, review round 111): a store through a RELOADED pointer to a
// pointer (`let mut q = &mut m; let pp = &mut q; **pp = v`, MIR `_10 = copy (*_5);
// (*_10) = _2`) did not rebind `m` in the interval domain. The SMT lane versions `m`
// fresh at that store, but the interval augmentation conjoined the stale `m ∈ [25,
// 25]` and `_7 ∈ [25, 25]` (`_7 = copy m`), which discharged the bounds row. Real
// extracted MIR (`-Ztrust-dump=mir`) of the programs quoted on each test, in
// `fixtures/review111/`; each panicking program was PROVED kernel-certified on stage-1
// sa157.
use trust_types::*;
use trust_vcgen::generate_vcs_with_discharge;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/review111/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every bounds row of the DISCHARGE path (the compiler's: interval proofs, then the
/// interval-augmented rest through the solver), with its verdict.
fn bounds_rows(name: &str) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    let (rest, discharged) = generate_vcs_with_discharge(&func);
    let is_bounds = |k: &VcKind| matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck);
    let mut rows: Vec<(String, VerificationResult)> = discharged
        .into_iter()
        .filter(|(vc, _)| is_bounds(&vc.kind))
        .map(|(vc, r)| (vc.formula.to_smtlib(), r))
        .collect();
    rows.extend(rest.into_iter().filter(|vc| is_bounds(&vc.kind)).map(|vc| {
        let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
        (vc.formula.to_smtlib(), r)
    }));
    rows
}

fn assert_not_all_proved(name: &str) {
    let rows = bounds_rows(name);
    assert!(!rows.is_empty(), "{name}: the indexing must carry a bounds row");
    assert!(
        rows.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
        "{name}: a panicking program must not be all PROVED\n{rows:#?}"
    );
}

fn assert_all_proved(name: &str) {
    let rows = bounds_rows(name);
    assert!(!rows.is_empty(), "{name}: the indexing must carry a bounds row");
    assert!(
        rows.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. })),
        "{name}: a correct program must keep its proof\n{rows:#?}"
    );
}

/// `let mut m = 25usize; let mut q = &mut m; let pp = &mut q; **pp = v; a[m / 1]` on
/// `a: &[u8; 26]` (`v = 26` panics); the bounds row was discharged by the stale
/// interval. Control: through ONE `&mut` (`let p = &mut m; *p = v`), the store folds
/// to `m` and was already refused.
#[test]
fn a_store_through_a_reloaded_pointer_rebinds_the_interval_of_its_referent() {
    assert_not_all_proved("u2");
    assert_not_all_proved("u1");
}

/// The same hole read by a range end: `**pp = 100` over `let mut m = 26` then `for i in
/// 0..m { a[i] }` on `[u8; 26]` (reached through p50's joined-copy end, `m` being
/// address-taken), and `for i in 0..(m / 2)` on `[u8; 13]` (no copy involved).
#[test]
fn a_range_end_written_through_a_reloaded_pointer_bounds_nothing() {
    assert_not_all_proved("q7");
    assert_not_all_proved("v1");
}

/// Review round 112: the forget above is not wider than reachability. A store through a
/// `&mut` PARAMETER that is never reseated writes caller memory, never a local of this
/// frame: `let mut m = 3; let r = &mut m; *r = 5; *v = w; a[m / 1]` (`v: &mut usize`,
/// `a: &[u8; 8]`) is correct and keeps its proof. A pointer derived from the parameter
/// (`let r = v as *mut usize`) is memory behind a pointer, and `*r` read after `*v =
/// 100` stays refused.
#[test]
fn a_parameter_store_keeps_the_intervals_of_frame_locals() {
    assert_all_proved("r1d");
    // Round 113: a borrow THROUGH the parameter (`let q = &mut v.1`) does not reseat it.
    assert_all_proved("field_mutborrow_only");
    assert_not_all_proved("rawalias");
}
