// Trust (2026-10-11, sweep2 p13_parse_i32 / a12_max_min): a `Some` from the std
// `first()`/`last()` of a slice reference seeded `coll_len(v) >= 1` on the abstract
// collection var named after the place, while the slice's bounds and range rows read
// its length metadata `v__slice_len`; `match v.first() { Some(_) => v[0], .. }` was
// refuted with `v = 1, v__slice_len = 0`. The `Some` arm now also knows
// `v__slice_len >= 1`. Real extracted MIR (`-Ztrust-dump=mir`) in
// `fixtures/first_last_slice_len/`.
use trust_types::*;
use trust_vcgen::generate_vcs_with_discharge;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/first_last_slice_len/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every bounds row of the discharge path, with its verdict.
fn bounds_rows(name: &str) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    let (rest, discharged) = generate_vcs_with_discharge(&func);
    let keep = |k: &VcKind| matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck);
    let mut rows: Vec<(String, VerificationResult)> = discharged
        .into_iter()
        .filter(|(vc, _)| keep(&vc.kind))
        .map(|(vc, r)| (vc.formula.to_smtlib(), r))
        .collect();
    rows.extend(rest.into_iter().filter(|vc| keep(&vc.kind)).map(|vc| {
        let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
        (vc.formula.to_smtlib(), r)
    }));
    assert!(!rows.is_empty(), "{name}: the index must carry a bounds row");
    rows
}

/// `match v.first() { Some(_) => v[0], None => 0 }` and `if let Some(_) = v.last() {
/// v[v.len() - 1] }` on `v: &[T]`.
#[test]
fn a_some_first_or_last_proves_the_slice_non_empty() {
    for name in ["first_some", "last_some"] {
        let rows = bounds_rows(name);
        assert!(
            rows.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. })),
            "{name}: every bounds row must be proved\n{rows:#?}"
        );
    }
}

/// `Some(_) => v[1]` (one element is not two) and `None => v[0]` (the empty arm).
#[test]
fn the_seed_proves_one_element_and_only_in_the_some_arm() {
    for name in ["first_some_bad", "first_none_bad"] {
        let rows = bounds_rows(name);
        assert!(
            rows.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
            "{name}: a panicking index must not be all PROVED\n{rows:#?}"
        );
    }
}
