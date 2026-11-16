// Trust (2026-10-11, sweep2 n13_div_round): `b != 0 ⟹ a % b < b` was emitted only
// for a constant, length or min/max-result divisor, so `if b == 0 { return 0 } b - a %
// b` on a parameter `b` was refuted with `b = 1, a % b = 2`. A never-written
// parameter or statement-defined single-static-assignment divisor now carries the
// fact. Real extracted MIR (`-Ztrust-dump=mir`) in `fixtures/rem_symbolic_divisor/`.
use trust_types::*;
use trust_vcgen::generate_vcs_with_discharge;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/rem_symbolic_divisor/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every subtraction-overflow row of the discharge path, with its verdict.
fn sub_rows(name: &str) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    let (rest, discharged) = generate_vcs_with_discharge(&func);
    let keep = |k: &VcKind| matches!(k, VcKind::ArithmeticOverflow { op: BinOp::Sub, .. });
    let mut rows: Vec<(String, VerificationResult)> = discharged
        .into_iter()
        .filter(|(vc, _)| keep(&vc.kind))
        .map(|(vc, r)| (vc.formula.to_smtlib(), r))
        .collect();
    rows.extend(rest.into_iter().filter(|vc| keep(&vc.kind)).map(|vc| {
        let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
        (vc.formula.to_smtlib(), r)
    }));
    assert!(!rows.is_empty(), "{name}: the subtraction must carry an overflow row");
    rows
}

/// `let r = a % b; b - r` (u64 parameter) and `b - a % b` (u32), each after `b != 0`.
/// (`let b = nz.get(); b - a % b` stays out: a call destination divisor carries no
/// fact, so a row hanging on an unmodelled return keeps its Unknown verdict.)
#[test]
fn a_remainder_is_below_a_single_valued_divisor() {
    for name in ["rem_param", "rem_inline_u32"] {
        let rows = sub_rows(name);
        assert!(
            rows.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. })),
            "{name}: every subtraction row must be proved\n{rows:#?}"
        );
    }
}

/// `b - r - 2` (underflows for `b = 1`) and a divisor reassigned after the remainder
/// (`d = a & 1; d - r` underflows for `a = 2, b = 3`).
#[test]
fn the_bound_is_strict_and_needs_the_divisor_unchanged() {
    for name in ["rem_bound_is_one_short", "rem_divisor_reassigned"] {
        let rows = sub_rows(name);
        assert!(
            rows.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
            "{name}: an underflowing subtraction must not be all PROVED\n{rows:#?}"
        );
    }
}
