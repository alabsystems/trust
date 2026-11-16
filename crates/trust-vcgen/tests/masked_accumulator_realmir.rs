// Trust (2026-10-10, sweep p21): `s = (s + b as u32) & 0xffff` in a loop was refused
// `s + b` overflow. Two interval holes: `x & m` with `x` unknown was Top although a
// non-negative `m` bounds it alone, and the function-wide environment joined the
// type-range seed of blocks where the add temp `_10 = copy s` held no value yet. Real
// extracted MIR (`-Ztrust-dump=mir`) of the programs quoted on each test, in
// `fixtures/masked_accumulator/`.
use trust_types::*;
use trust_vcgen::generate_vcs_with_discharge;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/masked_accumulator/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every overflow row of the DISCHARGE path (the compiler's: interval proofs, then the
/// interval-augmented rest through the solver), with its operator and verdict.
fn overflow_rows(name: &str) -> Vec<(BinOp, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    let (rest, discharged) = generate_vcs_with_discharge(&func);
    let op = |k: &VcKind| match k {
        VcKind::ArithmeticOverflow { op, .. } => Some(*op),
        _ => None,
    };
    let mut rows: Vec<(BinOp, VerificationResult)> =
        discharged.into_iter().filter_map(|(vc, r)| Some((op(&vc.kind)?, r))).collect();
    rows.extend(rest.into_iter().filter_map(|vc| {
        let op = op(&vc.kind)?;
        Some((op, router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1))
    }));
    rows
}

fn proved(rows: &[(BinOp, VerificationResult)], op: BinOp) -> bool {
    let of_op: Vec<_> = rows.iter().filter(|(o, _)| *o == op).collect();
    assert!(!of_op.is_empty(), "no {op:?} overflow row in {rows:#?}");
    of_op.iter().all(|(_, r)| matches!(r, VerificationResult::Proved { .. }))
}

/// `let mut s: u32 = 0; for &b in data { s = (s + b as u32) & 0xffff; } s as u16`
/// (sweep p21 `fold_checksum`), and the same loop followed by `s * 65537`, whose
/// product reaches exactly `u32::MAX`; each row is proved. Signed: `s: i32` masked by
/// `0x7fff` over `b as i32` with `b: i8` (a negative `b` never makes `s + b` overflow
/// either).
#[test]
fn a_masked_accumulator_bounds_its_own_add() {
    assert!(proved(&overflow_rows("fold_checksum"), BinOp::Add));
    let rows = overflow_rows("pos_mul_after");
    assert!(proved(&rows, BinOp::Add) && proved(&rows, BinOp::Mul), "{rows:#?}");
    assert!(proved(&overflow_rows("pos_signed_mask"), BinOp::Add));
}

/// Controls, each of which can overflow: the mask `0xffff_ffff` bounds nothing on a
/// `u32`; `s * 70000` after the `0xffff` loop exceeds `u32::MAX`; a negative mask
/// (`& -2` on `i32`) keeps the sign bit; and the copy temp of an unmasked `u8` counter
/// (`let t = x; x = t + 1` over `0..n`) is not bounded by its def site.
#[test]
fn a_mask_that_does_not_bound_proves_nothing() {
    assert!(!proved(&overflow_rows("neg_widemask"), BinOp::Add));
    let rows = overflow_rows("neg_mul_after");
    assert!(proved(&rows, BinOp::Add) && !proved(&rows, BinOp::Mul), "{rows:#?}");
    assert!(!proved(&overflow_rows("neg_signed_negmask"), BinOp::Add));
    assert!(!proved(&overflow_rows("neg_temp_loop"), BinOp::Add));
}
