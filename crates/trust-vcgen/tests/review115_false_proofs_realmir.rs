// Trust (2026-10-10, review round 115): meeting a single-assignment temp's merged
// interval with its def-site interval (`narrow_single_assignments_to_their_def`) let
// two pre-existing interval-transfer holes reach the VCs, which the type-range seed of
// the blocks before the def had diluted: arithmetic over a `u128` read an unknown
// operand as the `i128` range (`(x >> 121) as i32` was `[-64, 63]`; `x / 2^121`,
// `(x % y) >> 121` and `x as i128` after `x > 100` the same), each kernel-certified
// under `-Ztrust-policy=certify` on stage-1 sa161; and a `copy_nonoverlapping`
// statement was a no-op in the interval transfer while the SMT lane havocs every
// local at it. Round 116: a `Drop` terminator, which the SMT lane havocs at like a
// call, was not a write in the interval transfer at all, so a guard whose `drop`
// stores through the `&mut` it holds left the stale interval on its referent (that
// one predates the narrowing: `x / m` itself was kernel-certified). Real extracted
// MIR (`-Ztrust-dump=mir`) of the programs quoted on each test, in
// `fixtures/review115/`.
use trust_types::*;
use trust_vcgen::generate_vcs_with_discharge;

#[path = "support/test_router.rs"]
mod test_router;

fn load(name: &str) -> VerifiableFunction {
    let path = format!("{}/tests/fixtures/review115/{name}.json", env!("CARGO_MANIFEST_DIR"));
    let json = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
    serde_json::from_str(&json).expect("fixture MIR must deserialize")
}

/// Every row of the DISCHARGE path (the compiler's: interval proofs, then the
/// interval-augmented rest through the solver) that `keep` selects, with its verdict.
fn rows(name: &str, keep: fn(&VcKind) -> bool) -> Vec<(String, VerificationResult)> {
    let func = load(name);
    let router = test_router::deterministic_test_router();
    let (rest, discharged) = generate_vcs_with_discharge(&func);
    let mut rows: Vec<(String, VerificationResult)> = discharged
        .into_iter()
        .filter(|(vc, _)| keep(&vc.kind))
        .map(|(vc, r)| (vc.formula.to_smtlib(), r))
        .collect();
    rows.extend(rest.into_iter().filter(|vc| keep(&vc.kind)).map(|vc| {
        let r = router.verify_all(std::slice::from_ref(&vc)).into_iter().next().unwrap().1;
        (vc.formula.to_smtlib(), r)
    }));
    rows
}

fn assert_not_all_proved(name: &str, keep: fn(&VcKind) -> bool) {
    let rows = rows(name, keep);
    assert!(!rows.is_empty(), "{name}: the panicking operation must carry a row");
    assert!(
        rows.iter().any(|(_, r)| !matches!(r, VerificationResult::Proved { .. })),
        "{name}: a panicking program must not be all PROVED\n{rows:#?}"
    );
}

fn is_bounds(k: &VcKind) -> bool {
    matches!(k, VcKind::IndexOutOfBounds | VcKind::SliceBoundsCheck)
}

fn is_div_zero(k: &VcKind) -> bool {
    matches!(k, VcKind::DivisionByZero)
}

/// `let t = (x >> 121) as i32; a[(t + 64) as usize]` on `a: [u8; 128]`, `x: u128`
/// (`x = u128::MAX` indexes 191); `let t = (x / 2^121) as i32; 100 / (t - 64) as u32`
/// (`x = 64 << 121` divides by zero); `((x % y) >> 121) as i32` the same with
/// `y = u128::MAX`; and `if x > 100 { let s = ((x as i128) / 2^121) as i32; 100 /
/// (s + 64) as u32 }` (`x = 2^127` makes `x as i128` negative and `s = -64`).
#[test]
fn arithmetic_over_a_u128_bounds_nothing() {
    assert_not_all_proved("u128_s2", is_bounds);
    assert_not_all_proved("u128_h_div3", is_div_zero);
    assert_not_all_proved("u128_h_rem2", is_div_zero);
    assert_not_all_proved("u128_c1", is_div_zero);
}

/// `let mut m = 1usize; copy_nonoverlapping(&v, &mut m, 1); let t = m; a[t]` on
/// `a: [u8; 4]` through `core::intrinsics::copy_nonoverlapping`, which rustc lowers
/// to a statement (`v = 4` panics): the interval transfer kept `t ∈ [1, 1]`.
#[test]
fn a_pointer_copy_statement_forgets_the_intervals_it_may_write() {
    assert_not_all_proved("copy_intrinsic", is_bounds);
}

/// A guard holding `&mut m` whose `Drop` stores into it, dropped at the end of a
/// scope: `let mut m = 1; { let _g = H(&mut m); } x / m` (`H::drop` stores 0), the
/// copy `let t = m; m = y; x / t`, `G(&mut m, v)` (stores `v`, `v = 0` divides by
/// zero) directly, inside an `Option`, and through a `&mut` parameter's pointee.
#[test]
fn a_drop_forgets_the_intervals_it_may_write() {
    for name in ["drop_e5", "drop_g1", "drop_writes_div", "drop_in_option", "drop_param_pointee"] {
        assert_not_all_proved(name, is_div_zero);
    }
}

/// Review round 118: `let mut x = 1u64; asm!("mov {0}, {1}", inout(reg) x, in(reg) v);
/// 100 / x` (`v = 0` divides by zero). The `Opaque` terminator inline assembly lowers
/// to records no operands, so neither lane saw the output operand write `x`: the
/// division row was kernel-certified on the stale `x = 1` (the function is refused by
/// its unsupported-assembly rows).
#[test]
fn an_inline_asm_output_forgets_what_it_may_write() {
    assert_not_all_proved("asm_output", is_div_zero);
}
