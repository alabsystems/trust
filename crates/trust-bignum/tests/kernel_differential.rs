// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! THE EXECUTED KERNEL DIFFERENTIAL — `trust_bignum::Nat` vs the real
//! `clean_kernel` reduction lanes, on the same values.
//!
//! `tests/lean_semantics.rs` pins hand-transcribed Lean semantics with
//! clean-kernel source citations; `u64_agreement.rs`/`multi_limb.rs` pin
//! hardware-referenced `u128` agreement. Neither *executes* the kernel. This
//! file does: for every operation the carrier exposes, it builds the literal
//! application `Nat.<op> <lit a> <lit b>` as a kernel `Expr`, runs the real
//! `TypeChecker::whnf` — the SAME lane that reduces Nat literals when the
//! kernel checks a proof (`tc/reduction/nat.rs`, `reduce_nat`) — and compares
//! the kernel's literal against this runtime's answer, limb for limb.
//!
//! The two sides share NO arithmetic code (clean-kernel is a dev-dependency
//! only; the shipped runtime is zero-dependency), which is what makes
//! agreement evidence rather than tautology — the same frozen-R independence
//! argument, applied to the carrier. This suite is named in the
//! `OperationAgreement::TrustedRuntimeAgreement` TCB disclosure: it is the
//! executed half of the evidence class.
//!
//! Coverage: a full cross of edge values (zero, one, limb boundaries, 2^64,
//! 2^128, multi-limb giants) plus deterministic pseudo-random multi-limb
//! pairs, for `add`, `sub` (truncated), `mul`, `div` (`n/0 = 0`), `mod`
//! (`n%0 = n`), `beq`, and `ble`. Operands stay ≤ 4 limbs so `mul` remains
//! inside the kernel's 16-limb `checked_mul_big` bound — past it the kernel
//! deliberately leaves the term stuck, which the harness treats as a hard
//! failure rather than a skip, so the bound moving would be NOTICED here.

use clean_kernel::{BigNat, Environment, Expr, ExprKind, Literal, TypeChecker};
use trust_bignum::Nat;

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

/// `Nat.<op> <lit a> <lit b>` as a kernel expression.
fn binop_expr(op: &str, a: &[u64], b: &[u64]) -> Expr {
    Expr::app(
        Expr::app(Expr::const_str(op), Expr::bignat_lit(BigNat::from_limbs(a.to_vec()))),
        Expr::bignat_lit(BigNat::from_limbs(b.to_vec())),
    )
}

/// Run the kernel's whnf on `Nat.<op> a b` and demand a literal back.
///
/// A stuck term is a FAILURE, not a skip: every operand this harness builds is
/// inside the kernel's literal-reduction domain, so "did not reduce" means the
/// differential silently stopped measuring — the one way this suite could rot.
fn kernel_nat(tc: &TypeChecker<'_>, op: &str, a: &[u64], b: &[u64]) -> BigNat {
    let reduced = tc.whnf(&binop_expr(op, a, b));
    match reduced.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.clone(),
        other => panic!(
            "kernel whnf left `{op}` stuck on limbs {a:?} / {b:?}: got {other:?} — \
             the reduction lane this differential measures did not fire"
        ),
    }
}

/// Run the kernel's whnf on a boolean-valued `Nat.<op> a b`.
fn kernel_bool(tc: &TypeChecker<'_>, op: &str, a: &[u64], b: &[u64]) -> bool {
    let reduced = tc.whnf(&binop_expr(op, a, b));
    match reduced.kind() {
        ExprKind::Const(name, _) if name.to_string() == "Bool.true" => true,
        ExprKind::Const(name, _) if name.to_string() == "Bool.false" => false,
        other => panic!(
            "kernel whnf left `{op}` stuck on limbs {a:?} / {b:?}: got {other:?}"
        ),
    }
}

/// Read a kernel literal as a `trust_bignum::Nat`, through the canonicalizing
/// limb constructor — a VALUE conversion, not an arithmetic one: little-endian
/// limbs denote the same natural on both sides, and `from_limbs` only strips
/// most-significant zero limbs (the kernel spells zero `[0]` where this
/// runtime's canonical form is `[]`). No operation under test is involved.
fn as_runtime_value(kernel: &BigNat) -> Nat {
    Nat::from_limbs(kernel.limbs().to_vec())
}

/// One agreement check, all seven operations, one pair of limb vectors.
///
/// Both sides are constructed from the SAME limbs; the comparison is on
/// values (canonical form), with the decimal renderings in the failure
/// message so a divergence is actionable at any precision.
fn assert_agreement(tc: &TypeChecker<'_>, a_limbs: &[u64], b_limbs: &[u64]) {
    let a = Nat::from_limbs(a_limbs.to_vec());
    let b = Nat::from_limbs(b_limbs.to_vec());

    let arith: [(&str, Nat); 5] = [
        ("Nat.add", a.add(&b)),
        ("Nat.sub", a.sub(&b)),
        ("Nat.mul", a.mul(&b)),
        ("Nat.div", a.div(&b)),
        ("Nat.mod", a.rem(&b)),
    ];
    for (op, ours) in arith {
        let kernel = kernel_nat(tc, op, a_limbs, b_limbs);
        assert_eq!(
            as_runtime_value(&kernel),
            ours,
            "`{op}` diverged on a = {a}, b = {b}: kernel limbs {:?}, runtime {ours}",
            kernel.limbs(),
        );
    }

    assert_eq!(kernel_bool(tc, "Nat.beq", a_limbs, b_limbs), a == b, "beq on a = {a}, b = {b}");
    assert_eq!(kernel_bool(tc, "Nat.ble", a_limbs, b_limbs), a <= b, "ble on a = {a}, b = {b}");
}

/// xorshift64* — deterministic, seeded, dependency-free. Randomness here is
/// coverage spread, not entropy; a failure must reproduce, so the seed is
/// fixed and printed in the assert path via the values themselves.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Up to `max_limbs` random limbs, with bias toward boundary limb values
    /// (0, 1, u64::MAX) — where carry/borrow bugs live.
    fn limbs(&mut self, max_limbs: usize) -> Vec<u64> {
        let len = (self.next() as usize) % (max_limbs + 1);
        (0..len)
            .map(|_| match self.next() % 4 {
                0 => 0,
                1 => 1,
                2 => u64::MAX,
                _ => self.next(),
            })
            .collect()
    }
}

// ---------------------------------------------------------------------------
// The differential
// ---------------------------------------------------------------------------

/// Edge values, as limb vectors: every value `lean_semantics.rs` reasons about
/// by transcription is re-measured here against the executing kernel.
fn edge_values() -> Vec<Vec<u64>> {
    vec![
        vec![],                        // 0
        vec![1],                       // 1
        vec![2],
        vec![u64::MAX],                // 2^64 - 1
        vec![0, 1],                    // 2^64
        vec![1, 1],                    // 2^64 + 1
        vec![u64::MAX, u64::MAX],      // 2^128 - 1
        vec![0, 0, 1],                 // 2^128
        vec![5, 0, 0],                 // non-canonical spelling of 5
        vec![0, u64::MAX, 1],          // mixed magnitude
        vec![u64::MAX, 0, 0, 1],       // 4 limbs, sparse
    ]
}

#[test]
fn every_operation_agrees_with_the_kernel_on_the_edge_cross() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let edges = edge_values();
    for a in &edges {
        for b in &edges {
            assert_agreement(&tc, a, b);
        }
    }
}

#[test]
fn every_operation_agrees_with_the_kernel_on_randomized_multi_limb_values() {
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let mut rng = Rng(0x1657_8235_D5A6_29F1);
    for _ in 0..250 {
        let a = rng.limbs(4);
        let b = rng.limbs(4);
        assert_agreement(&tc, &a, &b);
    }
}

#[test]
fn the_division_by_zero_lane_is_measured_not_assumed() {
    // `n / 0 = 0` and `n % 0 = n` are the two places Lean's total functions
    // diverge hardest from Rust intuition. The edge cross above already hits
    // b = 0; this pins the pair EXPLICITLY so the property is named in a test
    // the day either side changes.
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    for a in edge_values() {
        let n = Nat::from_limbs(a.clone());
        assert_eq!(as_runtime_value(&kernel_nat(&tc, "Nat.div", &a, &[])), Nat::ZERO);
        assert_eq!(n.div(&Nat::ZERO), Nat::ZERO);
        assert_eq!(as_runtime_value(&kernel_nat(&tc, "Nat.mod", &a, &[])), n);
        assert_eq!(n.rem(&Nat::ZERO), n);
    }
}

#[test]
fn subtraction_truncates_identically_across_the_boundary() {
    // (a - b) with b > a is 0 on BOTH sides — measured at the exact boundary,
    // one below, one above, at multi-limb scale.
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let pairs: [(&[u64], &[u64]); 4] = [
        (&[0, 1], &[1, 1]),                 // 2^64 - (2^64 + 1) = 0
        (&[1, 1], &[0, 1]),                 // (2^64 + 1) - 2^64 = 1
        (&[u64::MAX], &[0, 1]),             // (2^64 - 1) - 2^64 = 0
        (&[0, 0, 1], &[u64::MAX, u64::MAX]), // 2^128 - (2^128 - 1) = 1
    ];
    for (a, b) in pairs {
        let ours = Nat::from_limbs(a.to_vec()).sub(&Nat::from_limbs(b.to_vec()));
        assert_eq!(as_runtime_value(&kernel_nat(&tc, "Nat.sub", a, b)), ours);
    }
}
