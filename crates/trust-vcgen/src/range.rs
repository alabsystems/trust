// trust_vcgen/range.rs: Shared integer range utilities
//
// Consolidates type_max_formula, type_min_formula, input_range_constraint,
// signed_min, signed_max, and unsigned_max that were previously duplicated
// across overflow.rs, shifts.rs, and casts.rs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

/// Return a formula representing the maximum value for an integer type.
/// For unsigned 128-bit, this returns Formula::UInt(u128::MAX) since u128::MAX
/// exceeds i128::MAX and cannot be represented as Formula::Int.
#[must_use]
pub(crate) fn type_max_formula(width: u32, signed: bool) -> Formula {
    // TOTAL (panic-free for every `u32` width); identical to the historical body for
    // every in-domain unsigned width (8/16/32/64/128). Out-of-domain widths — which no
    // real integer type uses — saturate to `i128::MAX` instead of overflowing: the
    // historical `(1i128 << width) - 1` `else` arm underflowed at `width == 127` and
    // shift-overflowed at `width >= 129`. Mirrored verbatim by
    // `trust_semantics::type_max_formula`.
    if signed {
        Formula::Int(signed_max(width))
    } else if width == 128 {
        Formula::UInt(u128::MAX)
    } else if width <= 126 {
        Formula::Int((1i128 << width) - 1)
    } else {
        Formula::Int(i128::MAX)
    }
}

/// Return a formula representing the minimum value for an integer type.
#[must_use]
pub(crate) fn type_min_formula(width: u32, signed: bool) -> Formula {
    if signed { Formula::Int(signed_min(width)) } else { Formula::Int(0) }
}

/// Minimum value for a signed integer of the given bit width.
///
/// Precondition: `1 <= width && width <= 128` (the only meaningful signed
/// bit-widths). Total/panic-free for every `u32`: in-contract widths return
/// exactly `-(1i128 << (width - 1))` (and `i128::MIN` at 128) — byte-identical
/// to `trust_semantics::signed_min`; out-of-domain widths (`0` or `> 128`),
/// which previously panicked with `Overflow(Sub)` / `Overflow(Shl)`, saturate
/// to `i128::MIN` (a sound bound, never makes a real overflow look in-range).
#[must_use]
pub(crate) fn signed_min(width: u32) -> i128 {
    if width == 128 {
        i128::MIN
    } else if width >= 1 && width <= 127 {
        -(1i128 << (width - 1))
    } else {
        i128::MIN
    }
}

/// Maximum value for a signed integer of the given bit width.
///
/// Precondition: `1 <= width && width <= 128`. Total/panic-free: in-contract
/// widths return exactly `(1i128 << (width - 1)) - 1` (and `i128::MAX` at 128)
/// — byte-identical to `trust_semantics::signed_max`; out-of-domain widths
/// saturate to `i128::MAX` (sound bound).
#[must_use]
pub(crate) fn signed_max(width: u32) -> i128 {
    if width == 128 {
        i128::MAX
    } else if width >= 1 && width <= 127 {
        (1i128 << (width - 1)) - 1
    } else {
        i128::MAX
    }
}

/// Maximum value for an unsigned integer of the given bit width.
///
/// Total/panic-free for every `u32`: in-domain widths (`0..=128`) are exact, and
/// an out-of-domain width (`> 128`, no such unsigned type) SATURATES to
/// `u128::MAX` — mirroring `signed_min`/`signed_max`'s out-of-contract handling.
/// The `>= 128` guard keeps `1u128 << width` from shift-overflowing when
/// `width > 128`; found by verifying this file with trustc's OWN verifier (the
/// flywheel), which flagged the old `width == 128`-only branch as a `[shift:left]`
/// violation. Behavior-identical for every real width (`8..=128`).
#[must_use]
pub(crate) fn unsigned_max(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// Constrain a variable to the valid range of its integer type.
#[must_use]
pub(crate) fn input_range_constraint(var: &Formula, width: u32, signed: bool) -> Formula {
    let min_f = type_min_formula(width, signed);
    let max_f = type_max_formula(width, signed);

    Formula::And(vec![
        Formula::Le(Box::new(min_f), Box::new(var.clone())),
        Formula::Le(Box::new(var.clone()), Box::new(max_f)),
    ])
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every width a real integer type can have, plus the out-of-domain widths
    /// whose saturating behaviour both copies must agree on (`0` underflows the
    /// `width - 1` shift; `127` is where the historical `(1 << w) - 1` wrapped;
    /// `129`/`255` shift past the i128 word).
    const CROSS_CHECK_WIDTHS: [u32; 11] = [0, 1, 7, 8, 16, 32, 64, 126, 127, 128, 255];

    /// The bound helpers are copied verbatim into `trust_semantics`, which
    /// states the Clean-kernel `RustVIR.noOverflow` denotation. The copy is
    /// what makes "the kernel definition and the SMT obligation denote the same
    /// arithmetic fact" true, so a divergence between the two is precisely a
    /// false-proof hazard: the kernel would certify a range the generator never
    /// asked about. Comparing them here — against the real definitions rather
    /// than a restatement of them — is what turns that claim into an enforced
    /// invariant.
    #[test]
    fn semantics_copy_of_the_bound_helpers_is_still_identical() {
        for width in CROSS_CHECK_WIDTHS {
            assert_eq!(
                signed_min(width),
                trust_semantics::signed_min(width),
                "signed_min diverged at width {width}"
            );
            assert_eq!(
                signed_max(width),
                trust_semantics::signed_max(width),
                "signed_max diverged at width {width}"
            );
            for signed in [false, true] {
                assert_eq!(
                    type_min_formula(width, signed),
                    trust_semantics::type_min_formula(width, signed),
                    "type_min_formula diverged at width {width} signed {signed}"
                );
                assert_eq!(
                    type_max_formula(width, signed),
                    trust_semantics::type_max_formula(width, signed),
                    "type_max_formula diverged at width {width} signed {signed}"
                );
            }
        }
    }

    /// The stronger form of the same invariant: the kernel-side VIOLATION
    /// formula must be the exact term the overflow VC generator emits for the
    /// Add/Sub Int class (`overflow_vc.rs`'s `out_of_range` disjunction), not
    /// merely a formula built from equal bounds. Structural equality is the
    /// right test because the kernel re-checks a term, not a semantics.
    #[test]
    fn semantics_violation_formula_is_the_emitted_out_of_range_term() {
        for width in CROSS_CHECK_WIDTHS {
            for signed in [false, true] {
                let result = Formula::Var("result".into(), Sort::Int);
                let emitted = Formula::Or(vec![
                    Formula::Lt(
                        Box::new(result.clone()),
                        Box::new(type_min_formula(width, signed)),
                    ),
                    Formula::Gt(Box::new(result), Box::new(type_max_formula(width, signed))),
                ]);
                assert_eq!(
                    emitted,
                    trust_semantics::noOverflow_violation_formula(width, signed, "result"),
                    "violation term diverged at width {width} signed {signed}"
                );
            }
        }
    }

    #[test]
    fn test_type_max_formula_u8() {
        assert_eq!(type_max_formula(8, false), Formula::Int(255));
    }

    #[test]
    fn test_type_max_formula_i8() {
        assert_eq!(type_max_formula(8, true), Formula::Int(127));
    }

    #[test]
    fn test_type_max_formula_u128() {
        assert_eq!(type_max_formula(128, false), Formula::UInt(u128::MAX));
    }

    #[test]
    fn test_type_max_formula_i128() {
        assert_eq!(type_max_formula(128, true), Formula::Int(i128::MAX));
    }

    #[test]
    fn test_type_min_formula_u32() {
        assert_eq!(type_min_formula(32, false), Formula::Int(0));
    }

    #[test]
    fn test_type_min_formula_i32() {
        assert_eq!(type_min_formula(32, true), Formula::Int(-(1i128 << 31)));
    }

    #[test]
    fn test_type_min_formula_i128() {
        assert_eq!(type_min_formula(128, true), Formula::Int(i128::MIN));
    }

    #[test]
    fn test_signed_min_max_i8() {
        assert_eq!(signed_min(8), -128);
        assert_eq!(signed_max(8), 127);
    }

    #[test]
    fn test_signed_min_max_i128() {
        assert_eq!(signed_min(128), i128::MIN);
        assert_eq!(signed_max(128), i128::MAX);
    }

    #[test]
    fn test_unsigned_max_u8() {
        assert_eq!(unsigned_max(8), 255);
    }

    #[test]
    fn test_unsigned_max_u128() {
        assert_eq!(unsigned_max(128), u128::MAX);
    }

    #[test]
    fn test_input_range_constraint_u32() {
        let var = Formula::Var("x".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 32, false);

        match constraint {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                // Check lower bound: 0 <= x
                assert!(matches!(
                    &clauses[0],
                    Formula::Le(min, v) if matches!(min.as_ref(), Formula::Int(0))
                        && matches!(v.as_ref(), Formula::Var(n, _) if n == "x")
                ));
                // Check upper bound: x <= (2^32 - 1)
                assert!(matches!(
                    &clauses[1],
                    Formula::Le(v, max) if matches!(v.as_ref(), Formula::Var(n, _) if n == "x")
                        && matches!(max.as_ref(), Formula::Int(n) if *n == (1i128 << 32) - 1)
                ));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_input_range_constraint_i16() {
        let var = Formula::Var("y".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 16, true);

        match constraint {
            Formula::And(clauses) => {
                assert_eq!(clauses.len(), 2);
                assert!(matches!(
                    &clauses[0],
                    Formula::Le(min, _) if matches!(min.as_ref(), Formula::Int(n) if *n == -32768)
                ));
                assert!(matches!(
                    &clauses[1],
                    Formula::Le(_, max) if matches!(max.as_ref(), Formula::Int(n) if *n == 32767)
                ));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }

    #[test]
    fn test_u128_input_range_constraint_uses_uint_upper_bound() {
        let var = Formula::Var("x".into(), Sort::Int);
        let constraint = input_range_constraint(&var, 128, false);

        match constraint {
            Formula::And(clauses) => {
                assert!(clauses.iter().any(|clause| matches!(
                    clause,
                    Formula::Le(_, rhs) if matches!(rhs.as_ref(), Formula::UInt(n) if *n == u128::MAX)
                )));
            }
            other => panic!("expected And, got {other:?}"),
        }
    }
}
