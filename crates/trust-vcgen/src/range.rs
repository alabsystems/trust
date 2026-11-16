// trust_vcgen/range.rs: Shared integer range utilities
//
// Integer bounds come from trust-semantics, the same definitions used by
// the kernel-facing overflow model. Range construction remains local.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;

// One implementation owns both VC bounds and kernel-facing bounds. Keeping
// this as an import also retains the canonical functions' existing contracts.
pub(crate) use trust_semantics::{signed_max, signed_min, type_max_formula, type_min_formula};

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

/// The exact mathematical carrier of a Rust scalar lowered to `Sort::Int`.
///
/// `char` must remain distinct from `u32`: its valid values stop at
/// `char::MAX` and exclude the surrogate interval. Treating it as an ordinary
/// 32-bit unsigned integer is conservative for proof attempts but is unsound
/// for bidirectional lanes that consume SAT as an executable counterexample.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RustScalarRange {
    Integer { width: u32, signed: bool },
    Char,
}

#[must_use]
pub(crate) fn rust_scalar_range(ty: &Ty) -> Option<RustScalarRange> {
    if matches!(ty, Ty::Char) {
        return Some(RustScalarRange::Char);
    }
    Some(RustScalarRange::Integer { width: ty.int_width()?, signed: ty.is_signed() })
}

/// Constrain an integer-sorted value to the exact Rust scalar carrier.
#[must_use]
pub(crate) fn rust_scalar_range_constraint(var: &Formula, range: RustScalarRange) -> Formula {
    match range {
        RustScalarRange::Integer { width, signed } => input_range_constraint(var, width, signed),
        RustScalarRange::Char => Formula::And(vec![
            Formula::Le(Box::new(Formula::Int(0)), Box::new(var.clone())),
            Formula::Le(Box::new(var.clone()), Box::new(Formula::Int(char::MAX as i128))),
            Formula::Or(vec![
                Formula::Le(Box::new(var.clone()), Box::new(Formula::Int(0xD7FF))),
                Formula::Ge(Box::new(var.clone()), Box::new(Formula::Int(0xE000))),
            ]),
        ]),
    }
}

#[must_use]
pub(crate) fn rust_type_range_constraint(var: &Formula, ty: &Ty) -> Option<Formula> {
    Some(rust_scalar_range_constraint(var, rust_scalar_range(ty)?))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every width a real integer type can have, plus the out-of-domain widths
    /// whose saturating behaviour the shared definitions retain (`0` underflows the
    /// `width - 1` shift; `127` is where the historical `(1 << w) - 1` wrapped;
    /// `129`/`255` shift past the i128 word).
    const CROSS_CHECK_WIDTHS: [u32; 11] = [0, 1, 7, 8, 16, 32, 64, 126, 127, 128, 255];

    /// Check the shared bounds against arithmetic independent of their shift
    /// implementation, including sentinel widths and the full u128 boundary.
    #[test]
    fn shared_bounds_match_independent_integer_carriers() {
        for width in (0..=256).chain([u32::MAX]) {
            let signed_magnitude = (1..=128).contains(&width)
                .then(|| 2u128.pow(width - 1));
            let min = signed_magnitude
                .map_or(i128::MIN, |m| -i128::try_from(m - 1).unwrap() - 1);
            let max = signed_magnitude
                .map_or(i128::MAX, |m| i128::try_from(m - 1).unwrap());
            assert_eq!(signed_min(width), min, "width {width}");
            assert_eq!(signed_max(width), max, "width {width}");
            assert_eq!(type_min_formula(width, true), Formula::Int(min));
            assert_eq!(type_max_formula(width, true), Formula::Int(max));
            assert_eq!(type_min_formula(width, false), Formula::Int(0));
            let unsigned = if width == 128 {
                Formula::UInt(u128::MAX)
            } else if width <= 127 {
                Formula::Int(i128::try_from(2u128.pow(width) - 1).unwrap())
            } else {
                Formula::Int(i128::MAX)
            };
            assert_eq!(type_max_formula(width, false), unsigned, "width {width}");
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
    fn char_range_is_not_the_u32_range() {
        let c = Formula::Var("c".into(), Sort::Int);
        assert_eq!(
            rust_type_range_constraint(&c, &Ty::Char),
            Some(Formula::And(vec![
                Formula::Le(Box::new(Formula::Int(0)), Box::new(c.clone())),
                Formula::Le(Box::new(c.clone()), Box::new(Formula::Int(char::MAX as i128)),),
                Formula::Or(vec![
                    Formula::Le(Box::new(c.clone()), Box::new(Formula::Int(0xD7FF))),
                    Formula::Ge(Box::new(c), Box::new(Formula::Int(0xE000))),
                ]),
            ]))
        );
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
