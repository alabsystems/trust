// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! A shared definedness/exactness check, never a proof or a source authority.

use crate::{Formula, Sort};

/// Whether this node is exactly `x % c` for an Int-sorted variable whose
/// authenticated declaration is unsigned, and a positive literal fitting that
/// same Rust integer type. The caller resolves the variable's unique declared
/// domain; it must not borrow an outer declaration beneath a quantifier.
///
/// In this fragment Rust cannot divide by zero or overflow, and its truncated
/// remainder is the mathematical Int remainder. Retaining the original node
/// therefore needs no wrapping translation or additional hypothesis. Computed
/// numerators, signed values, `/`, and nonliteral divisors are deliberately
/// outside this check. No solver result or definitional authority is granted.
#[must_use]
pub fn unsigned_literal_remainder_is_exact(
    formula: &Formula,
    domain_for_variable: impl FnOnce(&str) -> Option<(u32, bool)>,
) -> bool {
    let Formula::Rem(numerator, divisor) = formula else { return false };
    let name = match numerator.as_ref() {
        Formula::Var(name, Sort::Int) => name.as_str(),
        Formula::SymVar(name, Sort::Int) => name.as_str(),
        _ => return false,
    };
    let Some((width, false)) = domain_for_variable(name) else { return false };
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return false;
    }
    let literal = match divisor.as_ref() {
        Formula::Int(value) if *value > 0 => *value as u128,
        Formula::UInt(value) if *value > 0 => *value,
        _ => return false,
    };
    width == 128 || literal < (1_u128 << width)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn remainder(numerator: Formula, divisor: Formula) -> Formula {
        Formula::Rem(Box::new(numerator), Box::new(divisor))
    }

    #[test]
    fn only_total_unsigned_bare_variable_literal_remainders_are_exact() {
        let x = || Formula::var("x", Sort::Int);
        for width in [8, 16, 32, 64, 128] {
            let max = if width == 128 { u128::MAX } else { (1_u128 << width) - 1 };
            for divisor in [Formula::Int(1), Formula::Int(2), Formula::UInt(max)] {
                assert!(unsigned_literal_remainder_is_exact(&remainder(x(), divisor), |_| Some((
                    width, false
                ))));
            }
            assert!(!unsigned_literal_remainder_is_exact(&remainder(x(), Formula::Int(2)), |_| {
                Some((width, true))
            }));
            if width < 128 {
                assert!(!unsigned_literal_remainder_is_exact(
                    &remainder(x(), Formula::UInt(max + 1)),
                    |_| Some((width, false))
                ));
            }
        }
        let exact = remainder(x(), Formula::Int(2));
        assert!(!unsigned_literal_remainder_is_exact(&exact, |_| None));
        for width in [0, 1, 7, 24, 129] {
            assert!(!unsigned_literal_remainder_is_exact(&exact, |_| Some((width, false))));
        }
        for refused in [
            remainder(x(), Formula::Int(0)),
            remainder(x(), Formula::Int(-1)),
            remainder(x(), Formula::var("d", Sort::Int)),
            remainder(Formula::Add(Box::new(x()), Box::new(Formula::Int(1))), Formula::Int(2)),
            remainder(Formula::var("x", Sort::Bool), Formula::Int(2)),
            remainder(Formula::var("x", Sort::BitVec(32)), Formula::Int(2)),
            Formula::Div(Box::new(x()), Box::new(Formula::Int(2))),
        ] {
            assert!(
                !unsigned_literal_remainder_is_exact(&refused, |_| Some((32, false))),
                "{refused:?}"
            );
        }
        let symbolic = remainder(Formula::SymVar("x".into(), Sort::Int), Formula::Int(2));
        assert!(unsigned_literal_remainder_is_exact(&symbolic, |name| (name == "x")
            .then_some((32, false))));
    }

    #[test]
    fn exhaustive_u8_remainder_matches_its_mathematical_reading() {
        for divisor in 1..=u8::MAX {
            for numerator in 0..=u8::MAX {
                let machine = numerator % divisor;
                let mathematical = i128::from(numerator) % i128::from(divisor);
                assert_eq!(i128::from(machine), mathematical);
                assert!(0 <= mathematical && mathematical < i128::from(divisor));
            }
        }
    }
}
