// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT

use super::Formula;

/// Whether a literal makes Rust remainder total over the declared integer
/// domain. Positive, representable divisors exclude both zero and signed
/// MIN % -1; a computed or symbolic divisor needs a separate definedness proof.
/// Shared by the VC generator and compiler-proposition transport so admission
/// cannot silently differ at that boundary. This check grants no proof credit.
#[must_use]
pub fn is_total_machine_remainder_divisor(divisor: &Formula, width: u32, signed: bool) -> bool {
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return false;
    }
    let value = match divisor {
        Formula::Int(value) if *value > 0 => *value as u128,
        Formula::UInt(value) if *value > 0 => *value,
        _ => return false,
    };
    let max = if signed {
        (1_u128 << (width - 1)) - 1
    } else if width == 128 {
        u128::MAX
    } else {
        (1_u128 << width) - 1
    };
    value <= max
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn positive_machine_remainder_divisors_are_total_for_all_eight_bit_inputs() {
        for divisor in 1..=u8::MAX {
            assert!(is_total_machine_remainder_divisor(&Formula::UInt(divisor.into()), 8, false));
            for dividend in 0..=u8::MAX {
                assert!(dividend.checked_rem(divisor).is_some());
            }
        }
        for divisor in 1..=i8::MAX {
            assert!(is_total_machine_remainder_divisor(&Formula::Int(divisor.into()), 8, true));
            for dividend in i8::MIN..=i8::MAX {
                assert!(dividend.checked_rem(divisor).is_some());
            }
        }
    }

    #[test]
    fn positive_machine_remainder_divisors_respect_width_and_literal_boundaries() {
        for width in [8, 16, 32, 64, 128] {
            for signed in [false, true] {
                let max =
                    if signed { (1_u128 << (width - 1)) - 1 } else { u128::MAX >> (128 - width) };
                assert!(is_total_machine_remainder_divisor(&Formula::UInt(max), width, signed));
                if let Some(outside) = max.checked_add(1) {
                    assert!(!is_total_machine_remainder_divisor(
                        &Formula::UInt(outside),
                        width,
                        signed
                    ));
                }
                for divisor in [
                    Formula::Int(0),
                    Formula::UInt(0),
                    Formula::Int(-1),
                    Formula::Var("divisor".into(), super::super::Sort::Int),
                    Formula::Add(Box::new(Formula::Int(1)), Box::new(Formula::Int(1))),
                ] {
                    assert!(!is_total_machine_remainder_divisor(&divisor, width, signed));
                }
            }
        }
        for width in [0, 1, 7, 24, 129, u32::MAX] {
            assert!(!is_total_machine_remainder_divisor(&Formula::Int(1), width, false));
        }
        assert!(i8::MIN.checked_rem(-1).is_none());
    }
}
