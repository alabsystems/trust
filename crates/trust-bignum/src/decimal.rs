// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Decimal conversion — exact at any precision, fail-closed on parse.
//!
//! The parser accepts **ASCII digits only**: no sign (ℕ has none), no
//! whitespace, no `_` separators, no Unicode digits. Anything else is a typed
//! refusal naming the offending character and its byte offset — a carrier
//! runtime must never guess what a numeral meant. Leading zeros are accepted
//! (`"007"` is 7): they are redundant, not ambiguous.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Nat;

/// `10^0 ..= 10^19`; `10^19` is the largest power of ten below `2^64`, so the
/// parser and printer move 19 digits per limb operation.
const POW10: [u64; 20] = [
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
];

/// Why a decimal string was refused.
///
/// Manual `Display`/`Error` impls rather than `thiserror`: this crate's empty
/// dependency list is a design commitment (see `Cargo.toml`), and two small
/// impls do not justify a proc-macro closure inside a verified-binary runtime.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
pub enum ParseNatError {
    /// The input was empty. An empty string is not zero — it is nothing.
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    Empty,
    /// A character that is not an ASCII digit `0-9`.
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    InvalidDigit {
        /// Byte offset of the offending character in the input.
        #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
        offset: usize,
        /// The offending character itself.
        #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
        found: char,
    },
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl core::fmt::Display for ParseNatError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Empty => write!(
                f,
                "empty string is not a natural number; write `0` for zero"
            ),
            Self::InvalidDigit { offset, found } => write!(
                f,
                "invalid character {found:?} at byte offset {offset}: a Nat numeral is \
                 ASCII digits 0-9 only — no sign, no whitespace, no separators"
            ),
        }
    }
}

#[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
impl core::error::Error for ParseNatError {}

impl Nat {
    /// Parse a decimal numeral. ASCII digits only; fail-closed otherwise.
    ///
    /// # Errors
    ///
    /// * [`ParseNatError::Empty`] on the empty string;
    /// * [`ParseNatError::InvalidDigit`] on the first non-digit character,
    ///   naming it and its offset.
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn from_decimal(text: &str) -> Result<Self, ParseNatError> {
        if text.is_empty() {
            return Err(ParseNatError::Empty);
        }
        for (offset, found) in text.char_indices() {
            if !found.is_ascii_digit() {
                return Err(ParseNatError::InvalidDigit { offset, found });
            }
        }
        // All-ASCII-digit input; fold 19 digits at a time, most significant
        // first: value = value * 10^len(chunk) + chunk.
        let mut value = Self::ZERO;
        for chunk in text.as_bytes().chunks(19) {
            let mut chunk_value = 0u64;
            for &b in chunk {
                chunk_value = chunk_value * 10 + u64::from(b - b'0');
            }
            value = value.mul_limb(POW10[chunk.len()]).add_limb(chunk_value);
        }
        Ok(value)
    }

    /// Render as decimal — exact at any precision, no scientific notation, no
    /// truncation. The inverse of [`Nat::from_decimal`] up to leading zeros.
    #[must_use]
    #[cfg_attr(feature = "rustc-dep-of-std", stable(feature = "trust_bignum", since = "1.0.0"))]
    pub fn to_decimal(&self) -> String {
        if self.is_zero() {
            return String::from("0");
        }
        // Peel 19 digits per step: repeated division by 10^19.
        let chunk_divisor = POW10[19];
        let mut rest = self.clone();
        let mut chunks: Vec<u64> = Vec::new();
        while !rest.is_zero() {
            let (q, r) = rest.div_rem_limb(chunk_divisor);
            chunks.push(r);
            rest = q;
        }
        let mut out = String::new();
        // Most significant chunk bare; the rest zero-padded to 19.
        let mut chunks = chunks.into_iter().rev();
        if let Some(first) = chunks.next() {
            out.push_str(&alloc::format!("{first}"));
        }
        for chunk in chunks {
            out.push_str(&alloc::format!("{chunk:019}"));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::ParseNatError;
    use crate::Nat;
    use alloc::string::ToString;
    use alloc::vec;

    #[test]
    fn round_trips_exactly_on_and_past_the_limb_boundary() {
        for text in [
            "0",
            "1",
            "9",
            "10",
            "18446744073709551615",                    // 2^64 - 1: last single-limb value
            "18446744073709551616",                    // 2^64: first two-limb value
            "340282366920938463463374607431768211456", // 2^128
            "10000000000000000000",                    // 10^19: the chunk boundary itself
            "9999999999999999999",                     // 10^19 - 1
            "100000000000000000000000000000000000000000000000000000000000000000000000000000001",
        ] {
            let parsed = Nat::from_decimal(text).expect("valid numeral");
            assert_eq!(parsed.to_decimal(), text, "round trip must be exact");
        }
    }

    #[test]
    fn parses_known_limb_values_exactly() {
        assert_eq!(Nat::from_decimal("0").unwrap(), Nat::ZERO);
        assert_eq!(
            Nat::from_decimal("18446744073709551615").unwrap(),
            Nat::from_u64(u64::MAX)
        );
        assert_eq!(
            Nat::from_decimal("18446744073709551616").unwrap(),
            Nat::from_limbs(vec![0, 1])
        );
        assert_eq!(
            Nat::from_decimal("340282366920938463463374607431768211456").unwrap(),
            Nat::from_limbs(vec![0, 0, 1])
        );
    }

    #[test]
    fn leading_zeros_are_redundant_not_ambiguous() {
        assert_eq!(Nat::from_decimal("007").unwrap(), Nat::from_u64(7));
        assert_eq!(Nat::from_decimal("000").unwrap(), Nat::ZERO);
        // ... and rendering is canonical, so the round trip normalizes.
        assert_eq!(Nat::from_decimal("007").unwrap().to_decimal(), "7");
    }

    #[test]
    fn refuses_everything_that_is_not_an_ascii_numeral() {
        assert_eq!(Nat::from_decimal(""), Err(ParseNatError::Empty));
        for (text, offset, found) in [
            ("+1", 0, '+'),   // no sign — ℕ has none
            ("-1", 0, '-'),   // no negatives, ever
            (" 1", 0, ' '),   // no whitespace
            ("1 ", 1, ' '),
            ("1_000", 1, '_'), // no separators
            ("12a3", 2, 'a'),
            ("١٢", 0, '١'),   // no non-ASCII digits: fail closed, never guess
            ("⁵", 0, '⁵'),
        ] {
            assert_eq!(
                Nat::from_decimal(text),
                Err(ParseNatError::InvalidDigit { offset, found }),
                "{text:?} must be refused at the right position"
            );
        }
    }

    #[test]
    fn display_and_fromstr_are_the_decimal_lane() {
        let n: Nat = "340282366920938463463374607431768211456".parse().expect("valid");
        assert_eq!(n, Nat::from_limbs(vec![0, 0, 1]));
        assert_eq!(n.to_string(), "340282366920938463463374607431768211456");
        assert!("12x".parse::<Nat>().is_err());
    }

    #[test]
    fn parse_errors_render_with_position_and_character() {
        let err = Nat::from_decimal("12a3").unwrap_err();
        let text = err.to_string();
        assert!(text.contains("'a'"), "{text}");
        assert!(text.contains("offset 2"), "{text}");
        assert!(
            ParseNatError::Empty.to_string().contains("write `0`"),
            "the refusal must carry the fix (v7/D3)"
        );
    }
}
