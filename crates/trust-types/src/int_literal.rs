//! trust-types: the ONE reader of an integer literal written in a contract predicate.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache 2.0
//!
//! WHY THIS IS ONE MODULE AND NOT TWO COPIES
//! -----------------------------------------
//! Two text parsers read a contract predicate. The compiler's snippet tokenizer
//! (`rustc_mir_transform::trust_contract_query`) is the lane every `ensures`
//! takes; this crate's [`crate::spec_parse`] is the lane `requires`,
//! `invariant` and `decreases` take, and it is also the parser that re-reads
//! the snippet lowerer's own output. Before 2026-08-29 both accepted BARE
//! DECIMAL DIGITS and nothing else, which is recorded as §13.1 of
//! `docs/STRICT_VERIFICATION_FRAGMENT.md`:
//!
//! ```text
//! ensures result <= 999_999_999   ->  SpecEnsuresUnparseable, both rows UNKNOWN
//! ensures result <= 999999999     ->  proves
//! ```
//!
//! and the identical constant in the function BODY was fine either way. In the
//! `ensures` lane the refusal carried NO diagnostic at all: the clause became
//! `Unsupported`, the proof simply did not happen, and the only symptom was an
//! UNKNOWN row.
//!
//! Fixing that in two places would put one grammar in two hands, which is how
//! this repo's kind-binding tables drifted before. Both lanes call
//! [`read_contract_int_literal`], and both surface [`IntLiteralRefusal`]'s
//! `reason`/`fix` pair rather than inventing their own wording.
//!
//! WHAT THIS FUNCTION MAY AND MAY NOT DO
//! -------------------------------------
//! It changes a SPELLING and never a VALUE. Every accepted form denotes exactly
//! one integer and that integer is what comes back, so a caller that re-emits
//! `value.to_string()` has re-spelled the author's constant and nothing else.
//!
//! Two refusals are load-bearing rather than cosmetic, because dropping them
//! would manufacture a proof about a bound nobody wrote:
//!
//!  * A suffix is RANGE-CHECKED before it is dropped. `300u8` is rejected by
//!    rustc in a body, but a native contract clause is a parser island that is
//!    not type-checked as Rust, so `ensures result <= 300u8` would otherwise
//!    become the vacuous bound `result <= 300` over a `u8` result.
//!  * A value above `i128::MAX` is refused. The formula language carries an
//!    integer literal as `i128` ([`crate::spec_parse`]'s `Token::Int`), so a
//!    larger constant has no representation there; silently wrapping or
//!    saturating it would change which programs satisfy the clause.

/// Why an integer literal in a contract predicate cannot be read, with the
/// repair to offer its author.
///
/// The `fix` field exists because of standing ruling v7/D3: a refusal must
/// carry the fix, with options. "Unsupported" with no next step is a defect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntLiteralRefusal {
    /// The literal exactly as it was written.
    pub literal: String,
    /// Why it cannot be read, phrased to complete "`<literal>`: {reason}".
    pub reason: String,
    /// The repair, with options.
    pub fix: String,
}

/// The Rust integer type suffixes, with the bit width each names and whether it
/// is signed.
///
/// `usize`/`isize` are recorded at 64 bits: that is the pointer width of every
/// target this toolchain builds (`aarch64-apple-darwin`, `x86_64-apple-darwin`).
/// The width is used ONLY to refuse an out-of-range literal, so a width that is
/// too generous costs a refusal that would have been correct, never an accepted
/// value that is wrong.
const INT_SUFFIXES: &[(&str, u32, bool)] = &[
    ("u8", 8, false),
    ("u16", 16, false),
    ("u32", 32, false),
    ("u64", 64, false),
    ("u128", 128, false),
    ("usize", 64, false),
    ("i8", 8, true),
    ("i16", 16, true),
    ("i32", 32, true),
    ("i64", 64, true),
    ("i128", 128, true),
    ("isize", 64, true),
];

/// Every suffix, as one comma-separated list for a diagnostic.
const SUFFIX_MENU: &str =
    "`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`, `isize`";

/// The character run that a digit-led literal token occupies at the start of
/// `rest`, in bytes.
///
/// This is Rust's integer-literal token SHAPE — a digit followed by
/// alphanumerics and `_` — which is what makes `999_999_999`, `0xFF` and
/// `1000u32` one token instead of a number followed by a stray identifier. It
/// deliberately stops before `.`: a lone `.` is the projection separator
/// (`s.0`), `..` is the range token, and neither lane wants a digit run to
/// swallow either.
///
/// Returns 0 when `rest` does not start with an ASCII digit.
pub fn int_literal_run_len(rest: &str) -> usize {
    let bytes = rest.as_bytes();
    match bytes.first() {
        Some(byte) if byte.is_ascii_digit() => {}
        _ => return 0,
    }
    1 + int_literal_tail_len(&rest[1..])
}

/// How many more bytes of `rest` belong to a literal token that has ALREADY
/// started with a digit.
///
/// This is the same run as [`int_literal_run_len`] minus its leading digit, and
/// it exists because [`crate::spec_parse`] decides between a float and an
/// integer on the decimal-digit prefix alone: it has already consumed that
/// prefix by the time it knows the token is an integer, and needs to extend the
/// run rather than re-scan it.
pub fn int_literal_tail_len(rest: &str) -> usize {
    let bytes = rest.as_bytes();
    let mut index = 0;
    while index < bytes.len() && (bytes[index].is_ascii_alphanumeric() || bytes[index] == b'_') {
        index += 1;
    }
    index
}

/// Read one Rust integer literal written in a contract predicate.
///
/// Accepts exactly what Rust's own integer-literal grammar accepts — decimal,
/// `0x`/`0b`/`0o` prefixes, `_` separators anywhere after the first digit, and
/// the twelve integer type suffixes — and returns the single integer it
/// denotes. It never accepts a float; the caller decides whether a float is
/// meaningful in its lane.
pub fn read_contract_int_literal(spelling: &str) -> Result<u128, IntLiteralRefusal> {
    let refuse = |reason: String, fix: String| IntLiteralRefusal {
        literal: spelling.to_string(),
        reason,
        fix,
    };

    // Rust's radix prefixes are lower-case only: `0X1` is not Rust, and is
    // refused below as the unknown suffix `X1` rather than read as hex.
    let (radix, radix_name, prefix, body) = if let Some(rest) = spelling.strip_prefix("0x") {
        (16u32, "hexadecimal", "0x", rest)
    } else if let Some(rest) = spelling.strip_prefix("0b") {
        (2u32, "binary", "0b", rest)
    } else if let Some(rest) = spelling.strip_prefix("0o") {
        (8u32, "octal", "0o", rest)
    } else {
        (10u32, "decimal", "", spelling)
    };

    let digits_end = body.find(|ch: char| !ch.is_digit(radix) && ch != '_').unwrap_or(body.len());
    let (digits, suffix) = body.split_at(digits_end);
    let mut has_digit = false;
    let mut overflow = false;
    let mut value = 0u128;
    for ch in digits.chars() {
        if ch == '_' {
            continue;
        }
        has_digit = true;
        if !overflow {
            if let Some(digit) = ch.to_digit(radix)
                && let Some(next) = value
                    .checked_mul(u128::from(radix))
                    .and_then(|v| v.checked_add(u128::from(digit)))
            {
                value = next;
            } else {
                overflow = true;
            }
        }
    }

    if !has_digit {
        // `0x`, `0b_`, and — the case worth naming — `0b2`, whose `2` is not a
        // binary digit and is therefore read as the start of a suffix.
        return Err(refuse(
            format!("it has no {radix_name} digits"),
            if prefix.is_empty() {
                "write the constant in decimal digits".to_string()
            } else {
                format!(
                    "write at least one {radix_name} digit after `{prefix}`, or drop the \
                     prefix and write the constant in decimal"
                )
            },
        ));
    }

    if overflow {
        // Every character is a valid digit for the radix, so the only way this
        // parses badly is overflow.
        return Err(refuse(
            "it does not fit in 128 bits".to_string(),
            "write a bound at or below 170141183460469231731687303715884105727, which is \
             the largest integer a contract formula can carry"
                .to_string(),
        ));
    }

    if !suffix.is_empty() {
        let Some(&(_, width, signed)) = INT_SUFFIXES.iter().find(|(name, _, _)| *name == suffix)
        else {
            let cleaned: String = digits.chars().filter(|ch| *ch != '_').collect();
            return Err(refuse(
                format!("`{suffix}` is not a Rust integer type suffix"),
                format!("drop the suffix and write `{cleaned}`, or use one of {SUFFIX_MENU}"),
            ));
        };
        // A signed suffix admits the magnitude of its own MINIMUM, because
        // `-128i8` is legal Rust and reaches this reader as the unary negation
        // of the literal `128i8`.
        let limit = match (signed, width) {
            (false, 128) => u128::MAX,
            (false, _) => (1u128 << width) - 1,
            (true, _) => 1u128 << (width - 1),
        };
        if value > limit {
            let cleaned: String = digits.chars().filter(|ch| *ch != '_').collect();
            return Err(refuse(
                format!("{cleaned} does not fit in `{suffix}`"),
                format!(
                    "the largest `{suffix}` literal is {limit}; widen the suffix, drop it so \
                     the bound is read at the clause's own type, or lower the constant"
                ),
            ));
        }
    }

    // The formula language carries an integer literal as `i128`. Refusing here
    // is what keeps the refusal ATTRIBUTED to the literal: read further on and
    // the whole clause fails with a parse error that names nothing.
    if value > i128::MAX as u128 {
        return Err(refuse(
            "it is larger than the biggest integer a contract formula can carry".to_string(),
            "write a bound at or below 170141183460469231731687303715884105727, or state the \
             bound over a narrower type"
                .to_string(),
        ));
    }

    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(spelling: &str) -> u128 {
        read_contract_int_literal(spelling).expect(spelling)
    }

    fn err(spelling: &str) -> IntLiteralRefusal {
        read_contract_int_literal(spelling).expect_err(spelling)
    }

    #[test]
    fn every_spelling_measured_in_section_13_1_now_reads_the_same_value() {
        // The four spellings the strict-fragment file measured as two silent
        // UNKNOWN rows each, plus the one that already worked. All five denote
        // the same integer, which is the whole point: the defect was spelling,
        // never magnitude.
        assert_eq!(ok("999999999"), 999_999_999);
        assert_eq!(ok("999_999_999"), 999_999_999);
        assert_eq!(ok("0x3B9AC9FF"), 999_999_999);
        assert_eq!(ok("999999999u32"), 999_999_999);
        assert_eq!(ok("1_0"), 10);
        assert_eq!(ok("0b111"), 7);
    }

    #[test]
    fn radix_prefixes_and_separators_compose() {
        assert_eq!(ok("0xFF"), 255);
        assert_eq!(ok("0xff"), 255);
        assert_eq!(ok("0x_F_F"), 255);
        assert_eq!(ok("0b1010"), 10);
        assert_eq!(ok("0o777"), 511);
        assert_eq!(ok("0o7_7_7u16"), 511);
        assert_eq!(ok("0"), 0);
        assert_eq!(ok("0_"), 0);
        assert_eq!(ok("08"), 8);
    }

    #[test]
    fn every_integer_suffix_is_accepted_and_dropped() {
        for (name, _, _) in INT_SUFFIXES {
            assert_eq!(ok(&format!("5{name}")), 5, "{name}");
        }
    }

    #[test]
    fn a_suffix_is_range_checked_before_it_is_dropped() {
        // THE control that keeps this from manufacturing a vacuous bound:
        // `ensures result <= 300u8` over a `u8` result must not quietly become
        // `result <= 300`, which every `u8` satisfies.
        let refusal = err("300u8");
        assert_eq!(refusal.literal, "300u8");
        assert!(refusal.reason.contains("does not fit in `u8`"), "{}", refusal.reason);
        assert!(refusal.fix.contains("255"), "{}", refusal.fix);

        assert_eq!(ok("255u8"), 255);
        assert_eq!(ok("127i8"), 127);
        // `-128i8` is legal Rust and arrives here as the magnitude alone.
        assert_eq!(ok("128i8"), 128);
        assert!(read_contract_int_literal("129i8").is_err());
        assert_eq!(ok("18446744073709551615u64"), u64::MAX as u128);
        assert!(read_contract_int_literal("18446744073709551616u64").is_err());
    }

    #[test]
    fn a_malformed_literal_is_refused_with_a_named_fix() {
        let refusal = err("123abc");
        assert!(refusal.reason.contains("`abc` is not a Rust integer type suffix"));
        assert!(refusal.fix.contains("`u32`"), "{}", refusal.fix);
        assert!(refusal.fix.contains("write `123`"), "{}", refusal.fix);

        let refusal = err("0x");
        assert!(refusal.reason.contains("no hexadecimal digits"), "{}", refusal.reason);
        assert!(refusal.fix.contains("`0x`"), "{}", refusal.fix);

        // `0b2` is not "binary two"; `2` is not a binary digit, so it is read
        // as a suffix and the literal has no digits at all.
        assert!(read_contract_int_literal("0b2").is_err());
        // Rust's radix prefixes are lower-case only.
        assert!(read_contract_int_literal("0X1").is_err());
    }

    #[test]
    fn the_formula_carrier_ceiling_is_refused_rather_than_wrapped() {
        assert_eq!(ok("170141183460469231731687303715884105727"), i128::MAX as u128);
        let refusal = err("170141183460469231731687303715884105728");
        assert!(refusal.reason.contains("larger than"), "{}", refusal.reason);
        // Above 128 bits entirely.
        assert!(read_contract_int_literal("999999999999999999999999999999999999999999").is_err());
    }

    #[test]
    fn the_token_run_stops_before_a_projection_dot_and_a_range() {
        assert_eq!(int_literal_run_len("0.0"), 1);
        assert_eq!(int_literal_run_len("0..10"), 1);
        assert_eq!(int_literal_run_len("999_999_999 <= x"), 11);
        assert_eq!(int_literal_run_len("1000u32)"), 7);
        assert_eq!(int_literal_run_len("x"), 0);
        // The tail form is the run minus its leading digit, which is what a
        // caller that has already consumed the decimal prefix needs.
        assert_eq!(int_literal_tail_len("_999_999 <= x"), 8);
        assert_eq!(int_literal_tail_len("x3B9AC9FF)"), 9);
        assert_eq!(int_literal_tail_len(".0"), 0);
        assert_eq!(int_literal_tail_len("..10"), 0);
    }
}
