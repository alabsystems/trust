//! Unicode primitives: code-point reading over UTF-16 code units,
//! Canonicalize (ES2025 22.2.2.9.1) in both modes, and table lookups.
//!
//! Author: Andrew Yates
//! Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::generated::case_tables::{CANON_NONU, CANON_NONU_SOURCES, SCF, SCF_SOURCES};

/// Fold mode compiled into each consuming instruction (resolved from the
/// effective flags at that point in the pattern, so `(?i:…)` is static).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Fold {
    /// Not ignoreCase: identity.
    None,
    /// ignoreCase without u/v: Canonicalize via Default Case Conversion
    /// uppercasing (single-code-unit results only) + the ASCII asymmetry
    /// rule; operates on code units.
    NonU,
    /// ignoreCase with u or v: simple case folding; operates on code points.
    Scf,
}

fn seg_lookup(table: &[(u32, u32, i32, u8)], cp: u32) -> u32 {
    let idx = table.partition_point(|&(s, _, _, _)| s <= cp);
    if idx == 0 {
        return cp;
    }
    let (s, e, delta, stride) = table[idx - 1];
    if cp <= e && (cp - s) % stride as u32 == 0 {
        (cp as i64 + delta as i64) as u32
    } else {
        cp
    }
}

/// Simple case folding (scf). Identity for unmapped code points.
pub fn scf(cp: u32) -> u32 {
    seg_lookup(SCF, cp)
}

/// Non-Unicode-mode Canonicalize (ES2025 22.2.2.9.1 steps 2-3): uppercase
/// per Unicode Default Case Conversion; multi-code-unit results are
/// rejected; a non-ASCII code unit never canonicalizes to an ASCII one.
pub fn canon_nonu(unit: u32) -> u32 {
    debug_assert!(unit <= 0xFFFF);
    let up = seg_lookup(CANON_NONU, unit);
    if unit >= 128 && up < 128 {
        unit
    } else {
        up
    }
}

/// Canonicalize under a fold mode.
pub fn canonicalize(ch: u32, fold: Fold) -> u32 {
    match fold {
        Fold::None => ch,
        Fold::NonU => canon_nonu(ch),
        Fold::Scf => scf(ch),
    }
}

/// Ranges (sorted, merged) of code points that a fold mode maps to a
/// different value — the only points whose image differs from themselves.
pub fn fold_sources(fold: Fold) -> &'static [(u32, u32)] {
    match fold {
        Fold::None => &[],
        Fold::NonU => CANON_NONU_SOURCES,
        Fold::Scf => SCF_SOURCES,
    }
}

pub fn in_ranges(ranges: &[(u32, u32)], cp: u32) -> bool {
    let idx = ranges.partition_point(|&(s, _)| s <= cp);
    idx > 0 && cp <= ranges[idx - 1].1
}

pub fn is_lead(u: u16) -> bool {
    (0xD800..=0xDBFF).contains(&u)
}

pub fn is_trail(u: u16) -> bool {
    (0xDC00..=0xDFFF).contains(&u)
}

pub fn combine(lead: u16, trail: u16) -> u32 {
    0x10000 + (((lead as u32) - 0xD800) << 10) + ((trail as u32) - 0xDC00)
}

/// Read the character starting at `pos` (forward). In unicode mode a valid
/// surrogate pair reads as one code point (width 2); anything else is one
/// code unit. Returns (char, width). `pos` must be < len.
pub fn read_forward(input: &[u16], pos: usize, unicode: bool) -> (u32, usize) {
    let u = input[pos];
    if unicode && is_lead(u) && pos + 1 < input.len() && is_trail(input[pos + 1]) {
        (combine(u, input[pos + 1]), 2)
    } else {
        (u as u32, 1)
    }
}

/// Read the character ending at `pos` (backward). `pos` must be > 0.
pub fn read_backward(input: &[u16], pos: usize, unicode: bool) -> (u32, usize) {
    let u = input[pos - 1];
    if unicode && is_trail(u) && pos >= 2 && is_lead(input[pos - 2]) {
        (combine(input[pos - 2], u), 2)
    } else {
        (u as u32, 1)
    }
}

/// AdvanceStringIndex: width of the advance from `pos` (1, or 2 over a
/// surrogate pair in unicode mode). `pos` must be < len.
pub fn advance_width(input: &[u16], pos: usize, unicode: bool) -> usize {
    read_forward(input, pos, unicode).1
}

/// The `\s` set: WhiteSpace ∪ LineTerminator (ES2025 22.2.2.9 + 12.2/12.3).
pub static WHITESPACE_RANGES: &[(u32, u32)] = &[
    (0x09, 0x0D),     // TAB LF VT FF CR
    (0x20, 0x20),
    (0xA0, 0xA0),
    (0x1680, 0x1680),
    (0x2000, 0x200A),
    (0x2028, 0x2029), // LS PS
    (0x202F, 0x202F),
    (0x205F, 0x205F),
    (0x3000, 0x3000),
    (0xFEFF, 0xFEFF),
];

/// LineTerminator (for `.`, multiline `^`/`$`).
pub static LINE_TERMINATORS: &[(u32, u32)] =
    &[(0x0A, 0x0A), (0x0D, 0x0D), (0x2028, 0x2029)];

pub fn is_line_terminator(cp: u32) -> bool {
    in_ranges(LINE_TERMINATORS, cp)
}

/// Basic word characters (`\w` without the ui extension).
pub static WORD_BASIC: &[(u32, u32)] =
    &[(0x30, 0x39), (0x41, 0x5A), (0x5F, 0x5F), (0x61, 0x7A)];

/// WordCharacters(rer): basic, plus — iff ignoreCase AND either unicode
/// flag — every char whose Canonicalize (scf) lands in the basic set.
/// Computed from the scf table so a Unicode data refresh cannot silently
/// desynchronize it (U+017F LATIN SMALL LETTER LONG S, U+212A KELVIN SIGN
/// in Unicode 16.0).
pub fn word_char_extras() -> Vec<u32> {
    let mut extras = Vec::new();
    for &(a, b) in SCF_SOURCES {
        for cp in a..=b {
            if !in_ranges(WORD_BASIC, cp) && in_ranges(WORD_BASIC, scf(cp)) {
                extras.push(cp);
            }
        }
    }
    extras
}

pub fn is_word_char(cp: u32, extended: bool) -> bool {
    in_ranges(WORD_BASIC, cp) || (extended && (cp == 0x017F || cp == 0x212A))
}

/// The `\d` set.
pub static DIGIT_RANGES: &[(u32, u32)] = &[(0x30, 0x39)];

#[cfg(test)]
mod tests {
    use super::*;

    /// `is_word_char`'s hardcoded ui-extension must equal the set derived
    /// from the generated scf table (guards Unicode data refreshes).
    #[test]
    fn word_char_extras_match_tables() {
        assert_eq!(word_char_extras(), vec![0x017F, 0x212A]);
    }

    /// Non-unicode Canonicalize spot checks from the spec's rules.
    #[test]
    fn canon_nonu_rules() {
        assert_eq!(canon_nonu('a' as u32), 'A' as u32);
        assert_eq!(canon_nonu(0x00DF), 0x00DF); // ß: multi-unit uppercase rejected
        assert_eq!(canon_nonu(0x017F), 0x017F); // ſ: ASCII asymmetry rule
        assert_eq!(canon_nonu(0x212A), 0x212A); // K is already uppercase
        assert_eq!(canon_nonu(0x03C2), 0x03A3); // ς -> Σ
        assert_eq!(canon_nonu(0x03C3), 0x03A3); // σ -> Σ
        assert_eq!(canon_nonu(0x1F80), 0x1F80); // ᾀ: multi-char full uppercase
    }

    /// Simple case folding spot checks.
    #[test]
    fn scf_rules() {
        assert_eq!(scf('A' as u32), 'a' as u32);
        assert_eq!(scf(0x212A), 'k' as u32); // Kelvin
        assert_eq!(scf(0x017F), 's' as u32); // long s
        assert_eq!(scf(0x00DF), 0x00DF); // ß has no SIMPLE fold to ss
        assert_eq!(scf(0x10400), 0x10428); // Deseret
        assert_eq!(scf(0x0130), 0x0130); // İ: full folding only
    }
}
