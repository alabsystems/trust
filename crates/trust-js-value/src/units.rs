// WTF-16 strings: JS string values are sequences of UTF-16 code units, and
// lone surrogates are first-class observables, so the value model stores
// `Vec<u16>` — never Rust `String`.
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

/// A JS string as UTF-16 code units.
pub type Units = Vec<u16>;

/// Encode a Rust string as code units.
#[must_use]
pub fn units_from_str(s: &str) -> Units {
    s.encode_utf16().collect()
}

/// Lossy decode for diagnostics only (never for observables).
#[must_use]
pub fn units_to_lossy(u: &[u16]) -> String {
    String::from_utf16_lossy(u)
}

/// True iff the units spell exactly the given ASCII string.
#[must_use]
pub fn units_eq_ascii(u: &[u16], s: &str) -> bool {
    u.len() == s.len() && u.iter().zip(s.bytes()).all(|(&a, b)| a == u16::from(b))
}

/// Canonical array index ("0" .. "4294967294"): decimal digits, no leading
/// zero except "0" itself, value below 2^32-1.
#[must_use]
pub fn array_index_of(u: &[u16]) -> Option<u32> {
    if u.is_empty() || u.len() > 10 {
        return None;
    }
    if u.len() > 1 && u[0] == u16::from(b'0') {
        return None;
    }
    let mut n: u64 = 0;
    for &c in u {
        if !(0x30..=0x39).contains(&c) {
            return None;
        }
        n = n * 10 + u64::from(c - 0x30);
    }
    if n < u64::from(u32::MAX) {
        Some(u32::try_from(n).expect("bounded above"))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_index_canonicality() {
        assert_eq!(array_index_of(&units_from_str("0")), Some(0));
        assert_eq!(array_index_of(&units_from_str("42")), Some(42));
        assert_eq!(array_index_of(&units_from_str("01")), None);
        assert_eq!(array_index_of(&units_from_str("-1")), None);
        assert_eq!(
            array_index_of(&units_from_str("4294967294")),
            Some(4_294_967_294)
        );
        assert_eq!(array_index_of(&units_from_str("4294967295")), None);
        assert_eq!(array_index_of(&units_from_str("length")), None);
        assert_eq!(array_index_of(&units_from_str("")), None);
        assert_eq!(array_index_of(&units_from_str("1.5")), None);
    }

    #[test]
    fn ascii_compare() {
        assert!(units_eq_ascii(&units_from_str("length"), "length"));
        assert!(!units_eq_ascii(&units_from_str("length "), "length"));
        assert!(!units_eq_ascii(&units_from_str("Léngth"), "Length"));
    }
}
