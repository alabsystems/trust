// encodeURI / encodeURIComponent / decodeURI / decodeURIComponent (19.2.6):
// fully specified — Encode/Decode over UTF-16 code units with strict UTF-8
// validation, URIError on unpaired surrogates and malformed escape
// sequences, uppercase hex output, and decodeURI's preserved reserved set.
// Adversarially verified against both engines (9-vector URIError battery).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use crate::interp::{Abrupt, ERes, Interp};
use std::rc::Rc;
use trust_js_value::{ErrKind, JsValue, Units};

/// uriUnescaped: ASCII alphanumeric + - _ . ! ~ * ' ( )
fn is_unescaped(c: u16) -> bool {
    matches!(c,
        0x41..=0x5a | 0x61..=0x7a | 0x30..=0x39
        | 0x2d | 0x5f | 0x2e | 0x21 | 0x7e | 0x2a | 0x27 | 0x28 | 0x29)
}

/// uriReserved + '#': ; / ? : @ & = + $ , #
fn is_reserved_or_hash(c: u16) -> bool {
    matches!(c, 0x3b | 0x2f | 0x3f | 0x3a | 0x40 | 0x26 | 0x3d | 0x2b | 0x24 | 0x2c | 0x23)
}

fn hex_val(c: u16) -> Option<u8> {
    match c {
        0x30..=0x39 => Some(u8::try_from(c - 0x30).expect("digit")),
        0x41..=0x46 => Some(u8::try_from(c - 0x41 + 10).expect("digit")),
        0x61..=0x66 => Some(u8::try_from(c - 0x61 + 10).expect("digit")),
        _ => None,
    }
}

fn push_percent(out: &mut Units, byte: u8) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    out.push(0x25);
    out.push(u16::from(HEX[usize::from(byte >> 4)]));
    out.push(u16::from(HEX[usize::from(byte & 0xf)]));
}

/// Encode (19.2.6.5). `extra_unescaped` = keep reserved+# literal
/// (encodeURI).
fn encode(s: &Units, keep_reserved: bool) -> Result<Units, ()> {
    let mut out: Units = Vec::new();
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if is_unescaped(c) || (keep_reserved && is_reserved_or_hash(c)) {
            out.push(c);
            i += 1;
            continue;
        }
        // Code point (strict surrogate pairing).
        let cp: u32 = if (0xd800..=0xdbff).contains(&c) {
            let Some(&c2) = s.get(i + 1) else { return Err(()) };
            if !(0xdc00..=0xdfff).contains(&c2) {
                return Err(());
            }
            i += 2;
            0x10000 + ((u32::from(c) - 0xd800) << 10) + (u32::from(c2) - 0xdc00)
        } else if (0xdc00..=0xdfff).contains(&c) {
            return Err(());
        } else {
            i += 1;
            u32::from(c)
        };
        // UTF-8 encode.
        let ch = char::from_u32(cp).ok_or(())?;
        let mut buf = [0u8; 4];
        for b in ch.encode_utf8(&mut buf).as_bytes() {
            push_percent(&mut out, *b);
        }
    }
    Ok(out)
}

/// Decode (19.2.6.4). `preserve_reserved` = decodeURI (reserved escapes stay
/// escaped, in their ORIGINAL hex spelling).
fn decode(s: &Units, preserve_reserved: bool) -> Result<Units, ()> {
    let mut out: Units = Vec::new();
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        if c != 0x25 {
            out.push(c);
            i += 1;
            continue;
        }
        let start = i;
        let b0 = read_byte(s, &mut i)?;
        if b0 & 0x80 == 0 {
            // Single-byte: reserved set may be preserved verbatim.
            let unit = u16::from(b0);
            if preserve_reserved && is_reserved_or_hash(unit) {
                out.extend_from_slice(&s[start..i]);
            } else {
                out.push(unit);
            }
            continue;
        }
        // Multi-byte UTF-8: strict validation per spec (shortest form,
        // valid ranges, no surrogates).
        let n = match b0 {
            0xc2..=0xdf => 1,
            0xe0..=0xef => 2,
            0xf0..=0xf4 => 3,
            _ => return Err(()),
        };
        let mut cp: u32 = match n {
            1 => u32::from(b0 & 0x1f),
            2 => u32::from(b0 & 0x0f),
            _ => u32::from(b0 & 0x07),
        };
        let mut continuation = Vec::with_capacity(n);
        for _ in 0..n {
            let b = read_byte(s, &mut i)?;
            if b & 0xc0 != 0x80 {
                return Err(());
            }
            continuation.push(b);
            cp = (cp << 6) | u32::from(b & 0x3f);
        }
        // Range checks (shortest form + scalar values only).
        let ok = match n {
            1 => (0x80..=0x7ff).contains(&cp),
            2 => (0x800..=0xffff).contains(&cp) && !(0xd800..=0xdfff).contains(&cp),
            _ => (0x1_0000..=0x10_ffff).contains(&cp),
        };
        if !ok {
            return Err(());
        }
        if cp <= 0xffff {
            out.push(u16::try_from(cp).expect("checked"));
        } else {
            let v = cp - 0x10000;
            out.push(u16::try_from(0xd800 + (v >> 10)).expect("high"));
            out.push(u16::try_from(0xdc00 + (v & 0x3ff)).expect("low"));
        }
    }
    Ok(out)
}

fn read_byte(s: &Units, i: &mut usize) -> Result<u8, ()> {
    if s.get(*i) != Some(&0x25) {
        return Err(());
    }
    let h1 = s.get(*i + 1).copied().and_then(hex_val).ok_or(())?;
    let h2 = s.get(*i + 2).copied().and_then(hex_val).ok_or(())?;
    *i += 3;
    Ok((h1 << 4) | h2)
}

impl Interp {
    pub(crate) fn dispatch_uri(&mut self, encode_op: bool, component: bool, arg0: &JsValue) -> ERes {
        let s = self.to_string_units(arg0)?;
        if s.len() > crate::interp::MAX_STRING_UNITS / 4 {
            return Err(Abrupt::Fatal("URI input cap exceeded".to_string()));
        }
        let r = if encode_op {
            encode(&s, !component)
        } else {
            decode(&s, !component)
        };
        match r {
            Ok(u) => Ok(JsValue::Str(Rc::new(u))),
            Err(()) => Err(self.throw_native(ErrKind::Uri)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_value::{units_from_str as u, units_to_lossy};

    #[test]
    fn encode_vectors() {
        let ec = |s: &str| units_to_lossy(&encode(&u(s), false).unwrap());
        let e = |s: &str| units_to_lossy(&encode(&u(s), true).unwrap());
        assert_eq!(ec("Aa0-_.!~*'()"), "Aa0-_.!~*'()");
        assert_eq!(ec("#;/?:@&=+$,"), "%23%3B%2F%3F%3A%40%26%3D%2B%24%2C");
        assert_eq!(e("#;/?:@&=+$,"), "#;/?:@&=+$,");
        assert_eq!(e("a b"), "a%20b");
        assert_eq!(ec("é"), "%C3%A9");
        assert_eq!(ec("中"), "%E4%B8%AD");
        assert_eq!(ec("😀"), "%F0%9F%98%80");
        assert_eq!(ec(""), "");
        assert!(encode(&vec![0xd800], false).is_err());
        assert!(encode(&vec![0xdfff, 0x20], false).is_err());
    }

    #[test]
    fn decode_vectors() {
        let dc = |s: &str| units_to_lossy(&decode(&u(s), false).unwrap());
        let d = |s: &str| units_to_lossy(&decode(&u(s), true).unwrap());
        assert_eq!(dc("%41%42"), "AB");
        assert_eq!(dc("%E4%B8%AD"), "中");
        assert_eq!(dc("%F0%9F%98%80"), "😀");
        assert_eq!(d("a%20b%2Fc"), "a b%2Fc");
        assert_eq!(dc("a%20b%2Fc"), "a b/c");
        assert_eq!(d("%23%3B%2F%3F%3A%40%26%3D%2B%24%2C"), "%23%3B%2F%3F%3A%40%26%3D%2B%24%2C");
        assert_eq!(dc("%c3%a9"), "é"); // lowercase hex accepted
        for bad in ["%", "%GG", "%C0%80", "%E4%B8", "%80", "%F5%80%80%80", "%ED%A0%80"] {
            assert!(decode(&u(bad), false).is_err(), "should URIError: {bad}");
        }
    }
}
