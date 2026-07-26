// Literal decoding at the code-unit level: string-literal escape sequences
// (the parser hands us the raw source between the quotes) and template cooked
// values. Decoding is WTF-16-exact — `\uD800` produces a lone surrogate code
// unit, which Rust `String` cannot carry, so the decoder emits `Units`
// directly. Legacy octal / \8 \9 escapes are out of slice (the caller checks
// the parser's flag and refuses).
//
// Author: Andrew Yates
// Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0

use trust_js_value::Units;

/// Decode a string-literal body (source text between the quotes, escapes
/// intact). `Err` = out-of-slice escape shape.
pub fn decode_string_literal(raw: &str) -> Result<Units, String> {
    decode(raw)
}

/// Cooked value of one template piece (raw source between the delimiters).
/// <CR><LF> and <CR> normalize to <LF> first (spec 12.9.6 TV/TRV).
pub fn cook_template_piece(raw: &str) -> Result<Units, String> {
    let normalized = raw.replace("\r\n", "\n").replace('\r', "\n");
    decode(&normalized)
}

#[allow(clippy::too_many_lines)]
fn decode(raw: &str) -> Result<Units, String> {
    let chars: Vec<char> = raw.chars().collect();
    let mut out: Units = Vec::with_capacity(chars.len());
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c != '\\' {
            push_char(&mut out, c);
            i += 1;
            continue;
        }
        i += 1;
        let Some(&e) = chars.get(i) else {
            return Err("dangling backslash in literal (lexer bug?)".to_string());
        };
        match e {
            'n' => {
                out.push(0x0a);
                i += 1;
            }
            't' => {
                out.push(0x09);
                i += 1;
            }
            'r' => {
                out.push(0x0d);
                i += 1;
            }
            'b' => {
                out.push(0x08);
                i += 1;
            }
            'f' => {
                out.push(0x0c);
                i += 1;
            }
            'v' => {
                out.push(0x0b);
                i += 1;
            }
            '0' => {
                if chars.get(i + 1).is_some_and(char::is_ascii_digit) {
                    return Err("octal-adjacent escape (out of slice)".to_string());
                }
                out.push(0x00);
                i += 1;
            }
            '1'..='9' => {
                return Err("legacy octal / \\8 \\9 escape (out of slice)".to_string());
            }
            'x' => {
                let h: String = chars
                    .get(i + 1..i + 3)
                    .ok_or("truncated \\x escape")?
                    .iter()
                    .collect();
                let v = u16::from_str_radix(&h, 16).map_err(|_| "bad \\x escape".to_string())?;
                out.push(v);
                i += 3;
            }
            'u' => {
                if chars.get(i + 1) == Some(&'{') {
                    let mut j = i + 2;
                    let mut v: u32 = 0;
                    while j < chars.len() && chars[j] != '}' {
                        let d = chars[j]
                            .to_digit(16)
                            .ok_or("bad \\u{...} escape".to_string())?;
                        v = v * 16 + d;
                        if v > 0x10_ffff {
                            return Err("\\u{...} beyond U+10FFFF (lexer bug?)".to_string());
                        }
                        j += 1;
                    }
                    if j >= chars.len() {
                        return Err("unterminated \\u{...} escape".to_string());
                    }
                    push_code_point(&mut out, v);
                    i = j + 1;
                } else {
                    let h: String = chars
                        .get(i + 1..i + 5)
                        .ok_or("truncated \\u escape")?
                        .iter()
                        .collect();
                    let v =
                        u16::from_str_radix(&h, 16).map_err(|_| "bad \\u escape".to_string())?;
                    out.push(v); // lone surrogates land as-is (WTF-16)
                    i += 5;
                }
            }
            '\n' | '\u{2028}' | '\u{2029}' => {
                i += 1; // line continuation
            }
            '\r' => {
                i += 1;
                if chars.get(i) == Some(&'\n') {
                    i += 1;
                }
            }
            other => {
                push_char(&mut out, other);
                i += 1;
            }
        }
    }
    Ok(out)
}

fn push_char(out: &mut Units, c: char) {
    let mut buf = [0u16; 2];
    out.extend_from_slice(c.encode_utf16(&mut buf));
}

fn push_code_point(out: &mut Units, cp: u32) {
    if let Some(c) = char::from_u32(cp) {
        push_char(out, c);
    } else {
        // Surrogate code point via \u{D800}-style escape: single unit.
        out.push(u16::try_from(cp & 0xffff).expect("surrogate range"));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_js_value::units_from_str;

    #[test]
    fn escape_decoding() {
        assert_eq!(decode_string_literal("ab").unwrap(), units_from_str("ab"));
        assert_eq!(
            decode_string_literal("a\\nb\\t").unwrap(),
            units_from_str("a\nb\t")
        );
        assert_eq!(decode_string_literal("\\x41").unwrap(), units_from_str("A"));
        assert_eq!(
            decode_string_literal("\\u00e9").unwrap(),
            units_from_str("é")
        );
        assert_eq!(
            decode_string_literal("\\u{1F600}").unwrap(),
            units_from_str("😀")
        );
        // Lone surrogate survives.
        assert_eq!(decode_string_literal("\\uD800").unwrap(), vec![0xd800]);
        assert_eq!(decode_string_literal("\\u{D800}").unwrap(), vec![0xd800]);
        // Line continuation vanishes.
        assert_eq!(decode_string_literal("a\\\nb").unwrap(), units_from_str("ab"));
        // NUL escape; octal refuses.
        assert_eq!(decode_string_literal("\\0").unwrap(), vec![0]);
        assert!(decode_string_literal("\\07").is_err());
        assert!(decode_string_literal("\\1").is_err());
        // Identity escapes.
        assert_eq!(decode_string_literal("\\a\\'").unwrap(), units_from_str("a'"));
    }

    #[test]
    fn template_normalization() {
        assert_eq!(cook_template_piece("a\r\nb").unwrap(), units_from_str("a\nb"));
        assert_eq!(cook_template_piece("a\rb").unwrap(), units_from_str("a\nb"));
        assert_eq!(cook_template_piece("a\\\r\nb").unwrap(), units_from_str("ab"));
    }
}
