// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The acceptance gate for `trust-json`: a BYTE differential against the
//! incumbent `serde_json`, which is linked here and nowhere else.
//!
//! Everything compared below is compared as bytes or as an exact value, never
//! as "semantically the same JSON". The reason is in the crate header: this
//! tree hashes serialized JSON, so a differently-spelled but equally-valid
//! rendering is a silent digest change across every proof bundle.
//!
//! Deliberately NOT asserted: nothing. Every observable this crate produces on
//! the corpora below is asserted equal. Where the incumbent's behaviour is
//! surprising (`-0` parses to a float, `1e400` errors while `1e-400` does not,
//! DEL is not escaped, the `f32` and `f64` notation thresholds differ) there is
//! a named test, so a future edit that "fixes" one of them fails with the
//! reason on screen.
//!
//! # MUTATION LOG — what this file has been SEEN to catch
//!
//! Each defect below was applied to the crate, this binary was run, the listed
//! tests failed, and the defect was reverted and the suite re-run green. A test
//! never observed failing is not evidence, so this table is the claim.
//!
//! | # | defect injected | caught by |
//! |---|---|---|
//! | M1 | give `f32` the `f64` fixed/exponential threshold | `f32_bytes_match_over_random_bit_patterns` (51 413 / 996 166), `..._dense_exhaustive_stride` (227 282 / 4 378 905) |
//! | M2 | delete the round-half-to-even tie correction | `f64_bytes_match_over_random_bit_patterns` (**229** / 999 530), `f32_...` (2 031), `..._structured_values`, `compact_and_pretty_documents_are_byte_identical`, `parse_agrees_over_random_number_texts`, `..._round_tripped_random_documents` |
//! | M3 | drop the `+` on a positive exponent (the `ryu` spelling) | `exponent_is_signed_and_unpadded`, `subnormals_and_boundaries` |
//! | M4 | escape `/` as a JavaScript-safe writer would | `string_escaping_matches_for_every_bmp_scalar_value`, `..._over_random_mixed_strings`, `the_escape_policy_...`, `parse_agrees_over_random_byte_soup` |
//! | M5 | uppercase the `\u` hex digits | `string_escaping_matches_for_every_bmp_scalar_value`, `..._over_random_mixed_strings`, `the_escape_policy_...` |
//! | M6 | four-space pretty indent | `pretty_shape_is_exactly_the_incumbents`, `compact_and_pretty_documents_are_byte_identical` |
//! | M7 | drop the space in the pretty `": "` separator | `pretty_shape_is_exactly_the_incumbents`, `compact_and_pretty_documents_are_byte_identical` |
//! | M8 | emit object keys in reverse | `object_key_order_is_sorted_on_both_sides`, `compact_and_pretty_...`, `pretty_shape_...`, `parse_agrees_over_round_tripped_random_documents` |
//! | M9 | lose the minus sign on `i64::MIN` | `integer_bytes_match_at_the_boundaries_and_over_a_sweep` |
//! | M10 | parse `-0` as the integer 0 | `the_surprising_parse_behaviours_are_preserved`, `parse_agrees_on_an_enumerated_malformed_table`, `..._byte_soup` |
//! | M11 | compute `POW10` by repeated multiplication instead of literals | `parse_agrees_over_random_number_texts` + three other parse tests |
//! | M12 | validate the four `\u` hex digits before consuming them | `parse_agrees_on_an_enumerated_malformed_table`, `..._byte_soup` |
//! | M13 | check recursion depth after consuming the bracket | `recursion_limit_matches_the_incumbent` |
//! | M14 | accept a trailing comma in an array | `parse_agrees_on_an_enumerated_malformed_table` |
//! | M15 | drop the `.0` on integral floats (emit `1` for `1.0`) | nine tests, incl. 1 052 / 999 530 `f64` and 362 966 / 4 378 905 `f32` |
//!
//! M12 and M13 are not hypothetical: they are the two defects this file
//! actually found on its first run, before either was known to be wrong.
//!
//! # Where the rest of the gate is
//!
//! This binary is the GENERATED half: float bit patterns, Unicode sweeps,
//! random trees, random number texts, byte soup. The CHECKED-IN half — the
//! 2954-document corpus, the enumerated byte-exactness hazard table, empty
//! containers, deep nesting, and the typed-lens differential that drives one
//! `#[derive(Deserialize)]` from both trees — is `acceptance_gate.rs`, with its
//! own mutation log. Helpers both binaries need live in `common/mod.rs`.

use incumbent_serde_json as inc;
use trust_json as tj;
use trust_json::Formatter as _;

mod common;
use common::{Lcg, agree_on_parse as check_parse, to_inc};

// ---------------------------------------------------------------------------
// 0. Oracle identity. Prints what the incumbent actually does, so a backend
//    swap under us is visible in the test log instead of silent.
// ---------------------------------------------------------------------------

#[test]
fn oracle_identity() {
    let sentinels: [(&str, String); 6] = [
        ("1e30", inc::to_string(&1e30f64).unwrap()),
        ("1e-6", inc::to_string(&1e-6f64).unwrap()),
        ("1e-6f32", inc::to_string(&1e-6f32).unwrap()),
        ("1.0", inc::to_string(&1.0f64).unwrap()),
        (
            "tie 0x4307098d6fca6a8a",
            inc::to_string(&f64::from_bits(0x4307098d6fca6a8a)).unwrap(),
        ),
        ("DEL in a string", inc::to_string("\u{7f}").unwrap()),
    ];
    for (name, got) in &sentinels {
        println!("  oracle {name:<22} -> {got}");
    }
    // These four discriminate the float backend and the escape policy. If any
    // fires, the incumbent changed and every byte claim in this file is about
    // a different oracle -- STOP, do not "fix" trust-json to match.
    assert_eq!(sentinels[0].1, "1e+30", "float backend changed (ryu-style?)");
    assert_eq!(sentinels[1].1, "1e-6", "f64 fixed/exponential threshold moved");
    assert_eq!(
        sentinels[2].1, "0.000001",
        "f32 fixed/exponential threshold moved"
    );
    assert_eq!(sentinels[4].1, "810553441865041.2", "tie-break rule changed");
    assert_eq!(sentinels[5].1, "\"\u{7f}\"", "escape policy changed");
}

// ---------------------------------------------------------------------------
// 1. Floats.
// ---------------------------------------------------------------------------

fn tj_f64(v: f64) -> String {
    tj::to_string(&tj::Value::from(v)).unwrap()
}

fn tj_f32(v: f32) -> String {
    tj::ser::float::FloatBuffer::new()
        .format_finite_f32(v)
        .to_owned()
}

/// How many random bit patterns each float sweep draws. The `f64` tie
/// disagreement rate against a naive std-only implementation is 0.025%, so
/// 1_000_000 draws hit it ~250 times: the sweep is sized to make that failure
/// mode certain, not likely. `TRUST_JSON_DIFF_HEAVY=1` raises it 8x.
fn sweep_len() -> u64 {
    let heavy = std::env::var("TRUST_JSON_DIFF_HEAVY").is_ok();
    if heavy { 8_000_000 } else { 1_000_000 }
}

#[test]
fn f64_bytes_match_over_random_bit_patterns() {
    let n = sweep_len();
    let mut rng = Lcg::new(0x243F6A8885A308D3);
    let mut checked = 0u64;
    let mut first_bad: Option<(u64, String, String)> = None;
    let mut bad = 0u64;
    for _ in 0..n {
        let bits = rng.next_u64();
        let v = f64::from_bits(bits);
        if !v.is_finite() {
            continue;
        }
        checked += 1;
        let a = inc::to_string(&v).unwrap();
        let b = tj_f64(v);
        if a != b {
            bad += 1;
            if first_bad.is_none() {
                first_bad = Some((bits, a, b));
            }
        }
    }
    println!("  f64 random bit patterns: checked {checked}, disagreements {bad}");
    if let Some((bits, a, b)) = first_bad {
        panic!("f64 {bits:#018x}: incumbent {a}  trust-json {b}  ({bad} total)");
    }
}

#[test]
fn f32_bytes_match_over_random_bit_patterns() {
    let n = sweep_len();
    let mut rng = Lcg::new(0x13198A2E03707344);
    let mut checked = 0u64;
    let mut first_bad: Option<(u32, String, String)> = None;
    let mut bad = 0u64;
    for _ in 0..n {
        let bits = rng.next_u64() as u32;
        let v = f32::from_bits(bits);
        if !v.is_finite() {
            continue;
        }
        checked += 1;
        let a = inc::to_string(&v).unwrap();
        let b = tj_f32(v);
        if a != b {
            bad += 1;
            if first_bad.is_none() {
                first_bad = Some((bits, a, b));
            }
        }
    }
    println!("  f32 random bit patterns: checked {checked}, disagreements {bad}");
    if let Some((bits, a, b)) = first_bad {
        panic!("f32 {bits:#010x}: incumbent {a}  trust-json {b}  ({bad} total)");
    }
}

#[test]
fn f64_bytes_match_over_structured_values() {
    // Random bits almost never land on a "human" float, and human floats are
    // what this tree actually serializes: exponent boundaries, small decimals,
    // integral values, and the powers of ten that straddle the notation
    // threshold.
    let mut cases: Vec<f64> = vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        0.1,
        0.2,
        0.3,
        1.0 / 3.0,
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        f64::from_bits(2),
        f64::from_bits(0x000F_FFFF_FFFF_FFFF),
        9007199254740992.0,
        9007199254740993.0,
        123456789012345680000.0,
        0.1 + 0.2,
    ];
    for e in -330i32..=308 {
        cases.push(10f64.powi(e));
        cases.push(-(10f64.powi(e)));
        cases.push(1.5 * 10f64.powi(e));
        cases.push(9.999999999999999 * 10f64.powi(e));
    }
    let mut rng = Lcg::new(0xA4093822299F31D0);
    for _ in 0..200_000 {
        // A small integer scaled by a small power of ten: the shape that
        // dominates real documents.
        let m = rng.below(2_000_000) as f64 - 1_000_000.0;
        let e = rng.below(40) as i32 - 20;
        cases.push(m * 10f64.powi(e));
        cases.push(m / 10f64.powi(e));
    }
    let mut bad = 0;
    for v in &cases {
        if !v.is_finite() {
            continue;
        }
        let a = inc::to_string(v).unwrap();
        let b = tj_f64(*v);
        if a != b {
            bad += 1;
            if bad <= 5 {
                println!("  MISMATCH bits={:#018x} inc={a} tj={b}", v.to_bits());
            }
        }
    }
    println!("  f64 structured values: checked {}", cases.len());
    assert_eq!(bad, 0, "structured f64 disagreements");
}

#[test]
fn f32_bytes_match_over_a_dense_exhaustive_stride() {
    // A stride over the whole f32 space. 977 is prime, so the walk visits
    // every exponent and does not lock onto a mantissa pattern.
    let mut i: u32 = 0;
    let mut checked = 0u64;
    let mut bad = 0u64;
    let mut first: Option<(u32, String, String)> = None;
    loop {
        let v = f32::from_bits(i);
        if v.is_finite() {
            checked += 1;
            let a = inc::to_string(&v).unwrap();
            let b = tj_f32(v);
            if a != b {
                bad += 1;
                if first.is_none() {
                    first = Some((i, a, b));
                }
            }
        }
        if i > u32::MAX - 977 {
            break;
        }
        i += 977;
    }
    println!("  f32 stride-977 sweep: checked {checked}, disagreements {bad}");
    if let Some((bits, a, b)) = first {
        panic!("f32 {bits:#010x}: incumbent {a}  trust-json {b}  ({bad} total)");
    }
}

#[test]
fn non_finite_floats_render_as_null_on_both_sides() {
    for v in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert_eq!(inc::to_string(&v).unwrap(), "null");
        assert_eq!(tj_f64(v), "null");
    }
    assert!(inc::Number::from_f64(f64::NAN).is_none());
    assert!(tj::Number::from_f64(f64::NAN).is_none());
}

// ---------------------------------------------------------------------------
// 2. Integers.
// ---------------------------------------------------------------------------

#[test]
fn integer_bytes_match_at_the_boundaries_and_over_a_sweep() {
    macro_rules! chk_u {
        ($v:expr) => {{
            let v = $v;
            let a = inc::to_string(&v).unwrap();
            let b = tj::to_string(&tj::Value::from(v)).unwrap();
            assert_eq!(a, b, "u {v}");
        }};
    }
    macro_rules! chk_i {
        ($v:expr) => {{
            let v = $v;
            let a = inc::to_string(&v).unwrap();
            let b = tj::to_string(&tj::Value::from(v)).unwrap();
            assert_eq!(a, b, "i {v}");
        }};
    }
    chk_u!(0u64);
    chk_u!(1u64);
    chk_u!(u64::MAX);
    chk_u!(u64::MAX - 1);
    chk_i!(0i64);
    chk_i!(-1i64);
    chk_i!(i64::MIN);
    chk_i!(i64::MAX);
    chk_i!(i64::MIN + 1);

    // 128-bit goes through the Formatter directly; `Value` has no 128-bit
    // number, exactly as the incumbent's does not.
    let mut w = Vec::new();
    tj::CompactFormatter
        .write_i128(&mut w, i128::MIN)
        .unwrap();
    assert_eq!(
        String::from_utf8(w).unwrap(),
        inc::to_string(&i128::MIN).unwrap()
    );
    let mut w = Vec::new();
    tj::CompactFormatter
        .write_u128(&mut w, u128::MAX)
        .unwrap();
    assert_eq!(
        String::from_utf8(w).unwrap(),
        inc::to_string(&u128::MAX).unwrap()
    );

    let mut rng = Lcg::new(0x082EFA98EC4E6C89);
    for _ in 0..300_000 {
        let u = rng.next_u64();
        chk_u!(u);
        chk_i!(u as i64);
    }
}

// ---------------------------------------------------------------------------
// 3. Strings.
// ---------------------------------------------------------------------------

fn tj_str(s: &str) -> String {
    tj::to_string(&tj::Value::String(s.to_owned())).unwrap()
}

#[test]
fn string_escaping_matches_for_every_bmp_scalar_value() {
    let mut checked = 0u64;
    for cu in 0u32..=0xFFFF {
        let Some(c) = char::from_u32(cu) else {
            continue; // surrogates
        };
        let s: String = c.to_string();
        checked += 1;
        assert_eq!(inc::to_string(&s).unwrap(), tj_str(&s), "U+{cu:04X}");
    }
    println!("  BMP scalar values checked: {checked}");
    assert_eq!(checked, 0x1_0000 - 0x800, "surrogate accounting");
}

#[test]
fn string_escaping_matches_above_the_bmp() {
    let mut checked = 0u64;
    let mut cu = 0x1_0000u32;
    while cu <= 0x10_FFFF {
        let c = char::from_u32(cu).unwrap();
        let s = c.to_string();
        assert_eq!(inc::to_string(&s).unwrap(), tj_str(&s), "U+{cu:04X}");
        checked += 1;
        cu += 7;
    }
    println!("  astral scalar values checked (stride 7): {checked}");
}

#[test]
fn string_escaping_matches_over_random_mixed_strings() {
    let mut rng = Lcg::new(0x3F84D5B5B5470917);
    // Weighted so control characters, quotes and backslashes are COMMON --
    // a uniform draw over Unicode would almost never produce one.
    let interesting: Vec<char> = (0u32..0x20)
        .chain([0x22, 0x2F, 0x5C, 0x7E, 0x7F, 0x80, 0x85, 0xA0])
        .chain([0x2028, 0x2029, 0xFEFF, 0xFFFD])
        .filter_map(char::from_u32)
        .collect();
    for _ in 0..100_000 {
        let len = rng.below(24) as usize;
        let mut s = String::new();
        for _ in 0..len {
            if rng.below(3) == 0 {
                s.push(interesting[rng.below(interesting.len() as u64) as usize]);
            } else {
                loop {
                    let cu = rng.below(0x11_0000) as u32;
                    if let Some(c) = char::from_u32(cu) {
                        s.push(c);
                        break;
                    }
                }
            }
        }
        assert_eq!(inc::to_string(&s).unwrap(), tj_str(&s), "string {s:?}");
    }
}

#[test]
fn the_escape_policy_is_the_incumbents_and_not_a_safer_one() {
    // Named because each of these is a plausible "improvement" that would be a
    // byte regression.
    assert_eq!(tj_str("/"), "\"/\"", "solidus must NOT be escaped");
    assert_eq!(tj_str("\u{7f}"), "\"\u{7f}\"", "DEL must NOT be escaped");
    assert_eq!(
        tj_str("\u{2028}\u{2029}"),
        "\"\u{2028}\u{2029}\"",
        "line/paragraph separators must NOT be escaped"
    );
    assert_eq!(tj_str("é€𝄞"), "\"é€𝄞\"", "non-ASCII passes through");
    assert_eq!(
        tj_str("\u{0}\u{1}\u{b}\u{e}\u{1f}"),
        "\"\\u0000\\u0001\\u000b\\u000e\\u001f\"",
        "\\u escapes are LOWERCASE hex"
    );
    assert_eq!(
        tj_str("\u{8}\t\n\u{c}\r"),
        "\"\\b\\t\\n\\f\\r\"",
        "the five short escapes"
    );
    // ... and each of the above equals the incumbent.
    for s in [
        "/",
        "\u{7f}",
        "\u{2028}\u{2029}",
        "é€𝄞",
        "\u{0}\u{1}\u{b}\u{e}\u{1f}",
        "\u{8}\t\n\u{c}\r",
    ] {
        assert_eq!(inc::to_string(s).unwrap(), tj_str(s));
    }
}

// ---------------------------------------------------------------------------
// 4. Whole documents: compact and pretty.
// ---------------------------------------------------------------------------

fn random_value(rng: &mut Lcg, depth: u32) -> tj::Value {
    let pick = if depth >= 4 {
        rng.below(5)
    } else {
        rng.below(7)
    };
    match pick {
        0 => tj::Value::Null,
        1 => tj::Value::Bool(rng.below(2) == 0),
        2 => tj::Value::from(rng.next_u64()),
        3 => tj::Value::from(rng.next_u64() as i64),
        4 => {
            let bits = rng.next_u64();
            let f = f64::from_bits(bits);
            if f.is_finite() {
                tj::Value::from(f)
            } else {
                tj::Value::from(rng.below(1000) as f64 / 7.0)
            }
        }
        5 => {
            let n = rng.below(5) as usize;
            tj::Value::Array((0..n).map(|_| random_value(rng, depth + 1)).collect())
        }
        _ => {
            let n = rng.below(5) as usize;
            let mut m = tj::Map::new();
            for k in 0..n {
                let key = format!("k{}{}", rng.below(1000), "\u{7f}".repeat(k % 2));
                m.insert(key, random_value(rng, depth + 1));
            }
            tj::Value::Object(m)
        }
    }
}

#[test]
fn compact_and_pretty_documents_are_byte_identical() {
    let mut rng = Lcg::new(0xBE5466CF34E90C6C);
    for i in 0..20_000 {
        let v = random_value(&mut rng, 0);
        let iv = to_inc(&v);
        assert_eq!(
            inc::to_string(&iv).unwrap(),
            tj::to_string(&v).unwrap(),
            "compact case {i}"
        );
        assert_eq!(
            inc::to_string_pretty(&iv).unwrap(),
            tj::to_string_pretty(&v).unwrap(),
            "pretty case {i}"
        );
        assert_eq!(inc::to_vec(&iv).unwrap(), tj::to_vec(&v).unwrap());
        assert_eq!(
            inc::to_vec_pretty(&iv).unwrap(),
            tj::to_vec_pretty(&v).unwrap()
        );
    }
}

#[test]
fn pretty_shape_is_exactly_the_incumbents() {
    let src = r#"{"b":1,"a":[1,2,{"z":null}],"c":{},"d":[],"e":"x"}"#;
    let mine: tj::Value = tj::from_str(src).unwrap();
    let theirs: inc::Value = inc::from_str(src).unwrap();
    let p = tj::to_string_pretty(&mine).unwrap();
    assert_eq!(p, inc::to_string_pretty(&theirs).unwrap());
    // Spelled out, so a change to indent width or the `": "` separator is a
    // diff in this file and not only a diff in a hash.
    assert_eq!(
        p,
        "{\n  \"a\": [\n    1,\n    2,\n    {\n      \"z\": null\n    }\n  ],\n  \"b\": 1,\n  \"c\": {},\n  \"d\": [],\n  \"e\": \"x\"\n}"
    );
    // Top-level scalars get no decoration at all.
    for s in ["1", "null", "\"x\"", "[]", "{}"] {
        let m: tj::Value = tj::from_str(s).unwrap();
        let t: inc::Value = inc::from_str(s).unwrap();
        assert_eq!(
            tj::to_string_pretty(&m).unwrap(),
            inc::to_string_pretty(&t).unwrap(),
            "pretty {s}"
        );
    }
}

#[test]
fn object_key_order_is_sorted_on_both_sides() {
    let src = r#"{"z":1,"a":2,"m":3,"":4,"A":5,"\u00e9":6}"#;
    let mine: tj::Value = tj::from_str(src).unwrap();
    let theirs: inc::Value = inc::from_str(src).unwrap();
    assert_eq!(
        tj::to_string(&mine).unwrap(),
        inc::to_string(&theirs).unwrap()
    );
    assert_eq!(
        tj::to_string(&mine).unwrap(),
        r#"{"":4,"A":5,"a":2,"m":3,"z":1,"é":6}"#
    );
}

// ---------------------------------------------------------------------------
// 5. Parsing.
// ---------------------------------------------------------------------------


#[test]
fn parse_agrees_on_an_enumerated_malformed_table() {
    let cases = [
        // structure
        "",
        " ",
        "\t\n\r ",
        "[1,]",
        "{\"a\":1,}",
        "{'a':1}",
        "{\"a\" 1}",
        "{\"a\":}",
        "{\"a\"}",
        "[1 2]",
        "[1",
        "{",
        "{\"a\"",
        "{\"a\":1",
        "[",
        "]",
        "}",
        ",",
        ":",
        "[1]x",
        "nul",
        "nulll",
        "tru",
        "fals",
        "NULL",
        "None",
        "undefined",
        // strings
        "\"unterminated",
        "\"\\x\"",
        "\"\\\"",
        "\"\\u\"",
        "\"\\u12\"",
        "\"\\uZZZZ\"",
        "\"\\ud800\"",
        "\"\\udc00\"",
        "\"\\ud800\\udc00\"",
        "\"\\ud800x\"",
        "\"\\ud800\\u0041\"",
        "\"a\nb\"",
        "\"a\tb\"",
        "\"\u{7f}\"",
        // numbers
        "01",
        "-01",
        "+1",
        ".5",
        "5.",
        "1e",
        "1e+",
        "1e-",
        "1.e5",
        "-",
        "-.",
        "1e400",
        "-1e400",
        "1e-400",
        "1E2",
        "1e+2",
        "1e2",
        "0",
        "-0",
        "0.0",
        "-0.0",
        "1.0",
        "100",
        "9223372036854775807",
        "9223372036854775808",
        "-9223372036854775808",
        "-9223372036854775809",
        "18446744073709551615",
        "18446744073709551616",
        "123456789012345678901234567890",
        "1.2345678901234567890123456789",
        "0.1",
        "1e308",
        "1e309",
        "1e-323",
        "1e-324",
        "2.2250738585072014e-308",
        "5e-324",
        "1.7976931348623157e308",
        "1.7976931348623159e308",
        // duplicates and whitespace
        "{\"a\":1,\"a\":2}",
        "  [ 1 , 2 ]  ",
        "\n\n[1]\n\n",
        "[1]\n\nx",
        "{\n \"a\"\n :\n 1\n}",
        "{\n \"a\" \n 1\n}",
    ];
    for src in cases {
        check_parse(src);
    }
    println!("  malformed/edge table: {} cases", cases.len());
}

#[test]
fn parse_agrees_over_round_tripped_random_documents() {
    let mut rng = Lcg::new(0x9216D5D98979FB1B);
    for _ in 0..20_000 {
        let v = random_value(&mut rng, 0);
        let compact = tj::to_string(&v).unwrap();
        let pretty = tj::to_string_pretty(&v).unwrap();
        check_parse(&compact);
        check_parse(&pretty);
    }
}

#[test]
fn parse_agrees_over_random_number_texts() {
    // The number grammar has more corners than the rest of JSON put together,
    // and the incumbent's default float path is deliberately imprecise, so the
    // interesting question is whether we land on the SAME imprecise bits.
    let mut rng = Lcg::new(0xD1310BA698DFB5AC);
    for _ in 0..200_000 {
        let mut s = String::new();
        if rng.below(2) == 0 {
            s.push('-');
        }
        let int_digits = 1 + rng.below(25);
        for k in 0..int_digits {
            let d = if k == 0 {
                b'1' + rng.below(9) as u8
            } else {
                b'0' + rng.below(10) as u8
            };
            s.push(d as char);
        }
        if rng.below(2) == 0 {
            s.push('.');
            let frac = 1 + rng.below(25);
            for _ in 0..frac {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        if rng.below(2) == 0 {
            s.push(if rng.below(2) == 0 { 'e' } else { 'E' });
            match rng.below(3) {
                0 => s.push('+'),
                1 => s.push('-'),
                _ => {}
            }
            let ed = 1 + rng.below(4);
            for _ in 0..ed {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        check_parse(&s);
    }
}

#[test]
fn parse_agrees_over_random_byte_soup() {
    // Almost all of these are rejected; the point is that they are rejected at
    // the SAME position with the SAME message.
    let alphabet: &[u8] = b"{}[]\",:0123456789.eE+-\\ /\ttnulrfaseZ\n";
    let mut rng = Lcg::new(0x2FFD72DBD01ADFB7);
    let mut accepted = 0u64;
    for _ in 0..200_000 {
        let len = rng.below(14) as usize;
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            bytes.push(alphabet[rng.below(alphabet.len() as u64) as usize]);
        }
        let s = String::from_utf8(bytes).unwrap();
        if tj::from_str(&s).is_ok() {
            accepted += 1;
        }
        check_parse(&s);
    }
    println!("  byte soup: 200000 inputs, {accepted} accepted by both");
    assert!(accepted > 100, "the soup never produced valid JSON -- the generator, not the parser, is what got tested");
}

#[test]
fn the_surprising_parse_behaviours_are_preserved() {
    // Each of these is a plausible "bug" someone would fix, and each is a
    // byte-visible behaviour of the incumbent.
    let m = tj::from_str("-0").unwrap();
    let i = inc::from_str::<inc::Value>("-0").unwrap();
    assert!(m.is_f64() && i.is_f64(), "-0 parses to a FLOAT, not an int");
    assert_eq!(tj::to_string(&m).unwrap(), inc::to_string(&i).unwrap());
    assert_eq!(tj::to_string(&m).unwrap(), "-0.0");

    assert!(tj::from_str("1e400").is_err() && inc::from_str::<inc::Value>("1e400").is_err());
    assert_eq!(tj::from_str("1e-400").unwrap().to_string(), "0.0");
    assert_eq!(
        inc::from_str::<inc::Value>("1e-400").unwrap().to_string(),
        "0.0"
    );

    assert_eq!(
        tj::from_str(r#"{"a":1,"a":2}"#).unwrap().to_string(),
        r#"{"a":2}"#
    );
}

#[test]
fn recursion_limit_matches_the_incumbent() {
    for depth in [1usize, 2, 100, 126, 127, 128, 129, 200] {
        let s = "[".repeat(depth) + &"]".repeat(depth);
        let mine = tj::from_str(&s);
        let theirs = inc::from_str::<inc::Value>(&s);
        assert_eq!(
            mine.is_ok(),
            theirs.is_ok(),
            "depth {depth}: tj ok={} inc ok={}",
            mine.is_ok(),
            theirs.is_ok()
        );
        if let (Err(a), Err(b)) = (&mine, &theirs) {
            assert_eq!(a.to_string(), b.to_string(), "depth {depth}");
        }
    }
    // ... and lifting it works. The incumbent's half of this cannot be driven
    // without `serde::Deserialize` in scope, and adding `serde` as a
    // dev-dependency here would put a third-party trait crate back into the
    // gate's own graph, so only our side is exercised: the AGREEMENT that
    // matters (the limit is 128, and it errors with the same text) is the loop
    // above.
    let deep = "[".repeat(300) + &"]".repeat(300);
    let mut de = tj::Deserializer::from_str(&deep).disable_recursion_limit();
    assert!(de.parse_value().is_ok());
    assert!(tj::from_str(&deep).is_err(), "the limit still applies by default");
}
