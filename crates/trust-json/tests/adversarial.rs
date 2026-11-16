// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// ADVERSARIAL review harness. Unlike `differential_json.rs`, this file does not
// assert-and-die on the first divergence: it COLLECTS every disagreement so one
// run enumerates the whole set. It targets what a corpus author forgets.

use incumbent_serde_json as inc;
use trust_json as tj;

mod common;
use common::{abbreviated, first_difference, inc_from_slice, inc_from_str};

// ---------------------------------------------------------------------------
// Reporting harness
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Report {
    diffs: Vec<String>,
    checked: usize,
}

impl Report {
    fn note(&mut self, what: String) {
        self.diffs.push(what);
    }
    fn finish(&self, name: &str) {
        println!("== {name}: {} inputs, {} DIVERGENCES", self.checked, self.diffs.len());
        for (i, d) in self.diffs.iter().enumerate() {
            println!("  [{i}] {d}");
        }
    }
}

/// The note for two re-serializations of one input that disagree: the input,
/// abbreviated, and the first byte at which the renderings part, with a window
/// from each side. Never the documents: the inputs here run to a megabyte, and
/// a note carrying the input and both renderings in full (as this harness's
/// did) is a single multi-megabyte line in which the divergence cannot be
/// found. `None` when the renderings agree.
fn reserialize_note(label: &str, src: &str, ours: &str, theirs: &str) -> Option<String> {
    first_difference(ours, theirs)
        .map(|d| format!("{label} {}: reserialize differs at {d}", abbreviated(src)))
}

/// Compare a parse of `src` (as &str) both ways. Records, never panics.
fn cmp_parse(rep: &mut Report, src: &str, label: &str) {
    rep.checked += 1;
    let mine = tj::from_str(src);
    let theirs = inc_from_str(src);
    let shown = abbreviated(src);
    match (&mine, &theirs) {
        (Ok(a), Ok(b)) => {
            let am = tj::to_string(a).unwrap();
            let bm = inc::to_string(b).unwrap();
            if let Some(note) = reserialize_note(label, src, &am, &bm) {
                rep.note(note);
            }
            // carrier check
            if let (tj::Value::Number(x), inc::Value::Number(y)) = (a, b) {
                if x.is_u64() != y.is_u64() || x.is_i64() != y.is_i64() || x.is_f64() != y.is_f64()
                {
                    rep.note(format!("{label} {shown}: number carrier differs"));
                }
            }
        }
        (Err(a), Err(b)) => {
            if a.to_string() != b.to_string() {
                rep.note(format!(
                    "{label} {shown}: ERROR TEXT tj={:?} inc={:?}",
                    a.to_string(),
                    b.to_string()
                ));
            }
            if (a.classify() == tj::Category::Eof) != (b.classify() == inc::error::Category::Eof) {
                rep.note(format!("{label} {shown}: is_eof tj={} inc={}", a.is_eof(), b.is_eof()));
            }
        }
        (Ok(a), Err(b)) => rep.note(format!(
            "{label} {shown}: tj ACCEPTED as {}, inc rejected: {b}",
            abbreviated(&a.to_string())
        )),
        (Err(a), Ok(b)) => rep.note(format!(
            "{label} {shown}: tj REJECTED ({a}), inc accepted as {}",
            abbreviated(&b.to_string())
        )),
    }
}

/// Same, for `from_slice` on arbitrary bytes (never exercised by the shipped gate).
fn cmp_parse_bytes(rep: &mut Report, src: &[u8], label: &str) {
    rep.checked += 1;
    let mine = tj::from_slice(src);
    let theirs = inc_from_slice(src);
    let lossy = String::from_utf8_lossy(src);
    let shown = abbreviated(&lossy);
    match (&mine, &theirs) {
        (Ok(a), Ok(b)) => {
            let am = tj::to_string(a).unwrap();
            let bm = inc::to_string(b).unwrap();
            if let Some(note) = reserialize_note(label, &lossy, &am, &bm) {
                rep.note(note);
            }
        }
        (Err(a), Err(b)) => {
            if a.to_string() != b.to_string() {
                rep.note(format!(
                    "{label} {shown}: ERROR TEXT tj={:?} inc={:?}",
                    a.to_string(),
                    b.to_string()
                ));
            }
        }
        (Ok(_), Err(b)) => rep.note(format!("{label} {shown}: tj ACCEPTED, inc rejected: {b}")),
        (Err(a), Ok(_)) => rep.note(format!("{label} {shown}: tj REJECTED ({a}), inc accepted")),
    }
}

/// The harness's own failure report stays readable at the sizes it feeds.
///
/// Two 1 MiB renderings that part at one byte must produce a note that names
/// that byte and stays a few hundred bytes long. Before this, `enormous_inputs`
/// reported a divergence on its 100k-key object as one 5,033,389-byte line
/// (measured 2026-11-13 under the incumbent's `preserve_order` backing, on the
/// test sources from before a53889fef7, which did not yet take the incumbent's
/// tree in key order).
#[test]
fn a_divergence_note_names_the_difference_not_the_document() {
    let ours = "a".repeat(1 << 20);
    let mut theirs = ours.clone();
    theirs.replace_range(700_000..700_001, "b");
    let src = format!("\"{ours}\"");
    let note = reserialize_note("probe", &src, &ours, &theirs).expect("the renderings differ");
    assert!(note.len() < 1024, "the note is {} bytes: {}", note.len(), abbreviated(&note));
    assert!(note.contains("byte 700000 of 1048576 (ours) / 1048576 (theirs)"), "{note}");
    assert!(note.contains("(1048578 bytes)"), "the input's size is named: {note}");
    assert_eq!(reserialize_note("probe", &src, &ours, &ours), None);
}

// ---------------------------------------------------------------------------
// 1. Escapes and surrogates truncated at EOF -- the shipped table stops at
//    well-formed-but-invalid, never at truncated-mid-escape.
// ---------------------------------------------------------------------------

#[test]
fn truncated_escapes_and_surrogates() {
    let mut rep = Report::default();
    let cases: &[&str] = &[
        // backslash / \u truncation
        "\"\\",
        "\"\\u",
        "\"\\u0",
        "\"\\u00",
        "\"\\u000",
        "\"\\u0000",
        // leading surrogate then EOF at every stage
        "\"\\ud800",
        "\"\\ud800\\",
        "\"\\ud800\\u",
        "\"\\ud800\\ud",
        "\"\\ud800\\udc",
        "\"\\ud800\\udc0",
        "\"\\ud800\\udc00",
        // leading surrogate followed by a non-escape / wrong escape
        "\"\\ud800 \"",
        "\"\\ud800\\n\"",
        "\"\\ud800\\\\\"",
        "\"\\ud800\\t\"",
        // two leading surrogates
        "\"\\ud800\\ud800\"",
        "\"\\udbff\\udfff\"",
        "\"\\uD800\\uDC00\"",
        // trailing surrogate first
        "\"\\udc00\\ud800\"",
        // NUL and friends via escape
        "\"\\u0000\"",
        "\"a\\u0000b\"",
        "\"\\u001f\\u007f\"",
        // raw control bytes
        "\"a\u{0}b\"",
        "\"a\u{1f}b\"",
        // valid escapes at EOF inside nesting
        "[\"\\ud800",
        "{\"\\ud800",
        "{\"a\":\"\\ud800",
    ];
    for c in cases {
        cmp_parse(&mut rep, c, "escape");
    }
    rep.finish("truncated_escapes_and_surrogates");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 2. Integer / exponent overflow IN THE PARSER. The shipped generator caps
//    exponents at 4 digits, so the i32 overflow branch is never reached.
// ---------------------------------------------------------------------------

#[test]
fn parser_integer_and_exponent_overflow() {
    let mut rep = Report::default();
    let mut cases: Vec<String> = vec![
        // exponent needs >= 10 digits to overflow i32
        "1e99999999999".into(),
        "-1e99999999999".into(),
        "1e-99999999999".into(),
        "-1e-99999999999".into(),
        "0e99999999999".into(),
        "-0e99999999999".into(),
        "0e-99999999999".into(),
        "1E99999999999".into(),
        "1e+99999999999".into(),
        "0.0e99999999999".into(),
        "1.5e99999999999".into(),
        // exactly at the i32 boundary
        "1e2147483647".into(),
        "1e2147483648".into(),
        "1e-2147483647".into(),
        "1e-2147483648".into(),
        "1e-2147483649".into(),
        "0e2147483648".into(),
        // leading zeros pad the exponent past the overflow guard without
        // changing its value
        "1e0000000000000000000005".into(),
        "1e-0000000000000000000005".into(),
        "0e0000000000000000000000".into(),
        // u64 significand cut-over and the discard-the-rest path
        "18446744073709551615".into(),
        "18446744073709551616".into(),
        "18446744073709551617".into(),
        "184467440737095516150".into(),
        "-18446744073709551616".into(),
        "1844674407370955161500000000000000".into(),
        // u64 above 2^53 -- exactness of the integer carrier
        "9007199254740993".into(),
        "9007199254740995".into(),
        "-9007199254740993".into(),
        "12345678901234567890".into(),
    ];
    // very long digit strings (parse_long_integer / parse_decimal_overflow)
    for n in [30usize, 40, 100, 400, 1000] {
        cases.push("9".repeat(n));
        cases.push(format!("-{}", "9".repeat(n)));
        cases.push(format!("0.{}", "9".repeat(n)));
        cases.push(format!("{}.{}", "1".repeat(n), "7".repeat(n)));
        cases.push(format!("1.{}e10", "3".repeat(n)));
        cases.push(format!("{}e-10", "9".repeat(n)));
    }
    for c in &cases {
        cmp_parse(&mut rep, c, "number");
    }
    rep.finish("parser_integer_and_exponent_overflow");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 3. from_slice on non-UTF-8. NEVER exercised by the shipped gate, which only
//    calls from_str.
// ---------------------------------------------------------------------------

#[test]
fn from_slice_on_invalid_utf8() {
    let mut rep = Report::default();
    let cases: Vec<Vec<u8>> = vec![
        b"\"\xff\"".to_vec(),
        b"\"\x80\"".to_vec(),
        b"\"a\xffb\"".to_vec(),
        b"\"\xc3\"".to_vec(),             // truncated 2-byte seq
        b"\"\xe2\x82\"".to_vec(),         // truncated 3-byte seq
        b"\"\xed\xa0\x80\"".to_vec(),     // UTF-8-encoded lone surrogate
        b"\"\xf4\x90\x80\x80\"".to_vec(), // above U+10FFFF
        b"[\"\xff\"]".to_vec(),
        b"{\"\xff\":1}".to_vec(),
        b"{\"a\":\"\xff\"}".to_vec(),
        b"\"\\n\xff\"".to_vec(), // escape forces the scratch path first
        b"\"\xff\\n\"".to_vec(),
        b"[1,\xff]".to_vec(), // invalid byte OUTSIDE a string
        b"\xff".to_vec(),
        b"\xef\xbb\xbf[1]".to_vec(), // UTF-8 BOM
        b"\"\xff".to_vec(),          // invalid AND unterminated
        b"".to_vec(),
    ];
    for c in &cases {
        cmp_parse_bytes(&mut rep, c, "slice");
    }
    rep.finish("from_slice_on_invalid_utf8");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 4. Recursion limits through OBJECTS and mixed nesting. The shipped test only
//    uses `[`.
// ---------------------------------------------------------------------------

#[test]
fn recursion_limit_through_objects_and_mixed_nesting() {
    let mut rep = Report::default();
    for depth in [1usize, 2, 63, 64, 126, 127, 128, 129, 130, 200] {
        let arr = "[".repeat(depth) + &"]".repeat(depth);
        cmp_parse(&mut rep, &arr, "arr");

        let obj = "{\"a\":".repeat(depth) + "1" + &"}".repeat(depth);
        cmp_parse(&mut rep, &obj, "obj");

        let mixed: String =
            (0..depth).map(|i| if i % 2 == 0 { "[" } else { "{\"a\":" }).collect::<String>()
                + "1"
                + &(0..depth).rev().map(|i| if i % 2 == 0 { "]" } else { "}" }).collect::<String>();
        cmp_parse(&mut rep, &mixed, "mixed");

        // depth reached inside a sibling, so `ascend` correctness matters
        let siblings = format!(
            "[{},{}]",
            "[".repeat(depth) + &"]".repeat(depth),
            "[".repeat(depth) + &"]".repeat(depth)
        );
        cmp_parse(&mut rep, &siblings, "siblings");
    }
    rep.finish("recursion_limit_through_objects_and_mixed_nesting");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 5. Keys: empty, duplicates that COLLIDE ONLY AFTER UNESCAPING, escape-bearing
//    keys, normalisation look-alikes.
// ---------------------------------------------------------------------------

#[test]
fn adversarial_object_keys() {
    let mut rep = Report::default();
    let cases: &[&str] = &[
        r#"{"":1}"#,
        r#"{"":1,"":2}"#,
        // collide only after unescaping: "a" and "\u0061"
        r#"{"a":1,"\u0061":2}"#,
        r#"{"\u0061":1,"a":2}"#,
        // escape-bearing keys that must round-trip through the writer
        r#"{"\"":1,"\\":2,"\n":3,"\u0000":4,"\u001f":5}"#,
        r#"{"a\/b":1}"#,
        r#"{"\u007f":1}"#,
        // NFC vs NFD look-alikes: DIFFERENT strings, must stay two keys
        "{\"\u{e9}\":1,\"e\u{301}\":2}",
        // sort order across escapes and non-ASCII
        r#"{"z":1,"\u0000":2,"":3,"~":4,"\u007f":5,"é":6,"𝄞":7}"#,
        // astral key
        r#"{"\ud83d\ude00":1}"#,
        // key that is a lone leading surrogate escape (must be rejected)
        r#"{"\ud800":1}"#,
        // duplicate with different value carriers
        r#"{"a":1,"a":1.0}"#,
        r#"{"a":1.0,"a":1}"#,
        r#"{"a":-0,"a":0}"#,
        // three-way duplicate
        r#"{"a":1,"a":2,"a":3}"#,
    ];
    for c in cases {
        cmp_parse(&mut rep, c, "key");
    }

    // ... and the same, structurally: build the map on both sides and confirm
    // len + rendering agree after a colliding insert.
    rep.checked += 1;
    let mine: tj::Value = tj::from_str(r#"{"a":1,"\u0061":2}"#).unwrap();
    let theirs: inc::Value = inc::from_str(r#"{"a":1,"\u0061":2}"#).unwrap();
    if mine.as_object().unwrap().len() != theirs.as_object().unwrap().len() {
        rep.note("colliding-escape key count differs".into());
    }

    rep.finish("adversarial_object_keys");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 6. Enormous inputs.
// ---------------------------------------------------------------------------

#[test]
fn enormous_inputs() {
    let mut rep = Report::default();

    // 1 MiB string body, all escapable
    let big = "\\n".repeat(500_000);
    let src = format!("\"{big}\"");
    cmp_parse(&mut rep, &src, "1MiB-escapes");

    // 1 MiB flat array
    let arr = format!("[{}]", vec!["1"; 300_000].join(","));
    cmp_parse(&mut rep, &arr, "300k-array");

    // 100k-key object written in numeric order, which is not key order (`k10`
    // sorts before `k2`); the writer path is O(n). `cmp_parse` compares the
    // incumbent's tree in key order (`common::key_sorted`).
    let obj = format!(
        "{{{}}}",
        (0..100_000).map(|i| format!("\"k{i}\":{i}")).collect::<Vec<_>>().join(",")
    );
    cmp_parse(&mut rep, &obj, "100k-object");

    // A very long single number
    cmp_parse(&mut rep, &"1".repeat(100_000), "100k-digit-int");
    cmp_parse(&mut rep, &format!("0.{}", "1".repeat(100_000)), "100k-digit-frac");

    rep.finish("enormous_inputs");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 7. Wider byte soup than the shipped one: full ASCII alphabet incl. `d`,
//    control bytes, longer inputs.
// ---------------------------------------------------------------------------

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        let x = self.0;
        x ^ (x >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

#[test]
fn wide_byte_soup() {
    let mut rep = Report::default();
    // Everything the shipped soup has, PLUS: d (so \uD800 is reachable), all
    // hex letters, x, raw control bytes, DEL.
    let alphabet: &[u8] = b"{}[]\",:0123456789.eEabcdfABCDF+-\\/ \t\n\r\x00\x1f\x7fxtnulrsZ";
    let mut rng = Lcg(0x243F6A8885A308D3);
    let mut accepted = 0u64;
    for _ in 0..300_000 {
        let len = rng.below(20) as usize;
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            bytes.push(alphabet[rng.below(alphabet.len() as u64) as usize]);
        }
        // from_str path (all bytes above are ASCII, so this is always UTF-8)
        let s = String::from_utf8(bytes.clone()).unwrap();
        if tj::from_str(&s).is_ok() {
            accepted += 1;
        }
        cmp_parse(&mut rep, &s, "soup");
        if rep.diffs.len() > 40 {
            break;
        }
    }
    println!("  wide soup accepted-by-tj: {accepted}");
    rep.finish("wide_byte_soup");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

/// Same soup, but through `from_slice` with NON-ASCII bytes in the alphabet.
#[test]
fn wide_byte_soup_non_utf8() {
    let mut rep = Report::default();
    let alphabet: &[u8] = b"{}[]\",:019.eE\\/ \t\xff\x80\xc3\xa9\xed\xa0\x80tnulrsa";
    let mut rng = Lcg(0x13198A2E03707344);
    for _ in 0..200_000 {
        let len = rng.below(16) as usize;
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            bytes.push(alphabet[rng.below(alphabet.len() as u64) as usize]);
        }
        cmp_parse_bytes(&mut rep, &bytes, "soup8");
        if rep.diffs.len() > 40 {
            break;
        }
    }
    rep.finish("wide_byte_soup_non_utf8");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 8. Structured escape fuzz: strings built from escape fragments, so the
//    surrogate state machine is driven hard.
// ---------------------------------------------------------------------------

#[test]
fn escape_fragment_fuzz() {
    let mut rep = Report::default();
    let frags: &[&str] = &[
        "\\u", "\\ud800", "\\udc00", "\\udbff", "\\udfff", "\\u0041", "\\uffff", "\\u0000", "\\n",
        "\\\\", "\\\"", "\\/", "\\b", "\\f", "\\r", "\\t", "\\x", "\\", "a", "\u{7f}", "0", "d",
        "D", "8", "\\uD800", "\\uDC00", "\\u00", "\\ud80",
    ];
    let mut rng = Lcg(0xA4093822299F31D0);
    for _ in 0..200_000 {
        let n = rng.below(5) as usize;
        let mut s = String::from("\"");
        for _ in 0..n {
            s.push_str(frags[rng.below(frags.len() as u64) as usize]);
        }
        if rng.below(4) != 0 {
            s.push('"');
        }
        cmp_parse(&mut rep, &s, "esc");
        if rep.diffs.len() > 40 {
            break;
        }
    }
    rep.finish("escape_fragment_fuzz");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 9. f32 round-trip through Value, and 128-bit integers through Formatter --
//    neither is compared to the incumbent anywhere in the shipped gate.
// ---------------------------------------------------------------------------

#[test]
fn f32_values_through_value_and_128_bit_integers() {
    let mut rep = Report::default();
    let mut rng = Lcg(0x082EFA98EC4E6C89);

    // Value::from(f32) goes through f64::from -- compare with the incumbent's.
    for _ in 0..500_000 {
        let bits = rng.next_u64() as u32;
        let f = f32::from_bits(bits);
        if !f.is_finite() {
            continue;
        }
        rep.checked += 1;
        let mine = tj::to_string(&tj::Value::from(f)).unwrap();
        let theirs = inc::to_string(&inc::Value::from(f)).unwrap();
        if mine != theirs {
            rep.note(format!("Value::from(f32) {bits:#010x}: tj={mine} inc={theirs}"));
            if rep.diffs.len() > 20 {
                break;
            }
        }
    }

    // Formatter::write_i128 / write_u128 vs serde_json's.
    use trust_json::Formatter as _;
    let mut fmt = tj::CompactFormatter;
    let mut vals: Vec<i128> =
        vec![0, 1, -1, i128::MIN, i128::MAX, i64::MIN as i128, i64::MAX as i128];
    for _ in 0..50_000 {
        let hi = rng.next_u64() as u128;
        let lo = rng.next_u64() as u128;
        vals.push(((hi << 64) | lo) as i128);
    }
    for v in vals {
        rep.checked += 1;
        let mut buf = Vec::new();
        fmt.write_i128(&mut buf, v).unwrap();
        let mine = String::from_utf8(buf).unwrap();
        let theirs = inc::to_string(&v).unwrap();
        if mine != theirs {
            rep.note(format!("write_i128({v}): tj={mine} inc={theirs}"));
        }
        let u = v as u128;
        let mut buf = Vec::new();
        fmt.write_u128(&mut buf, u).unwrap();
        let mine = String::from_utf8(buf).unwrap();
        let theirs = inc::to_string(&u).unwrap();
        if mine != theirs {
            rep.note(format!("write_u128({u}): tj={mine} inc={theirs}"));
        }
    }

    rep.finish("f32_values_through_value_and_128_bit_integers");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
}

// ---------------------------------------------------------------------------
// 10. Round-trip stability.
//
// `parse -> serialize` IS a fixpoint after the first hop. It was not while the
// incumbent's float parse was the imprecise default one (measured then at 8.245%
// of random number texts, 8358 still moving after a THIRD hop); first-party/clean
// 99ddfe452 enabled `float_roundtrip` in clean-olean, feature unification made
// the incumbent correctly rounded workspace-wide, and trust-json's Cargo.toml
// now names that feature on the oracle. A correctly-rounded parse of a
// shortest-round-trip rendering returns the same bits, so hop 2 must equal hop
// 1, and this test asserts it. It also asserts that the two implementations
// move together: any input where trust-json's rendering differs from the
// incumbent's, at any hop, is a real defect.
//
// It matters: this tree hashes serialized JSON as a proof-bundle identity, so a
// parse that is not a fixpoint makes a bundle that takes two process hops hash
// differently from one that takes one.
// ---------------------------------------------------------------------------

#[test]
fn round_trip_agrees_with_the_incumbent_at_every_hop() {
    let mut rep = Report::default();
    let mut rng = Lcg(0x452821E638D01377);
    let mut unstable = 0u64;
    for _ in 0..200_000 {
        // numbers with an aggressive shape distribution
        let mut s = String::new();
        if rng.below(2) == 0 {
            s.push('-');
        }
        let int_digits = 1 + rng.below(40);
        for k in 0..int_digits {
            let d = if k == 0 { b'1' + rng.below(9) as u8 } else { b'0' + rng.below(10) as u8 };
            s.push(d as char);
        }
        if rng.below(2) == 0 {
            s.push('.');
            for _ in 0..(1 + rng.below(40)) {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        if rng.below(2) == 0 {
            s.push('e');
            match rng.below(3) {
                0 => s.push('+'),
                1 => s.push('-'),
                _ => {}
            }
            for _ in 0..(1 + rng.below(12)) {
                s.push((b'0' + rng.below(10) as u8) as char);
            }
        }
        rep.checked += 1;
        let m1 = tj::from_str(&s);
        let t1 = inc::from_str::<inc::Value>(&s);
        match (m1, t1) {
            (Ok(a), Ok(b)) => {
                let sa = tj::to_string(&a).unwrap();
                let sb = inc::to_string(&b).unwrap();
                if sa != sb {
                    rep.note(format!("{s:?} pass1 tj={sa} inc={sb}"));
                    if rep.diffs.len() > 20 {
                        break;
                    }
                    continue;
                }
                // Hop 2 and hop 3 must still AGREE, even where neither is
                // stable. Instability is the incumbent's; disagreement is ours.
                let sa2 = tj::to_string(&tj::from_str(&sa).unwrap()).unwrap();
                let sb2 = inc::to_string(&inc::from_str::<inc::Value>(&sb).unwrap()).unwrap();
                if sa2 != sb2 {
                    rep.note(format!("{s:?} hop2 tj={sa2} inc={sb2}"));
                }
                if sa != sa2 {
                    unstable += 1;
                }
                let sa3 = tj::to_string(&tj::from_str(&sa2).unwrap()).unwrap();
                let sb3 = inc::to_string(&inc::from_str::<inc::Value>(&sb2).unwrap()).unwrap();
                if sa3 != sb3 {
                    rep.note(format!("{s:?} hop3 tj={sa3} inc={sb3}"));
                }
            }
            (Err(_), Err(_)) => {}
            (Ok(_), Err(e)) => rep.note(format!("{s:?}: tj accepted, inc rejected {e}")),
            (Err(e), Ok(_)) => rep.note(format!("{s:?}: tj rejected {e}, inc accepted")),
        }
        if rep.diffs.len() > 20 {
            break;
        }
    }
    println!("  NOT a fixpoint after hop 1: {unstable} of {} checked", rep.checked);
    rep.finish("round_trip_agrees_with_the_incumbent_at_every_hop");
    assert!(rep.diffs.is_empty(), "{} divergences", rep.diffs.len());
    assert_eq!(unstable, 0, "a correctly-rounded parse must make hop 2 == hop 1");
}
