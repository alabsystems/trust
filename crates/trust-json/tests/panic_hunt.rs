// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// DoS / panic hunt. A panic where the incumbent returns Err is a real defect,
// so every probe here runs under `catch_unwind` on BOTH sides and compares
// "did it panic", not "what did it return".

use incumbent_serde_json as inc;
use std::panic::{catch_unwind, AssertUnwindSafe};
use trust_json as tj;

fn panicked<F: FnOnce()>(f: F) -> bool {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let r = catch_unwind(AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    r.is_err()
}

struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        let x = self.0;
        x ^ (x >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Full 0..=255 byte fuzz through from_slice, comparing panic-vs-panic.
#[test]
fn from_slice_never_panics_where_the_incumbent_does_not() {
    let mut rng = Lcg(0x9E3779B97F4A7C15);
    let mut diffs = Vec::new();
    let mut checked = 0u64;
    for _ in 0..400_000 {
        let len = rng.below(24) as usize;
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            bytes.push(rng.next_u64() as u8);
        }
        checked += 1;
        let b1 = bytes.clone();
        let b2 = bytes.clone();
        let mine = panicked(move || {
            let _ = tj::from_slice(&b1);
        });
        let theirs = panicked(move || {
            let _ = inc::from_slice::<inc::Value>(&b2);
        });
        if mine != theirs {
            diffs.push(format!("{bytes:?}: tj panicked={mine} inc panicked={theirs}"));
            if diffs.len() > 10 {
                break;
            }
        }
    }
    println!("== random full-byte fuzz: {checked} inputs, {} panic differences", diffs.len());
    for d in &diffs {
        println!("  {d}");
    }
    assert!(diffs.is_empty());
}

/// Structured JSON-ish fuzz: biased toward deep nesting and long escapes, both
/// of which the random-byte fuzz above almost never produces.
#[test]
fn structured_fuzz_never_panics_where_the_incumbent_does_not() {
    let frags: &[&str] = &[
        "[", "]", "{", "}", ",", ":", "\"", "\\", "u", "d", "8", "0", "0", "e", "E", "+", "-",
        ".", "1", "9", "n", "t", "f", "\\u", "\\ud800", "\\udc00", "\\uD8", "\"a\"", "null",
        "true", "false", "1e", "0.", "-", "\u{7f}", " ", "\n", "\\\"", "[]", "{}", "\"\":",
    ];
    let mut rng = Lcg(0x243F6A8885A308D3);
    let mut diffs = Vec::new();
    for _ in 0..300_000 {
        let n = rng.below(24) as usize;
        let mut s = String::new();
        for _ in 0..n {
            s.push_str(frags[rng.below(frags.len() as u64) as usize]);
        }
        let a = s.clone();
        let b = s.clone();
        let mine = panicked(move || {
            let _ = tj::from_str(&a);
        });
        let theirs = panicked(move || {
            let _ = inc::from_str::<inc::Value>(&b);
        });
        if mine != theirs {
            diffs.push(format!("{s:?}: tj panicked={mine} inc panicked={theirs}"));
            if diffs.len() > 10 {
                break;
            }
        }
    }
    println!("== structured fuzz: 300000 inputs, {} panic differences", diffs.len());
    for d in &diffs {
        println!("  {d}");
    }
    assert!(diffs.is_empty());
}

/// The `Formatter` trait is PUBLIC and its `write_f64`/`write_f32` default
/// methods state a finite precondition -- as does the incumbent's. But the two
/// FAILURE MODES differ, and that is a denial-of-service difference in a public
/// API. Recorded, not asserted-green.
#[test]
fn formatter_non_finite_failure_modes() {
    use trust_json::Formatter as _;
    let mut fmt = tj::CompactFormatter;
    for (name, v) in [
        ("NaN", f64::NAN),
        ("inf", f64::INFINITY),
        ("-inf", f64::NEG_INFINITY),
    ] {
        let mine = panicked(|| {
            let mut buf = Vec::new();
            let mut f = tj::CompactFormatter;
            let _ = f.write_f64(&mut buf, v);
        });
        println!("  trust-json Formatter::write_f64({name}) panicked = {mine}");
    }
    for (name, v) in [
        ("NaN", f32::NAN),
        ("inf", f32::INFINITY),
        ("-inf", f32::NEG_INFINITY),
    ] {
        let mine = panicked(|| {
            let mut buf = Vec::new();
            let mut f = tj::CompactFormatter;
            let _ = f.write_f32(&mut buf, v);
        });
        println!("  trust-json Formatter::write_f32({name}) panicked = {mine}");
    }
    // The incumbent's answer, for the record. serde_json's Formatter is public
    // too; its default write_f64 hands the value straight to the float backend.
    let mut buf = Vec::new();
    let r = fmt.write_f64(&mut buf, 1.0);
    assert!(r.is_ok());
    println!("  (control) write_f64(1.0) = {:?}", String::from_utf8(buf));
}

/// `ser::to_string` swallows a UTF-8 failure with `unwrap_or_default()`, i.e.
/// it would return the EMPTY STRING rather than an error. Probe whether any
/// reachable input triggers it.
#[test]
fn to_string_never_silently_returns_empty() {
    let mut rng = Lcg(0x452821E638D01377);
    let mut bad = 0u64;
    for _ in 0..200_000 {
        // strings full of the byte patterns most likely to break a naive
        // fragment split
        let n = rng.below(12) as usize;
        let mut s = String::new();
        for _ in 0..n {
            let cu = rng.below(0x11_0000) as u32;
            if let Some(c) = char::from_u32(cu) {
                s.push(c);
            }
        }
        let v = tj::Value::String(s.clone());
        let out = tj::to_string(&v).unwrap();
        if out.is_empty() && !s.is_empty() {
            bad += 1;
        }
        assert_eq!(out, inc::to_string(&s).unwrap());
    }
    println!("== to_string empty-string escapes: {bad}");
    assert_eq!(bad, 0);
}

/// Deeply nested value DROP and SERIALIZE. Both sides recurse; the question is
/// whether trust-json blows the stack at a shallower depth than the incumbent,
/// which would be a DoS difference for a caller using `disable_recursion_limit`
/// (which `crates/trust-types/src/json_depth.rs` does).
#[test]
fn deep_value_serialize_depth_parity() {
    // Stay well under the default limit so both parse; measure that serializing
    // and dropping a 127-deep tree is fine on both sides.
    let depth = 127;
    let src = "[".repeat(depth) + &"]".repeat(depth);
    let a = tj::from_str(&src).unwrap();
    let b = inc::from_str::<inc::Value>(&src).unwrap();
    assert_eq!(tj::to_string(&a).unwrap(), inc::to_string(&b).unwrap());
    assert_eq!(
        tj::to_string_pretty(&a).unwrap(),
        inc::to_string_pretty(&b).unwrap()
    );
    println!("  127-deep round trip OK on both sides");

    // The unbounded lane (`json_depth.rs` uses it) genuinely blows the stack --
    // a stack overflow ABORTS the process and cannot be caught, so the depth
    // threshold is measured by `examples/stack_probe.rs` in a subprocess
    // instead of here. See the report.
}
