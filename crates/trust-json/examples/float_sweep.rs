// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// EXHAUSTIVE f32 byte differential, plus a TIE-TARGETED f64 sweep.
//
// Why not a #[test]: exhaustive f32 is 2^32 values and takes minutes even in
// release, and the shipped gate's stride-977 sample covers 0.1% of the space.
// The tie-break correction in `ser/float.rs` is the one piece of that file that
// is an ALGORITHM rather than a transcription, and random bit patterns hit an
// exact tie about 1 time in 4000 -- so a targeted generator is worth more than
// another million random draws.
//
//   float_sweep f32-exhaustive [threads]
//   float_sweep f64-ties <count>

use inc::ser::Formatter as _;
use incumbent_serde_json as inc;
use trust_json as tj;
use trust_json::ser::float::FloatBuffer;

/// One (trust-json, serde_json) rendering pair for an f32, compared as bytes.
fn cmp_f32(v: f32, scratch: &mut Vec<u8>) -> Option<(String, String)> {
    let mut fb = FloatBuffer::new();
    let mine = fb.format_finite_f32(v);
    scratch.clear();
    let mut f = inc::ser::CompactFormatter;
    f.write_f32(scratch, v).unwrap();
    if mine.as_bytes() == scratch.as_slice() {
        None
    } else {
        Some((mine.to_owned(), String::from_utf8_lossy(scratch).into_owned()))
    }
}

fn cmp_f64(v: f64, scratch: &mut Vec<u8>) -> Option<(String, String)> {
    let mut fb = FloatBuffer::new();
    let mine = fb.format_finite_f64(v);
    scratch.clear();
    let mut f = inc::ser::CompactFormatter;
    f.write_f64(scratch, v).unwrap();
    if mine.as_bytes() == scratch.as_slice() {
        None
    } else {
        Some((mine.to_owned(), String::from_utf8_lossy(scratch).into_owned()))
    }
}

fn f32_exhaustive(threads: u32) {
    let chunk = (1u64 << 32) / u64::from(threads);
    let handles: Vec<_> = (0..threads)
        .map(|t| {
            let lo = u64::from(t) * chunk;
            let hi = if t == threads - 1 { 1u64 << 32 } else { lo + chunk };
            std::thread::spawn(move || {
                let mut scratch = Vec::with_capacity(32);
                let mut checked = 0u64;
                let mut diffs: Vec<(u32, String, String)> = Vec::new();
                for bits in lo..hi {
                    let v = f32::from_bits(bits as u32);
                    if !v.is_finite() {
                        continue;
                    }
                    checked += 1;
                    if let Some((a, b)) = cmp_f32(v, &mut scratch) {
                        if diffs.len() < 20 {
                            diffs.push((bits as u32, a, b));
                        }
                    }
                }
                (checked, diffs)
            })
        })
        .collect();

    let mut total = 0u64;
    let mut all: Vec<(u32, String, String)> = Vec::new();
    for h in handles {
        let (c, d) = h.join().unwrap();
        total += c;
        all.extend(d);
    }
    println!("f32 EXHAUSTIVE: {total} finite values checked, {} divergences", all.len());
    for (bits, a, b) in all.iter().take(20) {
        println!("  {bits:#010x}: tj={a} inc={b}");
    }
    assert!(all.is_empty(), "f32 divergences found");
}

/// Values whose exact decimal expansion is one digit longer than the shortest
/// round-trip rendering AND ends in 5 -- i.e. exact ties, where `zmij` (even)
/// and std's `{:e}` (away from zero) are free to disagree. Built as k/2^n for
/// small n, which is the only family that terminates in a 5.
fn f64_ties(count: u64) {
    let mut scratch = Vec::with_capacity(32);
    let mut rng: u64 = 0x9E3779B97F4A7C15;
    let mut next = || {
        rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        rng ^ (rng >> 31)
    };
    let mut checked = 0u64;
    let mut ties = 0u64;
    let mut diffs = Vec::new();

    for _ in 0..count {
        // integer part with 1..=17 significant digits, plus a k/2^n fraction
        let digits = 1 + (next() % 17);
        let mut m: u64 = 0;
        for _ in 0..digits {
            m = m.wrapping_mul(10).wrapping_add(next() % 10);
        }
        let shift = 1 + (next() % 6); // /2, /4, ... /64
        let frac_num = 1 + (next() % ((1u64 << shift) - 1).max(1));
        let v = m as f64 + (frac_num as f64) / ((1u64 << shift) as f64);
        if !v.is_finite() {
            continue;
        }
        // scale across magnitudes too
        for scale in [1.0f64, 1e-3, 1e3, 1e-9, 1e9] {
            let x = v * scale;
            if !x.is_finite() || x == 0.0 {
                continue;
            }
            for signed in [x, -x] {
                checked += 1;
                // Is it an exact tie? The shortest rendering has n digits; the
                // exact value needs n+1 and the last is a 5.
                let sci = format!("{signed:e}");
                let ndig =
                    sci.split('e').next().unwrap().chars().filter(char::is_ascii_digit).count();
                let exact = format!("{signed:.*}", 40usize);
                if exact.trim_end_matches('0').ends_with('5') && ndig <= 17 {
                    ties += 1;
                }
                if let Some((a, b)) = cmp_f64(signed, &mut scratch) {
                    if diffs.len() < 20 {
                        diffs.push((signed.to_bits(), a, b));
                    }
                }
            }
        }
    }
    println!(
        "f64 TIE-TARGETED: {checked} values checked ({ties} exact-decimal-ends-in-5), {} divergences",
        diffs.len()
    );
    for (bits, a, b) in &diffs {
        println!("  {bits:#018x}: tj={a} inc={b}");
    }
    assert!(diffs.is_empty(), "f64 tie divergences found");

    // ... and the same over plain random bit patterns, at higher volume than
    // the shipped gate's default.
    let mut checked2 = 0u64;
    let mut diffs2 = Vec::new();
    for _ in 0..count * 10 {
        let v = f64::from_bits(next());
        if !v.is_finite() {
            continue;
        }
        checked2 += 1;
        if let Some((a, b)) = cmp_f64(v, &mut scratch) {
            if diffs2.len() < 20 {
                diffs2.push((v.to_bits(), a, b));
            }
        }
    }
    println!("f64 RANDOM: {checked2} values checked, {} divergences", diffs2.len());
    for (bits, a, b) in &diffs2 {
        println!("  {bits:#018x}: tj={a} inc={b}");
    }
    assert!(diffs2.is_empty());

    // Value-level parity: the same numbers through the full Value writer.
    let mut d3 = 0u64;
    for _ in 0..100_000 {
        let v = f64::from_bits(next());
        if !v.is_finite() {
            continue;
        }
        let a = tj::to_string(&tj::Value::from(v)).unwrap();
        let b = inc::to_string(&inc::Value::from(v)).unwrap();
        if a != b {
            println!("  Value path {:#018x}: tj={a} inc={b}", v.to_bits());
            d3 += 1;
        }
    }
    println!("f64 Value-writer parity divergences: {d3}");
    assert_eq!(d3, 0);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    match args[1].as_str() {
        "f32-exhaustive" => {
            let t: u32 = args.get(2).map_or(8, |s| s.parse().unwrap());
            f32_exhaustive(t);
        }
        "f64-ties" => {
            let c: u64 = args.get(2).map_or(200_000, |s| s.parse().unwrap());
            f64_ties(c);
        }
        other => panic!("unknown mode {other}"),
    }
}
