// Trust test: narrowing cast guard -- safe variant (defined truncation — no obligation)
// VcKind: CastOverflow
// Expected: CastOverflow ABSENT
// Integer-to-integer `as` is DEFINED truncation/reinterpretation (owner
// decision 2026-07-06, trust-vcgen v2_build_cast_vc): the old CastOverflow
// obligation false-refuted every truncating cast and broke drop-in, so the
// guarded cast here carries no obligation to prove. Lossy-narrowing bug
// coverage lives in the falsification-gate pair lane
// (tests/trust-falsification/{proved,mutant}/channel_to_u8.rs, b030100324).
// ABSENT is a generation assertion: it forbids a CastOverflow transport row; it
// does not relabel absence as a proof.
// Safe pattern: if-guard `x <= 255` ensures value fits in u8 range
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn narrow_safe(x: u32) -> u8 {
    if x <= 255 {
        x as u8 // SAFE: guard ensures x fits in u8 range
    } else {
        u8::MAX // fallback: clamp to max u8 value
    }
}

fn main() {
    let _ = narrow_safe(100);
    let _ = narrow_safe(1000); // takes fallback branch
}
