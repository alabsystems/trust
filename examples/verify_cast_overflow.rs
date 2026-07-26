// Trust test: narrowing cast (defined truncation — no obligation)
// VcKind: CastOverflow
// Expected: CastOverflow ABSENT
// Integer-to-integer `as` is DEFINED truncation/reinterpretation (owner
// decision 2026-07-06, trust-vcgen v2_build_cast_vc): the old CastOverflow
// obligation false-refuted every truncating cast and broke drop-in. The cast
// result is range-tracked for downstream VCs instead. Lossy-narrowing bug
// coverage lives in the falsification-gate pair lane
// (tests/trust-falsification/{proved,mutant}/channel_to_u8.rs, b030100324).
// ABSENT is a generation assertion: it forbids a CastOverflow transport row; it
// does not relabel absence as a proof.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

fn narrow(x: u32) -> u8 {
    x as u8 // BUG: silently truncates when x > 255
}

fn main() {
    let _ = narrow(100);
}
