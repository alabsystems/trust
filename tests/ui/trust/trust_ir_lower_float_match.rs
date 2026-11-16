//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off -Aunused_features
#![feature(loop_match)]
//! Trust (wave-FLM): a FLOAT match lowers as a chain of `Inst::FCmp` — the
//! slice/str skeleton with the length test replaced by a float comparison.
//!
//! The surrounding comments said float pattern equality "must never be lowered
//! silently as int equality", which is correct about what must NOT be done and
//! had been read as a wall. rustc's own MIR settles the semantics: it builds
//! `Eq(const 1f32, x)` and `Le(const 2f32, x)` / `Lt(x, const 3f32)` with both
//! misses branching to the same next-arm entry, and `map_fcmp` is documented
//! byte-for-byte identical to the MIR-side oracle's table. So `OEq`/`OLe`/`OLt`
//! IS rustc's semantics.
//!
//! `nan_falls_through` is the pin that matters: NaN fails every ordered test
//! and reaches the default, exactly as the real program does — checked here by
//! VALUE, not by a tag.

pub fn classify(x: f32) -> u32 {
    match x {
        1.0 => 10,
        2.0..3.0 => 20,
        _ => 30,
    }
}

pub fn classify64(x: f64) -> u32 {
    match x {
        0.5 => 1,
        1.5..=2.5 => 2,
        _ => 3,
    }
}

pub fn nan_falls_through(x: f32) -> u32 {
    match x {
        1.0 => 10,
        2.0..3.0 => 20,
        _ => 30,
    }
}

fn main() {
    assert_eq!(classify(1.0), 10);
    assert_eq!(classify(2.0), 20);
    assert_eq!(classify(2.9), 20);
    assert_eq!(classify(3.0), 30);
    assert_eq!(classify(9.0), 30);
    assert_eq!(classify64(0.5), 1);
    assert_eq!(classify64(2.5), 2);
    assert_eq!(classify64(2.6), 3);
    assert_eq!(nan_falls_through(f32::NAN), 30);
    assert_eq!(nan_falls_through(-0.0), 30);
}
