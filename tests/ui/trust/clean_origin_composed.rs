//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **I5 — THE COMPOSED-CHAIN EMISSION, RUN.**
//! (`CleanOriginShape::Composed`, the third emittable Clean-origin body shape;
//! `crates/trust-clean-origin/src/emit.rs`.)
//!
//! `clean_origin_wrapping_binop.rs` runs the single-op emission; this file
//! runs the nested one — the linear wrapping-call chain. Every value asserted
//! below distinguishes the emitted semantics from a plausible mistranslation,
//! so a green run pins the chain and not merely that a call linked:
//!
//! * `wmix(u64::MAX, 1) == 0` — the INTERMEDIATE wraps (`u64::MAX + 1 = 0`)
//!   and the wrap propagates through the second op; saturating arithmetic
//!   would give `u64::MAX`, checked arithmetic would refuse to produce a
//!   value at all;
//! * `wtri(u64::MAX, 1) == 0` — the task's witness `(u64::MAX + 1) * 3 == 0`,
//!   wrap-through-intermediate with a NUMERAL root operand;
//! * `bmix(100) == 88` — the u8 case whose intermediate wraps:
//!   `100 + 200 = 300 ≡ 44 (mod 256)`, then `44 * 2 = 88`. Unwrapped integer
//!   math says 600 and saturating math says 255; only the wrapping chain
//!   says 88;
//! * `wmix(2, 3) == 10` while `wassoc(2, 3) == 8` — the ASSOCIATIVITY pin:
//!   same ops, same operand multiset, different tree, different value
//!   (control_6 half_4 pins the same fact at the gate);
//! * `W == 78` — CTFE traverses the gate AND interprets the emitted chain
//!   (`wrapping_add`/`wrapping_mul` are `const fn` in core), so the const
//!   lane is measured, not assumed.
//!
//! `gcd` stays impossible — recursion is provided by no shape, and this
//! fixture deliberately adds nothing recursive.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness
//! gate is a compilation-correctness check, deliberately NOT behind any
//! verification switch, and this fixture would be worthless if the flag could
//! disable the machinery it measures.

mod m {
    clean {
        def wmix (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a
        def wtri (a : UInt64) (b : UInt64) : UInt64 := (a + b) * 3
        def wassoc (a : UInt64) (b : UInt64) : UInt64 := a + (b * a)
        def tri3 (a : UInt64) (b : UInt64) (c : UInt64) : UInt64 := (a + b) * (c - 1)
        def bmix (a : UInt8) : UInt8 := (a + 200) * 2
    }
}

// CTFE: the const lane goes through `mir_for_ctfe`, whose only source of a
// Clean-origin body is the gated emission. (6 + 7) * 6 = 78.
const W: u64 = crate::m::wmix(6, 7);

fn main() {
    assert_eq!(m::wmix(2, 3), 10, "unwrapped: (2 + 3) * 2");
    assert_eq!(
        m::wmix(u64::MAX, 1),
        0,
        "WRAPPED THROUGH THE INTERMEDIATE: (u64::MAX + 1) wraps to 0 mid-chain"
    );
    assert_eq!(m::wtri(u64::MAX, 1), 0, "(u64::MAX + 1) * 3 == 0, numeral root operand");
    assert_eq!(m::wtri(2, 3), 15, "unwrapped: (2 + 3) * 3");
    assert_eq!(
        m::wassoc(2, 3),
        8,
        "ASSOCIATIVITY: a + (b * a) at (2, 3) is 8, and wmix(2, 3) is 10 — the emitted \
         chain must follow the tree, not re-associate it"
    );
    assert_eq!(m::tri3(2, 3, 4), 15, "three ops, both branches non-leaf: (2 + 3) * (4 - 1)");
    assert_eq!(m::tri3(1, 2, 0), u64::MAX.wrapping_mul(3), "wrap in the RIGHT branch: 3 * (0 - 1)");
    assert_eq!(
        m::bmix(100),
        88,
        "WRAPPED at u8: (100 + 200) = 300 = 44 mod 256, then 44 * 2 = 88 — not unwrapped \
         600, not saturating 255"
    );
    assert_eq!(W, 78, "CTFE of the emitted chain must agree with the runtime value");
}
