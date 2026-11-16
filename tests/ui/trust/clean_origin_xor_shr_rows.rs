//@ needs-trust-verify
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr
//! **`uint.xor` AND `uint.shr`, RUN** — the two raw-binop rows the Clean pin
//! `bf31976f48` unlocked (2026-09-23), called from a Rust `main` through the
//! minted `DefId`s at u64 and u8.
//!
//! `crates/trust-clean-origin/tests/landing7_selection_probes.rs` measures
//! both rows at the crate level — plan, the real template, side B's reader,
//! the frozen producer and the kernel gate (`l7_p11`..`l7_p15`). This fixture
//! is the part only a built compiler can measure: that the `BitXor`/`Shr` arms
//! of `clean_origin_mir::materialize` build the MIR those tests describe, and
//! that the binary computes what the Clean declaration says.
//!
//! # EVERY VALUE BELOW DISTINGUISHES SOMETHING
//!
//! * `bx64(12, 10) == 6` — `^` against the two operators sharing the
//!   realization: `|` gives 14 and `&` gives 8.
//! * `bx64(x, 0) == x` and `bx64(x, u64::MAX) == !x` — the xor BOUNDARIES: the
//!   identity and the complement. `bx64(x, x) == 0` is the self-inverse.
//! * `flip64` / `flip8` — the ALL-ONES numeral as a literal operand (`u64::MAX`
//!   and `255`), the widest value the operand's `ofNat` must carry intact; a
//!   literal truncated to a narrower width fails `flip64(0) == u64::MAX`.
//! * `shr0_*` — amount `0`, the low edge the shift-amount rule admits: the
//!   identity, at both widths.
//! * `shr63` / `shr7_8` — amount `N - 1`, the high edge: exactly the top bit
//!   survives. `shr63(1 << 63) == 1` and `shr63((1 << 63) - 1) == 0` pin the
//!   amount itself; an amount off by one flips one of them.
//! * `shr3_64(7) == 0`, `shr3_64(8) == 1` — AT and BELOW `2^3`, where an
//!   off-by-one amount flips the answer.
//! * `shr3_8(255) == 31` — the u8 carrier, with the width read from the
//!   signature: the shift is LOGICAL, so no sign bit is dragged in.
//! * `X`, `S` — CTFE traverses the faithfulness gate AND interprets the emitted
//!   bare `Rvalue::BinaryOp`, so the const lane is measured, not assumed.
//!
//! # WHY THE AMOUNTS ARE NUMERALS BELOW THE WIDTH, AND WHY THERE IS NO `<<<`
//!
//! The emitted `Shr` is MIR's, which takes its amount modulo the width exactly
//! as Lean's `>>>` does, so no amount is a wrong binary — but the frozen
//! producer the kernel checks the body against mints a shift only at a literal
//! amount below the width, so `a >>> b` and `a >>> 64` are refused as a
//! capability boundary (`l7_p14`). `a <<< k` has no row at all: swept over every
//! amount, the kernel identifies the only available reflection of `<<` (a
//! multiplication by `2^k`) with it at `k = 1` alone (`l7_p7`); `a * 2^k` is the
//! emitted spelling of that function.
//!
//! `-Z trust-verify=off` is the point, not a convenience: the faithfulness gate
//! is a compilation-correctness check, deliberately NOT behind any verification
//! switch, and this fixture would be worthless if the flag could disable the
//! machinery it measures.

mod m {
    clean {
        def bx64 (a : UInt64) (b : UInt64) : UInt64 := a ^^^ b
        def bx8 (a : UInt8) (b : UInt8) : UInt8 := a ^^^ b
        def flip64 (a : UInt64) : UInt64 := a ^^^ 18446744073709551615
        def flip8 (a : UInt8) : UInt8 := a ^^^ 255
        def shr0_64 (a : UInt64) : UInt64 := a >>> 0
        def shr3_64 (a : UInt64) : UInt64 := a >>> 3
        def shr63 (a : UInt64) : UInt64 := a >>> 63
        def shr0_8 (a : UInt8) : UInt8 := a >>> 0
        def shr3_8 (a : UInt8) : UInt8 := a >>> 3
        def shr7_8 (a : UInt8) : UInt8 := a >>> 7
    }
}

// CTFE: the const lane goes through `mir_for_ctfe`, whose only source of a
// Clean-origin body is the gated emission.
const X: u64 = crate::m::bx64(12, 10);
const S: u8 = crate::m::shr7_8(200);

fn main() {
    let x: u64 = 0xDEAD_BEEF_0123_4567;

    // ── `^^^` at u64, over two parameters ──────────────────────────────────
    let six = m::bx64(12, 10);
    println!("{six}");
    assert_eq!(six, 6, "`^` is neither `|` (14) nor `&` (8)");
    assert_eq!(m::bx64(x, 0), x, "xor with 0 is the identity");
    assert_eq!(m::bx64(x, u64::MAX), !x, "xor with all-ones is the complement");
    assert_eq!(m::bx64(0, u64::MAX), u64::MAX, "0 ^ all-ones");
    assert_eq!(m::bx64(x, x), 0, "xor is self-inverse");

    // ── `^^^` at u8 ────────────────────────────────────────────────────────
    assert_eq!(m::bx8(0b1100, 0b1010), 0b0110, "u8: `^` is neither `|` nor `&`");
    assert_eq!(m::bx8(200, 0), 200, "u8: xor with 0 is the identity");
    assert_eq!(m::bx8(200, u8::MAX), 55, "u8: xor with all-ones is the complement");
    assert_eq!(m::bx8(u8::MAX, u8::MAX), 0, "u8: xor is self-inverse");

    // ── `^^^` against the ALL-ONES literal ─────────────────────────────────
    assert_eq!(m::flip64(0), u64::MAX, "the u64 all-ones literal reached the binary intact");
    assert_eq!(m::flip64(u64::MAX), 0, "all-ones ^ all-ones");
    assert_eq!(m::flip64(x), !x, "u64: xor with the all-ones literal is the complement");
    assert_eq!(m::flip8(0), u8::MAX, "the u8 all-ones literal reached the binary intact");
    assert_eq!(m::flip8(0xA5), 0x5A, "u8: xor with the all-ones literal is the complement");

    // ── `>>>` at u64: amount 0, 3 and N - 1 ────────────────────────────────
    assert_eq!(m::shr0_64(x), x, "amount 0 is the identity");
    assert_eq!(m::shr0_64(u64::MAX), u64::MAX, "amount 0 at all-ones");
    assert_eq!(m::shr3_64(7), 0, "BELOW 2^3");
    assert_eq!(m::shr3_64(8), 1, "AT 2^3: an off-by-one amount flips this");
    assert_eq!(m::shr3_64(u64::MAX), u64::MAX >> 3, "a LOGICAL shift: no bit dragged in");
    assert_eq!(m::shr63(u64::MAX), 1, "amount N - 1: only the top bit survives");
    assert_eq!(m::shr63(1 << 63), 1, "amount N - 1: the top bit alone");
    assert_eq!(m::shr63((1 << 63) - 1), 0, "amount N - 1: everything below the top bit goes");

    // ── `>>>` at u8: amount 0, 3 and N - 1 ─────────────────────────────────
    assert_eq!(m::shr0_8(200), 200, "u8: amount 0 is the identity");
    assert_eq!(m::shr3_8(u8::MAX), 31, "u8: a LOGICAL shift, width from the signature");
    assert_eq!(m::shr3_8(8), 1, "u8: AT 2^3");
    assert_eq!(m::shr7_8(u8::MAX), 1, "u8: amount N - 1, only the top bit survives");
    assert_eq!(m::shr7_8(128), 1, "u8: amount N - 1, the top bit alone");
    assert_eq!(m::shr7_8(127), 0, "u8: amount N - 1, everything below the top bit goes");

    assert_eq!(X, 6, "CTFE of the emitted `^` must agree with the runtime value");
    assert_eq!(S, 1, "CTFE of the emitted `>>` must agree with the runtime value");
}
