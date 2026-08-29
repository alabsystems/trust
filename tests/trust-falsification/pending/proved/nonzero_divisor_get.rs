#![crate_type = "lib"]
// QUARANTINED — CAPABILITY GAP on the branch, over-refutation at the base.
// `a / d.get()` for a `NonZeroU32` divisor. IT DOES NOT FAULT: the type's own
// invariant makes `d.get()` nonzero, and unsigned division cannot overflow.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 2080 runs, sweep
// `d in 1..=256` plus {65535, 65536, u32::MAX-1, u32::MAX}, crossed with
// `a in {0, 1, 2, 255, 256, 65535, u32::MAX-1, u32::MAX}`.
//
// Measured under `-Ztrust-policy=certify`: pristine `70a7534fd1` answers
// `refuted` with `[divzero] FAILED`; `campaign-integration` answers
// `incomplete` — one row is now the explicit decline
// `unsupported MIR UnmodeledCalleeReturn: the obligation's verdict is the
// return value of an unmodelled call, which nothing in this body constrains`.
// That is the fail-closed treatment working: the base invented a zero divisor
// out of a free return value, the branch refuses to. It is still not a proof.
//
// WHAT IT WOULD TAKE: `NonZeroU32::get` has to be modelled — either summarised
// with its `!= 0` postcondition or lowered rather than havocked. Move it to
// `proved/` then. Note this fixture is ALSO the reason the class of declined
// rows cannot be gated from a `.rs` fixture at all; see the corpus README
// section "What this gate CANNOT see".
use core::num::NonZeroU32;
pub fn nonzero_divisor_get(a: u32, d: NonZeroU32) -> u32 {
    a / d.get()
}
