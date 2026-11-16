//@ revisions: liars idx ctrl
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[liars] check-fail
//@[idx] check-pass
//@[ctrl] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A plain MIR integer `Add`/`Sub`/`Mul` WRAPS (rustc_middle `mir::BinOp::Add`). With
//! `-C overflow-checks` off there is no `Assert` in front of it, so `1 + i32::MAX` is
//! `i32::MIN` and the binary does not panic (`literal_lhs_wrap_checks_off_run.rs`).
//! trust-vcgen's block definition took the wrap's width from the LEFT operand, and
//! `operand_ty` types a width-less literal from its VALUE (`1` is `i64`), so `1 + x` on
//! `i32` was modelled as wrapping at 2^64 with i64 operand ranges. The i32 wrap was not
//! representable and every clause below PROVED, although each is false of the binary
//! (BARE-BINOP-LITERAL-LHS-WIDTH-1, docs/KNOWN_HAZARDS.md). The place-first twins
//! (`x + 1`) read the place's width and were refuted. Reach: memory-safe and advisory
//! with an explicit `-Coverflow-checks=off`; default and certify canonicalize checks on.
//!
//! BEFORE (`scratchpad/stage1-w25f`, the wave-25 stage 1, tree of `a971311ee2`; measured
//! 2026-10-13 with exactly these revisions' flags plus `--cfg <revision>`, outside
//! compiletest): `liars` built exit 0, each of `inc1`, `h_lie`, `s_lie` and `neg0` reading
//! `Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked,
//! 1 skipped out of 3 obligation(s)` (both postcondition rows proved). `idx` built exit 0
//! with `idx` reading `2 proved … 1 skipped out of 3` and `1 obligation(s) were not
//! proved`: its bounds row was PROVED (ay-in-process), and its `x - n` row too, although
//! `idx(&a, i32::MAX)` indexes `18446744073709551615`. `ctrl` built exit 1, every twin
//! refused.
//!
//! AFTER (FIX PREPARED 2026-10-13, not built; predicted): the block definition reads
//! `(width, signed)` from the DESTINATION with both operands checked against it
//! (`guards::bare_binop_machine_shape`), so the def is the i32 wrap: `liars` is refused
//! on each liar, `idx` reads as its `x + 1` twin `idx_ctrl` reads on the BEFORE compiler
//! (`0 proved … 3 skipped out of 3`, three memory-safe panics demoted to the warning),
//! and `ctrl` is unchanged.

#[cfg(liars)]
pub fn inc1(x: i32) -> i32
//[liars]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::inc1`
    ensures result > x
{
    1 + x
}

#[cfg(liars)]
pub fn h_lie(x: i8) -> i8
//[liars]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::h_lie`
    ensures x <= 27 || result > 0
{
    100 + x
}

#[cfg(liars)]
pub fn s_lie(x: i32) -> i32
//[liars]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::s_lie`
    ensures x <= 0 || result < 0
{
    -2147483647 - x
}

#[cfg(liars)]
pub fn neg0(x: i32) -> i32
//[liars]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::neg0`
    ensures x >= 0 || result > 0
{
    0 - x
}

// A bounds row under a branch that is dead only if `1 + x` cannot wrap.
#[cfg(idx)]
pub fn idx(a: &[u8; 8], x: i32) -> u8 {
//[idx]~^ NOTE Trust verification: 0 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked, 3 skipped out of 3 obligation(s)
//[idx]~| WARN Trust Level 0 safety verification incomplete for `literal_lhs_wrap_checks_off::idx`: 3 obligation(s) were not proved
    let n = 1 + x;
    if n > x { 0 } else { a[(x - n) as usize] }
}

// The controls: a place LEFT operand, an unsigned literal (`ConstValue::Uint` carries
// its width) and an `i64` add, refused before the fix and after it.
#[cfg(ctrl)]
pub fn inc1_ctrl(x: i32) -> i32
//[ctrl]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::inc1_ctrl`
    ensures result > x
{
    x + 1
}

#[cfg(ctrl)]
pub fn h_ctrl(x: i8) -> i8
//[ctrl]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::h_ctrl`
    ensures x <= 27 || result > 0
{
    x + 100
}

#[cfg(ctrl)]
pub fn u_ctrl(x: u8) -> u8
//[ctrl]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::u_ctrl`
    ensures x <= 55 || result >= 200
{
    200 + x
}

#[cfg(ctrl)]
pub fn inc64_ctrl(x: i64) -> i64
//[ctrl]~^ ERROR Trust memory-safe verification failed for `literal_lhs_wrap_checks_off::inc64_ctrl`
    ensures result > x
{
    1 + x
}
