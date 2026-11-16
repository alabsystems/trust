//@ revisions: off_liars off_holds on_liars adv_off off_idx
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type=lib
//@[off_liars] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[off_holds] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[on_liars] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=on
//@[adv_off] compile-flags: -Ztrust-policy=advisory -Coverflow-checks=off
//@[off_idx] compile-flags: -Ztrust-policy=memory-safe -Coverflow-checks=off
//@[off_liars] check-fail
//@[off_holds] check-pass
//@[on_liars] check-pass
//@[adv_off] check-pass
//@[off_idx] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A plain MIR integer `Neg` WRAPS (rustc_middle `mir::UnOp::Neg`): `-i32::MIN` is
//! `i32::MIN`. The overflow check is a separate `Assert(OverflowNeg)` in front of
//! it, and with `-C overflow-checks` off there is none, so the binary returns
//! `i32::MIN` and does not panic (`neg_wraps_checks_off_postcondition_run.rs`).
//! trust-vcgen's block definition modelled the `Neg` as the mathematical `-x`
//! while the return pin was wrap-exact, so at `x == MIN` the postcondition query
//! contradicted itself and every clause PROVED there (NEG-WRAP-OFF-1,
//! docs/KNOWN_HAZARDS.md).
//!
//! BEFORE (scratchpad stage1-w16, main plus wave 16, measured 2026-10-05 with exactly
//! these revisions' flags and `--cfg <revision>`, outside compiletest): `off_liars`
//! built exit 0 — all 13 of the liars' postcondition rows PROVED
//! (trust-full-verifier, trust-exact-source-clause-discharge) although each clause is
//! false of the binary at `MIN`. `adv_off` built exit 0
//! with each liar's note reading `native verifier status: Inconclusive` (its
//! postcondition rows proved). `off_holds` and `on_liars` built exit 0. `off_idx`
//! built exit 0 with `1 obligation(s) were not proved` (the per-statement negation
//! row): the `a[n as usize]` bounds row was PROVED although `idx(i32::MIN)` indexes
//! `18446744071562067968` into an 8-element array.
//!
//! AFTER (MEASURED 2026-10-06 on the stage 1 of `0ac7a96d9f`, `integ/wave18`; the
//! same flags again measured on `scratchpad/stage1-w17`, the stage 1 of `9e11546767`,
//! gave the BEFORE above): the block definition is `ite(x == MIN, MIN, -x)`, so
//! `off_liars` is refused on each of the six liars; `off_holds` still compiles with
//! the true wrap claims proved; `on_liars` is unchanged (the `Assert` path guard
//! `x != MIN` selects the `-x` branch, and `-MIN` panics before it returns); and
//! `off_idx` reports the bounds row as a second unproved obligation (a memory-safe
//! panic, demoted to the warning). `adv_off` compiles with no liar proved: five read
//! `native verifier status: Failed`. `abs_like` reads `Inconclusive` (`proved=1,
//! unknown=2`, where BEFORE read `proved=2, unknown=1`), because both of its
//! postcondition rows now come back UNKNOWN (trust-full-verifier and
//! trust-exact-source-clause-discharge) instead of PROVED. The prediction said
//! `Failed` for it too; the annotation pins the measured `[postcond] UNKNOWN`, a note
//! BEFORE never printed (a proved row has none).
//!
//! Every revision still warns on each negation: the per-statement `x != MIN` row is
//! refuted and memory-safe/advisory demote it. With checks off that row is not a
//! runtime panic either; its memory-safe label is the residual SHIFT-1 recorded.

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn abs_like(x: i32) -> i32
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::abs_like`
//[adv_off]~^^ NOTE [postcond] UNKNOWN (trust-full-verifier)
    ensures result >= 0
{
    if x < 0 { -x } else { x }
}

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn neg_post(x: i32) -> i32
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::neg_post`
//[adv_off]~^^ NOTE native verifier status: Failed
    ensures x >= 0 || result > 0
{
    -x
}

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn neg_ne(x: i32) -> i32
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::neg_ne`
//[adv_off]~^^ NOTE native verifier status: Failed
    ensures result != x || x == 0
{
    -x
}

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn neg_i8(x: i8) -> i8
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::neg_i8`
//[adv_off]~^^ NOTE native verifier status: Failed
    ensures x >= 0 || result > 0
{
    -x
}

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn neg_i64(x: i64) -> i64
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::neg_i64`
//[adv_off]~^^ NOTE native verifier status: Failed
    ensures x >= 0 || result > 0
{
    -x
}

#[cfg(any(off_liars, on_liars, adv_off))]
pub fn neg_isize(x: isize) -> isize
//[off_liars]~^ ERROR Trust memory-safe verification failed for `neg_wraps_checks_off_postcondition::neg_isize`
//[adv_off]~^^ NOTE native verifier status: Failed
    ensures x >= 0 || result > 0
{
    -x
}

// The true twins: the claims Rust's wrapping negation makes true, MIN included.
// `x < -2147483647` is `x == i32::MIN` (`x < -127` is `x == i8::MIN`); the contract
// lowering refuses `-2147483648` and `i32::MIN` as unpreserved arithmetic, which
// would make these rows UNKNOWN for a reason that has nothing to do with `Neg`.
#[cfg(off_holds)]
pub fn neg_min_is_min(x: i32) -> i32
    ensures x >= -2147483647 || result == x
{
    -x
}

#[cfg(off_holds)]
pub fn abs_like_true(x: i32) -> i32
    ensures x < -2147483647 || result >= 0
{
    if x < 0 { -x } else { x }
}

#[cfg(off_holds)]
pub fn neg_i8_wraps(x: i8) -> i8
    ensures x >= -127 || result == x
{
    -x
}

#[cfg(off_holds)]
pub fn neg_post_true(x: i32) -> i32
    ensures x >= 0 || x < -2147483647 || result > 0
{
    -x
}

// A bounds row under a branch that is dead only if `-x` cannot wrap.
#[cfg(off_idx)]
pub fn idx(x: i32) -> u8 {
//[off_idx]~^ WARN Trust Level 0 safety verification incomplete for `neg_wraps_checks_off_postcondition::idx`: 2 obligation(s) were not proved
    let a = [1u8; 8];
    if x < 0 {
        let n = -x;
        if n > 0 { 0 } else { a[n as usize] }
    } else {
        0
    }
}
