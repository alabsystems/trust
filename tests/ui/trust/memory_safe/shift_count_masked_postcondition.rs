//@ revisions: off_liars off_holds on_liars off_strict_lower
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=memory-safe --crate-type=lib
//@[off_liars] compile-flags: -Coverflow-checks=off
//@[off_holds] compile-flags: -Coverflow-checks=off
//@[on_liars] compile-flags: -Coverflow-checks=on
//@[off_strict_lower] compile-flags: -Coverflow-checks=off -Ztrust-ir-lower=strict
//@[off_liars] check-fail
//@[off_holds] check-pass
//@[on_liars] check-pass
//@[off_strict_lower] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A plain MIR `Shl`/`Shr` shifts by `count.rem_euclid(BITS)` (rustc_middle
//! `mir::BinOp::Shl`); with `-C overflow-checks` off there is no `Assert` in front
//! of it, so an out-of-range count is not a panic and not UB — the binary computes
//! `1u32 << 33 == 2`. The MIR-derived spine modelled the count UNMASKED: the
//! trust-ir-bridge producer emitted a bare trust-ir shift (undefined at or above
//! BITS) that trust-mc encodes as a total `bvshl` (`== 0`), and
//! `trust_vcgen::chc::try_binop_to_formula` defined the body the same way
//! (docs/KNOWN_HAZARDS.md, "shift count").
//!
//! BEFORE (stage 1 of 782780ea0 plus the wave-7 fix, measured 2026-10-03 with
//! exactly these revisions' flags): `off_liars` built exit 0 — `konst`, `sym` and
//! `shr_sym` each had both postcondition rows PROVED (trust-full-verifier/trust-mc
//! and trust-exact-source-clause-discharge) although every one is false of the
//! binary. `off_holds` was refused: `konst_true`, `sym_true` and `shr_true` state
//! the value Rust computes and were REFUTED. `on_liars` built exit 0 (the overflow
//! `Assert` dominates every shift, so the liars' postconditions hold vacuously).
//!
//! AFTER (MEASURED 2026-10-03 on the stage 1 of `6011b74bad`): both producers apply
//! Rust's count mask, so `off_liars` is refused on the three refuted
//! postconditions, `off_holds` compiles with the true claims proved, and
//! `on_liars` is unchanged — under the `Assert` the mask is the identity.
//! `in_range` and `explicit_mask` are the controls that compile before and after.
//!
//! `off_strict_lower` pins the direct THIR producer to the same semantics: under
//! `-Ztrust-ir-lower=strict` a THIR-vs-MIR-oracle disagreement in the sampled
//! differential, or a re-derived MIR that differs from the built MIR, is a compile
//! error. Masking only the MIR-side oracle would make every symbolic-count body
//! below disagree (the oracle returns Rust's value where the THIR side traps); a
//! masked THIR unit that `to_mir` did not read back as the bare MIR shift would
//! make the re-derived MIR differ. BEFORE: exit 0 (both sides unmasked, so they
//! agreed — on traps). AFTER (measured on the stage 1 of `6011b74bad`): exit 0.
//!
//! Every revision still warns on each shift: the per-statement `amount < BITS`
//! row is refuted and memory-safe demotes it. With checks off that row is not a
//! runtime panic either (its memory-safe label is a recorded residual).

#[cfg(any(off_liars, on_liars))]
#[allow(arithmetic_overflow)]
pub fn konst(x: u8) -> u8
//[off_liars]~^ ERROR Trust memory-safe verification failed for `shift_count_masked_postcondition::konst`
    ensures result == 0
{
    x << 9u32
}

#[cfg(any(off_liars, on_liars))]
pub fn sym(x: u32, s: u32) -> u32
//[off_liars]~^ ERROR Trust memory-safe verification failed for `shift_count_masked_postcondition::sym`
    ensures s < 32 || result == 0
{
    x << s
}

#[cfg(any(off_liars, on_liars))]
pub fn shr_sym(x: u32, s: u32) -> u32
//[off_liars]~^ ERROR Trust memory-safe verification failed for `shift_count_masked_postcondition::shr_sym`
    ensures s < 32 || result == 0
{
    x >> s
}

// `9 & 7 == 1`: Rust's `1u8 << 9u32` is 2.
#[cfg(off_holds)]
#[allow(arithmetic_overflow)]
pub fn konst_true(x: u8) -> u8
    ensures x != 1 || result == 2
{
    x << 9u32
}

// `33 & 31 == 1`.
#[cfg(off_holds)]
pub fn sym_true(x: u32, s: u32) -> u32
    ensures x != 1 || s != 33 || result == 2
{
    x << s
}

#[cfg(off_holds)]
pub fn shr_true(x: u32, s: u32) -> u32
    ensures x != 4 || s != 33 || result == 2
{
    x >> s
}

// Controls: an in-range count, and a count the source masks itself.
#[cfg(off_holds)]
pub fn in_range(x: u32, s: u32) -> u32
    ensures x != 1 || s != 3 || result == 8
{
    x << s
}

#[cfg(off_holds)]
pub fn explicit_mask(x: u32, s: u32) -> u32
    ensures x != 1 || s != 33 || result == 2
{
    x << (s & 31)
}

// No contracts: the producers and the differentials only.
#[cfg(off_strict_lower)]
pub fn lower_shl(x: u32, s: u32) -> u32 {
    x << s
}

#[cfg(off_strict_lower)]
pub fn lower_shl_narrow(x: u8, s: u32) -> u8 {
    x << s
}

#[cfg(off_strict_lower)]
pub fn lower_ashr_signed_count(x: i32, s: i8) -> i32 {
    x >> s
}

#[cfg(off_strict_lower)]
pub fn lower_shr_usize(x: usize, s: u32) -> usize {
    x >> s
}

#[cfg(off_strict_lower)]
#[allow(arithmetic_overflow)]
pub fn lower_literal_out_of_range(x: u32) -> u32 {
    x << 33u32
}

#[cfg(off_strict_lower)]
pub fn lower_literal(x: u32) -> u32 {
    x << 3
}

#[cfg(off_strict_lower)]
pub fn lower_shl_assign(mut x: u64, s: u8) -> u64 {
    x <<= s;
    x
}

#[cfg(off_strict_lower)]
pub fn lower_source_mask(x: u32, s: u32) -> u32 {
    x << (s & 31)
}
