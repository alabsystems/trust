//@ revisions: liars holds pin
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type=lib
//@[liars] check-fail
//@[holds] check-pass
//@[pin] check-fail
//@ dont-check-compiler-stderr
//! A cast from an enum's discriminant to a SIGNED type of the SAME width is not the
//! identity when a tag sets the sign bit (CAST-ENUMDISC-SIGNED-1).
//!
//! `trust_vcgen::guards::cast_definition_formula`'s enum-disc-index arm emitted
//! `dest == disc` whenever the destination was at least as wide as the repr and every
//! tag was non-negative. It never read the destination's SIGNEDNESS, so
//! `#[repr(u8)] enum F { A = 200, B = 1 }` cast `as i8` got `_0 == _2` although
//! `F::A as i8 == -56`. Beside `_2 == 200`, value_facts' true tag image
//! `_0 == -56 || _0 == 1` and the `i8` range `_0 <= 127`, that equality is a
//! contradiction on the `F::A` path, so every claim about that path proved and the
//! Clean CIC kernel re-checked the proof (it derives `False` with `Int.lt_irrefl`).
//! The safety rows went the same way: `arr[(e as i8) as usize]` on `[u32; 2]` and
//! `x >> ((e as i8) as u32)` were kernel-certified, and both panic at runtime
//! (`enum_disc_cast_same_width_signed_is_not_identity_run.rs`).
//!
//! BEFORE (`scratchpad/stage1-w15r`, the stage 1 of main + wave 15, these flags with
//! `--emit=metadata`, measured 2026-10-05): `liars` built exit 0 with no error. Each
//! function reported every row proved, one of them kernel-certified ("2 proved ... of
//! which 1 kernel-certified" for the five contract functions, "1 proved ... 1
//! kernel-certified" for `idx` and `shift`), so none of the annotations below fired.
//! `holds` built exit 0, every row proved. `pin` failed exactly as annotated
//! (`c_i16_false`, a wider destination, was never an identity hazard).
//!
//! AFTER (predicted before the build; it held, MEASURED 2026-10-06 on the stage 1 of `9e11546767`): the arm emits the identity only when every tag is
//! representable unchanged in the destination (`0 <= tag <= MAX(dest)`), so the
//! liars' casts get no definition and value_facts' tag image is the only fact about
//! the result. The annotations were derived on the same stage 1 from a
//! line-for-line twin of `liars` in which each enum's repr is one step WIDER (`u16`
//! for `F` and `K`, `u32` for `G16`, `u64` for `G32`, `u128` for `GU`, same tags):
//! the cast then narrows, the arm's width gate skips it, and the VC holds exactly
//! the facts the fix leaves. The twin reported exactly these diagnostics: the
//! multi-variant `m_f` and `g32` and the safety-only `idx` and `shift` give a
//! "Level 0 safety verification incomplete" and a "strict verification failed"
//! error (the contract functions through the return-slot tripwire, `SpecUnverifiable`,
//! because the tag image is a disjunction and does not pin `_0`); the single-variant
//! `k_single`, `g16_bad` and `gu` give only the "strict verification failed" error,
//! with both rows FAILED (their image is one equality, which pins `_0` to the value
//! Rust computes and refutes the clause).
//!
//! `holds` is the control set: a wider signed destination (`as i16`, `as i32`), the
//! repr type itself, `as usize`, a tag set below `2^(w-1)` (`Small { 100, 1 } as
//! i8`) and a non-negative signed repr cast to unsigned (`S8 as u8`) keep the
//! identity and prove before and after. The unit rows
//! `enum_disc_same_width_signed_cast_of_a_high_tag_is_not_identity` and
//! `enum_disc_cast_that_preserves_every_tag_keeps_the_identity` in
//! `crates/trust-vcgen/src/guards.rs` pin the same split on the arm itself.

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum F {
    A = 200,
    B = 1,
}

#[repr(u8)]
pub enum K {
    A = 255,
}

#[repr(u16)]
pub enum G16 {
    A = 40000,
}

#[repr(u32)]
pub enum G32 {
    A = 0x8000_0000,
    B = 7,
}

#[repr(usize)]
pub enum GU {
    A = usize::MAX,
}

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum Small {
    A = 100,
    B = 1,
}

#[repr(i8)]
#[derive(Clone, Copy)]
pub enum S8 {
    A = 100,
    B = 1,
}

// `F::A as i8 == -56`.
#[cfg(liars)]
pub fn m_f(e: F) -> i8
//[liars]~^ ERROR Trust Level 0 safety verification incomplete for `enum_disc_cast_same_width_signed_is_not_identity::m_f`
//[liars]~| ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::m_f`
    ensures result >= 0
{
    e as i8
}

// `F::A` indexes `-56 as usize`, far past the end.
#[cfg(liars)]
pub fn idx(e: F, arr: &[u32; 2]) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `enum_disc_cast_same_width_signed_is_not_identity::idx`
    //[liars]~| ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::idx`
    arr[(e as i8) as usize]
}

// `F::A` shifts by `-56 as u32`.
#[cfg(liars)]
pub fn shift(e: F, x: u32) -> u32 {
    //[liars]~^ ERROR Trust Level 0 safety verification incomplete for `enum_disc_cast_same_width_signed_is_not_identity::shift`
    //[liars]~| ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::shift`
    x >> ((e as i8) as u32)
}

// A single-variant enum: before the fix the whole VC was contradictory. `K::A as i8 == -1`.
#[cfg(liars)]
pub fn k_single(e: K) -> i8
//[liars]~^ ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::k_single`
    ensures result == 0
{
    e as i8
}

// `40000 as i16 == -25536`.
#[cfg(liars)]
pub fn g16_bad(e: G16) -> i16
//[liars]~^ ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::g16_bad`
    ensures result == 40
{
    e as i16
}

// `0x8000_0000 as i32 == i32::MIN`.
#[cfg(liars)]
pub fn g32(e: G32) -> i32
//[liars]~^ ERROR Trust Level 0 safety verification incomplete for `enum_disc_cast_same_width_signed_is_not_identity::g32`
//[liars]~| ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::g32`
    ensures result > 0
{
    e as i32
}

// `usize::MAX as isize == -1`.
#[cfg(liars)]
pub fn gu(e: GU) -> isize
//[liars]~^ ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::gu`
    ensures result == 5
{
    e as isize
}

#[cfg(holds)]
pub fn c_i16_ge0(e: F) -> i16
    ensures result >= 0
{
    e as i16
}

#[cfg(holds)]
pub fn c_u8_ok(e: F) -> u8
    ensures result == 200 || result == 1
{
    e as u8
}

#[cfg(holds)]
pub fn c_usize_idx(e: F, arr: &[u32; 201]) -> u32 {
    arr[e as usize]
}

#[cfg(holds)]
pub fn c_small_i8(e: Small) -> i8
    ensures result >= 0
{
    e as i8
}

#[cfg(holds)]
pub fn c_s8_u8(e: S8) -> u8
    ensures result <= 100
{
    e as u8
}

#[cfg(holds)]
pub fn g16_ok(e: G16) -> i32
    ensures result == 40000
{
    e as i32
}

// A wider signed destination keeps the identity, so this false claim stays refused
// before and after.
#[cfg(pin)]
pub fn c_i16_false(e: F) -> i16
//[pin]~^ ERROR Trust strict verification failed for `enum_disc_cast_same_width_signed_is_not_identity::c_i16_false`
    ensures result == 1
{
    e as i16
}
