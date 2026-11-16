//@ revisions: ens idx shift
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[ens] run-pass
//@[idx] run-fail
//@[shift] run-fail
//@[idx] error-pattern: index out of bounds: the len is 2 but the index is 18446744073709551560
//@[shift] error-pattern: attempt to shift right with overflow
//@ ignore-emscripten no processes
//! The runtime WITNESS for `enum_disc_cast_same_width_signed_is_not_identity.rs`
//! (CAST-ENUMDISC-SIGNED-1): the same `F`, `m_f`, `idx` and `shift`, built with
//! verification OFF. `F::A as i8` is `-56`, so `m_f` returns a value its
//! `ensures result >= 0` excludes (`ens`), `idx` indexes `-56 as usize` into a
//! `[u32; 2]` (`idx`), and `shift` shifts a `u32` by `-56 as u32` (`shift`). Before
//! the fix all three functions were kernel-certified under `-Ztrust-policy=certify`
//! on `scratchpad/stage1-w15r` (the `liars` revision of the sibling built exit 0).
//!
//! MEASURED 2026-10-05 on `scratchpad/stage1-w15r` with these flags: `ens` exits 0
//! (the assertion below holds), `idx` panics with the pattern above and `shift` panics
//! with `attempt to shift right with overflow`, both exit 101. The binary does not
//! depend on the verifier, so the fix does not change it; the file pins the fact the
//! sibling's annotations rest on.

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum F {
    A = 200,
    B = 1,
}

#[inline(never)]
pub fn m_f(e: F) -> i8
    ensures result >= 0
{
    e as i8
}

#[inline(never)]
pub fn idx(e: F, arr: &[u32; 2]) -> u32 {
    arr[(e as i8) as usize]
}

#[inline(never)]
pub fn shift(e: F, x: u32) -> u32 {
    x >> ((e as i8) as u32)
}

fn main() {
    let e = std::hint::black_box(F::A);
    // Every revision names every function (and both variants), so none warns unused.
    assert_eq!(m_f(std::hint::black_box(F::B)), 1);
    if cfg!(ens) {
        assert_eq!(m_f(e), -56);
    } else if cfg!(idx) {
        println!("{}", idx(e, &[10, 20]));
    } else {
        println!("{}", shift(e, 1));
    }
}
