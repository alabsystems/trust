//@ needs-trust-verify
//@ only-64bit
//@ edition: 2021
//@ revisions: plain_index nonneg_repr_index neg_repr_index neg_repr_div
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[plain_index] check-pass
//@[nonneg_repr_index] check-pass
//@[neg_repr_index] check-fail
//@[neg_repr_div] check-fail
//! **A discriminant read can be negative (Trust, 2026-09-28).**
//!
//! vcgen's interval analysis gave every `Rvalue::Discriminant` the interval
//! `[0, i128::MAX]`, and it did so from the initial commit. It then conjoins its
//! intervals onto every VC it cannot discharge (`augment_vc_with_abstract_state`). For
//! `#[repr(i8)] enum E { A = -1, B = 2 }` the false `e >= 0` fact excluded the one
//! witness that matters. Two shapes were PROVED under `certify`:
//! * `t[e as usize]` over `[u32; 300]` (`tests/trust-falsification/mutant/
//!   repr_i8_neg_tag_index.rs`). It was refuted in the 2026-09-12 falsification run,
//!   and proved by 2026-09-19 once the sign-extending cast was related to its
//!   source exactly. The Clean kernel certified it, on the formula it was given;
//! * `100 / (e as i32 + 1)`: all five rows proved on the 2026-09-19 compiler, and a
//!   binary calling `f(E::A)` exits 101 with "attempt to divide by zero".
//!
//! A discriminant read now gets the hull of the enum's DECLARED discriminants, read at
//! the destination's type (`discriminant_interval`). An ordinary enum keeps
//! `[0, n - 1]`, which still proves an in-bounds index.
//!
//! * `plain_index`, `nonneg_repr_index`: POSITIVE.
//! * `neg_repr_index`, `neg_repr_div`: the two false proofs, now refuted. Each is
//!   annotated on `f`.

#[cfg(plain_index)]
pub enum E {
    A,
    B,
    C,
}

#[cfg(plain_index)]
pub fn f(e: E, t: &[u32; 3]) -> u32 {
    t[e as usize]
}

#[cfg(nonneg_repr_index)]
#[repr(i8)]
pub enum E {
    A = 0,
    B = 2,
}

#[cfg(nonneg_repr_index)]
pub fn f(e: E, t: &[u32; 3]) -> u32 {
    t[e as usize]
}

#[cfg(any(neg_repr_index, neg_repr_div))]
#[repr(i8)]
pub enum E {
    A = -1,
    B = 2,
}

#[cfg(neg_repr_index)]
pub fn f(e: E, t: &[u32; 300]) -> u32 {
    //[neg_repr_index]~^ ERROR Trust Level 0 safety verification incomplete for `negative_discriminant_interval::f`
    t[e as usize]
}

#[cfg(neg_repr_div)]
pub fn f(e: E) -> i32 {
    //[neg_repr_div]~^ ERROR Trust Level 0 safety verification incomplete for `negative_discriminant_interval::f`
    100 / (e as i32 + 1)
}
