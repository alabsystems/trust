//@ revisions: liars liars_opt holds pin
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type=lib -Coverflow-checks=on
//@[liars_opt] compile-flags: -O
//@[liars] check-fail
//@[liars_opt] check-fail
//@[holds] check-pass
//@[pin] check-fail
//@ dont-check-compiler-stderr
//! The signed-reduction accumulator lane must read the cast TARGET
//! (CAST-SIGNED-REDUCTION-TARGET-1).
//!
//! `loop_bounds::signed_addend_per_iteration_range` recognized `t += x as ACC` over
//! a for-each of a fixed `[iN; LEN]` and returned the ELEMENT's range
//! `[MIN(iN), MAX(iN)]` as the ADDEND's range, without looking at `ACC`.
//! `build_accumulator_bound_facts` then conjoined `MIN <= addend <= MAX`,
//! `init + K*MIN <= acc <= init + K*MAX` and the same pair for `acc + addend` onto
//! every VC. For an UNSIGNED `ACC` a negative element is a huge addend
//! (`-1i8 as u32 == 4294967295`), so those facts are false and they discharged the
//! real overflow: the VC of `sum_u32` carried `(<= _9 127)` and `(<= (+ t _9) 508)`
//! for `_9 = *x as u32`, and the Clean CIC kernel re-checked the row. The facts are
//! global, so `idx`'s bounds row was certified on them too.
//! `signed_reduction_unsigned_cast_target_not_proved_run.rs` is the runtime witness.
//!
//! BEFORE (`scratchpad/stage1-w15r`, the stage 1 of main + wave 15, these flags with
//! `--emit=metadata`, measured 2026-10-05): `liars` and `liars_opt` built exit 0 with
//! no error; every function reported all rows proved and kernel-certified ("2 proved
//! ... of which 2 kernel-certified", "3 ... 3" for `idx`), so none of the annotations
//! below fired. `holds` built exit 0, all rows kernel-certified. `pin` failed exactly
//! as annotated: those shapes never reached the lane (`for &x in a.iter()`, the
//! two-cast `*x as u8 as u16`) or exceeded its self-limit (`k3_u8`, `3 * 127 > 255`).
//!
//! AFTER (predicted before the build; it held, MEASURED 2026-10-06 on the stage 1 of `9e11546767`): the lane answers only when `ACC` is a signed type
//! that holds every element value (`is_modeled_identity_cast(iN, ACC)`), so each
//! liar gets no accumulator fact and the unsigned lane declines the signed element
//! as well. The annotations were derived on the same stage 1 from a line-for-line
//! twin of `liars` in which each `*x as T` reads `(*x as iW) as T` (`W` wider than
//! the element), a cast chain the lane does not recognize: at `-O0` and at `-O` the
//! twin reported exactly these diagnostics, the overflow row (and `idx`'s bounds row)
//! FAILED and every other row proved. `holds` keeps the lane (`i8 -> i32`,
//! `i16 -> i64`, the shapes of `tests/trust-falsification/proved/signed_accumulator.rs`)
//! and proves before and after; `pin` is unchanged.

#[cfg(any(liars, liars_opt))]
pub fn sum_u32(a: &[i8; 4]) -> u32 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::sum_u32`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::sum_u32`
    let mut t: u32 = 0;
    for x in a {
        t += *x as u32;
    }
    t
}

#[cfg(any(liars, liars_opt))]
pub fn sum_u16(a: &[i8; 300]) -> u16 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::sum_u16`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::sum_u16`
    let mut t: u16 = 0;
    for x in a {
        t += *x as u16;
    }
    t
}

// `2 * 127 <= u8::MAX` let the lane certify it; `[-1, -1]` adds 255 + 255.
#[cfg(any(liars, liars_opt))]
pub fn k2_u8(a: &[i8; 2]) -> u8 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::k2_u8`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::k2_u8`
    let mut t: u8 = 0;
    for x in a {
        t += *x as u8;
    }
    t
}

// The same-width reinterpret `i16 as u16`.
#[cfg(any(liars, liars_opt))]
pub fn k2_u16(a: &[i16; 2]) -> u16 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::k2_u16`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::k2_u16`
    let mut t: u16 = 0;
    for x in a {
        t += *x as u16;
    }
    t
}

// A WIDENING signed -> unsigned cast wraps too: `-1i32 as u64 == u64::MAX`.
#[cfg(any(liars, liars_opt))]
pub fn k4_u64(a: &[i32; 4]) -> u64 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::k4_u64`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::k4_u64`
    let mut t: u64 = 0;
    for x in a {
        t += *x as u64;
    }
    t
}

// The false facts are global: `t <= 508` also certified this bounds row, and
// `[-1, 0, 0, 0]` indexes 4294967295 without any overflow.
#[cfg(any(liars, liars_opt))]
pub fn idx(a: &[i8; 4], arr: &[u8; 509]) -> u8 {
    //[liars,liars_opt]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::idx`
    //[liars,liars_opt]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::idx`
    let mut t: u32 = 0;
    for x in a {
        t += *x as u32;
    }
    arr[t as usize]
}

#[cfg(holds)]
pub fn sum_i32(a: &[i8; 4]) -> i32 {
    let mut t: i32 = 0;
    for x in a {
        t += *x as i32;
    }
    t
}

#[cfg(holds)]
pub fn sum_i8(a: &[i8; 8]) -> i32 {
    let mut s: i32 = 0;
    for &x in a {
        s += x as i32;
    }
    s
}

#[cfg(holds)]
pub fn sum_i16(a: &[i16; 32]) -> i64 {
    let mut s: i64 = 0;
    for &x in a {
        s += x as i64;
    }
    s
}

#[cfg(pin)]
pub fn sum_u32_pat(a: &[i8; 4]) -> u32 {
    //[pin]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::sum_u32_pat`
    //[pin]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::sum_u32_pat`
    let mut t: u32 = 0;
    for &x in a.iter() {
        t += x as u32;
    }
    t
}

#[cfg(pin)]
pub fn sum_u16_2c(a: &[i8; 300]) -> u16 {
    //[pin]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::sum_u16_2c`
    //[pin]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::sum_u16_2c`
    let mut t: u16 = 0;
    for x in a {
        t += *x as u8 as u16;
    }
    t
}

#[cfg(pin)]
pub fn k3_u8(a: &[i8; 3]) -> u8 {
    //[pin]~^ ERROR Trust Level 0 safety verification incomplete for `signed_reduction_unsigned_cast_target_not_proved::k3_u8`
    //[pin]~| ERROR Trust strict verification failed for `signed_reduction_unsigned_cast_target_not_proved::k3_u8`
    let mut t: u8 = 0;
    for x in a {
        t += *x as u8;
    }
    t
}
