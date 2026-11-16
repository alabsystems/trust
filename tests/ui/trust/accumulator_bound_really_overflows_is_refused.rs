//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The refusing twin of `accumulator_bound_through_slices_and_adapters.rs`: the
//! same shapes where the sum REALLY overflows, each on an input it names. The
//! accumulator lane's bound `init + K * MAX(ELEM)` is self-limiting — a sum that
//! can exceed the accumulator's type leaves a bound above its MAX, which proves
//! nothing — so every one of these must stay refused. A green here is a false
//! proof.

// 300 bytes of 255 sum to 76500 > u16::MAX.
pub fn too_many(a: &[u8; 300]) -> u16 { //~ ERROR failed for `accumulator_bound_really_overflows_is_refused::too_many`
    let mut s = 0u16;
    for &b in a.iter() {
        s += b as u16;
    }
    s
}

// `take(300)` over 300 bytes of 255: the same 76500.
pub fn take_too_many(v: &[u8]) -> u16 { //~ ERROR failed for `accumulator_bound_really_overflows_is_refused::take_too_many`
    let mut s = 0u16;
    for &b in v.iter().take(300) {
        s += b as u16;
    }
    s
}

// 200 + 200 bytes of 255 sum to 102000 > u16::MAX.
pub fn chain_too_long(a: &[u8; 200], b: &[u8; 200]) -> u16 { //~ ERROR failed for `accumulator_bound_really_overflows_is_refused::chain_too_long`
    let mut s = 0u16;
    for &x in a.iter().chain(b.iter()) {
        s += x as u16;
    }
    s
}

// 16 bytes of 255, each shifted by 5, sum to 130560 > u16::MAX.
pub fn scaled_too_far(a: &[u8; 16]) -> u16 { //~ ERROR failed for `accumulator_bound_really_overflows_is_refused::scaled_too_far`
    let mut t = 0u16;
    for &x in a.iter() {
        t += (x as u16) << 5;
    }
    t
}

// Four 127s overflow an `i8` sum; the element is not widened, so no bound applies.
pub fn signed_narrow(a: &[i8; 4]) -> i8 { //~ ERROR failed for `accumulator_bound_really_overflows_is_refused::signed_narrow`
    let mut s = 0i8;
    for &b in a.iter() {
        s += b;
    }
    s
}
