//@ needs-trust-verify
//@ edition: 2021
//@ revisions: rebuilt skips_next none_arm empty_sibling add_before_test counter_bypass
//@ revisions: shared_next_count signed_to_unsigned user_min
//@ revisions: behind_some empty_sibling_ok add_before_test_ok nested
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[rebuilt] check-fail
//@[skips_next] check-fail
//@[none_arm] check-fail
//@[empty_sibling] check-fail
//@[add_before_test] check-fail
//@[counter_bypass] check-fail
//@[shared_next_count] check-fail
//@[signed_to_unsigned] check-fail
//@[user_min] check-fail
//@[behind_some] check-pass
//@[empty_sibling_ok] check-pass
//@[add_before_test_ok] check-pass
//@[nested] check-pass
//! **A loop's trip count bounds only the blocks behind its driver (Trust, 2026-09-29).**
//!
//! The accumulator lane mints `acc <= init + K * per_max`, and `K` must bound how
//! many times the self-add runs. It used to be the product of the trip counts of
//! every loop in the function. Each check-fail revision below overflowed at runtime
//! (`c: u8` unless noted) and was PROVED on the default lane and, kernel-certified,
//! under `certify` (the trip-count lane audit, 2026-09-29). `K` is now per block
//! (`trust_types::loop_nest`): a product over the loops CONTAINING the add, each
//! bounded by a driver edge every iteration crosses, with one more iteration where
//! the add is not behind that edge.
//!
//! * `rebuilt`: the range is built inside its own loop, so every iteration yields.
//! * `skips_next`: a `continue` cycle never calls `next`.
//! * `none_arm`: the add is on the `None` arm, which repeats forever.
//! * `empty_sibling`: an empty sibling loop made the product 0.
//! * `add_before_test`: the add runs before the counter test, 11 times for 10
//!   continuing iterations, and `a[c]` indexes one past an 11-element array.
//! * `counter_bypass`: a `continue` cycle passes neither the counter test nor its
//!   advance.
//! * `shared_next_count`: two `next` calls in one loop balanced a counter loop with
//!   a variable limit, so the product `3 * 3` bounded it.
//! * `signed_to_unsigned`: `x as u64` of a negative `i8` is huge, but the signed
//!   reduction lane bounded the addend by `[-128, 127]`.
//! * `user_min`: a user `fn min` ended in `::min` and bounded a range end.
//! * `behind_some` … `nested`: the correct twins, which must keep proving.

#[cfg(rebuilt)]
pub fn rebuilt() -> u8 {
    //[rebuilt]~^ ERROR Trust
    let mut c = 0u8;
    loop {
        let mut r = 0..10u32;
        match r.next() {
            Some(_) => c += 1,
            None => break,
        }
    }
    c
}

#[cfg(skips_next)]
pub fn skips_next(flag: bool) -> u8 {
    //[skips_next]~^ ERROR Trust
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        if flag {
            c += 1;
            continue;
        }
        match r.next() {
            Some(_) => {}
            None => break,
        }
    }
    c
}

#[cfg(none_arm)]
pub fn none_arm() -> u8 {
    //[none_arm]~^ ERROR Trust
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        match r.next() {
            Some(_) => {}
            None => c += 1,
        }
    }
}

#[cfg(empty_sibling)]
pub fn empty_sibling() -> u8 {
    //[empty_sibling]~^ ERROR Trust
    let mut c = 0u8;
    for _ in 0..0u32 {}
    for _ in 0..300u32 {
        c += 1;
    }
    c
}

#[cfg(add_before_test)]
pub fn add_before_test() -> u8 {
    //[add_before_test]~^ ERROR Trust
    let a = [7u8; 11];
    let mut c = 0usize;
    let mut i = 0u32;
    loop {
        c += 1;
        if i >= 10 {
            break;
        }
        i += 1;
    }
    a[c]
}

#[cfg(counter_bypass)]
pub fn counter_bypass(flag: bool) -> u8 {
    //[counter_bypass]~^ ERROR Trust
    let mut c = 0u8;
    let mut i = 0u32;
    loop {
        if flag {
            c += 1;
            continue;
        }
        if i >= 10 {
            break;
        }
        i += 1;
    }
    c
}

#[cfg(shared_next_count)]
pub fn shared_next_count(n: u32) -> u8 {
    //[shared_next_count]~^ ERROR Trust
    let mut a = 0..3u32;
    let mut b = 0..3u32;
    loop {
        if a.next().is_none() {
            break;
        }
        if b.next().is_none() {
            break;
        }
    }
    let mut c = 0u8;
    let mut i = 0u32;
    while i < n {
        c += 1;
        i += 1;
    }
    c
}

#[cfg(signed_to_unsigned)]
pub fn signed_to_unsigned(a: &[i8; 16]) -> u64 {
    //[signed_to_unsigned]~^ ERROR Trust
    let mut t = 0u64;
    for &x in a {
        t += x as u64;
    }
    t
}

#[cfg(user_min)]
pub mod lim {
    pub fn min(a: u32, _cap: u32) -> u32 {
        a
    }
}

#[cfg(user_min)]
pub fn user_min(n: u32) -> u8 {
    //[user_min]~^ ERROR Trust
    let mut c = 0u8;
    for _ in 0..lim::min(n, 10) {
        c += 1;
    }
    c
}

#[cfg(behind_some)]
pub fn behind_some() -> u8 {
    let mut c = 0u8;
    let mut r = 0..10u32;
    loop {
        match r.next() {
            Some(_) => c += 1,
            None => break,
        }
    }
    c
}

#[cfg(empty_sibling_ok)]
pub fn empty_sibling_ok() -> u8 {
    let mut c = 0u8;
    for _ in 0..0u32 {}
    for _ in 0..200u32 {
        c += 1;
    }
    c
}

#[cfg(add_before_test_ok)]
pub fn add_before_test_ok() -> u8 {
    let a = [7u8; 12];
    let mut c = 0usize;
    let mut i = 0u32;
    loop {
        c += 1;
        if i >= 10 {
            break;
        }
        i += 1;
    }
    a[c]
}

#[cfg(nested)]
pub fn nested() -> u8 {
    let mut c = 0u8;
    for _ in 0..10u32 {
        for _ in 0..20u32 {
            c += 1;
        }
    }
    c
}
