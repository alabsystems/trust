//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! A trivial setter's post-call value, and a copy of its target, describe the target
//! only until the next write of it. Each panics on the input named beside it.
//!
//! MEASURED FALSE PROOFS, 2026-09-30 (an adversarial audit; the 2026-09-17 pack
//! proves all seven): the assert lane renamed every setter fact and copy link at the
//! assert's use point, so a copy taken BEFORE the call, an earlier call's value, and
//! a copy overwritten afterwards all took the latest value.
//! `setter_fact_holds_until_the_next_write.rs` is the twin.
//!
//! Not one is proved: `earlier_call_value` is refuted, and the others keep their
//! runtime check (a warning): the lane withholds the stale fact and has nothing
//! left to refute them with.

#[inline(never)]
pub fn set(p: &mut u32, v: u32) { *p = v; }
#[inline(never)]
pub fn set7(p: &mut u32) { *p = 7; }

// x = 0: copy taken before the setter call.
pub fn pre_call_copy(mut x: u32) { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::pre_call_copy`
    let old = x;
    set(&mut x, 5);
    assert!(old == 5);
}

// x = 3: two copies straddling the call compared with each other.
pub fn copies_straddle_call(mut x: u32) { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::copies_straddle_call`
    let before = x;
    set7(&mut x);
    let after = x;
    assert!(before == after);
}

// any x: the first call's value re-stamped onto the second call's token.
pub fn earlier_call_value(mut x: u32) { //~ ERROR failed for `setter_fact_is_live_only_until_the_next_write_refused::earlier_call_value`
    set(&mut x, 5);
    set(&mut x, 7);
    assert!(x == 5);
}

// any x: copy after the call, then a direct overwrite of the target.
pub fn copy_then_overwrite(mut x: u32) { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::copy_then_overwrite`
    set(&mut x, 5);
    let b = x;
    x = 9;
    assert!(b == 9);
    let _ = x;
}

// x = 0, y = 1: overwrite with a parameter.
pub fn copy_then_overwrite_param(mut x: u32, y: u32) { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::copy_then_overwrite_param`
    set(&mut x, 5);
    let b = x;
    x = y;
    assert!(b == x);
}

// x = 3: debug_assert! form (debug build).
pub fn debug_assert_form(mut x: u32) { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::debug_assert_form`
    let before = x;
    set7(&mut x);
    debug_assert!(before == 7);
}

// x = 9: the assert guards an index; both rows proved (the bounds row certified).
pub fn assert_then_index(mut x: u32, a: &[u8; 4]) -> u8 { //~ WARN safety verification incomplete for `setter_fact_is_live_only_until_the_next_write_refused::assert_then_index`
    let old = x;
    set(&mut x, 3);
    assert!(old < 4);
    a[old as usize]
}
