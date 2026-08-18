//@ needs-trust-verify
//@ revisions: pass loop_i128_negative loop_u128_stall loop_isize_negative loop_usize_stall recursion_i128_negative recursion_u128_stall recursion_isize_negative recursion_usize_stall
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --test -Awarnings
//@[pass] run-pass
//@[loop_i128_negative] run-crash
//@[loop_i128_negative] error-pattern: kernel-certified Trust monitor failed
//@[loop_u128_stall] run-crash
//@[loop_u128_stall] error-pattern: kernel-certified Trust monitor failed
//@[loop_isize_negative] run-crash
//@[loop_isize_negative] error-pattern: kernel-certified Trust monitor failed
//@[loop_usize_stall] run-crash
//@[loop_usize_stall] error-pattern: kernel-certified Trust monitor failed
//@[recursion_i128_negative] run-crash
//@[recursion_i128_negative] error-pattern: kernel-certified Trust monitor failed
//@[recursion_u128_stall] run-crash
//@[recursion_u128_stall] error-pattern: kernel-certified Trust monitor failed
//@[recursion_isize_negative] run-crash
//@[recursion_isize_negative] error-pattern: kernel-certified Trust monitor failed
//@[recursion_usize_stall] run-crash
//@[recursion_usize_stall] error-pattern: kernel-certified Trust monitor failed
//@ dont-check-compiler-stderr

//! E5 monitor execution retains the exact signedness, width, and target pointer
//! carrier for both loop backedges and direct-self recursion edges. The signed
//! controls decrease but start below zero, while the unsigned controls remain
//! nonnegative but do not decrease. Each must fail for its own E5 condition;
//! no narrower carrier or Boolean postcondition monitor can supply the result.

fn loop_i128(mut measure: i128, mut again: bool) -> i128 {
    while again decreases measure {
        measure -= 1;
        again = false;
    }
    measure
}

fn loop_u128(mut measure: u128, mut again: bool) -> u128 {
    while again decreases measure {
        #[cfg(loop_u128_stall)]
        {
            measure = measure;
        }
        #[cfg(not(loop_u128_stall))]
        {
            measure -= 1;
        }
        again = false;
    }
    measure
}

fn loop_isize(mut measure: isize, mut again: bool) -> isize {
    while again decreases measure {
        measure -= 1;
        again = false;
    }
    measure
}

fn loop_usize(mut measure: usize, mut again: bool) -> usize {
    while again decreases measure {
        #[cfg(loop_usize_stall)]
        {
            measure = measure;
        }
        #[cfg(not(loop_usize_stall))]
        {
            measure -= 1;
        }
        again = false;
    }
    measure
}

#[inline(never)]
fn recurse_i128(measure: i128, again: bool) -> i128
    decreases measure
{
    if !again {
        return measure;
    }
    recurse_i128(measure - 1, false)
}

#[inline(never)]
fn recurse_u128(measure: u128, again: bool) -> u128
    decreases measure
{
    if !again {
        return measure;
    }
    #[cfg(recursion_u128_stall)]
    return recurse_u128(measure, false);
    #[cfg(not(recursion_u128_stall))]
    recurse_u128(measure - 1, false)
}

#[inline(never)]
fn recurse_isize(measure: isize, again: bool) -> isize
    decreases measure
{
    if !again {
        return measure;
    }
    recurse_isize(measure - 1, false)
}

#[inline(never)]
fn recurse_usize(measure: usize, again: bool) -> usize
    decreases measure
{
    if !again {
        return measure;
    }
    #[cfg(recursion_usize_stall)]
    return recurse_usize(measure, false);
    #[cfg(not(recursion_usize_stall))]
    recurse_usize(measure - 1, false)
}

#[test]
fn exact_extended_e5_carriers_execute_on_loops_and_recursion() {
    let loop_signed_start = if cfg!(loop_i128_negative) { -1 } else { 2 };
    let loop_pointer_signed_start = if cfg!(loop_isize_negative) { -1 } else { 2 };
    let recursion_signed_start = if cfg!(recursion_i128_negative) { -1 } else { 2 };
    let recursion_pointer_signed_start = if cfg!(recursion_isize_negative) { -1 } else { 2 };

    assert_eq!(loop_i128(loop_signed_start, true), loop_signed_start - 1);
    assert_eq!(loop_u128(2, true), if cfg!(loop_u128_stall) { 2 } else { 1 });
    assert_eq!(loop_isize(loop_pointer_signed_start, true), loop_pointer_signed_start - 1);
    assert_eq!(loop_usize(2, true), if cfg!(loop_usize_stall) { 2 } else { 1 });

    assert_eq!(recurse_i128(recursion_signed_start, true), recursion_signed_start - 1);
    assert_eq!(
        recurse_u128(2, true),
        if cfg!(recursion_u128_stall) { 2 } else { 1 },
    );
    assert_eq!(
        recurse_isize(recursion_pointer_signed_start, true),
        recursion_pointer_signed_start - 1,
    );
    assert_eq!(
        recurse_usize(2, true),
        if cfg!(recursion_usize_stall) { 2 } else { 1 },
    );
}
