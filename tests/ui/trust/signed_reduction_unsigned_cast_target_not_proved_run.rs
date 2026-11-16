//@ revisions: sum idx
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@ run-fail
//@[sum] error-pattern: attempt to add with overflow
//@[idx] error-pattern: index out of bounds: the len is 509 but the index is 4294967295
//@ ignore-emscripten no processes
//! The runtime WITNESS for `signed_reduction_unsigned_cast_target_not_proved.rs`
//! (CAST-SIGNED-REDUCTION-TARGET-1): the same `sum_u32` and `idx`, built with
//! verification OFF. `-1i8 as u32` is `4294967295`, so `sum_u32([-1, -1, 0, 0])`
//! overflows on its second add (`sum`), and `idx([-1, 0, 0, 0])` indexes `4294967295`
//! into a `[u8; 509]` with no overflow at all (`idx`). Before the fix both rows were
//! kernel-certified under `-Ztrust-policy=certify` on `scratchpad/stage1-w15r` (the
//! sibling's `liars` revision built exit 0), and the same rows were certified at `-O`.
//!
//! MEASURED 2026-10-05 on `scratchpad/stage1-w15r` with these flags: both revisions
//! build exit 0 and the binary panics with its pattern, exit 101. The binary does not
//! depend on the verifier, so the fix does not change it; the file pins the fact the
//! sibling's annotations rest on.

#[inline(never)]
pub fn sum_u32(a: &[i8; 4]) -> u32 {
    let mut t: u32 = 0;
    for x in a {
        t += *x as u32;
    }
    t
}

#[inline(never)]
pub fn idx(a: &[i8; 4], arr: &[u8; 509]) -> u8 {
    let mut t: u32 = 0;
    for x in a {
        t += *x as u32;
    }
    arr[t as usize]
}

fn main() {
    let arr = [7u8; 509];
    // Both revisions name both functions, so neither warns unused.
    assert_eq!(sum_u32(&std::hint::black_box([1, 2, 3, 4])), 10);
    assert_eq!(idx(&std::hint::black_box([1, 2, 3, 4]), &arr), 7);
    if cfg!(sum) {
        println!("{}", sum_u32(&std::hint::black_box([-1, -1, 0, 0])));
    } else {
        println!("{}", idx(&std::hint::black_box([-1, 0, 0, 0]), &arr));
    }
}
