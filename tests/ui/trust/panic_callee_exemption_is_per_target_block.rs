//@ needs-trust-verify
//@ edition: 2021
//@ revisions: default certify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[default] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//! NEW-EXEMPT-SPLIT (docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-28 — the
//! panic-callee exemption counted candidates, not blocks"): the refute lane's
//! panic-callee exemption is decided PER TARGET BLOCK.
//!
//! `all_calls_discharge_panic_free` skips every `assert!`/`panic!` failure
//! block's panic call once the `-full` refute lane has proved every such block
//! unreachable. That was decided by a COUNT, `#proved candidates == #target
//! blocks`. The candidate generator emits one candidate per PATH of a block and
//! none at all for a block whose guard it cannot ground, so in `s` below the
//! two proved paths of the `x != 50` block balanced the loop-carried
//! `t != 7` block, which was never a candidate. On the unfixed compiler `s`'s
//! catch-all was published `proved` with a Clean CIC kernel certificate over
//! the first block's paths alone, `calls_s` was proved on `s`'s registration,
//! and `fn main() { s(7); }` built rc 0 under `-Ztrust-policy=certify` and
//! exited 101 (`assertion failed: t != 7`).
//!
//! Revisions:
//! * `default` — `s` and `calls_s` now report what `s_control` reports
//!   (runtime-checked: a warning under the default policy).
//! * `certify` — the same functions under `-Ztrust-policy=certify`: `s`,
//!   `calls_s` and `s_control` are REFUSED.
//!
//! In both revisions the positive controls verify. `two_path_block_proved`
//! (ONE target block reached by two paths, both proved) and `calls_two_path`:
//! the retired count refused the exemption there (2 against 1); the per-block
//! rule grants it and the kernel certifies the grounded catch-all.
//! `both_blocks_proved` (two target blocks, the second reached through the
//! first `if`'s diamond, so three proved candidates) and `two_single` (two
//! target blocks, one path each): the kernel does NOT certify either grounded
//! disjunction, and the native trust_mc proof verifies them. The refute lane
//! used to re-point such a catch-all at that disjunction anyway, retiring the
//! native proof for a certificate that never came — `two_single` was refused
//! on the unfixed compiler, and `both_blocks_proved` escaped only because the
//! retired count (3 against 2) kept the lane from firing. The lane now
//! re-points a natively proved catch-all only when the kernel certifies the
//! replacement, as the re-pointing lane (`ground_panic_freedom_catchall`)
//! already did.

/// Block A (`x != 50`) is reached by two paths, both infeasible; block B
/// (`t != 7`) reads a loop-carried value and gets no candidate. `s(7)` panics.
pub fn s(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    if x < 3 || x > 100 {
        assert!(x != 50);
    }
    let mut i = 0u32;
    let mut t = 0u32;
    while i != 3 {
        t ^= x;
        i = i.wrapping_add(1);
    }
    assert!(t != 7);
    x
}

/// Discharged, on the unfixed compiler, by `s`'s false registration.
pub fn calls_s(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    s(x)
}

/// CONTROL: block B alone, refused before and after.
pub fn s_control(x: u32) -> u32 {
    //[default]~^ WARN Trust Level 0 safety verification incomplete for
    //[default]~| WARN Trust verification advisory for
    //[certify]~^^^ ERROR Trust Level 0 safety verification incomplete for
    //[certify]~| ERROR Trust strict verification failed for
    let mut i = 0u32;
    let mut t = 0u32;
    while i != 3 {
        t ^= x;
        i = i.wrapping_add(1);
    }
    assert!(t != 7);
    x
}

/// POSITIVE CONTROL: one target block reached by two paths, both infeasible.
pub fn two_path_block_proved(x: u32) -> u32 {
    if x < 3 || x > 100 {
        assert!(x != 50);
    }
    x
}

pub fn calls_two_path(x: u32) -> u32 {
    two_path_block_proved(x)
}

/// POSITIVE CONTROL: two target blocks, both infeasible; the second is reached
/// by two paths.
pub fn both_blocks_proved(x: u32) -> u32 {
    if x < 3 {
        assert!(x != 50);
    }
    if x > 100 {
        assert!(x != 7);
    }
    x
}

/// POSITIVE CONTROL: two target blocks, one path each, both infeasible.
pub fn two_single(x: u32) -> u32 {
    if x < 3 {
        assert!(x != 50);
    } else if x > 100 {
        assert!(x != 7);
    }
    x
}
