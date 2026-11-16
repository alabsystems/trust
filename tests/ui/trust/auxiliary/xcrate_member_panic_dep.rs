//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! An ordinary dependency, compiled the way `targo` compiles every dependency
//! unit: `-Ztrust-verify=off`, so nothing in this file is verified, plus
//! `-Zalways-encode-mir` so a caller that declares this crate in its bundling
//! scope (`-Ztrust-bundle-foreign-crate=xcpanic_dep`) can bundle these bodies.
//!
//! Every function except `quiet` has a site that DIVERGES, reachable on the
//! input `7`. `quiet` is the same shape with the panic replaced by a return,
//! so it is the positive control: the fix must not decline it.
//!
//! Non-generic on purpose. The declared bundling arm admits only callees with
//! empty generic arguments, so a generic witness would be absent for an
//! unrelated reason.
#![crate_name = "xcpanic_dep"]

/// The measured witness (stage-1 `a8c853de6f`): `h(black_box(7))` from a
/// declared-scope verifying caller built rc=0 and the binary exited 101.
pub fn h(x: u32) -> u32 {
    if x == 7 {
        panic!("boom")
    }
    x
}

/// One frame deeper, also measured rc=0 / exit 101. `g` has no diverging site
/// of its own; its callee `h` does.
pub fn g(x: u32) -> u32 {
    h(x)
}

pub fn unreach(x: u32) -> u32 {
    if x == 7 {
        unreachable!()
    }
    x
}

pub fn todo_at(x: u32) -> u32 {
    if x == 7 {
        todo!()
    }
    x
}

pub fn asserts(x: u32) -> u32 {
    assert!(x != 7);
    x
}

fn fail() -> ! {
    panic!("boom")
}

/// The diverging site is a call to a user `-> !` helper, not a panic entry
/// point. The key is the never-returning call, not the callee's name.
pub fn never(x: u32) -> u32 {
    if x == 7 {
        fail()
    }
    x
}

/// A panic ONE CALL DEEPER: the diverging site is inside std's `unwrap`, not in
/// this body. Measured 2026-09-24 (stage 1, 02d825d762, before the second half
/// of the fix): declared, `unwrap_at(black_box(None))` built rc=0 and exited 101.
pub fn unwrap_at(x: Option<u32>) -> u32 {
    x.unwrap()
}

/// The `expect` sibling over a slice lookup (same measurement: rc=0, exit 101).
pub fn expect_at(v: &[u32], i: usize) -> u32 {
    *v.get(i).expect("in range")
}

/// Positive control: `h` with the panic replaced by a return. No diverging
/// site, so it stays bundled.
pub fn quiet(x: u32) -> u32 {
    if x == 7 {
        return 0;
    }
    x
}
