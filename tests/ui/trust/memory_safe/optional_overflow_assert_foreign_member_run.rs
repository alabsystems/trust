//@ revisions: inc path
//@ run-fail
//@ needs-trust-verify
//@ aux-build:optional_overflow_assert_foreign_dep.rs
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=off
//@ compile-flags: -Ztrust-bundle-foreign-crate=optional_overflow_assert_foreign_dep
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! The runtime WITNESS for `optional_overflow_assert_foreign_member.rs`
//! (OVF-ASSERT-XCRATE-1): the `adv` and `path_adv` callers, built exactly as there
//! (advisory, overflow checks OFF, the dependency declared in the bundling scope),
//! with a `main`. The dependency was built with checks ON, and its own object code
//! runs both `inc` and `outer`'s copy of `inner`, so each call at `u32::MAX`
//! panics with `attempt to add with overflow` (exit 101) although this crate's
//! session has checks off. The binary does not depend on the verifier's verdict;
//! this file pins the fact the sibling's revisions rest on.
//!
//! MEASURED 2026-10-06 on the stage 1 of `4ccd862830` (`scratchpad/stage1-w18b`)
//! with these flags, outside compiletest: both revisions built rc=0 and exited 101
//! with that message, while the build reported the caller's panic-freedom row
//! proved ("1 proved"). Expected unchanged by the fix, which changes no codegen.

extern crate optional_overflow_assert_foreign_dep as dep;

#[cfg(inc)]
pub fn use_inc(x: u32) -> u32 {
    dep::inc(x)
}

#[cfg(path)]
pub fn use_outer(x: u32) -> u32 {
    dep::outer(x)
}

fn main() {
    #[cfg(inc)]
    println!("{}", use_inc(std::hint::black_box(u32::MAX)));
    #[cfg(path)]
    println!("{}", use_outer(std::hint::black_box(u32::MAX)));
}
