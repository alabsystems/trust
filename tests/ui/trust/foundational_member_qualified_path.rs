//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-pass
//! Two one-liners that an ordinary program writes without thinking, and that
//! the strict lane refused outright with no source-level workaround.
//!
//! Both refuse inside core, on `<usize as core::iter::traits::accum::Sum>::sum`
//! and its `u8` twin — core's own `Sum` implementation for a primitive, with
//! core's own overflow check inside it. Trust does not verify core, and the
//! tolerance for exactly that situation already existed: a bundled
//! std/core/alloc member's internal obligation is REPORTED under the default
//! policy, because that member's runtime check is retained bit-for-bit as
//! vanilla Rust rather than being an obligation Trust took over.
//!
//! The tolerance never fired here because it asked whether the member's path
//! STARTS WITH `core::`, and a trait-impl member is spelled `<SELF as TRAIT>::m`
//! — it starts with `<`. So the answer was "not core" for code that is plainly
//! core's, and a one-line program was refused.
//!
//! `foundational_member_user_impl_stays_refused.rs` is the other half: the same
//! spelling naming USER code must still be refused, because the whole argument
//! for tolerating this rests on the body being core's and not the user's.

pub fn filtered_count(v: &[u32]) -> usize {
    v.iter().filter(|x| **x > 2).count()
}

pub fn shout(s: &str) -> String {
    s.to_uppercase()
}

// References and generic arguments are what an iterator chain actually produces.
// `map(|x| x + 1)` reaches core's addition as
// `<&u32 as core::ops::arith::Add<u32>>::add`, and `fold` reaches it with the
// reference on the other side. Both halves are core's own code, so the
// recogniser walks the spelling instead of refusing anything that is not a bare
// primitive.
pub fn incremented(v: &[u32]) -> Vec<u32> {
    v.iter().map(|x| x + 1).collect()
}

pub fn folded(v: &[i32]) -> i32 {
    v.iter().fold(0, |a, b| a + b)
}

// 2026-10-06: collected into a `String`, not a `Vec<String>` joined afterwards. A
// `Vec<String>` from `&[u32]` reserves 24 bytes per four-byte source item upfront,
// which `docs/DECISION_QUEUE.md` D12 option (a) charges; that is not what this
// fixture is about. `FromIterator<String>` reserves nothing upfront.
pub fn rendered(v: &[u32]) -> String {
    v.iter().map(|x| x.to_string()).collect::<String>()
}
