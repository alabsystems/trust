//@ needs-trust-verify
//@ aux-build: std_member_identity_dep.rs
//@ revisions: strict default
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! CONTROL (refused before and after) for correction C4 of the Track R design
//! (2026-09-29): the runtime-checked disposition decides on the crate of the
//! resolved body, not on a path string plus foundational generic arguments, so an
//! AUTHENTIC std body instantiated at a DEPENDENCY's type could newly qualify.
//! That is sound only because the bundle is KEPT: whatever such a body calls in
//! user code stays on the success path's rows. This pins that it does.
//!
//! `f` does `filter().count()` (the refused `<usize as Sum>::sum::{closure#0}`,
//! kept as runtime-checked) and returns `w.clone()` for a `Vec<dep::T>`, where
//! `dep` is verify-off and `T::clone` panics on `T(7)`. The clone is returned,
//! not dropped: a `Vec<dep::T>` DROP is refused on its own (its glue runs `dep`'s
//! code), which would pin a different check.
//!
//! MEASURED on stage-1 `f6773df328e` (origin/main, m3 debug std): refused on the
//! lowering-FAILURE path ("native typed-TrustIr lowering did not complete" — the
//! old tolerance withheld itself on the masked dispatch). With the bundle kept and
//! NO further check, the success path refused it too (`<Vec<dep::T> as
//! Clone>::clone` is an absent callee whose unproved panic-freedom row is
//! fail-closed). The disposition now refuses it before that, by name: the
//! `Vec<dep::T>` instantiation is a masked fail-closed source, and a masked source
//! withholds the disposition, exactly as it withheld the old tolerance.
extern crate std_member_identity_dep as dep;

pub enum Tag {
    A,
    B,
}

pub fn f(t: Tag, v: &[u32; 3], w: &Vec<dep::T>) -> Vec<dep::T> {
    let k = v.iter().filter(|x| **x > 1).count();
    let n = match t {
        Tag::A => 1usize,
        Tag::B => 2usize,
    };
    if k == 7 || n == 7 {
        return Vec::new();
    }
    w.clone()
}

// Re-pinned 2026-10-15 (the merge of 2026-10-14): the counted panic-freedom aggregate now
// carries the member's Assert (one `runtime_checked` row), so no member is recorded under the
// runtime-checked disposition and its named refusal does not fire. `f` is refused one step
// later, as the paragraph above says the success path does: `<Vec<dep::T> as Clone>::clone`
// is a generic absent callee whose fail-closed row no policy tolerates.
//~? RAW error: Trust strict verification failed for `std_member_identity_not_widened::f`
//~? RAW an unproved assumption-panic row — a generic absent callee — keeps the function fail-closed
