//@ needs-trust-verify
//@ edition: 2021
//@ revisions: alloc_map alloc_vec alloc_delegating trusted_len advisory send_sync
//@ revisions: derive_clone_copy manual_trivial_clone macro_automatically_derived
//@ revisions: searcher_gat
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[alloc_map] check-fail
//@[alloc_vec] check-fail
//@[alloc_delegating] check-fail
//@[trusted_len] check-fail
//@[advisory] check-pass
//@[send_sync] check-pass
//@[derive_clone_copy] check-pass
//@[manual_trivial_clone] check-fail
//@[macro_automatically_derived] check-fail
//@[searcher_gat] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
#![cfg_attr(any(alloc_map, alloc_vec, alloc_delegating, advisory), feature(allocator_api))]
#![cfg_attr(any(trusted_len, macro_automatically_derived), feature(trusted_len))]
#![cfg_attr(manual_trivial_clone, feature(trivial_clone))]
#![cfg_attr(searcher_gat, feature(pattern))]
//! Trust (2026-09-29): AN `unsafe impl` OF A FOREIGN TRAIT IS A PROMISE NO LANE
//! CHECKS (`compiler/rustc_mir_transform/src/trust_verify/unsafe_impl_promise.rs`;
//! docs/KNOWN_HAZARDS.md, "CLOSED 2026-09-29 — a local `unsafe impl` of a foreign
//! unsafe trait (a user `Allocator`) was believed by the std code that calls it").
//!
//! `alloc_map` is the witness: `Bad::allocate` is safe code that returns a
//! dangling "allocation"; `HashMap::with_hasher_in(.., Bad)` behind `ManuallyDrop`
//! built rc=0 on main (`0.10.0+g4715fe060`, source of `7eddcd160b`; probe
//! `ua_md_map`), and the program died of SIGSEGV (exit 139) when hashbrown wrote
//! its control bytes through the pointer. The original probe
//! (`fa_user_alloc_dangling_map`, the same map WITHOUT `ManuallyDrop`) was refused
//! on main only by an unrelated drop-glue row.
//!
//! * `alloc_vec`: the same allocator behind a `Vec` (refused on main too, by a
//!   generic absent-callee row; now also by the promise).
//! * `alloc_delegating`: a CORRECT allocator that delegates to `Global` — the
//!   disclosed cost: no lane can tell it from `Bad`, so it is refused too.
//! * `trusted_len`: a marker `unsafe impl TrustedLen` with no method, whose
//!   `size_hint` lies — the reason the refusal is crate-level, not per body.
//! * `advisory`: the explicit survey reports the promise as a warning.
//! * `send_sync`: auto traits are the recorded residue (thread-safety is not
//!   modeled), so `unsafe impl Send`/`Sync` draw no such error.
//!
//! WHO MAKES THE PROMISE (2026-09-30). `#[derive(Clone, Copy)]` on a
//! non-generic type makes the BUILTIN `Clone` derive emit `unsafe impl
//! core::clone::TrivialClone` beside a `clone` that is the bitwise copy `*self`:
//! the compiler's promise, true by construction. The first version of this rule
//! (`0.10.0+g2a7366482`) refused it, and with it every such derive (ten ui
//! fixtures went red); an impl `tcx.is_builtin_derived` names is now out of scope.
//!
//! * `derive_clone_copy`: the builtin derive's `TrivialClone` impl is accepted
//!   (rc=0 on main).
//! * `manual_trivial_clone`: the same trait implemented by hand, beside a
//!   `clone` that is NOT a copy — the user's promise, and a false one — is
//!   refused.
//! * `macro_automatically_derived`: a `macro_rules!` expansion that writes
//!   `#[automatically_derived]` on its own `unsafe impl TrustedLen` is not a
//!   builtin derive (the attribute alone is not the test; the expansion is), so
//!   the lying impl is refused.
//!
//! All three built rc=0 on main `0.10.0+g07091c92c` (no promise rule there);
//! `0.10.0+g2a7366482` refused all three.

#[cfg(any(alloc_map, alloc_vec, advisory))]
use std::alloc::{AllocError, Allocator, Layout};
#[cfg(any(alloc_map, alloc_vec, advisory))]
use std::ptr::NonNull;

#[cfg(any(alloc_map, alloc_vec, advisory))]
pub struct Bad;

#[cfg(any(alloc_map, alloc_vec, advisory))]
unsafe impl Allocator for Bad {
    //[alloc_map,alloc_vec]~^ ERROR Trust verification cannot accept `unsafe impl
    //[advisory]~^^ WARN Trust verification cannot accept `unsafe impl
    fn allocate(&self, l: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Ok(NonNull::slice_from_raw_parts(NonNull::dangling(), l.size()))
    }
    unsafe fn deallocate(&self, _p: NonNull<u8>, _l: Layout) {}
}

#[cfg(any(alloc_map, advisory))]
pub fn f(k: u32) -> usize {
    let mut m = std::mem::ManuallyDrop::new(std::collections::HashMap::with_hasher_in(
        std::hash::RandomState::new(),
        Bad,
    ));
    m.insert(k, 1u64);
    m.len()
}

#[cfg(alloc_vec)]
pub fn f(x: u64) -> usize {
    let mut v = std::mem::ManuallyDrop::new(Vec::<u64, Bad>::with_capacity_in(4, Bad));
    v.push(x);
    v.len()
}

#[cfg(alloc_delegating)]
pub struct Delegating;

#[cfg(alloc_delegating)]
unsafe impl std::alloc::Allocator for Delegating {
    //[alloc_delegating]~^ ERROR Trust verification cannot accept `unsafe impl
    fn allocate(
        &self,
        l: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        std::alloc::Global.allocate(l)
    }
    unsafe fn deallocate(&self, p: std::ptr::NonNull<u8>, l: std::alloc::Layout) {
        // SAFETY: `p` came from `Global.allocate(l)` above, per this trait's contract.
        unsafe { std::alloc::Global.deallocate(p, l) }
    }
}

#[cfg(trusted_len)]
pub struct Liar(u8);

#[cfg(trusted_len)]
impl Iterator for Liar {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.0 == 0 {
            None
        } else {
            self.0 -= 1;
            Some(self.0)
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

#[cfg(trusted_len)]
unsafe impl std::iter::TrustedLen for Liar {}
//[trusted_len]~^ ERROR Trust verification cannot accept `unsafe impl

#[cfg(send_sync)]
pub struct Shared(*const u8);

#[cfg(send_sync)]
unsafe impl Send for Shared {}

#[cfg(send_sync)]
unsafe impl Sync for Shared {}

#[cfg(send_sync)]
pub fn g(x: u8) -> u8 {
    x / 2
}

#[cfg(derive_clone_copy)]
#[derive(Clone, Copy)]
pub struct Pair(u8, u8);

#[cfg(derive_clone_copy)]
pub fn swap(p: Pair) -> Pair {
    let q = p.clone();
    Pair(q.1, p.0)
}

#[cfg(manual_trivial_clone)]
pub struct Counter(u8);

#[cfg(manual_trivial_clone)]
impl Clone for Counter {
    fn clone(&self) -> Counter {
        Counter(self.0.wrapping_add(1))
    }
}

#[cfg(manual_trivial_clone)]
unsafe impl std::clone::TrivialClone for Counter {}
//[manual_trivial_clone]~^ ERROR Trust verification cannot accept `unsafe impl

#[cfg(macro_automatically_derived)]
pub struct Liar2(u8);

#[cfg(macro_automatically_derived)]
impl Iterator for Liar2 {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.0 == 0 {
            None
        } else {
            self.0 -= 1;
            Some(self.0)
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

#[cfg(macro_automatically_derived)]
macro_rules! lying_trusted_len {
    ($t:ty) => {
        #[automatically_derived]
        unsafe impl std::iter::TrustedLen for $t {}
        //[macro_automatically_derived]~^ ERROR Trust verification cannot accept `unsafe impl
    };
}

#[cfg(macro_automatically_derived)]
lying_trusted_len!(Liar2);

// `searcher_gat` (2026-10-08): a lying `Searcher` (it reports a match far past
// the haystack) behind a `Pattern` whose associated type is GENERIC, `type
// Searcher<'a> = S<'a>`, driving `str::split`. The promise is refused like the
// others. It is also the pin of a compiler crash the landing's probe round found
// on main `0.10.0+gde6288ddd` (probe `b_searcher`, rc=101): the trait-impl
// surface walk (`trust_verify/local_impl_surface.rs`, 2026-10-07) instantiated
// the generic associated type at the impl's arguments alone and panicked ("has
// parameters, but no args were provided in instantiate") before any diagnostic
// of this file's rule. A generic associated type now answers that walk `true`
// (fail-closed), and the build ends in errors, not in a crash.
#[cfg(searcher_gat)]
pub struct Pat;

#[cfg(searcher_gat)]
pub struct Srch<'a> {
    h: &'a str,
    done: bool,
}

#[cfg(searcher_gat)]
unsafe impl<'a> std::str::pattern::Searcher<'a> for Srch<'a> {
    //[searcher_gat]~^ ERROR Trust verification cannot accept `unsafe impl
    fn haystack(&self) -> &'a str {
        self.h
    }
    fn next(&mut self) -> std::str::pattern::SearchStep {
        if self.done {
            std::str::pattern::SearchStep::Done
        } else {
            self.done = true;
            std::str::pattern::SearchStep::Match(0, 1 << 40)
        }
    }
}

#[cfg(searcher_gat)]
impl std::str::pattern::Pattern for Pat {
    type Searcher<'a> = Srch<'a>;
    fn into_searcher(self, h: &str) -> Srch<'_> {
        Srch { h, done: false }
    }
}

#[cfg(searcher_gat)]
pub fn split_len(s: &str) -> usize {
    s.split(Pat).map(|x| x.len()).sum()
}
