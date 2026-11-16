//@ needs-trust-verify
//@ revisions: census walk_unresolved root_unresolved
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@[walk_unresolved] rustc-env:TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED=atomic_xadd
//@[root_unresolved] rustc-env:TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED=fetch_add
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[census] check-pass
//@[walk_unresolved] check-fail
//@[root_unresolved] check-fail
//! Trust (2026-10-08, std-absent-callee): a call the sysroot panic census cannot
//! RESOLVE to an instance is a panic site inside a std body, and a refused root at
//! the call itself — never followed, never assumed total.
//!
//! No well-typed monomorphic program is known to reach either arm
//! (`Instance::try_resolve` answers every call of a fully monomorphic std body),
//! so they are exercised through the census's fault seam
//! `TRUST_SYSROOT_CENSUS_FAULT_UNRESOLVED=<substring>`, which treats a root or
//! walked call whose rendered callee contains the substring as unresolved. The
//! seam can only turn a call the census would follow into a site or a refused
//! root: with the arms as they are it removes proof, never adds it, and that is
//! exactly what these revisions pin.
//!
//! `Atomic::<usize>::fetch_add` is censused TOTAL (`census`, check-pass; also
//! `certify_total_sysroot_callees.rs`): its body matches on the ordering and
//! calls `atomic_xadd` at each one.
//!
//! * `walk_unresolved`: the walk meets `atomic_xadd` unresolved. It is a site,
//!   so `fetch_add` reaches a panic site and `add_one` is refused, the note
//!   naming the unresolved call. If the arm treated an unresolved call as total
//!   (or skipped it), `fetch_add` would stay total and `add_one` would certify
//!   on a call the census never read.
//! * `root_unresolved`: the root `fetch_add` itself is unresolved. The census
//!   does not run, the call keeps its absent-callee row and `add_one` is refused
//!   with that reason. If the root arm granted the call, `add_one` would certify
//!   on a body nobody walked.
//!
//! `census` is the control: the same file without the fault certifies, so each
//! refusal comes from the arm the fault reaches and nothing else.
use std::sync::atomic::{AtomicUsize, Ordering};

pub fn add_one(a: &AtomicUsize) -> usize {
    //[walk_unresolved]~^ ERROR Trust strict verification failed
    //[walk_unresolved]~| NOTE an unresolved call to `core::intrinsics::atomic_xadd`
    //[root_unresolved]~^^^ ERROR Trust strict verification failed
    //[root_unresolved]~| NOTE it is a call whose instance does not resolve
    a.fetch_add(1, Ordering::Relaxed)
}
