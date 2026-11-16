//@ needs-trust-verify
//@ edition: 2021
//@ revisions: wide_element_4097 at_const_ceiling set_wide_element below_const_ceiling legal_u64_literal legal_wide_small
//@ revisions: set_bucket_bytes set_bucket_bytes_below
//@ revisions: at_object_limit set_at_object_limit
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[wide_element_4097] check-pass
//@[at_const_ceiling] check-pass
//@[set_wide_element] check-pass
//@[below_const_ceiling] check-pass
//@[legal_u64_literal] check-pass
//@[legal_wide_small] check-pass
//@[set_bucket_bytes] check-pass
//@[set_bucket_bytes_below] check-pass
//@[at_object_limit] check-fail
//@[set_at_object_limit] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
#![allow(dead_code)]
//! Trust (RULED 2026-10-08): THE ONLY BYTE CEILING ON A CONSTANT ALLOCATION COUNT
//! IS THE OBJECT LIMIT (docs/KNOWN_HAZARDS.md, "RULED 2026-10-08 ... a constant
//! allocation count of a wide element within the object limit is an
//! allocation-failure abort, not a modeled panic"; docs/DECISION_QUEUE.md,
//! ALLOC-BYTE-1).
//!
//! This file was written on the trust-open-false-accepts branch (2026-09-29) to
//! pin a 4 GiB byte ceiling on a constant count
//! (`UNBOUNDED_ALLOC_CONST_BYTE_CEILING`), after the salvage probe
//! `fa_vec_wc_const_control` — `Vec::<[u8; 1 << 50]>::with_capacity(4097)`,
//! `2^62 + 2^50` bytes — built rc=0 on main and aborted "memory allocation of
//! 4612811918334230528 bytes failed" (exit 134). That ceiling never reached
//! main. While the branch was landing, main took the owner's ruling of
//! 2026-09-29 ("delete the 256 MiB number; the lint reports only allocations
//! whose size is not provably bounded"): an allocation is judged against the
//! largest object the target can hold (`isize::MAX` at its pointer width, where
//! RawVec PANICS) and against nothing smaller. A constant count is a provably
//! bounded size, so the 4 GiB line was a second byte budget of the kind the
//! ruling deletes, and it was withdrawn at the landing merge. An allocation the
//! host cannot satisfy ABORTS (no unwinding, in a graph with no
//! allocation-error hook; a hook is charged separately); it is outside the
//! panic/UB claim.
//!
//! What the revisions pin now:
//!
//! * check-pass, every constant shape the withdrawn ceiling refused or
//!   admitted: `wide_element_4097` (the probe's shape; it would abort if run),
//!   `at_const_ceiling` and `below_const_ceiling` (`1048576` and `1048575`
//!   elements of 4 KiB: 4 GiB and one element fewer), `set_wide_element`
//!   (`HashSet` of 1 MiB elements, capacity 4096), `set_bucket_bytes` and
//!   `set_bucket_bytes_below` (`HashSet<[u8; 4096]>` at 600_000 and 400_000),
//!   `legal_u64_literal` (`vec![0u64; 40_000_000]`), `legal_wide_small`.
//! * check-fail, the object limit, which is a real panic: `at_object_limit`
//!   (`Vec::<[u8; 1 << 50]>::with_capacity(8192)`: `2^63` bytes, "capacity
//!   overflow") and `set_at_object_limit`
//!   (`HashSet::<[u8; 1 << 50]>::with_capacity(4097)`: `4097 * 2^50` bytes of
//!   elements are under `isize::MAX`, hashbrown's 8192 buckets are not: "Hash
//!   table capacity overflow").

#[cfg(wide_element_4097)]
pub fn f() -> usize {
    Vec::<[u8; 1 << 50]>::with_capacity(4097).len()
}

#[cfg(at_const_ceiling)]
pub fn f() -> usize {
    Vec::<[u8; 4096]>::with_capacity(1048576).len()
}

#[cfg(below_const_ceiling)]
pub fn f() -> usize {
    Vec::<[u8; 4096]>::with_capacity(1048575).len()
}

#[cfg(set_wide_element)]
pub fn f() -> usize {
    std::collections::HashSet::<[u8; 1 << 20]>::with_capacity(4096).len()
}

#[cfg(legal_u64_literal)]
pub fn f() -> usize {
    vec![0u64; 40_000_000].len()
}

#[cfg(legal_wide_small)]
pub fn f() -> usize {
    Vec::<[u8; 4096]>::with_capacity(1000).len()
}

#[cfg(set_bucket_bytes)]
pub fn f() -> usize {
    std::collections::HashSet::<[u8; 4096]>::with_capacity(600_000).len()
}

#[cfg(set_bucket_bytes_below)]
pub fn f() -> usize {
    std::collections::HashSet::<[u8; 4096]>::with_capacity(400_000).len()
}

#[cfg(at_object_limit)]
pub fn f() -> usize {
    //[at_object_limit]~^ ERROR Trust
    Vec::<[u8; 1 << 50]>::with_capacity(8192).len()
}

#[cfg(set_at_object_limit)]
pub fn f() -> usize {
    //[set_at_object_limit]~^ ERROR Trust
    std::collections::HashSet::<[u8; 1 << 50]>::with_capacity(4097).len()
}
