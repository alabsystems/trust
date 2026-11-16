//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ revisions: o2plain
//@ compile-flags: -Ztrust-verify=on -Copt-level=2 --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//~? RAW Trust
//! The OPTIMIZED soundness pin — and the one that guards the cast modeling.
//!
//! `absent_dep_callee_stays_closed.rs` proves that at the DEFAULT opt-level a
//! non-std absent callee (an unverified dependency's `*p`) stays fatal: policy B
//! tolerates only std's print backend, and the safety net there is literally
//! "non-std absent callee = fatal", never UB detection.
//!
//! At `-Copt-level>=2` that net does not apply, because `#[inline(always)]`
//! means there IS no absent callee — the dependency's raw dereference is inlined
//! directly into this crate's MIR, where it must be caught on its own merits.
//! This fixture exists because the `-O` cast modeling deliberately stops several
//! inlined-std casts from minting `unsupported_mir` rows, and an `unknown` row
//! is exactly the kind of incidental blocker that could have been the only thing
//! keeping this build red. If modeling those casts ever unmasks this
//! dereference, THIS test goes green and says so.
//!
//! It must stay RED. A green here is not a fixture to re-bless; it is a report
//! that the optimized lane accepts a dereference of an arbitrary `usize`.
//!
//! -O parity (2026-09-25): a verifying session inlines only under an EXPLICIT
//! `-Zmir-opt-level=2` now, so `mir2` states it and is the pin described above.
//! `o2plain` is the plain `-Copt-level=2` default: nothing is inlined, the
//! dependency's callee stays ABSENT, and the net above applies exactly as at the
//! default opt-level (measured on the stage-1 build of this change: refused).
extern crate policy_b_unverified_dep;

pub fn read_any(addr: usize) -> u32 {
    policy_b_unverified_dep::deref_raw(addr as *const u32)
}
