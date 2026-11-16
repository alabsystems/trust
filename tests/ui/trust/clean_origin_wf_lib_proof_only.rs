//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ build-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE

//! **A LIBRARY whose well-founded Clean def is used in PROOF position only,
//! from a PRIVATE module — verification ON.**
//!
//! wf1 probe 36d, verbatim, as an rlib. It is the shape a Lean-backed spec
//! library is made of: a recursive helper over `Nat`, a theorem about it
//! proved by kernel evaluation, a `UInt64` theorem that rewrites with it, and
//! a Rust contract that CITES that theorem. No Rust code ever calls `cnt`.
//!
//! Measured before 2026-09-16 (both toolchains): verification reported
//! `2 proved … 2 kernel-certified`, the citation kernel-discharged the
//! postcondition — and THEN the build died with
//! `error: internal: refusing to export a certificate for Clean declaration
//! `cnt``, because the rmeta encoder demands a verdict-digest row for EVERY
//! minted def, whatever its visibility and whether or not anything calls it,
//! and `WellFoundedFunctionalDefeq` has no wire tag. Moving the island into a
//! private module — the refusal's own first option — changed nothing.
//!
//! The export provider now writes a non-exportable notice for `cnt`, so the
//! library builds. `build-pass` rather than `check-pass` on purpose: the
//! measured failure was a full `--crate-type=lib` build.
//!
//! What this does NOT claim: that another crate may call `cnt` (it may not —
//! `clean_origin_wf_lib_direct_call_refused.rs`), or that another crate may
//! CITE `cnt_zero` (cross-crate Clean citation is a named boundary of I7
//! decision (e), untouched here).

#![crate_type = "rlib"]

mod proofs {
    clean {
        def cnt (f n : Nat) : Nat := if h : 0 < f then cnt (f - 1) (n + 1) else n
        termination_by f
        theorem cnt_zero (n : Nat) : cnt 0 n = n := rfl
        theorem u64_ge_self : forall (x : UInt64), Nat.le (UInt64.toNat x) (cnt 0 (UInt64.toNat x)) := by
          intro x
          rw [cnt_zero]
          exact @Nat.le.refl _
    }
}

pub fn keep(x: u64) -> u64 ensures result >= x by u64_ge_self { x }
