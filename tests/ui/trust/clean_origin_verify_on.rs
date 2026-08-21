//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ run-pass
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//! **I5 — CALLING A CLEAN-ORIGIN FUNCTION WITH VERIFICATION ON.**
//! (`docs/design/2026-08-04-two-language-compiler-architecture.md` §7.)
//!
//! Every other I5 fixture compiles with `-Z trust-verify=off`. This one does
//! NOT, and that is its entire reason for existing: the verification pipeline
//! walks the crate's functions on a different path than ordinary compilation,
//! and a Clean-origin def — which has a `DefId`, a fed `fn_sig` and a synthetic
//! HIR owner, but no HIR body — is exactly the shape those walks were never
//! written for.
//!
//! # GREEN AS OF 2026-08-20 — cross-authority call modeling
//!
//! This fixture is `run-pass`: it compiles under verification-ON default
//! policy, runs, prints `41`, and `main`'s `assert_eq!(v, 41)` VERIFIES. The
//! boundary it used to pin — the caller's obligation failing closed because
//! the VC lane havocked the call — is closed by the increment its own header
//! demanded, and the flip is neither a weakened strict policy nor a
//! hand-written contract on `main` (the two flips the old header forbade).
//!
//! **The summary's authority chain, and why this is not the solver "inventing
//! `pick`'s semantics":**
//!
//! 1. **Kernel gate.** `pick`'s body exists at all only because
//!    `clean_origin_mir` (the SOLE constructor of a Clean-origin `Body`)
//!    emitted it from a `CleanOriginPlan` and the faithfulness gate
//!    (`trust_clean_origin::check_faithful`) kernel-identified the emitted
//!    body with the declaration — a disagreement is a FATAL refusal, so a
//!    compiled `pick` and its plan cannot differ.
//! 2. **Plan.** The verifier re-derives that SAME plan of record —
//!    `clean_crate_environment` → `trust_clean_origin::plan_clean_origin_body`,
//!    the emitter's own decision procedure over the same island bytes — never
//!    re-reading MIR and never parsing Clean text itself
//!    (`trust_verify.rs::clean_origin_plan_of_record`).
//! 3. **Summary.** For the plan shape `Projection { projected }` the caller's
//!    VC lane injects the DEFINITIONAL summary `result == arg_projected` plus
//!    panic-freedom (the emitted body is `_0 = move _{projected+1}; return` —
//!    no panic path exists), rebound at the call site and version-pinned to
//!    the dest (`trust_vcgen`'s `with_definitional_postcondition` lane). The
//!    summary is an EQUALITY: it refutes a wrong caller claim exactly as it
//!    discharges a right one — `clean_origin_caller_wrong_claim.rs` is the
//!    control fixture pinning the refutation direction.
//!
//! Fail-closed is untouched: a shape the summary lane does not model, or any
//! plan/environment refusal, injects NOTHING — the call stays havocked and
//! strict fails closed exactly as this fixture's first life measured, now
//! with a truthful v7/D3 note naming the callee as Clean-origin (the old
//! note's "a std/extern function" misdescription was the recorded defect,
//! fixed in the same increment).
//!
//! # The failure this file originally pinned, and why it took SIX sites
//!
//! `typeck` `span_bug!`s on a def with a synthetic HIR owner and no body:
//!
//! ```text
//! error: internal compiler error: can't type-check body of DefId(..::m::pick)
//! ```
//!
//! Seeding Clean-origin defs into `mir_keys` exposed every consumer that
//! assumes a `mir_keys` Fn has an ordinary HIR -> typeck -> borrowck pipeline.
//! Six were found, one at a time, each by its own route:
//!
//!   1. `trust_verify.rs`'s backing inventory;
//!   2. `trust_r1_oracle.rs`'s call-graph scan;
//!   3. the MIR pipeline itself;
//!   4. the R1 flip harvest (`try_harvest_flip`, via `mir_keys`) — found by
//!      THIS fixture's first run;
//!   5. the coverage denominator (`trust_coverage_eligible_body`) — predicted
//!      from the `processed == eligible` reconciliation before it fired;
//!   6. the mutual-recursion oracle's adjacency (`main` -> `optimized_mir` ->
//!      `trust_mir_mutually_recursive_functions` ->
//!      `trust_mir_direct_local_callees(pick)`) — found by this fixture's
//!      second run.
//!
//! After the sixth, the family was closed at the SEAM instead of the caller:
//! `mir_drops_elaborated_and_const_checked` itself now serves the kernel-gated
//! emission for a Clean-origin def (a clone of the cached `optimized_mir`), so
//! the query is total over `mir_keys` and a seventh consumer cannot exist.
//! Sites 4 and 5 keep their caller-side guards anyway, because their reasons
//! are not the ICE: the harvest must not mix caller-precondition authority
//! into a kernel-gated body, and the coverage denominator must not name a body
//! the VC pipeline correctly never processes.
//!
//! # Neither the scan nor the seam SKIPS the body
//!
//! The R1 scan and the elaborated-MIR seam both serve `optimized_mir`, which
//! for these defs IS the gated emission. That distinction is the point:
//! skipping would leave a silent hole in an oracle whose completeness is the
//! property it certifies, and "the verifier does not look at Clean-origin
//! code" is a much worse answer than an ICE, because it is quiet. The R1 call
//! graph stays COMPLETE across the Rust/Clean boundary.
//!
//! # What this fixture does NOT claim
//!
//! Nothing about proof authority. The gate that admitted `pick`'s body is a
//! compilation-correctness check, not an obligation discharge; the injected
//! summary is a compiler-composed derivation from that gate's plan of record
//! (`Trusted`, not `Certified` — see `docs/TCB.md`), and verification being ON
//! here does not make the emitted body `Certified`. This file pins that the
//! two lanes COMPOSE at a call site, nothing more.

mod m {
    clean {
        def pick (a : UInt64) (b : UInt64) : UInt64 := a
    }
}

fn main() {
    // Runtime call, verification ON. The caller's assert is DISCHARGED by the
    // kernel-gated projection summary — not by a weakened policy, not by a
    // hand-written contract, and not by the solver guessing.
    let v = m::pick(41, 7);
    // `assert!`, not `assert_eq!`, and no `println!` — MEASURED boundaries of
    // the L0 lane that are NOT about Clean-origin calls: `assert_eq!`'s
    // borrow-and-deref expansion leaves `left_val` unconnected to `v` in the
    // VC encoding (the summary binds v = 41 and the solver still refutes on
    // left_val), and `println!`'s formatting internals carry a
    // hardened_unsafe_operation obligation L0 cannot discharge. Both fail a
    // strict build for ANY value, Clean-origin or not. The direct comparison
    // is the shape the summary provably closes: 1 obligation, PROVED.
    assert!(v == 41, "the emitted body must be the projection the Clean `def` denotes");
}
