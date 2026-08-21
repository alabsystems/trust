//@ needs-trust-verify
//@ aux-build:clean_origin_aux.rs
//@ run-pass
//@ compile-flags: -Z trust-verify=off
//@ dont-check-compiler-stderr

//! **I7 — the cross-crate Clean-origin call, positive lane.**
//!
//! `pick` was minted, gated, and digest-exported in `clean_origin_aux.rs`
//! (a separately compiled rlib). Calling it here traverses the FULL import
//! half:
//!
//!   1. name resolution finds `clean_origin_aux::m::pick` through the aux
//!      crate's rmeta (the module is `pub`; the def's visibility was forced
//!      `Public` at the mint);
//!   2. typeck uses the aux crate's ENCODED `fn_sig` (fed from the carrier
//!      decision at mint time);
//!   3. codegen instantiates the body LOCALLY: the aux marks Clean-origin
//!      defs `cross_crate_inlinable`, which excludes them from its
//!      `reachable_non_generics` (symbol_export's cross_crate_inlinable
//!      filter — the corrected I7 mechanism), so this crate cannot link an
//!      upstream symbol its own readmission never saw;
//!   4. the extern `optimized_mir` decode arm — THE CHOKEPOINT — runs
//!      `trust_clean_extern_readmission` before serving the body: digest
//!      decoded whole, the aux's island sources re-elaborated under THIS
//!      compiler's Clean kernel, `readmit` compared every digest field
//!      against the locally recomputed facts, and the decoded body re-passed
//!      the faithfulness gate under the LOCAL kernel.
//!
//! The assert is the value half: a wrong projection (returning `y`) is a
//! wrong binary, which is exactly the failure class this lane exists to make
//! impossible to reach silently.
//!
//! `-Z trust-verify=off` is load-bearing evidence: readmission and the local
//! re-gate are deliberately NOT behind the verification switch, so this
//! fixture proves the chokepoint runs even with verification off.
//!
//! # What this suite CANNOT honestly test, stated plainly (I7 scope 3)
//!
//! * **Kernel-version skew.** One test run hosts exactly one Clean kernel, so
//!   a ui test can never present a certificate minted under a DIFFERENT
//!   kernel to this compiler. The refusal decision is pinned at crate level —
//!   `crates/trust-clean-origin/tests/control_4_readmission_digest.rs`
//!   re-encodes a digest with a tampered `kernel_version` field and requires
//!   `ReadmissionRefusal::KernelVersionSkew` — and the rustc-level transport
//!   control is the planned run-make byte-patch of the digest's
//!   `kernel_version` bytes inside the emitted rlib (plan S7's sibling
//!   commit), which no ui directive can express.
//! * **Digest corruption/truncation.** Same boundary: a ui test has no
//!   honest mechanism to tamper rmeta bytes between the aux build and this
//!   build — anything simulated inside ordinary source would test a fake
//!   seam. The byte-level corruption controls (magic, truncation, field
//!   tamper) live in `control_4` against `VerdictDigest::decode`, whose
//!   refusals are exactly what the readmission provider surfaces as fatal
//!   v7/D3 notes. Nothing here pretends otherwise.

extern crate clean_origin_aux;

fn main() {
    let v = clean_origin_aux::m::pick(41, 7);
    assert_eq!(
        v, 41,
        "the imported Clean-origin body must be the projection the Clean `def` \
         denotes — 41 is parameter 0; observing 7 means the wrong-binary lane \
         the readmission chokepoint exists to close"
    );
}
