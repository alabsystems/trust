//@ needs-trust-verify
//@ aux-build:clean_origin_wf_lib_aux.rs
//@ build-fail
//@ compile-flags: -Z trust-verify=off

//! **A well-founded Clean def cannot be CALLED from another crate — the
//! two-crate negative control (close twin of
//! `clean_origin_wf_lib_wrapper_call.rs`, same aux).**
//!
//! The aux builds as a library because its export provider writes a
//! non-exportable NOTICE for `countdownSum` where a certificate would go: the
//! local gate admitted the def by `WellFoundedFunctionalDefeq`, an evidence
//! form the certificate wire format deliberately has NO TAG for, and no tag
//! was invented to get here. What must therefore stay impossible is this
//! crate running `countdownSum`'s body on the strength of nothing.
//!
//! The path resolves (`pub mod m`; the mint forces the def `Public`) and
//! type-checks against the aux's encoded `fn_sig`, so nothing stops this
//! before MIR. Codegen then needs the body: Clean-origin defs are
//! `cross_crate_inlinable`, so the aux emitted NO linkable symbol and this
//! crate must instantiate its own copy through the guarded extern
//! `optimized_mir` decode arm — THE CHOKEPOINT — which runs
//! `trust_clean_extern_readmission` first. That provider recognises the notice
//! and fatals with its v7/D3 note: what was refused, why (no wire tag for the
//! evidence form), and the options. There is no arm on which a recognised
//! notice serves a body.
//!
//! `build-fail`, not `check-fail`, and that is part of what is pinned: a
//! `--emit=metadata` pass of a binary never asks for an extern body, so
//! compiletest's build-fail pre-check (metadata-only must SUCCEED) holds and
//! the refusal arrives exactly where a body would first be needed.
//!
//! The note's text is rendered by `NonExportableNotice::import_note` and is
//! pinned against this file's `.stderr` by
//! `crates/trust-clean-origin/tests/control_28_non_exportable_notice.rs`
//! (no pre-push lane runs a `ui` test).
//!
//! What this suite cannot honestly test: replacing the notice with a forged
//! certificate needs rmeta byte-patching, which no ui directive expresses. The
//! decision is pinned at crate level (`control_28`: a notice never decodes as
//! a digest; `control_4`: a wire method tag that disagrees with the locally
//! observed method refuses), in the style `clean_origin_cross_crate_call.rs`
//! records for kernel skew.

extern crate clean_origin_wf_lib_aux;
extern crate trust_bignum;

fn main() {
    let out = clean_origin_wf_lib_aux::m::countdownSum(trust_bignum::Nat::from_u64(3));
    assert_eq!(out.to_u64(), Some(6));
}

//~? ERROR `clean_origin_wf_lib_aux::m::countdownSum` cannot be called from another crate
