//@ needs-trust-verify
//@ aux-build: policy_b_unverified_dep.rs
//@ revisions: io_error box_dyn_error dep_type io_error_advisory string u32
//@ revisions: io_error_certify box_dyn_error_certify
//@ compile-flags: -Ztrust-verify=on -Copt-level=0
//@[io_error_advisory] compile-flags: -Ztrust-policy=advisory
//@[io_error_certify] compile-flags: -Ztrust-policy=certify
//@[box_dyn_error_certify] compile-flags: -Ztrust-policy=certify
//@[io_error] build-pass
//@[box_dyn_error] build-pass
//@[dep_type] build-pass
//@[io_error_advisory] build-pass
//@[string] build-pass
//@[u32] build-pass
//@[io_error_certify] check-fail
//@[box_dyn_error_certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! X2 (2026-09-23): the compiler ICEd on ordinary `main` signatures.
//!
//! MEASURED on stage-1 `de437e35d`: `fn main() -> Result<(), std::io::Error> {
//! Ok(()) }`, the same with `Box<dyn std::error::Error>`, and with a verify-off
//! dependency's `dep::Bomb` each linked the binary and then exited 101:
//!
//!     `trimmed_def_paths` called, diagnostics were expected but none were emitted
//!
//! (backtrace: `entry_termination_dispatch_rows` <- `publish_body_verification_
//! outcome` <- `optimized_mir` <- `trust_ensure_whole_crate_verification`).
//! ROOT CAUSE: that seam rendered `main`'s return type with `{ret_ty}` into the
//! policy-B entry-`Termination` row's message. `Ty`'s `Display` goes through
//! `trimmed_def_paths`, which arms rustc's `must_produce_diag`; the row reaches
//! only the transport/JSON output, so when `main` has no other row nothing is
//! emitted and `DiagCtxtInner::drop` fires. The render is now under
//! `with_no_trimmed_paths!`, the idiom `advisory_println_no_trimmed_paths_ice.rs`
//! pins for the extractor.
//!
//! `build-pass` is the whole assertion for the first six revisions: an ICE is
//! exit 101, which the harness reports as a failure of the pass mode. The
//! policy is unchanged: the foreign/dynamic return type still publishes its
//! runtime-checked entry row (CONDITIONAL on the default lane) and `certify`
//! still refuses it — the two `*_certify` revisions pin that refusal, which
//! must stay. `string`/`u32` are the controls (no row, no ICE before either).
//! (Corrected 2026-10-03: for these zero-obligation `main`s the row reached the
//! human warning but NOT the JSON — the transport published `no_obligations:
//! proved` instead; `entry_termination_row_on_zero_obligation_main.rs` pins the wire.)
#[cfg(dep_type)]
extern crate policy_b_unverified_dep as dep;

#[cfg(any(io_error, io_error_advisory, io_error_certify))]
fn main() -> Result<(), std::io::Error> {
    //[io_error_certify]~^ ERROR Trust certify verification failed
    Ok(())
}

#[cfg(any(box_dyn_error, box_dyn_error_certify))]
fn main() -> Result<(), Box<dyn std::error::Error>> {
    //[box_dyn_error_certify]~^ ERROR Trust certify verification failed
    Ok(())
}

#[cfg(dep_type)]
fn main() -> Result<(), dep::Bomb> {
    Ok(())
}

#[cfg(string)]
fn main() -> Result<(), String> {
    Ok(())
}

#[cfg(u32)]
fn main() -> Result<(), u32> {
    Ok(())
}
