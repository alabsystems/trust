//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Awarnings
//@ dont-check-compiler-stderr
//@ build-pass
//! Regression for a THIR-to-TrustIR E0391 seen while compiling `regex-syntax` with verification
//! active. Inspecting `Result<impl Iterator, Error>` as an enum payload asked `layout_of` for the
//! defining function's opaque return type from inside its own `mir_built` query. That re-entered
//! opaque `type_of` through borrowck instead of returning a layout error.
//!
//! The THIR lowering must decline that optional ZST/layout classification before issuing the query.
//!
//! It re-broke from the other side, and the second cause is worth naming because the first fix
//! could not have prevented it. Every layout demand the *producer* makes is pre-gated
//! (`trust_thir_lower::layout_query_is_reentrant_safe`), but the differential runs the MIR-side
//! ORACLE — `trust-mir-extract`, a crate written for the post-borrowck verification pipeline —
//! from inside `mir_built` too, and its `layout_of` on a local decl had no such gate. So the
//! shape came back through a lane that never had the defence, and E0391 is fatal: this is valid
//! Rust failing to compile under batteries-on verification, not a coverage gap.

pub struct Range;
pub struct Error;

pub fn ranges(canonical_age: &str) -> Result<impl Iterator<Item = Range>, Error> {
    fn imp(_canonical_age: &str) -> Result<impl Iterator<Item = Range>, Error> {
        Ok(std::iter::once(Range))
    }

    imp(canonical_age)
}

fn main() {
    let _ = ranges("1.0");
}
