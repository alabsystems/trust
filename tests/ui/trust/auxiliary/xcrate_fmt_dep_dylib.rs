//@ compile-flags: -Ztrust-verify=off -Zalways-encode-mir
//! `xcrate_fmt_dep.rs`'s `Good`, built as a DYLIB: this aux deliberately omits
//! `no-prefer-dynamic`, so compiletest compiles it `--crate-type dylib -C
//! prefer-dynamic`. A dynamic library is loaded at run time, and the one that
//! loads need not be the one whose MIR a consumer re-derived, so declaring this
//! crate must buy nothing (`xcrate_rederivation_dylib.rs`, revision
//! `dylib_declared`). `-Zalways-encode-mir` is present so the refusal cannot be
//! the missing-MIR one.
#![crate_name = "xcfmt_dylib"]
use std::fmt;

pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
