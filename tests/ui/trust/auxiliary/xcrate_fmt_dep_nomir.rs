//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ no-prefer-dynamic
//! `xcrate_fmt_dep.rs`'s `Good`, built WITHOUT `-Zalways-encode-mir`: there is
//! no body to re-derive, so declaring the crate must buy nothing
//! (`xcrate_fmt_dep.rs`, revision `nomir`).
#![crate_name = "xcfmt_dep_nomir"]
use std::fmt;

pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
