//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Zalways-encode-mir
//@ no-prefer-dynamic
//! `xcrate_fmt_dep.rs`'s `Good`, built VERIFY-ON: its own compilation proves it.
//! A consumer must still grant it nothing unless it is DECLARED and re-derived
//! (`xcrate_fmt_dep.rs`, revisions `on_undeclared` and `on_declared`): the
//! dependency's own verification is never read (D4 — no rmeta bit).
#![crate_name = "xcfmt_dep_on"]
use std::fmt;

pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
