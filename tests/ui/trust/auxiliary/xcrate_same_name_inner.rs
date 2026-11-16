//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir
//@ compile-flags: -Cmetadata=inner -Cextra-filename=-inner
//@ no-prefer-dynamic
//! A crate NAMED `xcsame` that a consumer reaches only TRANSITIVELY, through
//! `xcrate_same_name_mid.rs`. Its own `-Cmetadata` gives it a different
//! `StableCrateId` from the `xcsame` the consumer binds with `--extern`
//! (`xcsame.rs`), and `-Cextra-filename` keeps the two artifacts apart on disk.
//! A declaration of the NAME `xcsame` must not cover this crate
//! (`xcrate_rederivation_identity.rs`, revision `same_name_transitive`). Its
//! `Good` is byte-identical to the bound twin's, so only identity differs.
#![crate_name = "xcsame"]
use std::fmt;

pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
