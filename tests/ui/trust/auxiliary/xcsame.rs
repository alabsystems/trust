//@ compile-flags: --crate-type=rlib -Ztrust-verify=off -Zalways-encode-mir -Cmetadata=bound
//@ no-prefer-dynamic
//! The `xcsame` a consumer BINDS (`aux-crate:xcsame=xcsame.rs`, i.e. an exact
//! `--extern xcsame=<path>`), next to a different crate of the same name that
//! arrives transitively (`xcrate_same_name_inner.rs`). A declaration of the name
//! `xcsame` covers THIS crate only (`xcrate_rederivation_identity.rs`). The file
//! is named after the crate because `aux-crate` derives the artifact path from
//! the file name.
#![crate_name = "xcsame"]
use std::fmt;

pub struct Good;
impl fmt::Debug for Good {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}
