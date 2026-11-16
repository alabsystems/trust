//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! An honest dependency (no crate-name forgery) with its own type named `Option`.
//! The defaulted type parameter makes rustc render the method WITHOUT generic
//! arguments, `option_as_deref_dep::Option::as_deref`, which is the spelling the
//! deleted `Option::as_deref` sentinel arm accepted (EXTRACT-REWRITE-1). Built with
//! verification off, as `targo` builds every dependency, so the body is absent from
//! the caller's bundle.

pub struct Option<T = Box<u8>>(pub T);

impl<T> Option<T> {
    #[inline(never)]
    pub fn as_deref(&self) -> u8 {
        panic!("user Option::as_deref panics")
    }
}
