//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! A verify-off DEPENDENCY whose `Debug` impl is PANIC-FREE but returns
//! `Err(fmt::Error)`: `println!` of it panics inside std (the F1 class,
//! cross-crate). `user_fmt_dep_err_declared` must refuse on error transparency
//! even though the re-derived impl passes the panic-freedom bar.
#![crate_name = "libderr"]
use core::fmt;
pub struct D;
impl fmt::Debug for D {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { Err(fmt::Error) }
}
