//@ trust-ladder-dep-flags: -Ztrust-verify=off
//! A verify-off DEPENDENCY whose `Debug` impl panics. Built the way `targo`
//! builds a dependency unit (`-Ztrust-verify=off`, encoded MIR), because a
//! verifying build of it would refuse. `user_fmt_dep_bad_declared` must refuse:
//! declaring the crate re-derives the impl here (D4-A), and the re-derivation
//! finds the panic.
#![crate_name = "libdbad"]
use core::fmt;
pub struct D;
impl fmt::Debug for D {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result { panic!("boom") }
}
