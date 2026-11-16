//@ revisions: default certify
//@ needs-trust-verify
//@ edition: 2021
//@[default] compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//! The control for `cow_with_user_to_owned_is_not_total.rs`: a `Cow` whose borrowed
//! type takes only sysroot `ToOwned` impls (`str`, and a derived-`Clone` local type
//! through the blanket `T: Clone` impl, whose `Borrow` is the identity) still
//! compares through the total sentinel.

use std::borrow::Cow;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct K(pub u8);
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct S<'a> {
    pub name: Cow<'a, str>,
    pub key: Cow<'a, K>,
}
pub fn s_eq(a: &S, b: &S) -> bool { a == b }
pub fn s_lt(a: &S, b: &S) -> bool { a < b }
