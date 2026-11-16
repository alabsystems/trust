//@ revisions: eq cmp clone
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! `Cow<'_, L>` with a user `impl ToOwned for L` runs the user's
//! `<M as Borrow<L>>::borrow` in its `Deref` (so in `eq`/`cmp`) and in `clone`.
//! Review round 23 (2026-10-01) measured a derived `PartialEq`/`Ord` over such a
//! field rewritten to the total sentinel: the crate certified (rc=0) while
//! `s_eq(Owned(M(L(1), 5)), Borrowed(&L(1)))` panicked on index 5 of a 1-element
//! table. A `Cow` is now a deep total container only when every `ToOwned` impl
//! that can apply to its borrowed type is a sysroot impl.

use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct L(pub u8);
pub struct M(pub L, pub u8);
impl Borrow<L> for M {
    fn borrow(&self) -> &L
        requires self.1 == 0
    {
        let t = [0u8; 1];
        let _ = t[self.1 as usize];
        &self.0
    }
}
impl ToOwned for L {
    type Owned = M;
    fn to_owned(&self) -> M { M(L(self.0), 0) }
}
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct S<'a> {
    pub c: Cow<'a, L>,
}
#[cfg(eq)]
pub fn s_eq(a: &S, b: &S) -> bool { a == b } //[eq]~ ERROR verification
#[cfg(cmp)]
pub fn s_cmp(a: &S, b: &S) -> Ordering { a.cmp(b) } //[cmp]~ ERROR verification
#[cfg(clone)]
pub fn s_clone<'a>(a: &S<'a>) -> S<'a> { a.clone() } //[clone]~ ERROR verification
