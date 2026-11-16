//@ needs-trust-verify
//@ revisions: verified off
//@[verified] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off -Ztrust-send-census --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A blanket impl whose method calls itself at a larger type. Nothing here
//! is ever instantiated that deep, and the program is valid. The spawn census
//! walks every body at the instances its calls name:
//!
//! - `Deep`: one call, one level larger. Resolving the instance one level
//!   under the recursion limit asks rustc for `T: Clone` at a type past it,
//!   and rustc answers with E0275: a valid program was REJECTED, in the
//!   verified lane with no flag too. The walk now stops short of that.
//! - `Wide`: two calls, at `(T, u8)` and at `[T; 1]`. No type doubles, so no
//!   size limit ends it: a tree of 2^128 instances of one body. One body is
//!   read at no more than a fixed number of instances.

pub trait Deep {
    fn deep(&self, n: u32);
}

impl<T: Clone> Deep for T {
    fn deep(&self, n: u32) {
        if n > 0 {
            (self.clone(), 0u8).deep(n - 1);
        }
    }
}

pub trait Wide {
    fn wide(&self, n: u32);
}

impl<T: Clone> Wide for T {
    fn wide(&self, n: u32) {
        if n > 0 {
            (self.clone(), 0u8).wide(n - 1);
            [self.clone()].wide(n - 1);
        }
    }
}
