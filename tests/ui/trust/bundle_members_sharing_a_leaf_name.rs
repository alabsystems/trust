//@ needs-trust-verify
//@ edition: 2021
//@ revisions: methods free_fns swapped
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[methods] check-pass
//@[free_fns] check-pass
//@[swapped] check-fail
//! **Two bundle members with one leaf name (Trust, 2026-09-28).**
//!
//! A local bundle member is named by the extractor's bare leaf, and trust-ir
//! takes a function's name as its link symbol. So `A::new` and `B::new`, both
//! called from one root, made the native bundle invalid ("functions #1 and #2
//! share the link symbol \"new\""). Certify refused this correct program, and the
//! default lane left its asserts runtime-checked. A member whose name another
//! bundle function shares is now named by its `def_path`.
//!
//! * `methods`, `free_fns`: POSITIVE. Inherent `new` on two types; `get` in two
//!   modules.
//! * `swapped`: the NEGATIVE, annotated on `f`. It asserts `a::get()` returns
//!   `b::get()`'s value. It must stay refuted, which shows the two same-named
//!   bodies are not confused with each other.

#[cfg(methods)]
pub struct A(pub u64);
#[cfg(methods)]
pub struct B(pub u64);
#[cfg(methods)]
impl A {
    pub fn new(x: u64) -> A {
        A(x)
    }
}
#[cfg(methods)]
impl B {
    pub fn new(x: u64) -> B {
        B(x)
    }
}
#[cfg(methods)]
pub fn f() {
    let a = A::new(1);
    let b = B::new(2);
    assert!(a.0 == 1);
    assert!(b.0 == 2);
}

#[cfg(any(free_fns, swapped))]
mod a {
    pub fn get() -> u32 {
        0
    }
}
#[cfg(any(free_fns, swapped))]
mod b {
    pub fn get() -> u32 {
        1
    }
}

#[cfg(free_fns)]
pub fn f() {
    assert!(a::get() == 0);
    assert!(b::get() == 1);
}

#[cfg(swapped)]
pub fn f() {
    //[swapped]~^ ERROR Trust
    // Both calls, so both `get` bodies are members and share the leaf name.
    let x = a::get();
    let y = b::get();
    assert!(y == 1);
    assert!(x == 1);
}
