//@ needs-trust-verify
//@ edition: 2021
//@ revisions: len returned strings loud
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[len] check-pass
//@[returned] check-pass
//@[strings] check-pass
//@[loud] check-fail
//! **A `vec![a, b, c]` literal verifies under `certify` (Trust, 2026-09-28).**
//!
//! The list form of `vec!` expands to
//! `box_assume_init_into_vec_unsafe(write_box_via_move(Box::new_uninit(), [..]))`. The
//! helper is `(b.assume_init() as Box<[T]>).into_vec()`: it reinterprets the initialized
//! box as a `Vec` over the same allocation, and runs no `T` code and no panic path. Its body
//! does not lower (the `Box<[T; N]>` -> `Box<[T]>` `Unsize` coercion needs slice metadata),
//! so the call was an absent callee, and every `vec![..]` literal carried a may-panic
//! marker that `certify` refused. The helper is now on the audited `EXACT_TOTAL` list.
//!
//! * `len`, `returned`, `strings`: POSITIVE.
//! * `loud`: the NEGATIVE. The literal itself is still total, but dropping the `Vec`
//!   drops its elements, and `Loud::drop` panics. `f` must stay refused; the annotation on
//!   it discriminates. `Loud::drop` fails on its own as well, so unannotated errors are
//!   allowed.

#[cfg(len)]
pub fn f() -> usize {
    let v = vec![1u32, 2, 3];
    v.len()
}

#[cfg(returned)]
pub fn f() -> Vec<u32> {
    vec![1u32, 2, 3]
}

#[cfg(strings)]
pub fn f() -> Vec<String> {
    vec![String::new(), String::new()]
}

#[cfg(loud)]
pub struct Loud;

#[cfg(loud)]
impl Drop for Loud {
    fn drop(&mut self) {
        panic!("loud");
    }
}

#[cfg(loud)]
pub fn f() -> usize {
    //[loud]~^ ERROR Trust Level 0 safety verification incomplete for `vec_literal_helper_is_total::f`
    let v = vec![Loud, Loud];
    v.len()
}
