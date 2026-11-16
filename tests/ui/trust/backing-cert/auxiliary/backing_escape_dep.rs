//@ compile-flags: --crate-type=rlib -Ztrust-verify=off
//@ edition: 2021
//@ no-prefer-dynamic
//! A dependency outside the sysroot. Its bodies are not in the certifying crate's
//! inventory, so what it does with a value it is handed is unverified. `touch`
//! receives `&mut T` (a mutable path to the struct — denied), while `consume` takes
//! `T` by value (ownership transfers away) and `borrow` takes `&T` (read only);
//! those two are sound to allow, matching the task's `*mut`/`&mut`-only boundary.

pub fn touch<T>(x: &mut T) -> &mut T {
    x
}

pub fn consume<T>(x: T) -> usize {
    drop(x);
    1
}

pub fn borrow<T>(x: &T) -> usize {
    core::mem::size_of_val(x)
}
