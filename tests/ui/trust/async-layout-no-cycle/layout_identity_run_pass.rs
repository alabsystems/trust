//@ revisions: off adv
//@ edition: 2021
//@ run-pass
//@[off] compile-flags: -Ztrust-verify=off
//@[adv] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ forbid-output: E0391
//@ forbid-output: E0733
//@ forbid-output: cycle detected
//! Layout identity: the size the TYPE SYSTEM computes for a future (`N`, a
//! const evaluated from the coroutine's layout — pre-steal elaborated MIR under
//! verification, `trust_local_coroutine_layout`) is the size of the value the
//! program builds (the optimized, codegened coroutine). The coroutine holds a
//! `String` across an `.await`, so its layout has a real saved local.
//! `inner_optimized_mir` also `bug!`s if the two layouts ever differ.

#![allow(dead_code)]

const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize {
    core::mem::size_of::<R>()
}

async fn ready() {}

async fn work() -> usize {
    let s = String::from("held across an await");
    ready().await;
    s.len()
}

const N: usize = size_of_ret(&work);

fn sized() -> [u8; N] {
    // `[7; N]` would not type-check even on stock rustc: a repeat count inside a
    // body is not evaluated eagerly (E0308 "found one with a size of N").
    core::array::from_fn(|_| 7)
}

fn main() {
    let fut = work();
    assert_eq!(core::mem::size_of_val(&fut), N);
    assert!(N >= core::mem::size_of::<String>());
    assert_eq!(sized().len(), N);
    drop(fut);
}
