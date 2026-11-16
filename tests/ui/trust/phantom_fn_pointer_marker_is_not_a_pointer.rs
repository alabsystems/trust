//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! `core::iter::Empty<T>` is `PhantomData<fn() -> T>`: a variance marker with no
//! field and no pointer, so no function is reachable through it. The type walks
//! treated its `fn` pointer type argument as a stored pointer into user code and
//! refused `empty::<u32>().max()` as not vanilla (sweep `w13`); they now judge a
//! `PhantomData` fn-pointer argument by its signature types. The twin `_refused.rs`
//! keeps a real fn pointer, carried by `Map`, refused.
pub fn empty_max() -> Option<u32> {
    core::iter::empty::<u32>().max()
}
