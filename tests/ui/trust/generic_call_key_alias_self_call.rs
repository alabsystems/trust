//@ revisions: wrapper blanket wrapper_decreases blanket_decreases two_params lifetime
//@ revisions: inherent concrete
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! GCKA-SELF-CALL-2 (2026-10-10): a generic trait impl's direct call to ITSELF is
//! a self call, and keeps its own body's key.
//!
//! GENERIC-CALL-KEY-ALIAS-1 tags a trait call whose arguments name a type
//! parameter and whose name is a local body's definition key
//! (`generic_call_key_alias_blanket_impl.rs`). Inside `impl<T> Depth for W<T>`,
//! `self.depth(n - 1)` prints `<W<T> as Depth>::depth`, the body's OWN key, so it
//! was tagged too. The trust-ir bridge then no longer bound the call to its own
//! body: it became a generic absent callee, which the default policy treats as
//! fatal. A terminating, panic-free recursive method of every generic trait impl
//! and every blanket impl was refused. The names now take the caller, and a call
//! whose arguments are its caller's own identity arguments for the trait item
//! the caller implements keeps its name
//! (`trust_mir_extract::convert::identity_self_call_of_caller`).
//!
//! Revisions, one shape each, selected by `--cfg <revision>`, all default policy:
//! * `wrapper`: `impl<T> Depth for W<T>`, recursion with no annotation.
//! * `blanket`: `impl<T: Marker> Tr for T`, the same.
//! * `wrapper_decreases`, `blanket_decreases`: the same with `decreases n`.
//! * `two_params`: two impl parameters and a trait parameter, called through
//!   `<Self as Gen<G>>::g`.
//! * `lifetime`: an impl lifetime parameter, erased in the call.
//! * `inherent`, `concrete`: controls the tag never reached (an inherent call is
//!   its own `FnDef`; a concrete call resolves).
//!
//! BEFORE (this file, each revision's flags plus `--cfg <revision> -Zui-testing
//! -Zdeduplicate-diagnostics=no -A unused --emit=metadata`, measured 2026-10-10):
//! every revision except the two controls exits 1 on the wave-20 stage 1
//! `8f3584d2fe`, with `error: Trust strict verification failed` and "an unproved
//! assumption-panic row — a generic absent callee — keeps the function
//! fail-closed"; the row counts are main's. On main's stage 1, `912bbdf300`, every
//! revision exits 0 with `2 proved, 0 failed, 0 unknown, 0 timed out, 1
//! runtime-checked, 1 skipped out of 4` (the runtime-checked panic-freedom row of
//! the recursive call, which the bridge lowers as `RecursiveDirectCall`, tolerated
//! with the advisory WARN). The controls exit 0 on both (`concrete`: `2 proved, 1
//! runtime-checked out of 3`).
//!
//! AFTER (the stage 1 of this change): every revision exits 0, and its output is
//! main's line for line except the engine batch's `elapsed_ms`. The alias the tag
//! closes stays closed: `generic_call_key_alias_blanket_impl.rs` is unchanged.

#[cfg(any(wrapper, wrapper_decreases))]
pub struct W<T>(pub T);

#[cfg(any(wrapper, wrapper_decreases))]
pub trait Depth {
    fn depth(&self, n: u32) -> u32;
}

#[cfg(wrapper)]
impl<T> Depth for W<T> {
    fn depth(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { self.depth(n - 1) }
    }
}

#[cfg(wrapper_decreases)]
impl<T> Depth for W<T> {
    fn depth(&self, n: u32) -> u32
        decreases n
    {
        if n == 0 { 0 } else { self.depth(n - 1) }
    }
}

#[cfg(any(blanket, blanket_decreases))]
pub trait Marker {}

#[cfg(any(blanket, blanket_decreases))]
pub trait Tr {
    fn a(&self, n: u64) -> u64;
}

#[cfg(blanket)]
impl<T: Marker> Tr for T {
    fn a(&self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.a(n - 1) }
    }
}

#[cfg(blanket_decreases)]
impl<T: Marker> Tr for T {
    fn a(&self, n: u64) -> u64
        decreases n
    {
        if n == 0 { 0 } else { self.a(n - 1) }
    }
}

#[cfg(two_params)]
pub struct P<A, B>(pub A, pub B);

#[cfg(two_params)]
pub trait Gen<G> {
    fn g(&self, n: u32) -> u32;
}

#[cfg(two_params)]
impl<A, B, G> Gen<G> for P<A, B> {
    fn g(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { <Self as Gen<G>>::g(self, n - 1) }
    }
}

#[cfg(lifetime)]
pub struct R<'a, X>(pub &'a X);

#[cfg(lifetime)]
pub trait Walk {
    fn walk(&self, n: u32) -> u32;
}

#[cfg(lifetime)]
impl<'a, X> Walk for R<'a, X> {
    fn walk(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { self.walk(n - 1) }
    }
}

#[cfg(any(inherent, concrete))]
pub struct V<T>(pub T);

#[cfg(inherent)]
impl<T> V<T> {
    pub fn depth(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { self.depth(n - 1) }
    }
}

#[cfg(concrete)]
pub trait Depth {
    fn depth(&self, n: u32) -> u32;
}

#[cfg(concrete)]
impl Depth for V<u8> {
    fn depth(&self, n: u32) -> u32 {
        if n == 0 { 0 } else { self.depth(n - 1) }
    }
}
