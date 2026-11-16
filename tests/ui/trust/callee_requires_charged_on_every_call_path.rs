//@ revisions: clone eq fn_ptr trait_item_ptr assoc_ptr dyn_item_ptr extern_alias_ptr user_trait inherent
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! A callee proved under its own `requires` is sound only if every caller
//! establishes that precondition. Each revision's callee PROVES on its own root
//! (the precondition bounds its index), so the only thing that can fail the build
//! is the unguarded CALLER, which calls it with `self.0` / `x` up to 255.
//!
//! Measured on the stage-1 build of `a449d93d255`, BEFORE the fix: `clone`, `eq`
//! and `fn_ptr` built rc=0 under certify with no diagnostic at all, and the
//! caller panics on input 15 (index out of bounds). vcgen took a trait-method
//! call's contract from the trait's DECLARATION, never the impl
//! (`add_direct_call_contract_summaries`), and the two paths charged no panic
//! carrier either (`resolve_local_trait_impl`'s arm; the reified-pointer
//! carve-out of the indirect-call gate). `user_trait` and `inherent` were already
//! refused and are the controls. docs/KNOWN_HAZARDS.md, OPEN 2026-09-30.
//!
//! `trait_item_ptr` / `assoc_ptr`: the first fix checked the `requires` of the
//! pointer's FUNCTION ITEM, which for `<S as Tr>::m` or `S::m` is the trait's
//! declaration, never the impl that runs; the review of 2026-09-30 certified both
//! and saw `c(&S(15))` panic. The item is now resolved to its impl first.
//!
//! `dyn_item_ptr`: `<dyn Tr as Tr>::m` resolves to a VIRTUAL instance whose def_id
//! is the declaration again; review round 17 certified it. Only an `Item` counts.
//!
//! `extern_alias_ptr`: a local `extern` block item `#[link_name]`-bound to a
//! `requires`-bearing `#[no_mangle]` fn has no body of its own; review round 18
//! certified a pointer reified from it. A foreign item is never its own root.

#[cfg(clone)]
pub struct K(pub u8);
#[cfg(clone)]
impl Clone for K {
    fn clone(&self) -> Self
        requires self.0 < 10
    {
        let t = [0u8; 10];
        K(t[self.0 as usize])
    }
}
#[cfg(clone)]
pub fn caller(a: &K) -> u8 { a.clone().0 } //[clone]~ ERROR verification failed

#[cfg(eq)]
pub struct K(pub u8);
#[cfg(eq)]
impl PartialEq for K {
    fn eq(&self, o: &Self) -> bool
        requires self.0 < 10
    {
        let t = [0u8; 10];
        t[self.0 as usize] == o.0
    }
}
#[cfg(eq)]
pub fn caller(a: K, b: K) -> bool { a == b } //[eq]~ ERROR verification failed

#[cfg(fn_ptr)]
fn g(x: u8) -> u8
    requires x < 10
{
    let t = [0u8; 10];
    t[x as usize]
}
#[cfg(fn_ptr)]
pub fn caller(x: u8) -> u8 { let f: fn(u8) -> u8 = g; f(x) } //[fn_ptr]~ ERROR verification failed

#[cfg(any(trait_item_ptr, assoc_ptr, dyn_item_ptr))]
pub trait Tr {
    fn m(&self) -> u8;
}
#[cfg(any(trait_item_ptr, assoc_ptr, dyn_item_ptr))]
pub struct S(pub u8);
#[cfg(any(trait_item_ptr, assoc_ptr, dyn_item_ptr))]
impl Tr for S {
    fn m(&self) -> u8
        requires self.0 < 10
    {
        let t = [0u8; 10];
        t[self.0 as usize]
    }
}
#[cfg(trait_item_ptr)]
pub fn caller(a: &S) -> u8 { let f: fn(&S) -> u8 = <S as Tr>::m; f(a) } //[trait_item_ptr]~ ERROR verification failed
#[cfg(assoc_ptr)]
pub fn caller(a: &S) -> u8 { let f: fn(&S) -> u8 = S::m; f(a) } //[assoc_ptr]~ ERROR verification failed
#[cfg(dyn_item_ptr)]
pub fn caller(d: &'static dyn Tr) -> u8 { let f: fn(&'static dyn Tr) -> u8 = <dyn Tr as Tr>::m; f(d) } //[dyn_item_ptr]~ ERROR verification failed

#[cfg(extern_alias_ptr)]
static T: [u8; 10] = [0; 10];
#[cfg(extern_alias_ptr)]
#[no_mangle]
pub fn g2(x: u8) -> u8
    requires x < 10
{
    T[x as usize]
}
#[cfg(extern_alias_ptr)]
unsafe extern "Rust" {
    #[link_name = "g2"]
    safe fn h(x: u8) -> u8;
}
#[cfg(extern_alias_ptr)]
pub fn caller(x: u8) -> u8 { let f: fn(u8) -> u8 = h; f(x) } //[extern_alias_ptr]~ ERROR verification failed

#[cfg(user_trait)]
pub trait Tr {
    fn m(&self) -> u8;
}
#[cfg(user_trait)]
pub struct S(pub u8);
#[cfg(user_trait)]
impl Tr for S {
    fn m(&self) -> u8
        requires self.0 < 10
    {
        let t = [0u8; 10];
        t[self.0 as usize]
    }
}
#[cfg(user_trait)]
pub fn caller(s: &S) -> u8 { s.m() } //[user_trait]~ ERROR verification failed

#[cfg(inherent)]
pub struct S(pub u8);
#[cfg(inherent)]
impl S {
    pub fn m(&self) -> u8
        requires self.0 < 10
    {
        let t = [0u8; 10];
        t[self.0 as usize]
    }
}
#[cfg(inherent)]
pub fn caller(s: &S) -> u8 { s.m() } //[inherent]~ ERROR verification failed
