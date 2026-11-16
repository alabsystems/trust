//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: callee reaches a std thread spawn through calls and drops
//@ forbid-output: const or static read here holds
//@ forbid-output: callable made into a fn pointer
//@ forbid-output: not enumerated (no spawn was found)
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! W11 spawn census, round 4 (precision): a TRAIT default that spawns,
//! OVERRIDDEN by a quiet impl item, is not what a read or naming of the impl
//! item runs. The census kept the trait DECLARATION as an edge beside the impl
//! item resolution selected (`Collector::const_item` always pushed it, "its
//! default"; `Collector::mention` pushed the trait `FnDef`'s own `DefId`; a
//! direct call's targets were `[callee, resolved]`), so `<Q as Tr>::F()`,
//! `let f: fn(&Q) = <Q as Go>::go`, `Some(&Q).map(Q::go)`, `Q.go()` and every
//! caller of them were refused as spawning though none can (review probe
//! q1.rs, 2026-09-29). The declaration is now an edge only when resolution
//! fails or selects the default itself (`trait_default_used_refused.rs`).
//! In `spawning` the defaults' own direct spawns are the only SPAWNS rows, and
//! no read, reification or call of `Q`'s items claims a spawn or escapes.
//! Since P2 (design 2026-09-29-spawn-census-by-construction §5.4, §7) the
//! default const's closure is a member of the `fn()` pool all the same (its
//! initializer mints it), so every call through a `fn()` pointer is INDIRECT:
//! `<Q as Tr>::F()`, `h()` and their callers, though `Q::F` holds `noop`. That
//! is the design's precision cost, without confinement; a `fn(&Q)` call is not
//! in that pool and carries no row.

#![allow(dead_code)]

fn noop() {}

trait Tr {
    #[cfg(spawning)]
    const F: fn() = || { let _h = std::thread::spawn(|| {}); }; //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    #[cfg(quiet)]
    const F: fn() = noop;
}

trait Go {
    #[cfg(spawning)]
    fn go(&self) { let _h = std::thread::spawn(|| {}); } //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    #[cfg(quiet)]
    fn go(&self) {}
}

pub struct Q;
impl Tr for Q {
    const F: fn() = noop;
}
impl Go for Q {
    fn go(&self) {}
}

pub fn const_default_overridden() { <Q as Tr>::F() } //[spawning]~ NOTE may spawn (indirect): an indirect call
pub fn const_default_overridden_short() { let h = Q::F; h() } //[spawning]~ NOTE may spawn (indirect): an indirect call
pub fn method_default_overridden_value() { let f: fn(&Q) = <Q as Go>::go; f(&Q) }
pub fn method_default_overridden_map() -> Option<()> { Some(&Q).map(Q::go) }
pub fn method_default_overridden_call() { Q.go() }
pub fn method_default_overridden_ufcs() { <Q as Go>::go(&Q) }
pub fn caller_of_quiet_const() { const_default_overridden() } //[spawning]~ NOTE may spawn (indirect): the callee, value or callable here reaches an indirect call
pub fn caller_of_quiet_value() { method_default_overridden_value() }
pub fn caller_of_quiet_call() { method_default_overridden_call() }
