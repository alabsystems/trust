//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (W11 round 3): a read of a TRAIT associated const whose value
//! is provided by a trait IMPL. The MIR constant names the trait's bodyless
//! declaration (`<S as Tr>::F` is `Const::Unevaluated { def: Tr::F, .. }`), so
//! the census once pushed an edge to the declaration only, never to the impl
//! const that holds `launch`: `<S as Tr>::F()`, `let h = S::F; h()` and a
//! `&'static dyn Fn()` impl const carried NO row (review probes n1.rs /
//! assoc.rs / more.rs, 2026-09-29). The read is resolved
//! (`Instance::try_resolve` in the reading body's typing environment) to the
//! impl const, a READ: an ESCAPES row ("const or static read here holds a
//! callable"), never a spawn claim. Since P2 (design
//! 2026-09-29-spawn-census-by-construction) a still-generic read resolves per
//! instance (`pick::<S>`, `generic_reader::<S>`), so `PICKED`, which W11 could
//! not enumerate (an UNKNOWN in both revisions), is exact: ESCAPES in
//! `spawning`, no row in `quiet`. Every call through a `fn()` pointer is
//! INDIRECT in `spawning` (the pool holds `launch`), `Q`'s quiet const
//! included. `quiet` is the same shapes with a spawn-free `launch`: no row.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

fn noop() {}

trait Tr {
    const F: fn();
}
struct S;
struct Q;
impl Tr for S {
    const F: fn() = launch;
}
impl Tr for Q {
    const F: fn() = noop;
}

pub fn assoc_override() { <S as Tr>::F() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

pub fn assoc_override_short() { let h = S::F; h() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

// The quiet impl of the same trait: resolution selects `Q`'s const, not `S`'s,
// so the read is no row; the call through the `fn()` pointer is INDIRECT.
pub fn assoc_override_quiet() { <Q as Tr>::F() } //[spawning]~ NOTE may spawn (indirect): an indirect call

trait Tdyn {
    const D: &'static dyn Fn();
}
impl Tdyn for S {
    const D: &'static dyn Fn() = &launch;
}
pub fn assoc_dyn() { (S::D)() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

// Still-generic: `T::F` selects no impl inside `pick`; its instance `pick::<S>`
// reads `S::F`, so `pick` (and the const it computes) reach `launch`.
const fn pick<T: Tr>() -> fn() { //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
    T::F
}
const PICKED: fn() = pick::<S>();
pub fn const_fn_generic() { PICKED() }
//[spawning]~^ NOTE const or static read here holds a callable that reaches a std thread spawn

fn generic_reader<T: Tr>() { T::F() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn generic_reader_caller() { generic_reader::<S>() } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn
