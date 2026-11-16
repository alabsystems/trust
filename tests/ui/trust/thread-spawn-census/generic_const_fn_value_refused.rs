//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a `const` / `static` / associated `const` / inline `const`
//! whose VALUE a still-generic `const fn` computes. The initializer only calls
//! `pick_go::<S>()` / `erase(&S)`; the callable (`<S as Go>::go`, or `S`'s
//! `dyn Go` vtable) is named inside the generic body, per instance. W11 never
//! evaluated an initializer and could not enumerate these values, so it
//! refused every read as an UNKNOWN, in the spawning AND the quiet revision.
//! Since P2 (design 2026-09-29-spawn-census-by-construction §5.3) the value
//! node's initializer is walked per instance (a compile-time call is a READ of
//! the callee instance, `pick_go::<S>`, whose reification is a CREATE), so
//! every read is exact: an ESCAPES row ("const or static read here holds a
//! callable") in `spawning`, and no row at all in `quiet`, whose impl is
//! spawn-free.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

pub trait Go {
    fn go(&self);
}
pub struct S;
impl Go for S {
    fn go(&self) { launch() } //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
}

pub const fn pick_go<T: Go>() -> fn(&T) { T::go } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called
pub const fn erase<T: Go + 'static>(t: &'static T) -> &'static dyn Go { t } //[spawning]~ NOTE callable made into a fn pointer or `dyn` value here reaches a std thread spawn when called

pub const PG: fn(&S) = pick_go::<S>();
pub static PS: fn(&S) = pick_go::<S>();
pub const ED: &dyn Go = erase(&S);
pub static TABLE: [fn(&S); 2] = [pick_go::<S>(), pick_go::<S>()];

pub struct Holder;
impl Holder {
    pub const ASSOC: fn(&S) = pick_go::<S>();
}

// A static whose initializer only names another static: the walk follows it.
pub static OUTER: &fn(&S) = &PS;

pub fn const_generic_method() { PG(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn static_generic_method() { PS(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn const_erased_by_generic_const_fn() { ED.go() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn static_table() { TABLE[1](&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn assoc_const() { Holder::ASSOC(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn inline_const() { (const { pick_go::<S>() })(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn nested_static() { (*OUTER)(&S) } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn
pub fn caller() { const_generic_method() } //[spawning]~ NOTE callee names, erases or reads a callable that reaches a std thread spawn

// A const whose value is computed by a NON-generic call returning a
// non-callable type is no edge at all: nothing to enumerate, no row.
pub const fn size_of_go<T: Go>() -> usize { core::mem::size_of::<fn(&T)>() }
pub const SIZE: usize = size_of_go::<S>();
pub fn reads_size() -> usize { SIZE }
