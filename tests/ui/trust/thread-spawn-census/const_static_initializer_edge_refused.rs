//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 2): a spawning callable stored in a `const` or
//! `static` initializer. CTFE never spawns, but the VALUE it computes can hold
//! a callable that does, and the body that reads the item calls it. Before
//! W11, const/static bodies were excluded from the census node set ("CTFE
//! cannot spawn a thread") and a read of the item was no edge, so every shape
//! below carried NO `UnmodeledThreadSpawnEffect` row; W11 refused every read
//! as an UNKNOWN ("callable value produced by const evaluation is not
//! enumerated"). Since P2 (design 2026-09-29-spawn-census-by-construction
//! §5.3) a read is a READ edge to the item's value node, whose facts are its
//! initializer's MIR (`mir_for_ctfe`, promoteds) and its evaluated
//! allocation; a callable in it is a CREATE. Every read below is an ESCAPES
//! row ("const or static read here holds a callable"), also when the const is
//! called directly (`HOOK()`), never a spawn claim. The closures inside the
//! initializers are bodies of their own (S2 rows on their lines). Every
//! fn-pointer call of shape `fn()` in the crate is INDIRECT, because the
//! `fn()` pool holds `launch` (`quiet_const`; design §7). `quiet` is the same
//! shapes with a spawn-free `launch` and no std spawn value: no row.

#![allow(dead_code)]

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

fn noop() {}

const HOOK: fn() = launch;
pub fn const_fn_ptr() { HOOK() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

// A const whose initializer is another const: an edge through the chain.
const HOOK_ALIAS: fn() = HOOK;
pub fn const_alias() { HOOK_ALIAS() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

// A TRIVIAL const (`_0 = const V`) has no `mir_for_ctfe`; the census reads its
// value instead (this used to be a debug-assertion ICE in the census).
const LIMIT: usize = 3;
pub fn trivial_const() -> usize { LIMIT }

static SHOOK: fn() = launch;
pub fn static_fn_ptr() { SHOOK() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

#[cfg(spawning)]
const SPAWN: fn(fn()) -> std::thread::JoinHandle<()> = std::thread::spawn::<fn(), ()>;
#[cfg(quiet)]
const SPAWN: fn(fn()) -> () = |f| f();
pub fn const_std_spawn_ptr() { let _ = SPAWN(noop); } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

const CLOSURE: fn() = || launch(); //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
pub fn const_closure_ptr() { CLOSURE() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

const DYN: &dyn Fn() = &launch;
pub fn const_dyn() { DYN() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

const TABLE: [fn(); 2] = [noop, launch];
pub fn const_table(i: usize) { TABLE[i]() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

struct Vtable {
    f: fn(),
}
const VTABLE: Vtable = Vtable { f: launch };
pub fn const_struct() { (VTABLE.f)() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

const fn pick() -> fn() {
    launch
}
const PICKED: fn() = pick();
pub fn const_via_const_fn() { PICKED() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

static DYN_STATIC: &(dyn Fn() + Sync) = &|| launch(); //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops
pub fn static_dyn() { DYN_STATIC() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

struct Hooks;
impl Hooks {
    const HOOK: fn() = launch;
}
pub fn assoc_const() { Hooks::HOOK() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

pub fn inline_const() { (const { launch as fn() })() } //[spawning]~ NOTE const or static read here holds a callable that reaches a std thread spawn

// A quiet const in the spawning revision: its read is no row, but its call is
// an indirect call of shape `fn()`, whose pool holds `launch`.
const QUIET: fn() = noop;
pub fn quiet_const() { QUIET() } //[spawning]~ NOTE may spawn (indirect): an indirect call
