//@ revisions: effects borrowed
//@ needs-trust-verify
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory --crate-type=lib
//@ dont-check-compiler-stderr
//@ edition: 2021
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! A body whose trust-ir never runs a destructor rustc's MIR runs must FAIL
//! `-Ztrust-ir-lower=strict`, named `Abstracted(drop, ..)`.
//!
//! The direct producer emits no `Inst::Drop` (plan step 2 increment 4 adds them), so a body that
//! drops a value with a destructor was spliced, codegen-licensed and strict-clean with the drop
//! gone: `guard_scope` below was spliced as `ret`, and the 2026-10-01 review linked a program in
//! which `consume`'s `Fd::drop` never ran (`drops observed = 0 (1 = correct)`). Strict read only
//! the producer's tag list, and these bodies carry no tag. Measured on this tree before the
//! effect-conservation gate: this file compiled under strict with exit 0.
//!
//! The gate (`trust_thir_lower::effect_conservation`) compares each body's effects with rustc's
//! own built MIR. A `Drop` terminator on a value that is not moved-out on every path is an effect;
//! the trust-ir carries none, so the body is tagged and refused. A value the body moves on (into
//! `mem::drop`, a call, the return value) is not dropped here, and those bodies stay clean.
//! `tests/run-make/trust-effect-conservation` pins the same verdicts in the dump's sidecar, the
//! F1 codegen refusal and probe channel C.
//!
//! Step 2 increment 4b (the producer emits drops, `crates/trust-thir-lower/src/drops.rs`):
//! `guard_scope` and `consume` now carry their `Inst::Drop`, the gate finds them equal to rustc's
//! drop elaboration, and they compile (with the other placed shapes, in
//! `trust_ir_lower_drops_placed.rs`). What stays refused here is what the producer does not place
//! yet, each for the reason the gate's detail names: a partial move whose OPEN drop still drops
//! part of the value (`take_a`: dropping the rest of `self` drops `b`), and coroutines
//! (`env_guard`, `env_copy`).
//!
//! Step 2 increment 4b residuals: the drop-and-replace through `&mut` (`guard_overwrite`) is placed
//! — the old `Guard` dropped through `slot` before the store — and compiles (with the other
//! residual shapes, in `trust_ir_lower_drops_placed_residuals.rs`).
//!
//! The 4b residuals review (2026-10-08): a borrowed temporary is dropped through the object's
//! home only where the placement PROVES the program reaches it nowhere else (DROPS-RES-5).
//! `temp_in_pair` stores the borrow's address into a tuple, where the proof cannot follow it, and
//! its `Counter` is not `Freeze` (a copy is not the same drop): its drops stay elided, refused
//! naming why (`a borrowed temporary's object is unproved`).
//!
//! Keep the early borrowed-temporary refusal in its own revision: an error while
//! building that body can preempt the later crate-finalization oracle checks.
//! The effects revision must independently reach and test those final checks.

unsafe extern "C" {
    fn close(fd: i32) -> i32;
}

pub struct Guard(pub i32);

impl Drop for Guard {
    fn drop(&mut self) {
        unsafe { close(self.0) };
    }
}

/// `let _g = Guard(fd);` — `Guard::drop` runs at the end of the scope. Since step 2 increment
/// 4b the trust-ir runs it too: clean.
pub fn guard_scope(fd: i32) {
    let _g = Guard(fd);
}

/// The caller hands over ownership; the callee closes it on return. Placed since 4b: clean.
pub fn consume(_f: Guard) {}

/// Overwriting a `Guard` through `&mut` drops the old one first. Placed since the 4b residuals:
/// clean.
pub fn guard_overwrite(slot: &mut Guard, fd: i32) {
    *slot = Guard(fd);
}

/// MOVED into `mem::drop`: the drop is inside that call, which the trust-ir carries. Clean.
pub fn guard_explicit_drop(fd: i32) {
    let g = Guard(fd);
    drop(g);
}

pub struct Pair {
    pub held: Guard,
    pub n: u32,
}

impl Pair {
    /// aterm-uds `Lifeline::cut`'s shape: the one field that needs dropping is MOVED into
    /// `mem::drop`, so dropping what is left of `self` runs nothing. Clean (a whole-local drop
    /// census called this a lost drop until the field-level analysis).
    pub fn cut(self) {
        drop(self.held);
    }
}

pub struct Two {
    pub a: Guard,
    pub b: Guard,
}

#[cfg(effects)]
impl Two {
    /// Moves `a` out; `b`'s `Guard::drop` still runs when `self` goes away.
    pub fn take_a(self) {
        //[effects]~^ ERROR the effect-conservation check refused it against the built MIR
        drop(self.a);
    }
}

/// A coroutine body's drop of its OWN env (`drop(_1)`) runs its upvars' drop glue: `g` is
/// captured by move and only borrowed, so `Guard::drop` runs when the block completes. The block's
/// body is refused; so is `env_guard`, which drops the coroutine VALUE `_f` (a coroutine's drop
/// glue depends on its state, which nothing here can compute).
#[cfg(effects)]
pub fn env_guard(g: Guard) {
    //[effects]~^ ERROR the effect-conservation check refused it against the built MIR
    let _f = async move {
        //[effects]~^ ERROR the effect-conservation check refused it against the built MIR
        let _r = &g;
    };
}

/// The same env drop over `Copy` upvars runs nothing: the async body stays clean (pinned also by
/// `trust_ir_lower_coroutine_upvar_env.rs`), and only the coroutine value's drop is refused.
#[cfg(effects)]
pub fn env_copy(n: u32) {
    //[effects]~^ ERROR the effect-conservation check refused it against the built MIR
    let _f = async move { n + 1 };
}

pub struct Counter {
    pub hits: std::cell::Cell<i32>,
}

impl Drop for Counter {
    fn drop(&mut self) {
        unsafe { close(self.hits.get()) };
    }
}

#[inline(never)]
pub fn mk_counter(fd: i32) -> Counter {
    Counter { hits: std::cell::Cell::new(fd) }
}

#[inline(never)]
pub fn bump(c: &Counter) -> i32 {
    c.hits.set(c.hits.get() + 1);
    0
}

/// The borrow's address goes into a tuple the placement does not follow: unproved, refused.
#[cfg(borrowed)]
pub fn temp_in_pair(fd: i32) -> i32 {
    //[borrowed]~^ ERROR Borrow(owned temporary home unproved)
    let g = &mk_counter(fd);
    let p = (g, 1);
    bump(p.0)
}
