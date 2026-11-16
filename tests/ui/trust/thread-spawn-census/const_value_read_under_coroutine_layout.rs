//@ revisions: advisory default off spawning
//@ needs-trust-verify
//@ edition: 2021
//@[advisory] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[default] compile-flags: -Ztrust-verify=on -Ztrust-policy=strict --crate-type lib
//@[off] compile-flags: -Ztrust-verify=off --crate-type lib
//@[spawning] compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@[advisory] check-fail
//@[default] check-fail
//@[off] check-fail
//@[spawning] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output:E0391
//@ forbid-output: cycle detected
//@ forbid-output: recursion in an async fn
//! Drop-in (release gate): a `const` whose PATTERN needs the layout of an
//! `async fn`'s future, read (as a callable) by a fn. Review of 638784cafa,
//! probes k01 / k05 / k07 (2026-09-29): stock rustc, `-Ztrust-verify=off` and
//! `origin/main` accepted these crates; the census turned each into E0391 (or
//! E0733) under `-Ztrust-verify=on` AND under the shipping default.
//!
//! Stock 1.101 rejects the `K::N` patterns themselves with E0158 (measured
//! 2026-10-17 on a stage1 built from the bf9448e4 pin tree; same upstream
//! regression as async-layout-no-cycle/const_pattern_in_body, recorded in
//! docs/DECISION_QUEUE.md). Drop-in is matching stock: every lane now fails
//! with that stock error at each pattern site — and still never with a cycle,
//! and the census/strict diagnostics below are still emitted.
//!
//! How: `run_required_analyses` checks each coroutine's layout right after its
//! borrowck (`layout_of`), which demands the coroutine's `optimized_mir` and
//! forces the census. The census then reached the value node `F` (read by
//! `reads_*` at a callable type) and built its MIR: `trivial_const` ->
//! `mir_built` -> `check_match` evaluates `K::N = size_of_ret(&work)`, whose
//! layout computation needs `optimized_mir(work::{closure#0})` — already on the
//! stack. W11 then read a value node under a `layout_of` only when its own MIR
//! pipeline had already completed, and declined `F` as an unknown.
//!
//! Since the async-layout change (2026-09-29, ported onto this census
//! 2026-09-30) that route is closed under verification: a coroutine's layout is
//! read from its pre-steal elaborated MIR (`trust_local_coroutine_layout`) and
//! the census is forced at the analysis seam, where no query is active, so it
//! no longer runs under a `layout_of`. Since P2 (design
//! 2026-09-29-spawn-census-by-construction) the census has no value-read
//! fallback at all (`CompletedOnly` is gone): it reads every value node. The
//! coroutine's errors are no longer emitted inside `run_required_analyses`
//! either, so they no longer cut the whole-crate walk short: the four
//! `reads_*` functions are now verified, and the shipping default refuses
//! each for its unresolved indirect call (as it does in a crate with no
//! `async` body at all).
//!
//! * `k05`: a generic inherent const `G<T>::F`, read by `reads::<T>`;
//! * `k01`: a trait impl const `<S as Tr>::F`, read through `X::F`;
//! * `k07`: a trait default const `Tr2::F`, read through `X::F`.
//!
//! `default` states the shipping default: it refuses the async body and the
//! four `reads_*` functions (Trust refusals, which drop-in permits) and nothing
//! else reports an error; `advisory` and `off` compile. `spawning` makes `one`
//! spawn and pins what the census says, never a spawn claim and never a
//! cycle: a read whose value it resolves is an ESCAPES row ("const or static
//! read here holds a callable"; `EARLY`, `G::<T>::F`), and a read through the
//! fn's own type parameter (`X::F`, R1) is no row, but the call through the
//! `fn()` pointer it yields is INDIRECT (the pool holds `one`).

#![allow(dead_code)]

#[cfg(not(spawning))]
fn one() {}

#[cfg(spawning)]
fn one() {
    let _handle = std::thread::spawn(|| {});
}

fn two() {}

pub const EARLY: fn() = one;

pub fn reads_early() {
    EARLY()
}

pub async fn work() -> u8 { //[default]~ ERROR Trust strict verification failed
    1
}

pub const fn size_of_ret<F: Fn() -> R, R>(_: &F) -> usize {
    core::mem::size_of::<R>()
}

pub struct K;
impl K {
    pub const N: usize = size_of_ret(&work);
}

// k05
pub struct G<T>(T);
impl<T> G<T> {
    pub const F: fn() = match 8usize {
        K::N => one,
        //~^ ERROR constant pattern cannot depend on generic parameters
        _ => two,
    };
}
pub fn reads<T>() {
    (G::<T>::F)()
}

// k01
pub struct S;
pub trait Tr {
    const F: fn();
}
impl Tr for S {
    const F: fn() = match 8usize {
        K::N => one,
        //~^ ERROR constant pattern cannot depend on generic parameters
        _ => two,
    };
}
pub fn reads_impl<X: Tr>() {
    (X::F)()
}

// k07
pub trait Tr2 {
    const F: fn() = match 8usize {
        K::N => one,
        //~^ ERROR constant pattern cannot depend on generic parameters
        _ => two,
    };
}
pub struct S2;
impl Tr2 for S2 {}
pub fn reads_default<X: Tr2>() {
    (X::F)()
}
