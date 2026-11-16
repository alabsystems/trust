//@ needs-trust-verify
//@ edition: 2021
//@ revisions: proc_macro_punct proc_macro_ident rustc_private_hashbrown condvar_two_mutexes mutex_lock_over_refusal
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@ check-fail
//! W4 HASHMAP (2026-09-25, redo) — only `hashbrown` joins the policy-B vanilla
//! class, and only by STRUCTURAL identity: the crate that defines the ADT std's
//! `HashMap`/`HashSet` field is declared as. Sysroot RESIDENCY, and being one of
//! the crates std is built from, are NOT enough.
//!
//! EVERY REVISION MUST STAY REFUSED. Fix the compiler, never this file.
//!
//!   * `proc_macro_punct` / `proc_macro_ident` — `proc_macro` is resident in the
//!     compiler's own library directory and is not std's table crate:
//!     `Punct::new` panics on an unsupported character, `Ident::new` on an
//!     invalid identifier.
//!   * `rustc_private_hashbrown` — the sysroot's own `hashbrown`, named DIRECTLY
//!     by the local crate under `#![feature(rustc_private)]`: the loader records
//!     it as a direct dependency, so the credit is withdrawn for the whole
//!     compilation (fail-closed) — and its `get_many_mut` (duplicate keys panic)
//!     is excluded by identity as well.
//!   * `condvar_two_mutexes` — std's pthread `Condvar`/`Mutex` carry `libc`
//!     types in their fields. The first attempt (`w4-hashmap`, stage-1
//!     `f828ea3d9`) credited every crate std is built from, which made them
//!     foundational through `libc`: this function built rc=0 there and a driver
//!     calling it with two mutexes panicked "attempted to use a condition
//!     variable with two mutexes" (exit 101). `libc` is not std's table crate.
//!   * `mutex_lock_over_refusal` — an OVER-REFUSAL kept on purpose and pinned:
//!     `Mutex::lock` + a saturating add cannot panic, and it is refused on main
//!     (stage-1 `7c7e46061`) for the same `libc`-field reason. Crediting `libc`
//!     is a separate, unaudited decision (docs/TCB.md); this pin moves only with
//!     it.
//!
//! Measured on the baseline (main, stage-1 `7c7e46061`): all refused.
#![cfg_attr(rustc_private_hashbrown, feature(rustc_private))]

#[cfg(any(proc_macro_punct, proc_macro_ident))]
extern crate proc_macro;

#[cfg(proc_macro_punct)]
pub fn punct(c: char) -> proc_macro::Punct {
    //[proc_macro_punct]~^ ERROR Trust strict verification failed for `sysroot_resident_not_std_not_vanilla::punct`
    proc_macro::Punct::new(c, proc_macro::Spacing::Alone)
}

#[cfg(proc_macro_ident)]
pub fn ident(s: &str) -> proc_macro::Ident {
    //[proc_macro_ident]~^ ERROR Trust strict verification failed for `sysroot_resident_not_std_not_vanilla::ident`
    proc_macro::Ident::new(s, proc_macro::Span::call_site())
}

#[cfg(rustc_private_hashbrown)]
extern crate hashbrown;

#[cfg(rustc_private_hashbrown)]
#[allow(deprecated)]
pub fn many(m: &mut hashbrown::HashMap<u32, u32, std::hash::RandomState>, a: u32, b: u32) {
    //[rustc_private_hashbrown]~^ ERROR Trust strict verification failed for `sysroot_resident_not_std_not_vanilla::many`
    if let [Some(x), Some(y)] = m.get_many_mut([&a, &b]) {
        core::mem::swap(x, y);
    }
}

#[cfg(condvar_two_mutexes)]
pub fn condvar_two_mutexes(cv: &std::sync::Condvar, m: &std::sync::Mutex<bool>) -> bool {
    //[condvar_two_mutexes]~^ ERROR Trust strict verification failed for `sysroot_resident_not_std_not_vanilla::condvar_two_mutexes`
    let g = match m.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    };
    match cv.wait_timeout(g, std::time::Duration::from_millis(1)) {
        Ok((g, _)) => *g,
        Err(e) => *e.into_inner().0,
    }
}

#[cfg(mutex_lock_over_refusal)]
pub fn mutex_lock_over_refusal(m: &std::sync::Mutex<u64>, x: u64) -> u64 {
    //[mutex_lock_over_refusal]~^ ERROR Trust strict verification failed for `sysroot_resident_not_std_not_vanilla::mutex_lock_over_refusal`
    let mut g = match m.lock() {
        Ok(g) => g,
        Err(e) => e.into_inner(),
    };
    *g = g.saturating_add(x);
    *g
}
