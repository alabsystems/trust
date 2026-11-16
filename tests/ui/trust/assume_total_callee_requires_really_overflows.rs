//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ revisions: direct param collect_inline promoted assoc_const table_static
//@ compile-flags: -Ztrust-verify=off -Coverflow-checks=on
//@[collect_inline] compile-flags: -Zinline-mir=yes
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//! The WITNESS for `assume_total_does_not_cover_callee_requires.rs`
//! (docs/KNOWN_HAZARDS.md, "FIX PREPARED 2026-09-30 … — `#[trust::assume_total]`
//! charged none of its calls"): the same `add1` and `p`, built with verification
//! OFF. Nothing elided `add1`'s overflow check, so `p(u32::MAX)` — outside
//! `requires x < 100` — panics, directly (`direct`), through the fn pointer an
//! `assume_total` body calls (`param`), inside the `Map` an inlined `map(add1)`
//! hands to `collect` (`collect_inline`, `-Zinline-mir=yes`: the one call left in
//! `p` names `add1` only in an ADT type argument), and through the `fn` field of a
//! PROMOTED `&H { f: add1 }` handed to a function that calls it (`promoted`: no type
//! in `p` names `add1`, only the promoted constant's value does), and through the
//! associated constant of a local impl that a function generic over the trait
//! evaluates (`assoc_const`, the third review's route: `p` names only `MyT`), and
//! through the `fn` field of a `static` that a verified `table()` returns to the body
//! (`table_static`, the residual (b) route: at `-O0` nothing in `p` holds the static).
//! The minting-site seam (2026-10-03, built and tested) refuses the `static`'s and the
//! promoted's and the associated constant's initializers when verification is ON; this
//! file is built with it OFF, where the seam does not run (it runs only after the
//! verification-enabled check in `trust_ensure_whole_crate_verification`).
//!
//! Verified BEFORE the fix, `add1`'s check was elided under its `requires` and the
//! `assume_total` body that calls it was skipped, so nothing charged the call: the
//! same library built under `-Ztrust-policy=certify` (and under the default policy)
//! and linked into a verify-off `main` RETURNED `p(u32::MAX) = 0` for `direct` and
//! `param`, and — the source of this file with the same flags — for
//! `collect_inline` (measured 2026-09-30 on a stage 1 of `fbc6068e3`); for
//! `promoted`, the same `p` with `H` and `run_h` in a verify-off dependency returned
//! `[0]` for `[u32::MAX]` at `-O0`, `-Zinline-mir=yes` and `-Copt-level=3
//! -Zmir-opt-level=2` (the same stage 1; `run_h` is in a dependency there because a
//! verified `run_h`, a call through a fn-pointer field, is refused on its own). So
//! admitting `p` was admitting a wrong value, not a panic that `assume_total` could
//! assume away.
//! `-Coverflow-checks=on` keeps this build's check whatever opt-level the suite
//! runs at.

pub fn add1(x: u32) -> u32
    requires x < 100
{
    x + 1
}

#[cfg(direct)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    add1(y)
}

#[cfg(param)]
#[trust::assume_total]
fn call(f: fn(u32) -> u32, y: u32) -> u32 {
    f(y)
}

#[cfg(param)]
pub fn p(y: u32) -> u32 {
    call(add1, y)
}

#[cfg(collect_inline)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    [y].iter().copied().map(add1).collect::<Vec<u32>>()[0]
}

#[cfg(any(promoted, table_static))]
pub struct H {
    pub f: fn(u32) -> u32,
}

#[cfg(any(promoted, table_static))]
fn run_h(h: &H, y: u32) -> u32 {
    (h.f)(y)
}

#[cfg(promoted)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    run_h(&H { f: add1 }, y)
}

#[cfg(assoc_const)]
pub struct H {
    pub f: fn(u32) -> u32,
}

#[cfg(assoc_const)]
pub trait HasH {
    const H: H;
}

#[cfg(assoc_const)]
fn run_assoc<T: HasH>(y: u32) -> u32 {
    (T::H.f)(y)
}

#[cfg(assoc_const)]
pub struct MyT;

#[cfg(assoc_const)]
impl HasH for MyT {
    const H: H = H { f: add1 };
}

#[cfg(assoc_const)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    run_assoc::<MyT>(y)
}

#[cfg(table_static)]
static HG: H = H { f: add1 };

#[cfg(table_static)]
pub fn table() -> &'static H {
    &HG
}

#[cfg(table_static)]
#[trust::assume_total]
pub fn p(y: u32) -> u32 {
    run_h(table(), y)
}

fn main() {
    println!("p(u32::MAX) = {}", p(std::hint::black_box(u32::MAX)));
}
