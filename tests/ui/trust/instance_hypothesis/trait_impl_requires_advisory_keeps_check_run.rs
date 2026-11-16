//@ revisions: trait_route pointer_route
//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory -Coverflow-checks=on
//@ error-pattern: attempt to add with overflow
//@ ignore-emscripten no processes
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//! ADVISORY-REQUIRES-INSTANCE (KNOWN_HAZARDS, CLOSED 2026-10-04), the runtime half.
//! Under `-Ztrust-policy=advisory` a trait impl method's `requires` is charged to no
//! call and the impl is not refused. Its own run kernel-certified the `x + 1`
//! overflow check UNDER `x < 100` and `elide_kernel_certified_checks` DROPPED it.
//! BEFORE (stage 1 of `1177c327fa`, 2026-10-04): this source built with exactly
//! these flags printed `0` and exited 0, while `direct`'s row read `proved`; after
//! the bundling decline alone the row read `runtime_checked` and the binary still
//! printed `0` — a runtime check the row named was not in the program. Advisory
//! now removes no check proved under a caller precondition, so the call panics.
//! The fn-pointer route (`pointer_route`, no trait involved) had the same effect: an
//! `unknown` row and a wrapped `0`. Each revision runs one route, so each half of
//! the elision gate is pinned on its own.

pub trait Td {
    fn m(&self, x: u32) -> u32;
}

pub struct S;

impl Td for S {
    fn m(&self, x: u32) -> u32
    requires x < 100
    {
        x + 1
    }
}

pub fn add1(x: u32) -> u32
requires x < 100
{
    x + 1
}

#[inline(never)]
pub fn direct(y: u32) -> u32 {
    S.m(y)
}

#[inline(never)]
pub fn via_pointer(y: u32) -> u32 {
    let fp: fn(u32) -> u32 = add1;
    fp(y)
}

fn main() {
    let y = std::hint::black_box(u32::MAX);
    #[cfg(trait_route)]
    let r = direct(y);
    #[cfg(pointer_route)]
    let r = via_pointer(y);
    println!("{r}");
}
