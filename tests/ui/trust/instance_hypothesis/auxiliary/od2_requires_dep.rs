//@ compile-flags: --crate-type=rlib -Ztrust-verify=on -Coverflow-checks=on -Zalways-encode-mir
//@ edition: 2021
//@ no-prefer-dynamic
//! OD-1 phase 2 x ADVISORY-REQUIRES-CROSS-CRATE: a dependency, verified on the
//! default policy, whose GENERIC body carries both an open dispatch (one instance
//! hypothesis, its own row) and a `requires` that proves its `i + 1` cannot
//! overflow. `fr` is public, so another crate can call it with any `i`: its check
//! must stay in the encoded MIR every consumer monomorphizes.

pub trait Tr {
    fn m(&self) -> u32;
}

pub fn fr<X: Tr>(x: &X, i: u32) -> u32
    requires i < 100
{
    let _ = x.m();
    i + 1
}
