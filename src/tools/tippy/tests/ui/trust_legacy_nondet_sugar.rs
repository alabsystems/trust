//! Legacy Kani nondet *vocabulary* in expression position: `kani::any()` and
//! `kani::assume()` map to the Trust-native harness spelling `any()` /
//! `assume()`. This lives in its own fixture (not `trust_legacy_spec_sugar.rs`)
//! because a local `mod kani` — needed so the calls resolve — would shadow the
//! `register_tool(kani)` namespace the attribute fixture relies on.
// The machine-applicable suggestion drops the `kani::` qualifier; applied it
// would leave bare `any()`/`assume()` which do not resolve here, so no rustfix.
//@no-rustfix
#![warn(clippy::trust_legacy_spec_sugar)]
#![allow(dead_code)]

// A local `kani` module so the calls resolve; the early lint pass fires on the
// syntactic path regardless of what it resolves to.
mod kani {
    pub fn any<T: Default>() -> T {
        T::default()
    }
    pub fn assume(_cond: bool) {}
}

fn uses_legacy_nondet() -> i32 {
    let a: i32 = kani::any();
    //~^ trust_legacy_spec_sugar
    kani::assume(a > 0);
    //~^ trust_legacy_spec_sugar
    a
}

// A turbofished call keeps its type arguments after the qualifier is dropped.
fn uses_turbofish() -> u32 {
    kani::any::<u32>()
    //~^ trust_legacy_spec_sugar
}

// Bare `any()` / `assume()` (the native spelling) is NOT linted: no `kani`
// qualifier. Provide local free functions so these resolve on their own.
fn any<T: Default>() -> T {
    T::default()
}
fn assume(_cond: bool) {}

fn uses_native_vocab() -> i32 {
    let a: i32 = any();
    assume(a > 0);
    a
}

fn main() {}
