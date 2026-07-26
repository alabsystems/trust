//@ battery-lane: D-legacy
//@ battery-expect: tippy-emits-lean
//@ battery-flags: --crate-type=lib
//@ battery-tool: tippy
//! LANE D (legacy frontend → Lean) — THE NONDET VOCABULARY.
//!
//! `d1_kani_contracts.rs` covers the contract attributes. This file covers the
//! lint's other two arms — `kani::any()` and `kani::assume()` — which are
//! ordinary function calls rather than attributes, so they need a real `kani`
//! module to resolve against. That module is exactly what shadows the
//! registered tool namespace, which is why the two halves cannot share a file.
//!
//! Same question, same answer: the lint fires and suggests the NATIVE RUST
//! spelling (`any()`, `assume()` with the `kani::` qualifier deleted), never
//! Lean:
//!
//!     warning: legacy `kani::any()`; use the native harness `any()`
//!     warning: legacy `kani::assume()`; use the native harness `assume()`
//!
//! Worth stating plainly, because it is the part of the owner directive that
//! is hardest: for the nondet vocabulary there is no Lean to emit. `any()` and
//! `assume()` are harness plumbing, not propositions. Only a CONTRACT has a
//! candidate translation, and even there the honest target is a native clause
//! plus an island definition — not a theorem, since a cited theorem's
//! statement is a function of the compiler's E6 encoding of the annotated
//! body, which is unreachable from an attribute token stream.

pub mod kani {
    pub fn any<T: Default>() -> T {
        T::default()
    }
    pub fn assume(_cond: bool) {}
}

/// A harness in the legacy dialect: nondet input, constrained, then exercised.
pub fn check_range() {
    let x: u32 = kani::any();
    kani::assume(x < 1000);
    let _doubled = x * 2;
}

/// The turbofished spelling, which the lint must also catch.
pub fn check_turbofish() {
    let y = kani::any::<u8>();
    kani::assume(y != 0);
    let _halved = y / 2;
}
