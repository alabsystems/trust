//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-PO2b): a COROUTINE literal in value position — the `async fn`
//! shell's tail and a `let`-bound `async {}` block — carries the same
//! zero-field `opaque_alias` sort wave-PO2 minted for its unrevealed-opaque
//! type. The shell's `Return` then types against the PO2-mapped signature.
//! The body is SYMBOLIC (`param_opaque`): never spliced, never sampled, and
//! the MIR-side oracle fails closed on `ty::Coroutine`, so the differential
//! answers NotRun for every body this touches — the elided captures are
//! unobservable in every channel that runs.

async fn shell(x: u64) -> u64 {
    x * 2
}

fn holds_future() -> usize {
    let fut = async { 7u64 };
    core::mem::size_of_val(&fut)
}

fn main() {
    let _f = shell(21);
    let _n = holds_future();
}
