//! Unstable module containing the unstable contracts lang items and attribute macros.

pub use crate::macros::builtin::{contracts_ensures as ensures, contracts_requires as requires};

/// This is an identity function used as part of the desugaring of the `#[ensures]` attribute.
///
/// This is an existing hack to allow users to omit the type of the return value in their ensures
/// attribute.
///
/// Ideally, rustc should be able to generate the type annotation.
/// The existing lowering logic makes it rather hard to add the explicit type annotation,
/// while the function call is fairly straight forward.
#[unstable(feature = "contracts_internals", issue = "128044" /* compiler-team#759 */)]
// Similar to `contract_check_requires`, we need to use the user-facing
// `contracts` feature rather than the perma-unstable `contracts_internals`.
// Const-checking doesn't honor allow_internal_unstable logic used by contract expansion.
#[rustc_const_unstable(feature = "contracts", issue = "128044")]
// TRUST: the `'static` bound is deliberately ABSENT, and its removal is the
// difference between an `ensures` clause that can mention a reference
// parameter and one that cannot.
//
// This function is the identity (`{ cond }`); the bounds constrain the
// closure's TYPE, not its body. Its only consumer,
// `core::intrinsics::contract_check_ensures`, requires exactly
// `C: Fn(&Ret) -> bool + Copy` -- no `'static`. So `'static` here was
// strictly stronger than the consuming path needs.
//
// `Copy` IS load-bearing: the checker is built at entry and invoked at every
// return point, so it must survive repeated use. A closure capturing a shared
// reference is Copy, which is why dropping `'static` alone is enough.
//
// What it unblocks: with `'static`, `move |ret: &Cst| ret.degree == a.degree`
// on `fn f(a: &Cst) -> Cst` is a hard compile error ("requires that '1 must
// outlive 'static") -- a purely SCALAR postcondition, rejected only because it
// names a borrowed parameter. That made it impossible for any checking rule to
// relate its output to its inputs.
#[lang = "contract_build_check_ensures"]
pub const fn build_check_ensures<Ret, C>(cond: C) -> C
where
    C: Fn(&Ret) -> bool + Copy,
{
    cond
}

/// Runtime enforcement endpoint for a kernel-certified Trust monitor.
///
/// Calls are synthesized only from a `trust-spec-elab` monitor carrying a
/// Clean proof of `monitor(args, out) = true ↔ P`. Unsupported clauses have no
/// call at all; this function therefore never receives a placeholder `true`.
/// The diagnostic item lets the Trust MIR pass reference the exact sysroot
/// function without exposing a user-facing runtime API or compiler flag.
#[doc(hidden)]
#[unstable(feature = "contracts_internals", issue = "128044")]
#[rustc_diagnostic_item = "trust_certified_monitor_check"]
#[inline(never)]
pub fn certified_monitor_check(cond: bool) {
    if !cond {
        crate::panicking::panic_nounwind("kernel-certified Trust monitor failed");
    }
}
