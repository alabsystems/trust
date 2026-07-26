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
#[lang = "contract_build_check_ensures"]
pub const fn build_check_ensures<Ret, C>(cond: C) -> C
where
    C: Fn(&Ret) -> bool + Copy + 'static,
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
