//@ needs-trust-verify
//@ aux-build: fmt_member_tolerance_dep.rs
//@ revisions: strict default
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Copt-level=0 --crate-type lib
//@[strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Refuted 2026-09-28: the policy-B bundled std-member tolerance on the LOWERING-
//! FAILURE path waved through a derived `Debug` whose field is a verify-off
//! dependency's type.
//!
//! The derive expands to `Formatter::debug_tuple_field1_finish(f, "A", &__self_0 as
//! &dyn Debug)`. With a std built with debug assertions (a `bootstrap.toml` whose
//! `[rust] debug-assertions`/`overflow-checks` reach std — see
//! docs/KNOWN_HAZARDS.md), the bundled member `DebugTuple::field_with::<..>` carries
//! an overflow `Assert` the exact Div/Rem/BoundsCheck admission lane refuses. That
//! refusal discarded the WHOLE bundle — including the row for the `<dyn Debug as
//! Debug>::fmt` call core makes on the dependency's value — and the tolerance then
//! reported the member's own Assert as the only undischarged obligation. Its gates
//! read only the root's own MIR, and the fold-mask walk exempts every inherent item
//! under `core::fmt`, so nothing looked at the `&dyn Debug` handed to core.
//!
//! MEASURED BEFORE (stage-1 `trustc` at `f992e2c307d`, std WITH debug assertions,
//! `-Ztrust-policy=strict`, this shape with this aux): exit 0, one advisory warning,
//! `TRUST_JSON` crate summary `functions_verified:1,total_proved:1,total_unknown:0`;
//! a verify-off `main` printing `{:?}` of `E::A(dep::Inner(7))` against that rlib
//! exited 101 in the dependency. With a release std the member is not refused, the
//! bundle lowers, and the dyn row refuses the impl (exit 1) — so this file is
//! red-before only where std carries debug assertions, and must be refused on both.
//! On stage-1 `9edd8e85013` WITHOUT the fix: both revisions failed with "ui test did
//! not emit an error" on the debug std, and passed on the release std.
//!
//! AFTER: the tolerance re-judges every call into core's inherent formatting
//! machinery (`lowering_failure_fmt_machinery_reach`, since 2026-09-29
//! `fmt_machinery_reach_without_verdict`, which withholds the runtime-checked
//! std-member disposition that replaced the tolerance); the `&dyn Debug` here was
//! minted from `&&dep::Inner`, whose `Debug` impl (peeled through core's `&T`
//! forwarding impl) is neither core's own at a foundational type nor a local
//! formatting impl with a verdict of its own, so the build is refused. The pin is
//! the text both refusals share (`… verification failed for`), which keeps it
//! green on either std configuration.
extern crate fmt_member_tolerance_dep as dep;

#[derive(Debug)]
//~^ ERROR verification failed for
pub enum E {
    A(dep::Inner),
    B,
}
