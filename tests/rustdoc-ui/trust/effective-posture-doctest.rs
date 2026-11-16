// Trust: `trustdoc --test` under a committed Trust posture followed by the effective
// off-switch. The collecting trustdoc session is evidence-deauthorized and decides on the
// EFFECTIVE configuration, so it accepts and neutralizes the posture; the doctest itself
// is then compiled by the canonical `trustc` with the same `-Z` list, whose last-wins
// answer is verification OFF, and runs. `ay-then-off` is ay's committed posture verbatim
// followed by `-Ztrust-verify=off`.
//
// Before the fix both revisions were refused before a single doctest was collected
// ("compiler frontend rejects semantic, evidence, or backend control `-Ztrust-verify`"),
// measured on seal 7d5533b2 and on origin/main from b827bf0e13 through 9e0251329f.
//
//@ check-pass
//@ revisions: ay-then-off every-selector-then-off
//@ compile-flags: --test --test-args=--test-threads=1
//@ normalize-stdout: "tests/rustdoc-ui/trust" -> "$$DIR"
//@ normalize-stdout: "finished in \d+\.\d+s" -> "finished in $$TIME"
//@[ay-then-off] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify -Ztrust-verify-level=2
//@[ay-then-off] compile-flags: -Ztrust-verify-profile=unix_hardened
//@[ay-then-off] compile-flags: -Ztrust-verify-include-dependencies=yes -Ztrust-ir-lower=strict
//@[ay-then-off] compile-flags: -Ztrust-verify=off
//@[every-selector-then-off] compile-flags: -Ztrust-verify=on -Ztrust-policy=certify
//@[every-selector-then-off] compile-flags: -Ztrust-verify-level=2
//@[every-selector-then-off] compile-flags: -Ztrust-verify-profile=unix_hardened
//@[every-selector-then-off] compile-flags: -Ztrust-verify-include-dependencies=yes
//@[every-selector-then-off] compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//@[every-selector-then-off] compile-flags: -Ztrust-verify-output=json -Ztrust-memory-notes
//@[every-selector-then-off] compile-flags: -Ztrust-proof-artifact-root={{build-base}}/trust/no-proofs
//@[every-selector-then-off] compile-flags: -Ztrust-verify-timeout-ms=1
//@[every-selector-then-off] compile-flags: -Ztrust-verify-effort=1
//@[every-selector-then-off] compile-flags: -Ztrust-verify-worker-threads=1
//@[every-selector-then-off] compile-flags: -Ztrust-verify-function-budget-ms=1
//@[every-selector-then-off] compile-flags: -Ztrust-verify-function-budget-steps=1
//@[every-selector-then-off] compile-flags: -Ztrust-no-adapter-yield -Ztrust-no-r1
//@[every-selector-then-off] compile-flags: -Ztrust-bundle-foreign-crate=core
//@[every-selector-then-off] compile-flags: -Ztrust-ir-flip=no -Ztrust-instance-flip=no

#[cfg(trust_verify)]
compile_error!("the doctest collector ran with Trust verification active");

/// The doctest is compiled by the canonical compiler with the caller's `-Z` list; its
/// effective verification must be off, and its body must run.
///
/// ```
/// #[cfg(trust_verify)]
/// compile_error!("the doctest was compiled with Trust verification active");
///
/// fn triple(x: u32) -> u32 {
///     x * 3
/// }
/// assert_eq!(triple(14), 42);
/// ```
pub fn documented() {}
