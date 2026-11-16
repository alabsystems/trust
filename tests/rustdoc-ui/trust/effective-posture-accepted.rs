// Trust: trustdoc is an evidence-deauthorized frontend. It produces no verification
// evidence, so it decides Trust options on the EFFECTIVE (last-wins, fully parsed)
// configuration, never on each `-Ztrust-*` occurrence. Every revision below resolves to
// verification OFF, so every posture selector in it is inert here: trustdoc accepts the
// posture, neutralizes it, and documents a vanilla crate (`cfg(trust_verify)` absent).
// `ay-then-off` is ay's committed `.cargo/config.toml` posture, verbatim, followed by the
// `-Ztrust-verify=off` Targo appends for documentation passes.
//
// Before the fix every revision except `plain-off` was refused with "compiler frontend
// rejects semantic, evidence, or backend control `-Ztrust-…`" (or, for the policy alone,
// "rejects typed Trust evidence control `-Ztrust-policy`"), measured on seal 7d5533b2 and
// on origin/main from b827bf0e13 through 9e0251329f.
//
//@ check-pass
//@ revisions: plain-off on-then-off certify-then-off level-then-off lower-then-off
//@ revisions: ay-then-off every-selector-then-off
//@[plain-off] compile-flags: -Ztrust-verify=off
//@[on-then-off] compile-flags: -Ztrust-verify=on -Ztrust-verify=off
//@[certify-then-off] compile-flags: -Ztrust-policy=certify -Ztrust-verify=off
//@[level-then-off] compile-flags: -Ztrust-verify-level=2 -Ztrust-verify=off
//@[lower-then-off] compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
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

#![crate_name = "posture"]

// The neutralized session is vanilla: had any revision kept verification on, this
// crate would not document.
#[cfg(trust_verify)]
compile_error!("trustdoc documented this crate with Trust verification active");

/// One.
pub fn one() -> u32 {
    1
}
