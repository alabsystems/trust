//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=strict -Ztrust-ir-lower-mutate-finalization
//@ dont-check-compiler-stderr
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR

//! **The strict CONTROL for `advisory_invalid_module_is_a_warning.rs`.**
//!
//! Same source, `strict` instead of `advisory`. Routing a producer-side invalid
//! module on the policy is only correct if the fail-closed lanes still REFUSE:
//! a proof claim must never rest on a module the validator rejects. Without
//! this file the advisory test alone is satisfied by deleting the check
//! outright, which is precisely the change that would be wrong.
//!
//! WHAT IS ASSERTED IS THE PRESENCE OF THE REFUSAL. Since re-point 5 the
//! invalid module is manufactured by `-Ztrust-ir-lower-mutate-finalization`
//! (see the advisory half), the crate itself is empty, and the refusal that
//! arrives under strict is the crate-finalization error itself, pinned at file
//! level. `dont-check-compiler-stderr` stays set: the sentence, not the full
//! rendering, is the contract.
//!
//! (A same-sentence pairing was tried on 2026-09-16 and reverted the same day:
//! it is only reachable on a shape where NO function has an unproved row, and
//! the declaration-signing campaign has retired every such shape it has met.
//! Pinning a property that only exists between two capability states is how a
//! control ends up measuring the calendar.)
//!
//! THE SHAPE IS INCIDENTAL. See the long note in the advisory half — including
//! why this file going GREEN is a finding and not a pass, why
//! `fmt::Arguments`-by-value was chosen as durable by design, and what to do
//! when no producer gap refuses any more.

// Nothing in this crate is wrong; the invalid module is manufactured by the
// knob (see the advisory half). Under strict that refusal is fatal.
fn main() {}

// The ONE refusal that arrives under strict is the spanless crate-finalization
// error the probe manufactures — file-level annotation form.
//~? ERROR trust-ir-lower semantic finalization failed
