//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #29 (falsification): the BARE (non-body-bound) trust-wp claim lane
//! must refuse machine arithmetic — blueprint amendment 1 extended from the
//! body-bound lane (93929aa2c7) to the bare lane.
//!
//! `ensures result + 1 > result` is provable over unbounded Int (the
//! sibling's linear-int rule accepts the free-variable tautology) but FALSE
//! at `u64::MAX` under Rust's wrapping machine semantics. Before the #29
//! gate, the bare lane lowered this predicate into a
//! `trust_wp.trust-formula.v1` claim and the NATIVE-LANE diagnostic read
//! "verified by trust_wp NativeTrustWpBundleVerifier" — a false proof at
//! native-lane granularity, held out of the final verdict only by the
//! sealed-authority gate (a single-gate defense).
//!
//! This fixture pins the post-gate state: the claim is REFUSED at
//! materialization ("is not an eligible canonical typed claim" citing the
//! arithmetic operator), so the native trust-wp lane can never report the
//! claim verified; the obligation demotes exactly like any unlowerable
//! predicate and the strict build fails.
pub fn arith_add(x: u64) -> u64 ensures result + 1 > result { x }
//~^ ERROR strict verification failed
