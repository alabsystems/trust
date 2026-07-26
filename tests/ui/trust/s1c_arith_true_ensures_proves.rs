//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-pass
//! Machine{w} ACCEPTANCE (the campaign's headline pin, ratified L1 rule 4): a
//! TRUE arithmetic contract PROVES END-TO-END — every obligation of this
//! function is discharged, def-site clause marker included.
//!
//! `ensures result == x + 1` with the declared precondition excluding the
//! single wrap point is UNSAT-to-violate in declared-width QF_BV. The full
//! chain: trust-vcgen admits the arithmetic clause into the refutable
//! body-aware lane and translates the assembled VC wholesale into Machine{64}
//! wrapping bitvectors; trust-mir-extract lowers the contract row at the same
//! declared width (instead of parking it as `unsupported_machine_arithmetic`);
//! the native typed CHC/PDR lane proves the standalone query and its sealed
//! PdrInvariant candidate is consumed through the fresh-exact replay,
//! minting a `FreshExactDirectChcPdr` receipt; and
//! `ExactSourceClauseDischarge` seals the def-site marker from that receipt —
//! its authority bar (`KernelCertified | FreshExactDirectChcPdr`, never
//! `SolverRevalidated`) is unchanged and still load-bearing.
//!
//! Remove the `requires` and the clause still never FALSE-proves: `bvadd`
//! wraps at `u64::MAX`, which is precisely what the unbounded-`Int` reading
//! missed. The sibling pin (s1c_arith_ensures_no_false_pass) holds that
//! falsification direction; this fixture must never start passing via a lane
//! that would also prove the sibling's wrap-false clause.
pub fn inc(x: u64) -> u64
    requires x < 18446744073709551615
    ensures result == x + 1
{
    x + 1
}
