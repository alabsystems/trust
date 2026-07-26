//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ compile-flags: --crate-type=lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ check-fail
//! Task #23 Slice 1, amendment 1 (falsification): machine-arithmetic in an
//! `ensures` predicate must NEVER let the build pass when the clause is
//! FALSE. `result + 1 > result` is provable over unbounded `Int` but false at
//! `u64::MAX` under the machine wrap — the confirmed false-proof vector.
//!
//! Three generations of containment, each still load-bearing:
//!  * the bridge's `spec_predicate_to_sibling_json` v1 fragment refuses ALL
//!    arithmetic (comparisons + boolean connectives only), so the body's
//!    machine semantics are never equated with `Int` arithmetic via a
//!    defining equation;
//!  * the #29 amendment-1 gate refuses arithmetic at the bare-claim
//!    materialization point (see twp29_bare_add_never_proved.rs for the
//!    native-lane pin), so the claim never reaches the sibling;
//!  * the Machine{w} lane (ratified L1 rule 4) reads the clause at its
//!    DECLARED width: the body-aware postcondition VC and the contract row
//!    are pure declared-width QF_BV where `bvadd(result, 1)` WRAPS, so the
//!    negated clause is SATisfiable at exactly `u64::MAX` — the `Int`
//!    spelling that once re-solved strict-UNSAT no longer exists to solve,
//!    and no row proves (0 proved; the wrap witness holds every lane at
//!    fail-closed).
//!
//! This fixture pins the load-bearing outcome: the build FAILS and the
//! postcondition row is never accepted. Its positive twin
//! (s1c_arith_true_ensures_proves) pins the same lane's capability frontier —
//! containment is no longer bought by amputating the whole arithmetic
//! contract class.
pub fn arith_tautology(x: u64) -> u64 ensures result + 1 > result { x }
//~^ ERROR strict verification failed
