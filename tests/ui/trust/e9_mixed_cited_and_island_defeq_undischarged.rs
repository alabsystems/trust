//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//! CLOSE NEGATIVE TWINS of `e9_mixed_cited_and_island_defeq_discharge`. A mixed
//! surface kernel-discharges ONLY when every `ensures` clause of the function is
//! individually kernel-proven — cited clauses by their theorem, uncited clauses
//! by definitional equality against an island definition they name — with
//! nothing left over. Every function below has the positive fixture's body and
//! at least one clause that DOES certify on its own; each must still fail, and
//! the clause that certifies must NOT be credited. A twin that starts compiling
//! is a soundness incident, not a fixture to re-bless.
//!
//! Every function keeps a `result == <island def>(a, b)` clause on purpose: its
//! rows are fail-closed sentinels that ONLY this kernel route can close, so
//! "Trust strict verification failed" on a twin is direct evidence that the
//! certifying clauses were not credited.
//!
//! `max2` is `min2` with its branches swapped, so this island cannot fail to
//! elaborate for a reason the positive fixture's island does not share.
//!
//! `dont-require-annotations: ERROR` tolerates only the SECONDARY Level-0 error
//! some twins also raise; every twin's primary refusal is pinned explicitly.

clean {
    def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    def max2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then b else a
    theorem min2_le_left (a b : UInt64) : min2 a b <= a := by
      unfold min2
      split <;> omega
}

// TWIN 1 — the UNCITED island clause is FALSE (the body is a min, the clause
// says max). The cited clause is true and its theorem certifies; that must buy
// nothing. The defeq refusal is a hard error, exactly as on an all-uncited
// surface.
pub fn false_island_clause(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == max2(a, b)
    //~^ ERROR uncited `ensures` naming the Clean island definition `max2` was not discharged by definitional equality
    ensures result <= a by min2_le_left
{
    if a < b { a } else { b }
}

// TWIN 2 — an ORDINARY uncited clause that is FALSE, beside a true island
// clause and a true cited clause. It names no island definition, so it has no
// kernel route, so the whole function declines.
pub fn false_ordinary_clause(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == min2(a, b)
    ensures result <= a by min2_le_left
    ensures result == 12345
{
    if a < b { a } else { b }
}

// TWIN 3 — a THIRD clause with no kernel route, after an island clause that DID
// certify. The third clause is TRUE and a solver may well prove it; that is not
// a kernel proof of it, and the rows are not attributed to clauses, so the two
// certifying clauses are discarded rather than credited. Said out loud, with
// options, instead of the old silent bail.
pub fn third_clause_without_route(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == min2(a, b)
    ensures result <= a by min2_le_left
    ensures result <= b
    //~^ ERROR this uncited `ensures` calls no admissible Clean island definition
{
    if a < b { a } else { b }
}

// TWIN 4 — TWIN 3 with the route-less clause authored FIRST. Nothing has
// certified on the defeq route when it is reached, so it is the mixed-surface
// NOTE that explains why the certified citation discharges nothing.
pub fn route_less_clause_first(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result <= b
    //~^ NOTE this uncited `ensures` has no Clean-kernel route
    ensures result == min2(a, b)
    ensures result <= a by min2_le_left
{
    if a < b { a } else { b }
}

// TWIN 5 — the CITED clause misses (`min2_le_left` does not prove `>=`), beside
// an island clause that certifies alone. No handoff happens, so the island
// clause is not judged, let alone credited.
pub fn missed_citation(a: u64, b: u64) -> u64
    //~^ ERROR Trust strict verification failed for
    ensures result == min2(a, b)
    ensures result >= a by min2_le_left
    //~^ ERROR citation `min2_le_left` failed the strict Clean statement/certification audit
{
    if a < b { a } else { b }
}

fn main() {
    let _ = (
        false_island_clause(1, 2),
        false_ordinary_clause(1, 2),
        third_clause_without_route(1, 2),
        route_less_clause_first(1, 2),
        missed_citation(1, 2),
    );
}
