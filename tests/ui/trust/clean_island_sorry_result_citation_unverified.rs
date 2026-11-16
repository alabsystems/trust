//@ needs-trust-verify
//@ compile-flags: -Z trust-verify=off
//@ check-fail
//@ dont-require-annotations: NOTE
//! The unverified-lane citation allowance must never launder a `sorry`-backed
//! island. `native_clause_citation_result_unverified` pins that a cited
//! `ensures` mentioning `result` builds under `-Ztrust-verify=off` with a "NOT
//! checked" note; this is the twin that pins WHERE that stops: the same clause
//! shape, in a crate whose island reaches the incomplete-proof marker, is a
//! hard error and carries NO such note.
//!
//! Two independent gates hold that line and this fixture pins their
//! conjunction end-to-end. Since 2026-09-13 the island rejection is reported at
//! the resolve-time mint seam, so the verify pass — and with it the E9 citation
//! sweep — never runs on this crate at all, which is the strongest form of "no
//! positive evidence". Behind that, `CleanIslandSession::audit_cited_theorem`
//! (the body-independent audit the allowance runs) refuses on a tainted session
//! before consulting its environment, and refuses an axiom-backed theorem on
//! its own; `trust-certify`'s
//! `cited_theorem_audit_is_body_independent_and_never_a_statement_match` pins
//! that half directly.
//!
//! This fixture deliberately checks its `.stderr`: the pin is not only that
//! there is an error, it is that the allowance's note is ABSENT. Do NOT add
//! `dont-check-compiler-stderr`. (The annotation sits OUTSIDE the island: its
//! body is Clean text verbatim to the closing `}`.)
//! RE-PIN 2026-11-15: Clean (bcacce6e0, in the pin since e64e4b7901) ships the
//! admission markers (`sorry`, `trustedArith`, `trustedAy`) in an opt-in fragment,
//! not in the prelude the island registers into, so the island is refused when it
//! names one, before the publish audit that used to refuse it. Still a hard error
//! with nothing registered (docs/OPEN_ISSUES.md ISLAND-MARKER-DIAGNOSTIC-1).

clean {
    theorem registered_before_failure : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => @Nat.le.refl (UInt64.toNat x)
    theorem hole : True := sorry
}
//~^^ ERROR `hole` did not elaborate

pub fn keep(x: u64) -> u64
    ensures result >= x by registered_before_failure
{
    x
}

fn main() {
    let _ = keep(1);
}
