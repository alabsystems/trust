//@ battery-lane: C-combo
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=on --crate-type=lib
//! LANE C NEGATIVE CONTROL — a citation must PROVE the clause, not merely
//! exist.
//!
//! ## The distinction this file exists to draw
//!
//! There are two completely different ways a `by <thm>` can fail, and only one
//! of them is evidence about verification:
//!
//! - **The name does not resolve.** `ensures x >= x by no_such_theorem` fails
//!   with ``cited theorem `no_such_theorem` is not registered in any Clean
//!   island or the prelude``
//!   (`compiler/rustc_mir_transform/src/trust_verify.rs:5494-5504`; pinned by
//!   `tests/ui/trust/e9_postcondition_citation_undischarged.rs:31-33`). That is
//!   a LOOKUP failure. It would fail identically if the kernel were a stub that
//!   accepted every proof it could find, so it proves nothing about proof
//!   checking. In this battery's vocabulary it is the `reject-wrong-reason`
//!   class: green-looking, worthless.
//! - **The name resolves to a real, kernel-accepted theorem that does not
//!   prove the stated clause.** That fails with ``citation `{name}` failed the
//!   strict Clean statement/certification audit: {detail}`` and the note
//!   "statement drift and authority/provenance failures are hard citation
//!   errors; there is no router fallback (E9)" (`trust_verify.rs:5560-5573`).
//!   That is a STATEMENT failure — the kernel compared the theorem's
//!   proposition against the clause's elaborated obligation and refused.
//!
//! **This file is the second kind, deliberately.** `tests/ui/trust/
//! native_clause_citation_mismatch.rs:9-15` pins the mechanism at minimum size
//! with `theorem zero_eq_thm : 0 = 0 := rfl`. A battery wants the stronger
//! version: a theorem with real mathematical content, proved from the kernel's
//! own library, about a genuinely different subject.
//!
//! ## Why the mismatch here is not a near-miss
//!
//! `nat_le_doubled : ∀ n : Nat, Nat.le n (Nat.add n n)` is TRUE, is proved
//! (not axiomatized) from `Nat.le_add_right`
//! (`first-party/clean/crates/clean-kernel/src/env/algebra_nat_mul_cancel_proof.rs:254-274`,
//! `Nat.le_add_right : ∀ n k : Nat, Nat.le n (Nat.add n k)`), and kernel-checks
//! — the same lemma `b3_library_composition.rs` builds on. It simply says
//! nothing about the clause below, whose elaborated obligation is
//! `∀ x, Nat.le (UInt64.toNat x) (UInt64.toNat x)` once `result` is bound to
//! the imported defining equation of the function
//! (`tests/ui/trust/e9_result_binding_discharge.rs:5-12`). Doubling a `Nat` and
//! reflexivity on a `UInt64` are not the same proposition, and no
//! instantiation makes them one.
//!
//! ## Why this is a real control and not decoration
//!
//! The clause `result >= x` on the body `x` is **true**, and the solver lane
//! can prove it independently. The file must be rejected anyway: E9 citation
//! drift is a hard build error with no fallback, so an authored-but-wrong
//! citation cannot be quietly rescued by whatever else happens to succeed. If
//! this file compiles, then `by <thm>` is decoration — a name the compiler
//! looks up rather than a proof it checks — and every cited pass in Lane C
//! (`c1_cited_min2.rs` above all) means only "some theorem by that name
//! exists".
//!
//! The positive control `keep` shares the island, the signature, the body and
//! the clause with the rejected function. The ONLY difference is which theorem
//! is cited. That isolates the rejection to the citation's statement — it
//! cannot be blamed on the island being unregistered, the session being
//! tainted, the clause being outside the supported fragment, or the body being
//! unadmissible, because all four hold identically for the function that
//! succeeds.
//!
//! Kernel constants verified against
//! `first-party/clean/crates/clean-kernel/src/env/`: `Nat.le`/`Nat.le.refl`
//! (`order_le_lt.rs:212-218`), `Nat.le_add_right`
//! (`algebra_nat_mul_cancel_proof.rs:254-274`), `UInt64.toNat`
//! (`data_types_uint.rs:114-115`), `Nat.add`/`Nat` (`data_types_nat.rs`).

clean {
    theorem u64_ge_refl : forall (x : UInt64),
        Nat.le (UInt64.toNat x) (UInt64.toNat x) :=
        fun x => Nat.le.refl (UInt64.toNat x)

    theorem nat_le_doubled : forall (n : Nat),
        Nat.le n (Nat.add n n) :=
        fun n => Nat.le_add_right n n
}

/// POSITIVE CONTROL — the right theorem for this clause. Identical to
/// `c1_cited_min2.rs:45` and `tests/ui/trust/e9_result_binding_discharge.rs:20`,
/// which are check-pass fixtures. If THIS one fails, the file has measured
/// something other than what it claims and its rejection must not be scored.
pub fn keep(x: u64) -> u64 ensures result >= x by u64_ge_refl { x }

/// THE CONTROL — same island, same signature, same body, same clause; the only
/// change is the cited theorem.
///
/// `nat_le_doubled` is real, true and kernel-checked, so this is NOT an
/// unresolved name. It is refused because it does not prove
/// `Nat.le (UInt64.toNat x) (UInt64.toNat x)`.
pub fn cites_the_wrong_theorem(x: u64) -> u64
    ensures result >= x by nat_le_doubled
{
    x
}
