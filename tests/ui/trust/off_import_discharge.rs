//@ revisions: unopt opt
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=off
//@[opt] compile-flags: -O
//@ build-pass
//@ dont-require-annotations: NOTE
//! TG3 (COMPILE-TIME-FACTS-1, owner ruling 2026-11-05: "checks are supposed to
//! be check at compile time!"): a Clean island that names a `trust_import_*`
//! constant is checked in EVERY build, `-Ztrust-verify=off` included.
//!
//! Before TG3 this file was a hard error with verification off: the island
//! "names the kernel-import namespace, which is populated only by an enabled
//! verification walk". Now the kernel-only lane E6-imports exactly the bodies
//! the island names, the kernel checks each theorem against the imported term,
//! and the citations that cite those theorems are judged with `result` bound to
//! the same term. No VC is generated and no solver runs.
//!
//! The kernels are written the way the two-language plan's proof workers write
//! them: fixed-width scalar parameters, `&&` trees, comparisons, `if`/`else`
//! and a `match` on an integer with literal arms (no guards). The `opt`
//! revision reads the MIR-opt-level-2 body a `-O` build with verification off
//! emits code for; both revisions must discharge the same obligations.
//!
//! The close negative twin is `off_import_mutant.rs` (one `&&` mutated to `||`
//! must be refused).

pub fn member_approval(authority: bool, eligible: bool, writer: bool) -> bool
    ensures result == (authority && (eligible && writer)) by member_approval_is_exact
    //~^ NOTE kernel-discharges this postcondition statement
{
    authority && (eligible && writer)
}

pub fn admissible(limit: u64, previous: u64, proposed: u64) -> bool
    ensures result == (previous <= proposed && proposed <= limit) by admissible_is_exact
    //~^ NOTE kernel-discharges this postcondition statement
{
    previous <= proposed && proposed <= limit
}

pub fn merge_spent(left: u64, right: u64) -> u64 {
    if left < right { right } else { left }
}

pub fn classify(code: u8) -> u8 {
    match code {
        0 => 10,
        1 => 20,
        _ => 0,
    }
}

clean {
    theorem member_approval_is_exact (authority eligible writer : Bool) :
        trust_import_off_import_discharge__member_approval authority eligible writer =
            (authority && eligible && writer) := by
      simp only [trust_import_off_import_discharge__member_approval]
    theorem admissible_is_exact (limit previous proposed : UInt64) :
        trust_import_off_import_discharge__admissible limit previous proposed =
            (decide (previous <= proposed) && decide (proposed <= limit)) := by
      simp only [trust_import_off_import_discharge__admissible]
    theorem merge_is_a_receipt (left right : UInt64) :
        Or (Eq (trust_import_off_import_discharge__merge_spent left right) left)
           (Eq (trust_import_off_import_discharge__merge_spent left right) right) :=
      @Decidable.casesOn (LT.lt left right)
        (fun (d : Decidable (LT.lt left right)) =>
          Or (Eq (@ite UInt64 (LT.lt left right) d right left) left)
             (Eq (@ite UInt64 (LT.lt left right) d right left) right))
        (instDecidableUInt64Lt left right)
        (fun (_ : Not (LT.lt left right)) => Or.inl (Eq.refl left))
        (fun (_ : LT.lt left right) => Or.inr (Eq.refl right))
    theorem classify_one : trust_import_off_import_discharge__classify 1 = 20 := rfl
    theorem classify_other : trust_import_off_import_discharge__classify 7 = 0 := rfl
}
//~^^^^^^^^^^^^^^^^^^^^^ NOTE Clean island kernel-checked after program admission

fn main() {
    assert!(member_approval(true, true, true));
    assert!(admissible(10, 3, 5));
    assert_eq!(merge_spent(3, 9), 9);
    assert_eq!(classify(1), 20);
}
