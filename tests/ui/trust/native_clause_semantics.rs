//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ build-pass
//! Semantic regression for native signature postconditions. These must reach
//! `trust_contracts` as supported predicates; scalar and quantified clauses
//! must remain visible (proved when a proof-grade backend can replay them,
//! otherwise fail-closed UNKNOWN), while the quantified case remains a visible
//! obligation until the proof backend supports quantified replay. The old
//! grammar-only wiring silently lowered native predicates to `Unsupported`.

// The nonfatal policy isolates contract semantics from unrelated proof-grade
// coverage gaps in the default whole-function obligation. These notes are the
// end-to-end assertions: native postconditions reach the verifier instead of
// disappearing as parser-level `Unsupported`; proof-evidence gaps are reported
// explicitly as UNKNOWN.
pub fn identity(x: i32) -> i32
    //~^ NOTE Trust verification: 2 proved
    //~| NOTE of which 1 kernel-certified
    ensures result == x
{
    x
}

pub fn constant() -> i32
    //~^ NOTE Trust verification: 2 proved
    //~| NOTE of which 1 kernel-certified
    ensures result == 7
{
    7
}

pub fn quantified_identity(x: i32) -> i32
    //~^ NOTE Trust verification: 1 proved, 0 failed, 1 unknown
    //~| NOTE [unknown] UNKNOWN
    ensures forall i: usize, i == i ==> result == x
{
    x
}

fn main() {}
