//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-pass
//! E6 admission expansion I1′ (design note 2026-09-28 §6): `==` and `!=` over
//! `bool` are E6-imported, so an uncited clause naming a Clean island
//! definition discharges by definitional equality.
//!
//! * `==` arrives through `recognize_admissible_body`'s `ComparisonBool`, whose
//!   `Bool` domain the importer now routes to the new producer
//!   `admit_bool_cmp_function` — DISPATCHING ON THE OPERATOR: only `==` gets
//!   the equality image (`e6_bool_cmp_refusals.rs` pins `<`/`<=`/`>`).
//! * `!=` is the first node of the E6-ONLY reader (`read_e6_body`), consulted
//!   after the frozen chain answers `None`; `recognize_admissible_body` is not
//!   widened.
//!
//! `lit_value` is ay's shape (`v == pos`), R6 in the design note. `-O` is the
//! twin, because the readers see the optimizer's MIR. Before I1′ every
//! function here was refused ("…to be E6-admitted …; it is not").

clean {
    def beq_isl (a b : Bool) : Bool := a == b
    def bneq_isl (a b : Bool) : Bool := a != b
    def keep_isl (v : Bool) : Bool := v == Bool.true
}

pub fn lit_value(v: bool, pos: bool) -> bool
    ensures result == beq_isl(v, pos)
{
    v == pos
}

pub fn differ(a: bool, b: bool) -> bool
    ensures result == bneq_isl(a, b)
{
    a != b
}

// The operands in the other order still denote the same Bool (`==`/`!=` are
// symmetric), so the island spelled `b != a`'s model closes too.
pub fn differ_swapped(a: bool, b: bool) -> bool
    ensures result == bneq_isl(b, a)
{
    b != a
}

fn main() {}
