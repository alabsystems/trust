//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 14 — interpreter Borrow-of-fat pass-through): chain item (2b) of the
// vtable campaign, a first-party/trust-ir PIN MOVE. The pinned reference interpreter's
// Borrow/BorrowMut arm accepted only thin pointer values, so a body whose return lifetime
// is tied to `&self` — where mir_built REBORROWS the marshalled literal (`_0 = &(*_2)`)
// over a fat `&str` value — refused with "Borrow: expected pointer value, got fatptr<str>"
// (a precisely-classed oracle incapacity, `clean-skip-other`, slice 8's measured residue).
// The interpreter now passes a `FatPtr` operand of Borrow/BorrowMut through VERBATIM (a
// reborrow of a fat pointer is the identity on the (data, metadata) pair — the thin arm's
// pass-through semantics, one value kind over); the differential needed NO change (its
// tracked-Borrow audit arms were already type-blind: they key on the tracked value id, not
// the pointee kind).
//
// Every lane below must keep COMPILING — a lowering decline is a coverage decision, never
// an error — and each pins one side of the slice-14 boundary.

// THE FREED SHAPE (explicit-paths-pass::Trait::description, hrtb-trait-upcasting::as_str —
// the two measured Agreed movers): return lifetime tied to `&self`, one literal, so the
// oracle module is GlobalAddr(__trust_bytes) -> PtrFromParts(FatPtr(Str)) -> Borrow ->
// Return, and the whole chain is the slice-7/8 paired-admission audit's tracked closure.
pub trait Reborrow {
    fn description(&self) -> &str {
        "hello world!"
    }
}
impl Reborrow for () {}

pub struct MyStruct;
impl MyStruct {
    pub fn as_str(&self) -> &str {
        "static"
    }
}

// SCOPE PIN (match-const-fn-structs::main's family — measured NOT-Agreed, by design): a
// call-free body whose module carries MORE THAN ONE live paired bytes global (each arm's
// literal is reborrowed into the shared multi-block local). The interpreter now EXECUTES
// it to completion (the reborrows pass through) and the unit returns match, but the
// observation walk's <=1-distinct-admitted-global bound refuses the green tail
// fail-closed (clean-skip-unmodeled-observation, never a verdict). The interpreter
// change moves execution, not admission.
pub fn multi_literal(c: bool) {
    let _s = if c { "one" } else { "two" };
}

fn main() {}
