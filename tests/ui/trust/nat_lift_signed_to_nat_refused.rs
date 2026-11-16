//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//! nat-lift REFUSAL fixture D-1: a signed value has no `Nat`.
//!
//! `i64` carries negative values and the lift table is a table of EXACT
//! injections, so there is no `i64 -> Nat` row. The tempting wrong answer is to
//! read the two's-complement bit pattern, which would turn `-1` into
//! `18446744073709551615` — a well-typed goal about a number the author never
//! wrote, which the kernel would happily check. Measured in
//! `crates/trust-spec-elab/tests/nat_lift_probes.rs::neg_bit_pattern_reading_is_not_the_signed_value`.
//!
//! The pin below is on the REASON, not on the message HEAD: the head
//! ("uncited `ensures` naming the Clean island definition … was not discharged
//! by definitional equality") is what EVERY undischarged uncited island clause
//! prints, so a fixture pinned on it would also pass if the clause were refused
//! for an unrelated cause. Measured 2026-09-18 on stage1 from this tree.
//!
//! The refusal names the type, says why the bit-pattern reading is wrong, and
//! offers three concrete options (v7/D3): state the definition over `Int` and
//! write `x as int`; make the parameter unsigned; or keep a `BitVec` definition
//! and relate it to the `Nat` one with a theorem. The `as int` route is the
//! supported one and is exercised by the crate-level WE-3 test.

clean {
    def nat_id (n : Nat) : Nat := n
}

fn ident(x: i64) -> i64
    ensures (result as nat) == nat_id(x as nat)
    //~^ ERROR is an `i64`, which can be negative and has no `Nat` value
{
    x
}

fn main() {
    let _ = ident(-3);
}
