//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@[unopt] check-pass
//@[opt] check-fail
//! E6 admission expansion I4′ (design note 2026-09-28 §6): value decision
//! trees are E6-imported by the E6-only TREE reader, so an uncited clause
//! naming a Clean island definition discharges by definitional equality.
//!
//! * `if`/`else` returning a value: a select with CONSTANT arms (probe
//!   `f03_select_const_arms`'s shape, which the frozen select refuses), a
//!   chain of thresholds (apdf's `subr_bias`, R12), a `bool`-conditioned
//!   select, and `if a > b { a } else { b }` — `>` swaps the OPERANDS and
//!   keeps the arms (review H7), so the island's `if a > b then a else b`
//!   meets it.
//! * `match` on a `u8` with literal arms and `_` (a multi-target
//!   `switchInt`), minted as the design note's `if x = v then … else …`
//!   chain — which is how the island is spelled (Clean's own `match` on a
//!   `UInt8` literal elaborates through `==`, a different proposition).
//! * `matches!` and a `match` with `bool`-literal arms fold to `||` of
//!   equality tests (R8, R21's 0x00/0xff test).
//!
//! Each parameter binds at its own carrier. `-O` is the twin, because the
//! readers see the optimizer's MIR. Before I4′ every function here was
//! refused ("…to be E6-admitted …; it is not").
//!
//! `guarded` pins a KNOWN `-O` ASYMMETRY (`docs/KNOWN_HAZARDS.md`, "an E6
//! `match` guard discharges without `-O` and is refused with it",
//! 2026-09-29): a guard `n if n > 5` is read as the decision it lowers to
//! without `-O`, and discharges; under `-O` the MIR keeps the guard's borrow
//! of its binding (`_2 = &_1; … copy (*_2)`), so the FACET gate refuses the
//! `&u8` local (and the shape gate names the borrow) and the same program
//! fails. It fails CLOSED — no revision certifies anything the other refutes —
//! but it contradicts the `-O` parity ruling, so the `opt` revision is
//! `check-fail` on exactly that function until a reader is widened for it
//! (not in this slice).

clean {
    def sel_const_isl (a b : UInt64) : UInt64 := if a < b then 0 else 1
    def subr_bias_isl (n : UInt32) : UInt32 := if n < 1240 then 107 else if n < 33900 then 1131 else 32768
    def pick_isl (c : Bool) (a b : UInt64) : UInt64 := if c then a else b
    def max_isl (a b : UInt8) : UInt8 := if a > b then a else b
    def three_arm_isl (x : UInt8) : UInt8 := if x = 0 then 10 else if x = 1 then 20 else if x = 7 then 30 else 0
    def small_code_isl (x : UInt8) : Bool := x == 1 || x == 2
    def edge_byte_isl (x : UInt8) : Bool := x == 0 || x == 255
    def guard_isl (x : UInt8) : UInt8 := if x > 5 then 1 else 0
}

pub fn select_const_arms(a: u64, b: u64) -> u64
    ensures result == sel_const_isl(a, b)
{
    if a < b { 0 } else { 1 }
}

pub fn subr_bias(n: u32) -> u32
    ensures result == subr_bias_isl(n)
{
    if n < 1240 {
        107
    } else if n < 33900 {
        1131
    } else {
        32768
    }
}

pub fn pick(c: bool, a: u64, b: u64) -> u64
    ensures result == pick_isl(c, a, b)
{
    if c { a } else { b }
}

pub fn max_u8(a: u8, b: u8) -> u8
    ensures result == max_isl(a, b)
{
    if a > b { a } else { b }
}

pub fn three_arm(x: u8) -> u8
    ensures result == three_arm_isl(x)
{
    match x {
        0 => 10,
        1 => 20,
        7 => 30,
        _ => 0,
    }
}

pub fn small_code(x: u8) -> bool
    ensures result == small_code_isl(x)
{
    matches!(x, 1 | 2)
}

pub fn edge_byte(x: u8) -> bool
    ensures result == edge_byte_isl(x)
{
    match x {
        0 | 255 => true,
        _ => false,
    }
}

pub fn guarded(x: u8) -> u8
    ensures result == guard_isl(x)
    //[opt]~^ ERROR was refused by the FACET gate
    //[opt]~^^^ ERROR Trust strict verification failed for `e6_select_match_defeq::guarded`
    //[opt]~^^^^ ERROR Trust Level 0 safety verification incomplete for `e6_select_match_defeq::guarded`
{
    match x {
        n if n > 5 => 1,
        _ => 0,
    }
}

fn main() {}
