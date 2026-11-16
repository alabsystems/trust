//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//! E6 admission expansion I4′ — the REFUSALS. Each of the four is a
//! BODY-side mutation against a fixed island (design note 2026-09-28 §5 rule
//! 5): the tree reader reads the body, the producer mints it, and the KERNEL
//! refuses the clause as not definitionally equal — swapped arms, a threshold
//! moved by one, a wrong `otherwise` value, and `>=` against `>` with
//! asymmetric arms (they differ exactly at `a == b`, review H7).
//!
//! A fifth case used to pin a CLAUSE-LANE limit here: `bool_to_int(c: bool) ->
//! u8` against the correct model was refused because the clause was typed at
//! its parameters' `Bool` carrier. That case flipped to a discharge with
//! E9-RESULT-CARRIER-1 and lives in `e9_cited_result_carrier_discharge.rs`.

clean {
    def sel_const_isl (a b : UInt64) : UInt64 := if a < b then 0 else 1
    def subr_bias_isl (n : UInt32) : UInt32 := if n < 1240 then 107 else if n < 33900 then 1131 else 32768
    def three_arm_isl (x : UInt8) : UInt8 := if x = 0 then 10 else if x = 1 then 20 else if x = 7 then 30 else 0
    def above_isl (a b : UInt8) : UInt8 := if a > b then 1 else 0
}

pub fn arms_swapped(a: u64, b: u64) -> u64
    ensures result == sel_const_isl(a, b)
    //~^ ERROR the two sides are not definitionally equal
{
    if a < b { 1 } else { 0 }
}

pub fn threshold_moved(n: u32) -> u32
    ensures result == subr_bias_isl(n)
    //~^ ERROR the two sides are not definitionally equal
{
    if n < 1241 {
        107
    } else if n < 33900 {
        1131
    } else {
        32768
    }
}

pub fn otherwise_wrong(x: u8) -> u8
    ensures result == three_arm_isl(x)
    //~^ ERROR the two sides are not definitionally equal
{
    match x {
        0 => 10,
        1 => 20,
        7 => 30,
        _ => 1,
    }
}

pub fn ge_against_gt(a: u8, b: u8) -> u8
    ensures result == above_isl(a, b)
    //~^ ERROR the two sides are not definitionally equal
{
    if a >= b { 1 } else { 0 }
}

fn main() {}
