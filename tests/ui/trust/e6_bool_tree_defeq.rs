//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-pass
//! E6 admission expansion I3′ (design note 2026-09-28 §6): `bool` connective
//! trees are E6-imported by the E6-only TREE reader
//! (`trust_types::e6_expr::read_e6_tree`), so an uncited clause naming a Clean
//! island definition discharges by definitional equality.
//!
//! rustc lowers `&&`/`||` into short-circuit branches; the reader merges each
//! branch at its join and folds the decisions back into `&&`/`||`/`!`, nested
//! to the right as Clean parses `a && b && c`. `&`/`|`/`^` over `bool` are
//! single statements (the facet firewall closes them over `bool` since I3′).
//! Leaves are `bool` parameters and comparisons of integer parameters and
//! literals — `!=` over integers included.
//!
//! The first three are ay's soundness gates VERBATIM (design note §7, R3–R5);
//! then a 3-way `||` over comparisons (the I0 fixture's former shape-gate
//! case), a 6-way `||` classifier (R8), `is_printable_fallback`'s `!=` (R9),
//! a negated `&&`, and `bool` and `u8` parameters mixed. `-O` is the twin,
//! because the readers see the optimizer's MIR. Before I3′ every function
//! here was refused ("…to be E6-admitted …; it is not").

clean {
    def gate_keeps_sat_isl (was_sat confirmed enforce : Bool) : Bool := was_sat && (confirmed || !enforce)
    def lemma_admitted_isl (self_ind init_valid entry_ind : Bool) : Bool := self_ind && init_valid && entry_ind
    def xor_parity_isl (acc contribution : Bool) : Bool := xor acc contribution
    def any3_isl (a b c : UInt64) : Bool := decide (a < b) || decide (b < c) || decide (a = c)
    def odd_small_isl (x : UInt8) : Bool := x == 1 || x == 3 || x == 5 || x == 7 || x == 9 || x == 11
    def printable_isl (x : UInt8) : Bool := x != 127 && decide (32 <= x)
    def nand_isl (a b : Bool) : Bool := !(a && b)
    def before_unless_isl (a b : UInt8) (c : Bool) : Bool := decide (a < b) && !c
}

pub fn gate_keeps_sat(was_sat: bool, confirmed: bool, enforce: bool) -> bool
    ensures result == gate_keeps_sat_isl(was_sat, confirmed, enforce)
{
    was_sat && (confirmed || !enforce)
}

pub fn lemma_admitted_inductive(self_ind: bool, init_valid: bool, entry_ind: bool) -> bool
    ensures result == lemma_admitted_isl(self_ind, init_valid, entry_ind)
{
    self_ind & init_valid & entry_ind
}

pub fn xor_accumulate_parity(acc: bool, contribution: bool) -> bool
    ensures result == xor_parity_isl(acc, contribution)
{
    acc ^ contribution
}

pub fn any_of_three(a: u64, b: u64, c: u64) -> bool
    ensures result == any3_isl(a, b, c)
{
    a < b || b < c || a == c
}

pub fn odd_small(x: u8) -> bool
    ensures result == odd_small_isl(x)
{
    x == 1 || x == 3 || x == 5 || x == 7 || x == 9 || x == 11
}

pub fn is_printable_fallback(x: u8) -> bool
    ensures result == printable_isl(x)
{
    x != 0x7f && x >= 0x20
}

pub fn nand(a: bool, b: bool) -> bool
    ensures result == nand_isl(a, b)
{
    !(a && b)
}

pub fn before_unless(a: u8, b: u8, c: bool) -> bool
    ensures result == before_unless_isl(a, b, c)
{
    a < b && !c
}

fn main() {}
