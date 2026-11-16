//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//! E6 admission expansion I3′ — the REFUSALS. The kernel re-types every mint
//! but cannot see a wrong READING of the body (design note 2026-09-28 §5 rule
//! 5), so each case below is a BODY-side mutation against a fixed island: the
//! body the reader would have to misread for the clause to discharge.
//!
//! * `||` where the model says `&&`; `s & i | n` against `s && i && n`; a
//!   comparison leaf with its operands swapped; a negation moved to the other
//!   operand. Each is admitted (the tree reader reads it) and refused by the
//!   KERNEL as not definitionally equal.
//! * Stays outside the fragment, refused by the SHAPE gate with the construct
//!   named (I0): an ORDERING over `bool` inside a tree (no image, review H1),
//!   a bit operation over `u8` (increment I2′), and a comparison whose operand
//!   is computed — which no single construct explains, so the tree reader's
//!   own refusal names it.

clean {
    def and_isl (c e : Bool) : Bool := c && e
    def and3_isl (s i n : Bool) : Bool := s && i && n
    def lt_or_eq_isl (a b : UInt8) : Bool := decide (a < b) || a == b
    def gate_isl (w c e : Bool) : Bool := w && (c || !e)
    def ord_isl (a b c : Bool) : Bool := (!a && b) || c
    def bit_isl (a b : UInt8) : Bool := decide (a &&& b = 0) || decide (a < b)
    def comp_isl (a b : Bool) (x : UInt8) : Bool := decide ((if a = true then x else 0) < 5) || b
}

pub fn or_against_and(c: bool, e: bool) -> bool
    ensures result == and_isl(c, e)
    //~^ ERROR the two sides are not definitionally equal
{
    c || e
}

pub fn and_or_against_and3(s: bool, i: bool, n: bool) -> bool
    ensures result == and3_isl(s, i, n)
    //~^ ERROR the two sides are not definitionally equal
{
    s & i | n
}

pub fn swapped_leaf(a: u8, b: u8) -> bool
    ensures result == lt_or_eq_isl(a, b)
    //~^ ERROR the two sides are not definitionally equal
{
    b < a || a == b
}

pub fn negation_moved(w: bool, c: bool, e: bool) -> bool
    ensures result == gate_isl(w, c, e)
    //~^ ERROR the two sides are not definitionally equal
{
    w && (!c || e)
}

pub fn ordering_in_a_tree(a: bool, b: bool, c: bool) -> bool
    ensures result == ord_isl(a, b, c)
    //~^ ERROR the construct outside the E6 fragment is the ordering comparison `<` (`BinOp::Lt`) on `bool`
{
    (a < b) || c
}

pub fn bit_op_over_u8(a: u8, b: u8) -> bool
    ensures result == bit_isl(a, b)
    //~^ ERROR the construct outside the E6 fragment is the bit operation `&` (`BinOp::BitAnd`) on `u8`
{
    a & b == 0 || a < b
}

pub fn computed_operand(a: bool, b: bool, x: u8) -> bool
    ensures result == comp_isl(a, b, x)
    //~^ ERROR the construct outside the E6 fragment is a comparison `<` over `u8` whose operand is computed outside the arithmetic fragment
{
    (if a { x } else { 0 }) < 5 || b
}

fn main() {}
