//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//! E6 admission expansion I1′ — the REFUSALS, each a BODY-side mutation
//! against a fixed island (design note 2026-09-28 §5 rule 5): the kernel
//! cannot see a wrong reading of the body, so the only test that the reader
//! and the mint dispatch on the right operator is a wrong body against a
//! right model.
//!
//! * `<`, `<=` and `>` over `bool` are ORDERINGS. `recognize_admissible_body`
//!   reads them as `ComparisonBool { cmp: Lt | Le }` (`>` by operand swap), and
//!   the mint must refuse them rather than give them the `==` image — at
//!   `(false, true)` Rust's `a < b` is `true` and `a == b` is `false` (review
//!   H1). Each is refused at the MINT, naming the operator.
//! * `!=` against an `==` model: `!=` IS admitted now, so this one reaches the
//!   kernel and is refused THERE as not definitionally equal.
//! * a comparison of a comparison against a `bool` (`(x < y) == c`) and `!=`
//!   over integers are READ since I3′ (the E6-only tree reader), so each is
//!   now a body-side mutation against a WRONG model (`<=` for `<`, `==` for
//!   `!=`), refused by the kernel as not definitionally equal.
//! * `==` over `bool` beside an integer parameter: the single-domain mint
//!   refuses it, naming the carriers.

clean {
    def beq_isl (a b : Bool) : Bool := a == b
    def beq_of (x y : UInt8) (c : Bool) : Bool := decide (x <= y) == c
    def ne_isl (a b : UInt8) : Bool := a == b
    def beq_mixed (a : Bool) (n : UInt8) : Bool := a == a
}

pub fn ordered_lt(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //~^ ERROR was refused at the MINT: all four E6 facets hold and the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`
{
    a < b
}

pub fn ordered_le(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //~^ ERROR an ordering over `bool`
{
    a <= b
}

pub fn ordered_gt(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //~^ ERROR an ordering over `bool`
{
    a > b
}

pub fn not_equal_against_eq(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //~^ ERROR was not discharged by definitional equality
{
    a != b
}

pub fn eq_of_comparison(x: u8, y: u8, c: bool) -> bool
    ensures result == beq_of(x, y, c)
    //~^ ERROR the two sides are not definitionally equal
{
    (x < y) == c
}

pub fn ne_over_ints(a: u8, b: u8) -> bool
    ensures result == ne_isl(a, b)
    //~^ ERROR the two sides are not definitionally equal
{
    a != b
}

pub fn eq_beside_an_int(a: bool, n: u8) -> bool
    ensures result == beq_mixed(a, n)
    //~^ ERROR was refused
{
    let _ = n;
    a == a
}

fn main() {}
