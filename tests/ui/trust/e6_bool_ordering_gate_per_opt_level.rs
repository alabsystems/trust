//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! WHERE each comparison over `bool` is refused, at each MIR opt level — the
//! claim `docs/TWO_LANGUAGE_CONVERSION_GUIDE.md` §5b makes, pinned (review of
//! E6 expansion I1′: the guide said the orderings are "refused at the mint",
//! which holds only for the MIR the default and `-O` lanes produce).
//!
//! * default (`mir-opt-level` 1) and `-O` (2): the body is one statement,
//!   `_0 = Lt(copy _1, copy _2)`. The SHAPE gate reads an ordering as
//!   `ComparisonBool` (`>`/`>=` by operand swap) and the MINT refuses it,
//!   because only `==` has the equality image. `==` and `!=` discharge.
//! * `-Zmir-opt-level=0`: the comparison lands in a temporary and the body
//!   ends `_0 = copy _3`, which the frozen chain does not read. Since E6
//!   expansion I3′ the E6-only TREE reader reads it: `==`/`!=` discharge here
//!   too, and the orderings are refused by the SHAPE gate (the tree reader has
//!   no image for an ordering over `bool` either).
//!
//! No revision certifies an ordering against the equality island: that is the
//! soundness half, and it holds at all three levels.

clean {
    def beq_isl (a b : Bool) : Bool := a == b
    def bne_isl (a b : Bool) : Bool := a != b
}

pub fn lt(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //[unopt,opt]~^ ERROR the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`, but the kernel import was not minted: an ordering over `bool`
{
    a < b
}

pub fn le(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //[unopt,opt]~^ ERROR the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`, but the kernel import was not minted: an ordering over `bool`
{
    a <= b
}

pub fn gt(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //[unopt,opt]~^ ERROR the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`, but the kernel import was not minted: an ordering over `bool`
{
    a > b
}

pub fn ge(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
    //[unopt,opt]~^ ERROR the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`, but the kernel import was not minted: an ordering over `bool`
{
    a >= b
}

// `==` and `!=` discharge at every level: through the frozen chain and the
// I1′ node where the body is one statement, through the tree reader at
// `-Zmir-opt-level=0`.
pub fn eq(a: bool, b: bool) -> bool
    ensures result == beq_isl(a, b)
{
    a == b
}

pub fn ne(a: bool, b: bool) -> bool
    ensures result == bne_isl(a, b)
{
    a != b
}

fn main() {}
