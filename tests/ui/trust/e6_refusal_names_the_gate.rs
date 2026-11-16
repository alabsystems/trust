//@ needs-trust-verify
//@ revisions: unopt opt
//@ compile-flags: -Ztrust-verify=on
//@[opt] compile-flags: -O
//@ check-fail
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: HELP
//@ dont-require-annotations: ERROR
//@ normalize-stderr: "elapsed_ms=\d+" -> "elapsed_ms=$$TIME"
//! I0 fixture (E6 admission expansion, design note 2026-09-28 §6): every E6
//! refusal names the GATE that refused the function's kernel import — the FACET
//! gate (Pure, Total, Deterministic, NoPanic), the SHAPE gate
//! (`recognize_admissible_body`, island forwarding) or the MINT — and the
//! construct it refused.
//!
//! Before I0 every function below produced the one sentence "ensures discharge
//! requires the specified function `…` to be E6-admitted (its defining equation
//! kernel-imported); it is not", with and without `-O`, and only
//! `TRUST_E6_DEBUG` told a facet refusal from a shape refusal.
//!
//! Nothing here changes a verdict: every clause was refused before and is
//! refused now (the refusal sentence is a prefix of the new one). The texts
//! come from `trust_certify::clean_island::explain_e6_admission_refusal`; its
//! crate tests pin the same wording without a compiler build. `-O` is the
//! twin (`mir-opt-level` 2), because the readers see the optimizer's MIR.
//!
//! The second half pins the texts' TRUTH (review of I1′): a parameter with no
//! carrier is named even when the E6-only reader read the body; `char`,
//! `usize` and `isize` parameters are spelled as written, not as the `u32` and
//! pointer-width integers the extraction lowers them to; the carrier list
//! names them; and a mint refused because another function's import already
//! holds the mangled kernel name says so and names the holder.

clean {
    def land (a b : UInt64) : UInt64 := a &&& b
    def shl1 (v : UInt32) : UInt32 := v <<< 1
    def widen (x : UInt32) : UInt64 := x.toUInt64
    def sel_lt (c : Bool) (a b : UInt64) : Bool := decide ((if c = true then a else b) < 10)
    def blt (a b : Bool) : Bool := a == b
    def bne_isl (a b : Bool) : Bool := a != b
}

// SHAPE gate (the gate is pinned in the `.stderr`; the annotation pins the construct): a bit
// operation no reader reads.
pub fn bit_and(a: u64, b: u64) -> u64
    ensures result == land(a, b)
    //~^ ERROR the construct outside the E6 fragment is the bit operation `&` (`BinOp::BitAnd`) on `u64`
{
    a & b
}

// FACET gate: a shift carries an overflow `Assert` and a cast of its amount;
// the shift itself is what is named (the `.stderr` pins that half).
pub fn shift_left(v: u32) -> u32
    ensures result == shl1(v)
    //~^ ERROR was refused by the FACET gate (Pure, Total, Deterministic and NoPanic must all be established)
{
    v << 1
}

// SHAPE gate: a plain `as` cast.
pub fn widen_cast(x: u32) -> u64
    ensures result == widen(x)
    //~^ ERROR the construct outside the E6 fragment is the cast `u32 as u64`
{
    x as u64
}

// SHAPE gate: no single construct is outside the fragment (a two-way branch,
// a `u64` `<`); the E6-only tree reader names what it stopped at. (The 3-way
// `||` that stood here is admitted since I3′: `e6_bool_tree_defeq.rs`.)
pub fn select_then_compare(c: bool, a: u64, b: u64) -> bool
    ensures result == sel_lt(c, a, b)
    //~^ ERROR the construct outside the E6 fragment is a comparison `<` over `u64` whose operand is computed outside the arithmetic fragment
{
    (if c { a } else { b }) < 10
}

// MINT: the shape gate reads an ordering over `bool` as a comparison, and the
// mint refuses it.
pub fn bool_lt(a: bool, b: bool) -> bool
    ensures result == blt(a, b)
    //~^ ERROR was refused at the MINT: all four E6 facets hold and the shape gate (`recognize_admissible_body`) read its body as `ComparisonBool`
{
    a < b
}

// MINT, through the E6-only reader, with a parameter that has no carrier: the
// reader reads `a != b`, but `u: ()` has no scalar kernel carrier, so the mint
// is never asked. The refusal names the parameter and the carriers (review:
// it said "the kernel refused the defining equation", which it never did).
pub fn ne_beside_unit(a: bool, b: bool, u: ()) -> bool
    ensures result == bne_isl(a, b)
    //~^ ERROR the kernel import was not minted: the parameter `u: ()` has no scalar kernel carrier (the carriers are `bool`, `u8`..`u64`, `u128`, `i8`..`i128`, `usize` and `isize` (at the target's pointer width), and `char` (as its `u32` scalar value))
{
    a != b
}

// MINT: parameters are spelled as WRITTEN. The extraction the E6 lane reads
// lowers `char` to `u32` and `usize`/`isize` to the pointer-width integers,
// and the refusal used to print those (`c: u32`, `i: i64`).
pub fn ne_beside_char(a: bool, b: bool, c: char) -> bool
    ensures result == bne_isl(a, b)
    //~^ ERROR its parameters span more than one carrier (`a: bool`, `b: bool`, `c: char`), and the `bool` comparison mint is single-domain
{
    a != b
}

pub fn eq_beside_usize(a: bool, b: bool, n: usize) -> bool
    ensures result == blt(a, b)
    //~^ ERROR its parameters span more than one carrier (`a: bool`, `b: bool`, `n: usize`), and the `bool` comparison mint is single-domain
{
    a == b
}

pub fn ne_beside_isize(a: bool, b: bool, i: isize) -> bool
    ensures result == bne_isl(a, b)
    //~^ ERROR its parameters span more than one carrier (`a: bool`, `b: bool`, `i: isize`), and the `bool` comparison mint is single-domain
{
    a != b
}

// MINT: a kernel-NAME collision. `Collide::pair` and `Collide__pair` both
// mangle to `trust_import_e6_refusal_names_the_gate__Collide__pair`; the one
// minted first (the method, walked first) holds the name, and the kernel
// refuses the second declaration (`DuplicateName`). The refusal says so
// (review: it blamed "a literal outside its carrier"). The holder's own clause
// discharges against its own image; nothing is certified against the other's.
pub struct Collide;

impl Collide {
    pub fn pair(a: bool, b: bool) -> bool
        ensures result == bne_isl(a, b)
    {
        a != b
    }
}

#[allow(non_snake_case)]
pub fn Collide__pair(a: bool, b: bool) -> bool
    ensures result == bne_isl(a, b)
    //~^ ERROR its kernel name `trust_import_e6_refusal_names_the_gate__Collide__pair` is already held by the import minted for `e6_refusal_names_the_gate::Collide::pair`
{
    a != b
}

fn main() {}
