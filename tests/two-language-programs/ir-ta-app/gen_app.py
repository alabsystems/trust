#!/usr/bin/env python3
"""Assemble the Part A two-language program from per-feature blocks.

`app.rs` (checked in next to this file) is `gen_app.py --all`: ONE crate that exercises every
Rust-half and Lean-half feature of DESIGN.md Part A and folds every result into one number.

`run.sh` calls this again with `--features <ids>` to build `app_max.rs`: the MAXIMAL program
the compiler under test accepts, i.e. the blocks whose minimal probe (probes/<probe>.rs) was
accepted by that compiler (native build AND --emit=trust-ir). Each block is textually the
probe's feature under block-unique names, so a block's acceptance is predicted by its probe.

Every block contributes `(items, expr, expect)`; `program()` folds `expr` values in block
order with a panic-free, std-free mixer, so the reference interpreter can execute it and the
expected value is computable here without running anything (`--expect`).
"""
import argparse
import sys

MASK = (1 << 64) - 1


def mix(acc, v):
    return ((acc << 5) & MASK) ^ (acc >> 3) ^ v


# id, probe (file stem under probes/), header lines, items, expr, expected value of expr
BLOCKS = [
    dict(id="rust.contracts", probe="p01_rust_contracts", items='''
// ---- rust.contracts: requires / ensures / decreases ------------------------------------
#[inline(never)]
pub fn clamp_add(x: u64, y: u64) -> u64
    requires x <= 1000
    requires y <= 1000
    ensures result == x + y
{
    x + y
}
#[inline(never)]
pub fn countdown(n: u64) -> u64
    decreases n
{
    if n > 0 { countdown(n - 1) } else { 7 }
}
''', expr="clamp_add(40, 2) + countdown(5)", expect=49),
    dict(id="rust.loop_invariant", probe="p02_rust_loop_invariant", items='''
// ---- rust.loop_invariant: `invariant` + `decreases` on a while loop ---------------------
#[inline(never)]
pub fn sum_below(n: u64) -> u64
    requires n <= 1000
{
    let mut i = 0u64;
    let mut s = 0u64;
    while i < n
        invariant i <= n
        decreases n - i
    {
        s = s + i;
        i += 1;
    }
    s
}
''', expr="sum_below(10)", expect=45),
    dict(id="rust.struct_enum_match", probe="p03_rust_struct_enum_match", items='''
// ---- rust.struct_enum_match ---------------------------------------------------------------
pub struct Pt { pub x: u64, pub y: u64 }
pub enum Shape { Circle(u64), Rect(u64, u64), Empty }
#[inline(never)]
pub fn norm1(p: &Pt) -> u64 { p.x + p.y }
#[inline(never)]
pub fn area(s: &Shape) -> u64 {
    match s {
        Shape::Circle(r) => *r * *r * 3,
        Shape::Rect(w, h) => *w * *h,
        Shape::Empty => 0,
    }
}
''', expr="norm1(&Pt { x: 3, y: 4 }) + area(&Shape::Rect(2, 5)) + area(&Shape::Circle(2)) + area(&Shape::Empty)", expect=29),
    dict(id="rust.slice_index", probe="p04_rust_slice_index", items='''
// ---- rust.slice_index: a bounds obligation --------------------------------------------------
#[inline(never)]
pub fn nth(xs: &[u64], i: usize) -> u64
    requires i < xs.len()
{
    xs[i]
}
''', expr="nth(&[7u64, 8, 9], 1)", expect=8),
    dict(id="rust.checked_arith", probe="p05_rust_checked_arith", items='''
// ---- rust.checked_arith: overflow + div-by-zero obligations ---------------------------------
#[inline(never)]
pub fn scale(a: u32, b: u32) -> u32
    requires a <= 1000
    requires b <= 1000
{
    a * b + a
}
#[inline(never)]
pub fn ratio(a: u64, b: u64) -> u64 {
    if b == 0 { 0 } else { a / b }
}
''', expr="scale(6, 7) as u64 + ratio(100, 7)", expect=62),
    dict(id="rust.closure", probe="p06_rust_closure", items='''
// ---- rust.closure: a capturing closure ------------------------------------------------------
#[inline(never)]
pub fn apply_twice(k: u64, x: u64) -> u64 {
    let add_k = |v: u64| v + k;
    add_k(add_k(x))
}
''', expr="apply_twice(5, 1)", expect=11),
    dict(id="rust.u128", probe="p07_rust_u128", items='''
// ---- rust.u128: a constant above i128::MAX --------------------------------------------------
#[inline(never)]
pub fn wide(a: u64, b: u64) -> u64 {
    let big: u128 = 0xFFFF_FFFF_0000_0000_0000_0000_0000_0000;
    let p = ((a as u128) * (b as u128)) ^ big;
    ((p >> 64) as u64) ^ (p as u64)
}
''', expr="wide(0x1_0000_0001, 0x1_0000_0003) & 0xFFFF", expect=None),
    dict(id="rust.mut_ref", probe="p08_rust_mut_ref", items='''
// ---- rust.mut_ref: a `&mut` function (give-back shape) ---------------------------------------
#[inline(never)]
pub fn bump(x: &mut u64, by: u64) {
    *x = *x + by;
}
#[inline(never)]
pub fn bump_twice(start: u64) -> u64 {
    let mut v = start;
    bump(&mut v, 5);
    bump(&mut v, 6);
    v
}
''', expr="bump_twice(10)", expect=21),
    dict(id="rust.std_call", probe="p09_rust_std_call", items='''
// ---- rust.std_call: a call into an UPSTREAM (`core`) body -----------------------------------
#[inline(never)]
pub fn wrap_inc(x: u64) -> u64 {
    x.wrapping_add(1)
}
''', expr="wrap_inc(u64::MAX) + wrap_inc(4)", expect=5),
    dict(id="lean.wrapping_uint64", probe="p10_lean_wrapping_uint64", items='''
// ---- lean.wrapping_uint64 (tier gate) + Rust -> Lean call -----------------------------------
pub mod lw {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
        def addmul (a : UInt64) (b : UInt64) : UInt64 := a * b + a
        def wsub (a : UInt64) (b : UInt64) : UInt64 := a - b
    }
}
''', expr="lw::wsum(40, 2) + lw::addmul(6, 7) + lw::wsum(lw::wsub(1, 2), 3)", expect=92),
    dict(id="lean.projection_literal", probe="p11_lean_projection_literal", items='''
// ---- lean.projection_literal ---------------------------------------------------------------
pub mod lp {
    clean {
        def snd (a : UInt64) (b : UInt64) : UInt64 := b
        def k32 (a : UInt32) : UInt32 := 300
    }
}
''', expr="lp::snd(1, 9) + lp::k32(0) as u64", expect=309),
    dict(id="lean.bool_cmp", probe="p12a_lean_bool_cmp", items='''
// ---- lean.bool_cmp: Bool comparison (`decide`) ---------------------------------------------
pub mod lbc {
    clean {
        def lt (a : UInt64) (b : UInt64) : Bool := a < b
        def eqf (a : UInt64) (b : UInt64) : Bool := a == b
    }
}
''', expr="(lbc::lt(3, 9) as u64) + 2 * (lbc::eqf(7, 7) as u64) + 4 * (lbc::lt(9, 3) as u64)", expect=3),
    dict(id="lean.bool_connective", probe="p12b_lean_bool_connective", items='''
// ---- lean.bool_connective: not / && / || ---------------------------------------------------
pub mod lbn {
    clean {
        def neg (b : Bool) : Bool := not b
        def conj (a : Bool) (b : Bool) : Bool := a && b
        def disj (a : Bool) (b : Bool) : Bool := a || b
    }
}
''', expr="(lbn::neg(false) as u64) + 2 * (lbn::conj(true, true) as u64) + 4 * (lbn::disj(false, false) as u64)", expect=3),
    dict(id="lean.let", probe="p13_lean_let", items='''
// ---- lean.let ------------------------------------------------------------------------------
pub mod ll {
    clean {
        def sq_let (x : UInt64) : UInt64 := let y := x + 1; y * y
        def nested_let (x : UInt64) : UInt64 := let y := x; let z := y + 1; z
    }
}
''', expr="ll::sq_let(3) + ll::nested_let(5)", expect=22),
    dict(id="lean.select", probe="p14_lean_select", items='''
// ---- lean.select: `if`-select (tier structural) ---------------------------------------------
pub mod ls {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
''', expr="ls::min2(100, 41) + ls::min2(3, 8)", expect=44),
    dict(id="lean.inductive_in_module", probe="p15a_lean_inductive_in_module", items='''
// ---- lean.inductive_match: an `inductive` + `match` (tier general) ---------------------------
pub mod li {
    clean {
        inductive Tri where
          | one : Tri
          | two : Tri
          | three : Tri

        def triRank (t : Tri) : UInt64 :=
          match t with
          | Tri.one => 1
          | Tri.two => 2
          | Tri.three => 3

        def keepTri (a : UInt64) (b : UInt64) : UInt64 := a
    }
}
''', expr="li::keepTri(2, 9)", expect=2),
    dict(id="lean.inductive_wrapped", probe="p15c_lean_inductive_wrapped", items='''
// ---- lean.inductive_match, reached from Rust through a machine-width wrapper -----------------
pub mod liw {
    clean {
        inductive Duo where
          | lo : Duo
          | hi : Duo

        def duoRank (t : Duo) : UInt64 :=
          match t with
          | Duo.lo => 1
          | Duo.hi => 2

        def rankOfHi (x : UInt64) : UInt64 := duoRank Duo.hi
    }
}
''', expr="liw::rankOfHi(0)", expect=2),
    dict(id="lean.nat_structural", probe="p16_lean_nat_structural", header="extern crate trust_bignum;", items='''
// ---- lean.nat_structural: structural recursion over Nat (the Nat-handle lane) ----------------
clean {
    def tozero : Nat -> Nat
      | 0 => 0
      | n + 1 => tozero n
}
#[inline(never)]
pub fn nat_structural(v: u64) -> u64 {
    match tozero(trust_bignum::Nat::from_u64(v)).to_u64() { Some(r) => r + 11, None => 0 }
}
''', expr="nat_structural(3)", expect=11),
    dict(id="lean.nat_wf", probe="p17_lean_nat_wf", header="extern crate trust_bignum;", items='''
// ---- lean.nat_wf: well-founded recursion over Nat --------------------------------------------
clean {
    def countdownSum (n : Nat) : Nat := if h : 0 < n then n + countdownSum (n - 1) else 0
    termination_by n
}
#[inline(never)]
pub fn nat_wf(v: u64) -> u64 {
    match countdownSum(trust_bignum::Nat::from_u64(v)).to_u64() { Some(r) => r, None => 0 }
}
''', expr="nat_wf(5)", expect=15),
    dict(id="two_lang.citation", probe="p18_theorem_citation", items='''
// ---- two_lang.citation: a Lean theorem + a Rust `ensures … by thm` ---------------------------
clean {
    theorem min2_le_left : forall (x : UInt64) (y : UInt64),
        Nat.le (UInt64.toNat (if x < y then x else y)) (UInt64.toNat x) :=
        fun x y => Decidable.casesOn
            (motive := fun (d : Decidable (LT.lt x y)) =>
                Nat.le (UInt64.toNat (Decidable.casesOn (motive := fun _ => UInt64)
                    d (fun _ => y) (fun _ => x))) (UInt64.toNat x))
            (instDecidableUInt64Lt x y)
            (fun h => Iff.mp (Nat.not_lt (UInt64.toNat x) (UInt64.toNat y)) h)
            (fun h => @Nat.le.refl (UInt64.toNat x))
}
#[inline(never)]
pub fn rmin2(a: u64, b: u64) -> u64 {
    if a < b { a } else { b }
}
#[inline(never)]
pub fn pick_min(x: u64, y: u64) -> u64
    ensures rmin2(x, y) <= x by min2_le_left
{
    rmin2(x, y)
}
''', expr="pick_min(41, 7)", expect=7),
    dict(id="two_lang.lean_calls_rust", probe="p19_lean_calls_rust", items='''
// ---- two_lang.lean_calls_rust: Lean -> Rust (RustCallChain) ---------------------------------
#[inline(never)]
pub fn rx55(x: u64) -> u64 { x ^ 0x55 }
clean {
    def thrice_rx (x : UInt64) : UInt64 := rx55 (rx55 (rx55 x))
}
''', expr="thrice_rx(5)", expect=80),
    dict(id="two_lang.cross_crate", probe="p20_cross_crate", header="extern crate dep;", items='''
// ---- two_lang.cross_crate: dep's Rust fn AND dep's Clean def ---------------------------------
#[inline(never)]
pub fn through_dep(a: u64, b: u64) -> u64 {
    dep::m::dep_mix(a, b) + dep::dep_clamp(99, 50)
}
''', expr="through_dep(10, 4)", expect=84),
]


def wide_expect():
    a, b = 0x1_0000_0001, 0x1_0000_0003
    p = (a * b) ^ 0xFFFF_FFFF_0000_0000_0000_0000_0000_0000
    return (((p >> 64) & MASK) ^ (p & MASK)) & 0xFFFF


for _b in BLOCKS:
    if _b["id"] == "rust.u128":
        _b["expect"] = wide_expect()


def select(features):
    if features is None:
        return list(BLOCKS)
    known = {b["id"] for b in BLOCKS}
    bad = [f for f in features if f not in known]
    if bad:
        sys.exit(f"gen_app: unknown feature id(s): {bad}")
    return [b for b in BLOCKS if b["id"] in features]


def expected(blocks):
    acc = 0
    for b in blocks:
        acc = mix(acc, b["expect"])
    return acc


def render(blocks, title):
    headers = []
    for b in blocks:
        h = b.get("header")
        if h and h not in headers:
            headers.append(h)
    out = []
    out.append(f"//! {title}")
    out.append("//! GENERATED by parta/gen_app.py — edit the blocks there, not this file.")
    out.append("//! Features: " + ", ".join(b["id"] for b in blocks))
    out.append(f"// EXPECT: {expected(blocks)}")
    out.append("#![allow(dead_code)]")
    out.extend(headers)
    for b in blocks:
        out.append(b["items"].rstrip("\n"))
    out.append('''
// ---- the fold: panic-free and std-free, so the reference interpreter can run it --------------
#[inline(never)]
pub fn mix(acc: u64, v: u64) -> u64 {
    (acc << 5) ^ (acc >> 3) ^ v
}

/// Nullary entry: every feature's result folded into ONE number.
pub fn program() -> u64 {
    let mut acc = 0u64;''')
    for b in blocks:
        out.append(f"    acc = mix(acc, {b['expr']}); // {b['id']} = {b['expect']}")
    out.append('''    acc
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}''')
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--features", help="comma-separated block ids")
    ap.add_argument("--list", action="store_true", help="print `id probe expect` rows")
    ap.add_argument("--expect", action="store_true", help="print only the expected value")
    ap.add_argument("-o", "--out")
    a = ap.parse_args()
    if a.list:
        for b in BLOCKS:
            print(b["id"], b["probe"], b["expect"])
        return
    feats = None if a.all or a.features is None else [f for f in a.features.split(",") if f]
    blocks = select(feats)
    if a.expect:
        print(expected(blocks))
        return
    title = ("Part A — the FULL two-language program (every feature of DESIGN.md Part A)."
             if feats is None else
             "Part A — the MAXIMAL two-language program the compiler under test accepts.")
    text = render(blocks, title)
    if a.out:
        open(a.out, "w").write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
