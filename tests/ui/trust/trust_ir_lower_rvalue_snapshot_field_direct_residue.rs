//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=on -Ztrust-policy=advisory
//@ needs-trust-verify
//@ dont-require-annotations: WARN
//@ dont-require-annotations: NOTE
//! **RESIDUE PIN (2026-09-16): a USER-WRITTEN aggregate literal with a borrowed
//! rvalue field is still refused under strict.**
//!
//! `trust_ir_lower_rvalue_snapshot_field.rs` admits the `format_args!` shape —
//! `super let args = (&f(x),)` — because that tuple element is minted at the
//! wave-SB CALL-ARGUMENT snapshot, the one site that consults rustc's
//! promotability rule and ledgers the pointer for `borrow_ptr_field_admissible`.
//! The four shapes below carry the SAME borrowck argument (a `FnDef` call
//! temporary is never promoted, so an aggregate holding `&f(x)` cannot escape
//! the frame) but their `&f(x)` is minted at a different borrow site, which the
//! landing deliberately did not touch. They therefore keep the pre-existing
//! `Tuple(borrow ptr field)` / `Adt(borrow ptr field)` refusal, and this file
//! pins that boundary so a later widening moves a fixture rather than a
//! sentence: when the second mint learns the predicate, these four go green
//! and this file must be deleted (or folded into the admitted-shape fixture).
//!
//! What is NOT claimed: nothing about the values — only where the lane's reach
//! ends today, measured on a stage1 built from the landing tree.

fn f(x: u32) -> u32 {
    x.wrapping_add(1)
}

fn g(y: u32) -> u32 {
    y.wrapping_mul(3)
}

struct S<'a> {
    r: &'a u32,
    tag: u8,
}

fn take_pair(p: (&u32,)) -> u32 {
    let _ = p;
    1
}

fn take_s(s: S<'_>) -> u8 {
    let _ = s;
    1
}

fn take_opt(p: (&Option<u32>,)) -> bool {
    let _ = p;
    true
}

fn take_arr(p: (&[u32; 2],)) -> u32 {
    let _ = p;
    1
}

pub fn through_tuple(x: u32) -> u32 { //~ ERROR could not fully lower this body
    take_pair((&f(x),))
}

pub fn through_struct(y: u32) -> u8 { //~ ERROR could not fully lower this body
    take_s(S { r: &g(y), tag: 1 })
}

pub fn through_enum(x: u32) -> bool { //~ ERROR could not fully lower this body
    take_opt((&Some(f(x)),))
}

pub fn through_array(x: u32) -> u32 { //~ ERROR could not fully lower this body
    take_arr((&[f(x), 1],))
}

fn main() {
    through_tuple(1);
    through_struct(2);
    through_enum(3);
    through_array(4);
}
