//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower=strict -Ztrust-verify=off
//! Trust (wave-LV): the BY-VALUE enum `if let` CONDITION lowers as a real discriminant
//! `Switch` — the same shape `lower_enum_match_general` already emits for
//! `match e { V(..) => .., _ => .. }` — instead of refusing as
//! `Let(pure-value scrutinee)` + `If(cond unsupported)`.
//!
//! Under `-Ztrust-ir-lower=strict` this file pins BOTH halves of the verdict at once, and
//! the second half is the one that matters:
//!
//!   1. every body LOWERS (no unsupported shape), and
//!   2. the MIR re-derived from the producer's own trust-ir AGREES with the built MIR.
//!
//! (2) is why the lane emits `Inst::Switch` rather than the `ICmp(Eq)` + `CondBr` its
//! shared-ref sibling `try_lower_if_let_ref_enum` emits. Built MIR lowers EVERY enum
//! `if let` as `Discriminant(place)` + `switchInt`, so the compare-and-branch spelling
//! reads CLEAN and then mismatches:
//!
//!   built   `b0: switch(disc(isize,deref(a1)))[1->b1,else->b2]`
//!   derived `b0: switch(bin(Eq,bool,disc(isize,deref(a1)),c:uint:1:w32))[0->b1,else->b2]`
//!
//! A body that is clean but strict-red has not been lowered. Every function below was
//! chosen because its built MIR is structurally identical to its `match` twin (only block
//! NUMBERING differs, which the comparator normalizes), so this file fails loudly the
//! moment the lane stops emitting the switch shape.
//!
//! DELIBERATELY ABSENT, each refused by its own tag and each verified refused rather than
//! silently mislowered — a strict fixture cannot contain them, so they are named here:
//!   * `if let E::A(1) = e`  -> `IfLetValue(literal payload subpattern)`. A literal payload
//!     test is a SECOND branch point this one-case switch does not build, AND the `match`
//!     lane's existing spelling of it is itself a measured derived-MIR mismatch
//!     (`b1: switch(fld(downcast(a1,0),0))[1->b2,else->b3]` vs
//!     `b1: switch(bin(Eq,bool,fld(downcast(a1,0),0),c:int:1))[0->b2,else->b3]`).
//!   * `if let Foo::X { ref foo } = x` -> `EnumMatch(non-binding payload subpattern)` from
//!     the SHARED classifier (`ref` / `ref mut` payload bindings).
//!   * `if let Some::<Zst>(t) = ..`   -> `EnumMatch(zst payload binding)`.
//!   * `if let A(_) | B(_) = e`       -> `IfLetValue(or-pattern)`: a MULTI-target test, and
//!     one `SwitchCase` would take the ELSE edge for every other alternative.
//!   * a NON-pure (opaque-payload) enum scrutinee keeps the wave-ER opaque channel
//!     byte-for-byte; the lane's G2 never claims it.

pub enum E {
    A(i32),
    B,
    C,
}

pub enum F {
    P { i: i32, j: i32 },
    Q,
}

// Two-variant enum, WILDCARD payload, value-producing: `switch(disc)[1->then, else->else]`.
fn opt_wild(o: Option<i32>) -> i32 {
    if let Some(_) = o { 1 } else { 0 }
}

// Payload BINDING: the `ThenPrologue` `ExtractField` runs in the then block only.
fn opt_bind(o: Option<i32>) -> i32 {
    if let Some(x) = o { x } else { 0 }
}

// Three-variant enum, NILADIC variant, tested variant is not the last one.
fn e_unit(e: E) -> i32 {
    if let E::B = e { 1 } else { 0 }
}

// Same, tested variant IS the last one — the case value comes from the ledgered
// discriminant, never from a fold of the arm order.
fn e_last(e: E) -> i32 {
    if let E::C = e { 1 } else { 0 }
}

// Three-variant enum with a payload binding on variant 0.
fn e_payload(e: E) -> i32 {
    if let E::A(x) = e { x } else { 0 }
}

// STRUCT variant, two payload bindings at distinct field indices.
fn f_struct(f: F) -> i32 {
    if let F::P { i, j } = f { i + j } else { 0 }
}

// NO else arm (unit-typed `if`), with a merged outer local across the join.
fn no_else(o: Option<i32>) -> i32 {
    let mut n = 0;
    if let Some(x) = o {
        n = x;
    }
    n
}

// `while let` — its desugar reaches the same `lower_if` entry point (measured: the refusal
// it carries today is `If(cond unsupported)` at the desugar's own macro context).
fn while_let(o: Option<i32>) -> i32 {
    let mut n = 0;
    while let Some(x) = o {
        n = x;
        break;
    }
    n
}

fn main() {
    if opt_wild(Some(3)) != 1 || opt_wild(None) != 0 {
        std::process::exit(1);
    }
    if opt_bind(Some(3)) != 3 || opt_bind(None) != 0 {
        std::process::exit(2);
    }
    if e_unit(E::B) != 1 || e_unit(E::C) != 0 {
        std::process::exit(3);
    }
    if e_last(E::C) != 1 || e_last(E::B) != 0 {
        std::process::exit(4);
    }
    if e_payload(E::A(9)) != 9 || e_payload(E::C) != 0 {
        std::process::exit(5);
    }
    if f_struct(F::P { i: 2, j: 5 }) != 7 || f_struct(F::Q) != 0 {
        std::process::exit(6);
    }
    if no_else(Some(4)) != 4 || no_else(None) != 0 {
        std::process::exit(7);
    }
    if while_let(Some(8)) != 8 || while_let(None) != 0 {
        std::process::exit(8);
    }
}

