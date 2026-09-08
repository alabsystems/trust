//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-TNB): a tuple/struct MATCH-ARM bind may carry what its `let` twin already carries.
//!
//! The arm classifier serves BOTH bind and test, and a TESTED field genuinely must be scalar --
//! it feeds an integer-width query and an `ICmp`. The scalar gate was applied to BINDS by
//! PROXIMITY rather than by argument, and the `let`-destructure twin, which has no tests to
//! serve, never acquired it. The disagreement is the same operation in two spellings:
//!
//!     let A { a: v } = x; *v          -> CLEAN today
//!     match x { A { a: v } => *v }    -> refused, TupleMatch(non-scalar field binding)
//!
//! Nothing downstream of the gate needed the value to be scalar. The bind carrier is already
//! `(top-level element index, local)` -- this shape's NATIVE form. That is what distinguishes it
//! from the three sub-shapes of the same tag family that landed before it: each of those had to
//! be BENT into the carrier (one by proving the subpattern binds nothing, one by packing a
//! three-part payload address into the u32 key, one by collapsing a whole subpattern into a
//! length test). This one was already in the carrier's shape, so the carrier was never the
//! constraint -- a fourteen-way `matches!` on the element's mapped type was.
//!
//! THREE SITES MOVE TOGETHER: the classifier, its single-arm defensive re-check, and the
//! multi-arm extraction loop. The third carries a DIFFERENT tag, so widening the first two alone
//! would refuse the widened bind there instead and read as a lane that does nothing rather than
//! as a lane half-landed.
//!
//! `Ty::Enum` IS CARVED OUT, and that carve-out is the fragile part of this wave. The multi-arm
//! extraction loop intercepts an enum-typed field and pushes the DISCRIMINANT into its results,
//! not the value -- and that loop is the bind loop's only source. Admitting `Ty::Enum` would
//! `set_local` the TAG under the enum's own name: a silent WRONG VALUE, not a coverage gap. The
//! carve-out is invisible from the classifier (it is a property of what a loop five hundred lines
//! below writes), which is exactly why it is spelled at the predicate rather than delegated to
//! the sibling predicate's answer. `enum_field_stays_refused` is its pin.
//!
//! Not under `=strict`: the negatives must keep their tags.

#![allow(dead_code, unused_variables)]

struct A {
    a: Box<i32>,
}

struct P {
    x: i32,
    y: i32,
}

// THE LANE: the RFC bind-by-move-pattern-guards corpus shape.
pub fn box_field_bind(n: i32) -> i32 {
    let x = A { a: Box::new(n) };
    match x {
        A { a: v } => *v,
    }
}

// The `let` TWIN, clean before this wave and after. It is the whole diagnosis.
pub fn box_field_let(n: i32) -> i32 {
    let x = A { a: Box::new(n) };
    let A { a: v } = x;
    *v
}

// A STRUCT-typed field bind.
struct Q {
    p: P,
}

pub fn struct_field_bind() -> i32 {
    let q = Q { p: P { x: 3, y: 4 } };
    match q {
        Q { p } => p.x + p.y,
    }
}

// A STRUCT-typed TUPLE element bind.
pub fn tuple_elem_bind() -> i32 {
    let t = (P { x: 5, y: 6 }, 7i32);
    match t {
        (p, k) => p.x + k,
    }
}

// With a GUARD, which is the shape the corpus file varies three ways.
pub fn guarded_bind(n: i32) -> i32 {
    let x = A { a: Box::new(n) };
    match x {
        A { a: v } if *v == 42 => *v,
        _ => 0,
    }
}

// FAIL-CLOSED: an ENUM-typed field. If this body ever lowers clean, the extraction loop is
// binding the DISCRIMINANT under the enum's own name and the carve-out has been removed.
enum E {
    X,
    Y,
}

struct W {
    e: E,
    k: i32,
}

pub fn enum_field_stays_refused() -> i32 {
    let w = W { e: E::Y, k: 1 };
    match w {
        W { e, k } => match e {
            E::X => k,
            E::Y => k + 1,
        },
    }
}

// FAIL-CLOSED: a `Ty::Unit` field -- both the value-less unit and the opaque-param placeholder.
// Binding it would hand a value to something whose type says there is none. A later reader
// widening the allow-list to reach this body buys a census number by loosening what the
// predicate means.
struct Foo<T>(T);

impl<T: Copy> Foo<T> {
    pub fn call(self) -> T {
        match self {
            Foo(t) => t,
        }
    }
}

fn main() {}
