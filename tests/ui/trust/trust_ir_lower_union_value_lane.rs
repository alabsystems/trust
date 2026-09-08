//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-UVL): a UNION reached at a WHOLE-VALUE position — a const's own
//! declared type, a local, a param, an array element — and the UNION LITERAL that
//! builds one. Before this wave `map_ty` had no `is_union` test at all, so a union
//! type fell to the terminal catch-all and took a bare `Ty` tag, while
//! `ExprKind::Adt` refused the literal with `Adt(union)`. Those two tags stood
//! ALONE on eight corpus bodies (`union-packed`'s four consts, `union-const-eval`,
//! `union-const-codegen`, `union-inherent-method`, `union_constant::UNINIT`), and
//! they are one mechanism: neither can retire without the other.
//!
//! The VALUE is unchanged. `map_ty`'s catch-all already returned `Ty::Unit`, and
//! the literal now produces the matching value-less spelling — the producer's own
//! information-free placeholder `Const { Ty::Unit, PhantomData }`. Nothing is
//! claimed about the union's BYTES, which is the point: a union literal writes one
//! lane and leaves the rest indeterminate, so a `Constant::Aggregate` seed would
//! assert more than the source does.
//!
//! What replaces the tags is CONFINEMENT, not a model. `register_union_value_lane`
//! installs exactly the pair the shipped union FIELD lane installs
//! (`register_union_lane`): `opaque_collapse`, so the interpretation differential
//! never samples the fabricated lane, and `contains_call`, so the body is NotRun
//! outright. `Lowered::union_lane` ORs the new bool in, and `crate_module::splice_ok`
//! refuses any body carrying it — so nothing here can reach codegen. That is the
//! same status the union FIELD lane's REFUSAL 4 of 4 already assigns to a struct
//! literal carrying a placeholder lane; this is that sentence's other half.
//!
//! DELIBERATELY NOT under `=strict`: a union-lane body is refused by `splice_ok`,
//! so the derived-MIR channel has nothing to compare and the flag would pin a
//! property this lane does not have.
//!
//! FAIL-CLOSED and pinned below: reading a union FIELD keeps its own
//! `Field(non-tuple/struct aggregate)` decline (the oracle's bridge refuses union
//! field PROJECTION too), and matching on a union scrutinee keeps
//! `Match(union scrutinee)`. Neither is widened here.

#![allow(dead_code, unused_variables)]

#[repr(C)]
union U {
    a: u32,
    b: f32,
}

#[repr(C, packed)]
union P {
    a: u8,
    b: u32,
}

// The const's own declared TYPE is the union — this is the `Ty` half, and the
// initializer is the `Adt(union)` half. Four of the eight retired corpus bodies
// are exactly this shape (`union-packed`'s CU/CUP1/CUP2/CUP4C).
const CU: U = U { a: 1 };
const CP: P = P { a: 2 };

// A union-typed LOCAL: the whole-value position with no const-eval involved.
pub fn local_value(x: u32) -> u32 {
    let _u = U { a: x };
    x + 1
}

// A union-typed PARAM. `map_ty` sees the union at the signature, never at a
// struct field, so the positional `(StructId, u32)` ledger cannot key it — which
// is why the confinement needed a body-level bool.
pub fn param_value(u: U, y: u32) -> u32 {
    y + 1
}

// A union at an ARRAY ELEMENT — the third whole-value spelling the union FIELD
// lane's own doc names as one it declines.
pub fn array_element(x: u32) -> u32 {
    let _a = [U { a: x }, U { b: 0.5 }];
    x
}

// The initializer operand is lowered for its EFFECTS: this must not lose the
// increment. (The body is confined either way, but a dropped side effect would be
// a producer bug waiting for the confinement to be relaxed.)
pub fn effectful(mut x: u32) -> u32 {
    let _u = U {
        a: {
            x += 1;
            x
        },
    };
    x
}

// FAIL-CLOSED: a union FIELD READ is NOT widened by this wave.
pub fn field_read_still_declines(x: u32) -> u32 {
    let u = U { a: x };
    unsafe { u.a }
}

fn main() {}
