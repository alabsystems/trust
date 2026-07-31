//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//! Trust (#174): an enum with a STRUCT payload lowers first-class and splices.
//!
//! This was refused for a long time under the name "the enum-struct-payload
//! NO-GO". `register_enum` walled every variant field to a seedable scalar,
//! partly because `splice_ok` required enum variant fields to be table-free,
//! which in turn was required because pass 1 interned the assembled module's
//! tables in the fixed order enums -> structs -> types: an enum def could not
//! name a struct id that had not been interned yet.
//!
//! That ordering was an ASSEMBLER CONVENTION, never a format rule. In
//! first-party/trust-ir, `ty_layout_shape_inner`'s `Ty::Struct(id)` arm
//! resolves by lookup in `self.structs`, and the validator's
//! enum-variant-field check is a dangling-reference check through
//! `module.struct_def(id)` — also a lookup. Both demand RESOLVABILITY, not an
//! order. So pass 1 now interns the enum+struct DAG TOPOLOGICALLY (cycles and
//! out-of-range ids fail the body closed), `splice_ok` checks resolvability
//! alone, and `enum_variant_field_admissible` admits a struct payload whose
//! registered def carries a size.
//!
//! Verified out-of-band on the dumped module: `trust-ir validate` reports
//! "module is well-formed" for `enum @E { A(struct.0), B }`, and for the
//! two-level `Option<NonZeroU64>` chain `enum -> struct.1 -> struct.0`.
//!
//! The measured effect was to convert bodies from clean-but-unmodelled into
//! modelled: OPAQUE-COLLAPSE 768 -> 110, MODELLED 4838 -> 5495 on ui_sample.

pub struct Pair {
    pub a: i32,
    pub b: i64,
}

pub enum E {
    A(Pair),
    B,
}

// Match on a struct-payload variant, binding the payload and projecting it.
pub fn read(e: E) -> i32 {
    match e {
        E::A(p) => p.a,
        E::B => 0,
    }
}

// Construct one.
pub fn make(x: i32, y: i64) -> E {
    E::A(Pair { a: x, b: y })
}

// The std shape this really unlocks: a niche-optimized enum over a struct
// payload, whose def chains one struct through another.
pub fn opt_nonzero(v: Option<std::num::NonZeroU64>) -> i32 {
    match v {
        Some(_) => 1,
        None => 0,
    }
}

// A struct-payload variant that is NOT variant 0 — the seed path only
// materializes variant 0, so this pins that the admission gate is per-variant
// for sizability and variant-0-only for seedability.
pub enum Late {
    Zero,
    One(Pair),
}
pub fn late(l: Late) -> i64 {
    match l {
        Late::Zero => 0,
        Late::One(p) => p.b,
    }
}

fn main() {}
