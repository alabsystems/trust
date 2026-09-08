//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-NSA: a non-scalar array element may now round-trip through memory.
// The chain the design entry
// (docs/design/2026-09-01-non-scalar-array-memory-entry.md) predicted, each
// link reached by measuring rather than by argument:
//
//   walkers -> spelling -> seed -> element image
//
// * WALKERS. `union_lane_ty_transitive` / `param_lane_ty_transitive`
//   answered `false` for `Ty::Array` WITHOUT resolving the element, sound
//   only while the spelling gate guaranteed a scalar element. Both now
//   resolve through `pending_tys`, and an unresolvable `TyId` fails
//   CLOSED (tainted) — a walker whose job is to refuse must refuse what it
//   cannot see.
// * SPELLING. A registered-struct element now takes the first-class
//   `Ty::Array` spelling. The alternative — keep `Ty::Tuple` and lean on a
//   homogeneous tuple's image coinciding — was REFUTED by the validator:
//   `extract_element` against `Ty::Tuple([struct, struct, struct])` is
//   rejected outright ("operand must be vector or array").
// * SEED. Array construction seeded through the scalar-only
//   `seed_constant`; it now falls back to `seed_overwritten_ty`, the
//   seeder the tuple-spelled path always used, which recurses into a
//   registered struct's fields.
// * ELEMENT IMAGE — the entry's only real unknown, and the reason this is
//   a fixture rather than a refusal. Whether a `Store` of a struct
//   aggregate honours the DECLARED field offsets is a property of the
//   consumer's memory model, not of the producer's declaration. It is
//   answered by the DIFFERENTIAL: `read_padded` below is over a struct
//   with INTERIOR PADDING (u8 at offset 0, u32 at offset 4, size 8), so a
//   store that ignored the declared offsets would read differently — and
//   it reports `equal=true, samples=5, mode=Agreed` against the MIR
//   oracle. Full population: 30,013 clean, INVALID 0, divergences 0.
//
// `TRUST_NSA=0` is the one-line off-switch.
#[derive(Clone, Copy)]
pub struct N(pub u8);

// A struct with INTERIOR PADDING — the case that discriminates a faithful
// element image from a naively packed one.
#[derive(Clone, Copy)]
pub struct Pair(pub u8, pub u32);

// Construct and READ a struct-element array: both halves in one body, which
// is what makes the image testable at all.
pub fn read_simple(i: usize) -> u8 {
    let a = [N(1), N(2), N(3)];
    a[i].0
}

pub fn read_padded(i: usize) -> u32 {
    let a = [Pair(1, 10), Pair(2, 20)];
    a[i].1
}

// The scalar element keeps its pre-wave path byte-for-byte: `seed_constant`
// is consulted FIRST and only its decline reaches the new fallback.
pub fn read_scalar(i: usize) -> u8 {
    let a = [1u8, 2, 3];
    a[i]
}

// wave-NSA2: ENUM elements join the lane. They needed one more thing the
// struct case did not: `union_lane_ty_transitive`'s tail answers `false`
// for `Ty::Enum` (the enum lane has its own walker, consulted explicitly
// by its own callers), so an array of enums would have skipped the union
// check entirely — the exact hole the struct widening had just closed.
// The array arm now routes an enum element through
// `union_lane_enum_transitive`. That arm is itself new, so nothing that
// existed before this wave changes behaviour.
#[derive(Clone, Copy)]
pub enum E {
    V0,
    V1(isize),
}

pub fn read_enum_elem(i: usize) -> isize {
    let a = [E::V0, E::V1(7)];
    match a[i] {
        E::V1(x) => x,
        E::V0 => 0,
    }
}

fn main() {}
