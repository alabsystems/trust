//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-NSL): the INLINE array-to-slice path admits the same element types the LOCAL
//! path does, and the zero-length fn-ptr containment question was decided on ground truth (the
//! mint no longer asks it at all -- see GATE B).
//!
//! GATE A -- PARITY. `lower_inline_array_to_slice`'s own doc asserts, verbatim, "the same three
//! gates `build_slice_fat_ptr` applies, kept verbatim so the two paths accept exactly the same
//! shapes". wave-NSA and wave-NSA2 widened three of the four element gates from `is_scalar_ty`
//! and left this one; `grep "is_scalar_ty(&elem_ty)"` returned exactly one hit in the whole file
//! and it was here. The two paths silently stopped accepting the same shapes and the doc became
//! false. Measured A/B on the SAME element type: `const S: &[P] = &[P { .. }]` refused with
//! `Slice(non-scalar element)` while `let arr = [P { .. }]; let s: &[P] = &arr;` lowered CLEAN.
//! A coverage answer that depended on whether an array LOCAL existed.
//!
//! GATE B -- GROUND TRUTH. `map_ty`'s zero-length arm asked the TABLE-FREE containment walk,
//! which owes `true` to every `Ty::Struct`/`Ty::Enum` because it holds no tables, and refused
//! the array as `Ty(array elem fn-ptr)`. wave-NSL moved it to the table-bearing walk. Since
//! 2026-09-23 the gate is GONE: every fixed-size array is a first-class `Ty::Array` whatever its
//! length, `[fn(); 2]` included, so "a producer-minted array element never reaches
//! `func_types`" was no longer kept at the mint for any non-zero length, and a refusal that
//! fired only when N == 0 decided coverage on a value. The splice keeps a `Ty::Func` out of the
//! assembled module on its own predicate (`type_entry_ok`/`def_field_ok`/`remap_ty` ->
//! `ty_table_free`), at every length.
//!
//! THE TWO GATES WERE ONE COMMIT. Measured then: with A lifted and B left alone, `const EMPTY:
//! &[C] = &[]` did not retire -- it SWAPPED `Slice(non-scalar element)` for `Ty(array elem
//! fn-ptr)`. Anyone lifting A, measuring +0 and closing the class would have been reading B's
//! shadow.
//!
//! The retiring body has ZERO elements, so no element is ever stored, loaded or addressed: the
//! emitted value is an empty array constant, an `Alloca`, a `Store` and a `PtrFromParts` with
//! length 0 -- the same "the address is real, the length is 0, no element is ever read"
//! argument the shipped `&[B; 0]` lane already makes, and the identical machinery is already
//! `mode=Agreed` for `const S: &[u8] = &[]`.
//!
//! Not under `=strict`: the negative pin must keep its tag.

#![allow(dead_code)]

pub struct C;

pub struct P {
    a: u8,
    b: u32,
}

// THE LANE (`custom-eq-branch-pass::EMPTY` reduced): an empty slice of a struct element. Needs
// gate A to get past the element admission and gate B to get a real `Ty::Array(_, 0)` out of
// `map_ty` instead of the fail-closed `Ty::Unit` placeholder.
pub const EMPTY: &[C] = &[];

// The COLLATERAL body, which needs gate B alone (`detect-extra-ub::VALID_ARRAY` reduced).
pub const V: [Option<i32>; 0] = {
    let e = [None; 0];
    e
};

// The SCALAR-ELEMENT control for the same shape, clean before this wave and after.
pub const VS: [i32; 0] = {
    let e = [0; 0];
    e
};

// The PARITY PAIR that made the divergence visible: same element type, same length, and before
// this wave only the second one lowered.
pub const S: &[P] = &[P { a: 1, b: 2 }, P { a: 3, b: 4 }];

pub fn via_local() -> usize {
    let arr = [P { a: 1, b: 2 }, P { a: 3, b: 4 }];
    let s: &[P] = &arr;
    s.len()
}

// A `[T; 0]` whose element carries a `Ty::Func` field. Gate B used to refuse it at the mint;
// it now lowers exactly as a non-empty fn-pointer array does, and it does not SPLICE: the
// element struct's `Ty::Func` field fails `def_field_ok` (`ty_table_free`), so no per-body
// `func_types` id can reach the assembled module through it.
pub struct HasFnPtr {
    f: fn(),
}

pub const FP: [HasFnPtr; 0] = [];

// FAIL-CLOSED, deliberately NOT widened: a TUPLE element. Its first premise is gone -- since
// 2026-09-23 a tuple-element array is a first-class `Ty::Array` like every fixed-size array (no
// longer `Ty::Tuple([T; N])`), and the two lane walkers resolve an array's element through the
// types table. What remains is the MEMORY half: admitting it here would `Alloca` the array and
// address element `i` at `i * size_of(T)`, which needs the tuple's layout (trust-ir has no
// tuple layout evidence unless a `TupleLayoutDescriptor` was registered for exactly that tuple
// type). That is a separate widening with its own measurement, not a side effect of the
// respelling. Excluded for +1 body.
pub const TUP: &[(&str, &str)] = &[("", ""); 3];

fn main() {}
