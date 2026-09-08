//@ dont-check-compiler-stderr
//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//@ edition: 2021
//! Trust (wave-NSL): the INLINE array-to-slice path admits the same element types the LOCAL
//! path does, and the zero-length fn-ptr containment question is decided on ground truth.
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
//! which owes `true` to every `Ty::Struct`/`Ty::Enum` because it holds no tables. The
//! table-bearing sibling already exists and is already called this exact way for fn-ptr
//! signature components. It still answers `true` for an unregistered id and still delegates
//! every spelling it does not model back to the table-free walk, so the invariant -- a
//! producer-minted `Ty::Array`'s element must not reach `func_types`, because the splice's
//! `TyId` re-interning is non-recursive -- is preserved exactly and merely decided on ground
//! truth instead of on ignorance.
//!
//! THE TWO GATES ARE ONE COMMIT. Measured: with A lifted and B left alone, `const EMPTY: &[C] =
//! &[]` does not retire -- it SWAPS `Slice(non-scalar element)` for `Ty(array elem fn-ptr)`.
//! Anyone lifting A, measuring +0 and closing the class would have been reading B's shadow.
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

// FAIL-CLOSED, and gate B's mutation proof: a `[T; 0]` whose element really does carry a
// `Ty::Func` field must STILL be refused. If this body ever lowers clean, gate B has become a
// rubber stamp and the splice invariant it protects is gone.
pub struct HasFnPtr {
    f: fn(),
}

pub const FP: [HasFnPtr; 0] = [];

// FAIL-CLOSED, deliberately NOT widened: a TUPLE element. It looks free -- the tuple-element
// array VALUE builds clean today -- but the slice element gate and `map_ty`'s ARRAY SPELLING
// gate are one decision. A tuple-element array still takes the legacy `Ty::Tuple([T; N])`
// spelling, so admitting it here would `Alloca` a `Ty::Tuple` and hand out a slice fat pointer
// whose declared element type is not the allocation's element type, with the element address
// computation resting on an unstated tuple-layout-equals-array-layout assumption. Moving tuples
// to the `Ty::Array` spelling first requires teaching the two lane walkers to resolve a
// tuple-in-array element, which the pinned array-spelling test already names as the
// prerequisite. Excluded for +1 body.
pub const TUP: &[(&str, &str)] = &[("", ""); 3];

fn main() {}
