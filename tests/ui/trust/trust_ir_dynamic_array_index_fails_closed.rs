//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#202 regression, REWRITTEN for Step 5 — docs/design/DIRECT-LANE-PROOF-AUTHORITY.md):
// this fixture used to pin "a DYNAMIC array index must fail closed". That refusal is retired for
// the covered shape: the direct lane now emits the bounds check built MIR emits.
//
// HISTORY THE FILE KEEPS. #202: the dynamic path once emitted `ExtractElement` over the
// then-Tuple spelling of `[T; N]` — an ILL-FORMED module (`InvalidVectorElementOp`), lowered
// "clean". #191: the constant path once emitted a bare read with no bounds gate, turning the
// guaranteed panic `arr[10]` on a `[u32; 5]` into a value-returning function. Both defects
// leaned on the same over-broad sentence — "the interpreter traps out-of-bounds" — which is an
// argument about EXECUTION inside the differential harness and says nothing about the emitted
// module's well-formedness or obligations. Nothing forces a module through the interpreter.
//
// THE COVERED SHAPE (Step 5): a `ty::Array` base with a compile-time length, a usize-mapped
// index (64-bit targets), a scalar element, lowerable non-borrow-ptr operands. For it the arm
// emits `Const Usize len` + `ICmp Ult(index, len)` + `Assert(InBounds)` BEFORE the
// `ExtractElement` — MIR's exact shape (`Lt(Copy(index), len)`, expected=true) — and records a
// Pending `BoundsCheck` obligation row (`...#bounds_check#o{n}`, source_id
// `trust-thir-lower/direct-assert@1`). A row is a CLAIM, not a verdict: Pending, formula-free,
// no public identity, no proof authority at any current tier.
//
// STILL REFUSED (each tag names its fix): non-constant array length (generic/unevaluated `N`),
// non-usize index mapping (non-64-bit targets, where `map_ty` fails usize closed), unlowerable
// or borrow-ptr index, non-array base (`Vec`), non-scalar element — and the constant arm's #191
// OOB gate is byte-untouched.

// (a) DYNAMIC index — the POSITIVE covered shape now: lowers WITH a bounds `Assert` and a
//     recorded `bounds_check` obligation row. Before Step 5 this was tagged
//     `Index(dynamic index bounds unmodeled)`.
fn dynamic_index(i: usize) -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[i]
}

// A computed dynamic index is the same lane — the index being an expression rather than a bare
// local must not route it anywhere else. The bounds assert covers the COMPUTED value.
fn dynamic_index_computed(i: usize) -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[i + 1]
}

// (b) THE BOUNDARY: a CONSTANT in-bounds index still takes the constant fast-path (`Const I64` +
//     `ExtractElement` behind the #191 compile-time bounds gate, no runtime assert needed — the
//     gate already decided). If a future change routes it through the dynamic arm's runtime
//     assert, the obligation surface silently grows a row per constant index; if it makes this
//     fail closed, the fix was applied one level too high.
fn const_index_in_bounds() -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[2]
}

// (c) Array CONSTRUCTION is untouched — pinned so the construction/index trade-off stays
//     visible.
fn construct() -> [u32; 3] {
    [7, 8, 9]
}

// (d) SLICE indexing takes a different path entirely (a faithful fat-pointer read: data pointer
//     out, GEP, Load) and must not be caught by any array-arm refusal. Step 5 DISCLOSURE: this
//     lane emits NO bounds `Assert` and NO obligation row — an OOB index traps only in the
//     interpreter, which is the #191-class gap the array path above just closed. The slice lane
//     still carries it, disclosed at `lower_slice_index`; closing it needs the slice len
//     modeled off the fat pointer's metadata lane.
fn slice_index(s: &[u32], i: usize) -> u32 {
    s[i]
}

fn main() {}
