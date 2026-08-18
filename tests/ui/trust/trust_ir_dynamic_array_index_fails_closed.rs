//@ check-pass
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
//
// Trust (#202) regression: a DYNAMIC array index must fail closed, and a CONSTANT one must not.
//
// THE DEFECT. `map_ty` spells `[T; N]` (N > 0) as `Ty::Tuple([T; N])`. The dynamic-index path used
// to emit `Inst::ExtractElement { array: <that tuple>, .. }`, but `ExtractElement` requires an
// operand whose type `supports_element_ops()` — and that is `Ty::Vector | Ty::Array` ONLY
// (first-party/trust-ir/crates/trust-ir/src/ty.rs). So every dynamic index emitted an ILL-FORMED
// module: `InvalidVectorElementOp`, "operand must be vector or array". Measured at 7 occurrences
// across 2 corpus files.
//
// WHY IT SURVIVED SO LONG. The arm's own comment justified the lowering with the INTERPRETER: its
// `eval_extract_element` really does accept a runtime index over an `Aggregate` and really does trap
// on out-of-bounds, so the emitted code executed correctly and the bounds obligation was genuinely
// discharged. That argument is about EXECUTION and says nothing about WELL-FORMEDNESS — nothing
// forces a module through the interpreter. #191 made the same mistake one branch over, borrowing
// this comment's out-of-bounds-trap justification for the CONSTANT path, where it did not hold at
// all. Two defects from one over-broad sentence is why the comment now carries its history.
//
// AND THE VALIDATOR IS RIGHT, which is why this is a producer fix and not a format relaxation: a
// runtime index over a TUPLE is ill-typed in general, because tuple elements may differ in type
// while `ExtractElement` carries a single result `ty`. Widening `supports_element_ops` to accept a
// homogeneous tuple would clear the class at zero coverage cost — and make the producer/oracle
// spelling divergence permanent in the format. The oracle already spells arrays first-class
// (`trust-ir-bridge`), so the tuple spelling is the side that is wrong.

// (a) DYNAMIC index — must fail closed, tagged `Index(dynamic index over tuple-spelled array)`.
//     Before #202 this lowered "clean" while emitting an invalid module.
fn dynamic_index(i: usize) -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[i]
}

// A computed dynamic index is the same lane — the index being an expression rather than a bare
// local must not route it anywhere else.
fn dynamic_index_computed(i: usize) -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[i + 1]
}

// (b) THE BOUNDARY, and the half most at risk from a careless fix: a CONSTANT in-bounds index still
//     lowers via `ExtractField`, which IS legal over a tuple aggregate. If a future change makes
//     this fail closed too, the fix was applied one level too high.
fn const_index_in_bounds() -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    a[2]
}

// (c) Array CONSTRUCTION is untouched — it is the other operation over the tuple spelling, and the
//     one that a `Ty::Array` respell would have broken. Pinned here so that trade-off stays visible.
fn construct() -> [u32; 3] {
    [7, 8, 9]
}

// (d) SLICE indexing takes a different path entirely (a faithful fat-pointer read: ExtractField of
//     the data pointer, GEP, Load). It must not be caught by the array-index refusal.
fn slice_index(s: &[u32], i: usize) -> u32 {
    s[i]
}

fn main() {}
