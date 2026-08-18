// LANE P (adversarial review of lane K, 2026-08-13) — shapes where one block plays
// TWO roles, which `plan_branch_markers` permits (it forbids only arm∩join and
// duplicate arms/joins).
//
// THIS FILE WAS THE SUFFICIENCY COUNTEREXAMPLE, AND IS NOW THE REGRESSION FIXTURE FOR
// ITS CLOSURE (2026-08-13). `join_is_head`, `chain_of_ifs` and `double_nested_cond`
// passed EVERY condition in `plan_branch_markers` — the plan engaged and the shim
// emitted markers — and the sequence was still not built's:
//
//   line 2: built `mk b0.0:live s2:bool` vs derived `mk b2.0:dead s1:u32`
//
// Built's `as_temp` opens the OUTER comparison's result temp in the head block,
// BEFORE evaluating the inner `if`; the shim's linear instruction walk reaches the
// inner branch first. Ordering rule (1) in `plan_branch_markers` catches this when the
// inner value is a MARKED result; here it is a join block PARAMETER, so the rule did
// not fire.
//
// CLOSED by the JOIN-PARAMETER rule: a join block's parameter may be consumed only by a
// terminator. MEASURED at that fix, independently sealed control (352aa0306d) vs
// subject, this file, `-Copt-level=3`:
//
//   join_is_head        derived `mk b2.0:dead s1:u32`  ->  derived `<end>`
//   chain_of_ifs        derived `mk b2.0:dead s1:u32`  ->  derived `<end>`
//   double_nested_cond  derived `mk b2.0:dead s1:u32`  ->  derived `<end>`
//
// i.e. the shim stops offering a WRONG sequence and offers NONE. Both positive controls
// (`arm_is_head_shared_join`, `min_if`) keep `markers_exact: true` and their flips; the
// whole-crate clean-kernel differential moved 0 of 13769 rows at either opt level.
//
// MEASURED, control (trust e4f16776fa) vs subject (lane K rebased), both drivers
// independently sealed with unique dylib leaf names:
//
//   join_is_head            agreed/mk=False -> agreed/mk=False   (refused by the oracle)
//   chain_of_ifs            agreed/mk=False -> agreed/mk=False   (refused by the oracle)
//   double_nested_cond      agreed/mk=False -> agreed/mk=False   (refused by the oracle)
//   arm_is_head_shared_join agreed/mk=False -> agreed/mk=TRUE    (a real gain)
//   min_if                  agreed/mk=False -> agreed/mk=TRUE    (a real gain)
//
// No verdict moved, and the emitted objects are BYTE-IDENTICAL between the two
// drivers. The plan being unsound about markers costs `markers_exact`, never
// correctness — which is the property the whole design rests on, demonstrated rather
// than asserted.

// (a) A JOIN that is also the HEAD of the next branch: the inner `if`'s join block
//     receives the outer condition's `StorageDead` at position 0 AND mints its own
//     condition temp there. If the emitter ordered those two wrongly the sequence
//     would be off by one.
#[inline(never)]
pub fn join_is_head(a: u32, b: u32, c: u32) -> u32 {
    if (if a == 0 { b } else { c }) == 0 { 1 } else { 2 }
}

// (b) An ARM that is also the HEAD of a nested branch AND whose own join is the
//     outer join (a reconvergence two levels up).
#[inline(never)]
pub fn arm_is_head_shared_join(a: u32, b: u32) -> u32 {
    if a == 0 {
        if b == 0 { 1 } else { 2 }
    } else {
        3
    }
}

// (c) The condition is the result of a nested if-expression compared to a constant,
//     with BOTH arms of the inner branch themselves branching.
#[inline(never)]
pub fn double_nested_cond(a: u32, b: u32, c: u32) -> u32 {
    if (if a == 0 {
        if b == 0 { 1u32 } else { 2 }
    } else if c == 0 {
        3
    } else {
        4
    }) == 1
    {
        10
    } else {
        20
    }
}

// (d) Three branches in sequence, each join feeding the next head.
#[inline(never)]
pub fn chain_of_ifs(a: u32, b: u32, c: u32) -> u32 {
    if (if (if a == 0 { b } else { c }) == 0 { a } else { b }) == 0 { 1 } else { 2 }
}

// (e) POSITIVE CONTROL.
#[inline(never)]
pub fn min_if(a: u32, b: u32) -> bool {
    if a == 0 { b == 1 } else { b == 2 }
}
