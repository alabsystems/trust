// LANE P (adversarial review of lane K, 2026-08-13) — multi-block marker shapes lane K
// did NOT build.
//
// MEASURED, control (trust e4f16776fa) vs subject (lane K rebased onto it), both drivers
// independently sealed with unique dylib leaf names and cross-checked by offering the
// control a flag only the subject knows (`-Ztrust-sat-perturb=marker-arm`, REFUSED).
//
//   7 rows moved, ALL `agreed/mk=False -> agreed/mk=True`. 0 verdict changes, 0 lost
//   `markers_exact`, 0 new mismatch. Flips 1 -> 8 at `-O3`; 16 -> 16 at `-O0` (where
//   `markers_exact` is not gated). Emitted objects BYTE-IDENTICAL at `-Copt-level` 0, 1
//   and 3 — the derived bodies differ (markers + trampoline) and the machine code does not.
//
// Negative controls that must NOT move, and did not:
//   match_int      the `Inst::Switch` lane — `mk=True` and flipping in BOTH drivers.
//                  Every currently-flipping multi-block body is this shape.
//   ptr_cond/ref_cond  lane K's own hazard #3 (ref/ptr-typed condition operand). Both stay
//                  `unsupported`; `ptr_cond` dies at "shim: ICmp on non-scalar type" and
//                  every route in `mb_hazard3.rs` (`p as usize` in the condition, in an arm,
//                  via `&`, under `&`-arithmetic) dies EARLIER STILL, at the producer
//                  ("2 unsupported THIR shape(s)"). The hazard was not reachable.
//   andand_cond    a PRE-EXISTING differential `mismatch` on main, unchanged by lane K.
//   shift_arm      the shift guard; `mk=False` in both drivers at both check settings.
//
// Perturbation battery (subject): baseline 8 exact -> marker-order 4, marker-drop 1,
// marker-arm 1, agg-field-order 8 (inert here, as lane N recorded).
//
// Every function here is a body the multi-block plan (`plan_branch_markers`) must either
// reproduce EXACTLY or refuse. The oracle is `IR/<crate>.coverage.json`'s
// `derived_mir.markers_exact` plus the flip log; nothing here is allowed to turn an
// `agreed` verdict into `unsupported`/`mismatch` relative to the control driver.

// ---------------------------------------------------------------------------
// (1) CONDITION OPERAND LIVE ACROSS BOTH ARMS AND USED AFTER THE JOIN.
// The condition reads `a`; both arms read `a`; the join value reads `a`. Built's
// operand temp for the condition is a COPY, so its region scope still ends at the
// arm entries — but the plan's "result used exactly once, in its own block" rule
// applies to instruction RESULTS, not params, so this is admitted and must be exact.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn cond_operand_live_across(a: u32, b: u32) -> u32 {
    if a == 0 { a & b } else { a | b }
}

// The same, but the condition's operand is itself an instruction RESULT used once.
#[inline(never)]
pub fn cond_result_operand(a: u32, b: u32) -> bool {
    if (a & b) == 0 { a > b } else { a < b }
}

// ---------------------------------------------------------------------------
// (2) EARLY RETURN INSIDE ONE ARM (two `Return` terminators, no `let`).
// The plan refuses `n_return != 1`. Must stay refused, and must not lose a verdict.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn early_return(a: u32, b: u32) -> u32 {
    if a == 0 {
        return b;
    }
    b + 0
}

// ---------------------------------------------------------------------------
// (3) A LOOP whose condition is a marked result (back edge).
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn loop_cond(mut a: u32, b: u32) -> u32 {
    while a > b {
        a = a - b;
    }
    a
}

// ---------------------------------------------------------------------------
// (4) NESTED BRANCHES SHARING A TEMP: the OUTER condition's operand is also the
// INNER condition's operand. If the plan let the outer condition's deferred deads
// leak into the inner branch's schedule the sequence would be wrong.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn nested_shared_operand(a: u32, b: u32) -> u32 {
    if a == 0 {
        if a == b { 1 } else { 2 }
    } else if a == 1 {
        3
    } else {
        4
    }
}

// Two SIBLING diamonds in sequence (the first join is the second head).
#[inline(never)]
pub fn sibling_diamonds(a: u32, b: u32) -> u32 {
    let x = if a == 0 { 1u32 } else { 2u32 };
    if b == 0 { x } else { x + 0 }
}

// ---------------------------------------------------------------------------
// (5) A MATCH WITH A GUARD.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn match_guard(a: u32, b: u32) -> u32 {
    match a {
        0 if b > 3 => 10,
        0 => 11,
        _ => 12,
    }
}

// A match on an integer with three arms (the `Inst::Switch` lane, which the plan
// refuses outright — every currently-flipping multi-block body is this shape).
#[inline(never)]
pub fn match_int(a: u32) -> u32 {
    match a {
        0 => 1,
        1 => 2,
        _ => 3,
    }
}

// ---------------------------------------------------------------------------
// (6) `&&` IN CONDITION POSITION — the arms share the ELSE block (2 preds).
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn andand_cond(a: u32, s: u32, e: u32) -> u32 {
    if a >= s && a < e { 1 } else { 0 }
}

// ---------------------------------------------------------------------------
// (7) DEGENERATE ARM — `if c { .. }` with unit type; the join IS the else edge.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn degenerate_if(a: u32, b: &mut u32) {
    if a == 0 {
        *b = 1;
    }
}

// ---------------------------------------------------------------------------
// (8) BOTH CONDITION OPERANDS CONSTANT (deads list empty on both arms).
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn const_cond(a: u32) -> u32 {
    if 1u32 == 2u32 { a } else { a + 0 }
}

// ---------------------------------------------------------------------------
// (9) POINTER-TYPED CONDITION OPERAND — lane K hazard #3. The comparison is on
// raw pointers, so `mf_operand` would mint a POINTER-typed marker temp.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn ptr_cond(p: *const u32, q: *const u32, x: u32, y: u32) -> u32 {
    if p == q { x } else { y }
}

// A shared-reference-typed condition operand.
#[inline(never)]
pub fn ref_cond(p: &u32, q: &u32, x: u32, y: u32) -> u32 {
    if core::ptr::eq(p, q) { x } else { y }
}

// ---------------------------------------------------------------------------
// (10) MARKED RESULT FEEDING A MARKED RESULT inside an ARM (not the condition):
// rule (1) of the two ordering rules only fires for marked results. An arm whose
// value is `(a & b) == d` has an UNMARKED outer result (consumed by `Br`), so it
// stays in the class and must be exact.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn arm_nested_expr(a: u32, b: u32, d: u32) -> bool {
    if a == 0 { (a & b) == d } else { (b & d) == a }
}

// ---------------------------------------------------------------------------
// (11) A CONDITION WHOSE RESULT IS USED TWICE (cond + arm value).
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn cond_used_twice(a: u32, b: u32) -> bool {
    let c = a == b;
    if c { c } else { !c }
}

// ---------------------------------------------------------------------------
// (12) A STRUCT-FIELD (ExtractField) CONDITION OPERAND, no `let`.
// ---------------------------------------------------------------------------
pub struct S {
    pub k: u32,
    pub j: u32,
}

#[inline(never)]
pub fn field_cond(s: S, x: u32) -> u32 {
    if s.k == 0 { s.j } else { x }
}

// A BOOL STRUCT FIELD as the condition: the cond is an `ExtractField`, not a
// marked result, so the plan must refuse (the `param_cond` tripwire, one step out).
pub struct B {
    pub f: bool,
    pub g: u32,
}

#[inline(never)]
pub fn field_bool_cond(s: B, x: u32) -> u32 {
    if s.f { s.g } else { x }
}

// ---------------------------------------------------------------------------
// (13) A CAST-FREE SHIFT in an arm with overflow-checks OFF — the shift guard.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn shift_arm(a: u32, b: u32) -> u32 {
    if a == 0 { b << 1 } else { b >> 1 }
}

// ---------------------------------------------------------------------------
// (14) THREE-DEEP NESTING, both arms branching (two inner joins).
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn deep_nest(a: u32, b: u32, c: u32) -> u32 {
    if a == 0 {
        if b == 0 { 1 } else { 2 }
    } else if c == 0 {
        3
    } else {
        4
    }
}

// ---------------------------------------------------------------------------
// (15) LANE K's OWN ADMITTED SHAPES, replicated so this crate carries a positive
// control alongside the negatives.
// ---------------------------------------------------------------------------
#[inline(never)]
pub fn min_if(a: u32, b: u32) -> bool {
    if a == 0 { b == 1 } else { b == 2 }
}

#[inline(never)]
pub fn bvar_in_range(idx: u32, start: u32, end: u32) -> bool {
    if end == u32::MAX { idx >= start } else { idx >= start && idx < end }
}
