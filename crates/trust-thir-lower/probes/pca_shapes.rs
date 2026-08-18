// Trust (LANE PCA, plan-clause audit, 2026-08-17) — the FOUR OLDER PLANS' clause corpus.
//
// The operand (wave-MF), branch (lane K), field-write and interior-borrow plans already have a
// large inherited corpus. What that corpus is thin on is the population that would WITNESS the
// clauses nobody has ever seen fire: a plain-block clause needs unsafe/async bodies, a
// predecessor-count clause needs a diamond, a join-of-two-branches clause needs two branches
// sharing a join, an arm-of-two-branches clause needs a shared arm.
#![allow(dead_code, unused_variables, unused_unsafe, clippy::needless_bool)]
#![allow(clippy::eq_op, clippy::identity_op, clippy::let_and_return, clippy::precedence)]
#![allow(clippy::nonminimal_bool, clippy::needless_late_init, clippy::collapsible_else_if)]
#![allow(clippy::comparison_chain, clippy::needless_return, clippy::self_assignment)]

#[derive(Clone, Copy)]
pub struct C3 {
    pub a: u32,
    pub b: u64,
    pub c: u8,
}

#[derive(Clone, Copy)]
pub struct One(pub u32);

#[derive(Clone, Copy)]
pub struct Mixed {
    pub s: u8,
    pub w: u64,
}

// =================================================================================================
// W5 / I5 / H3 — the BLOCK CHECK MODE clauses (`unsafe`), on both plans and on the tail predicate.
// =================================================================================================

/// An `unsafe` body whose whole content is one field write.
pub unsafe fn sh_w5_unsafe_fn_write(w: &mut C3, v: u32) {
    w.a = v;
}

/// A body that is an `unsafe` BLOCK wrapping one write.
pub fn sh_w5_unsafe_block_write(w: &mut C3, v: u32) {
    unsafe {
        w.a = v;
    }
}

/// An `unsafe` block wrapping two writes.
pub fn sh_w5_unsafe_block_two(w: &mut C3, v: u32, u: u8) {
    unsafe {
        w.a = v;
        w.c = u;
    }
}

/// A write followed by an `unsafe`-block tail.
pub fn sh_w5_write_then_unsafe_tail(w: &mut C3, v: u32) -> u32 {
    w.a = v;
    unsafe { w.a }
}

/// An `unsafe` body whose whole content is one interior borrow.
pub unsafe fn sh_i5_unsafe_borrow(s: &C3) -> &u64 {
    &s.b
}

/// An `unsafe`-BLOCK interior borrow.
pub fn sh_i5_unsafe_block_borrow(s: &C3) -> &u64 {
    unsafe { &s.b }
}

// =================================================================================================
// I9 / I10 — the interior-borrow plan's REBORROW requirement and its marker-free place.
// =================================================================================================

/// The plain admitted shape: a scalar field borrow with the reborrow adjustment pair.
pub fn sh_i_ok_scalar(s: &C3) -> &u64 {
    &s.b
}

/// Borrow of the FIRST field.
pub fn sh_i_ok_first(s: &C3) -> &u32 {
    &s.a
}

/// Borrow of the LAST field.
pub fn sh_i_ok_last(s: &C3) -> &u8 {
    &s.c
}

/// Borrow of a newtype's only field.
pub fn sh_i_ok_newtype(s: &One) -> &u32 {
    &s.0
}

/// Borrow of the WHOLE receiver — no projection, and no interior offset.
pub fn sh_i9_whole(s: &C3) -> &C3 {
    s
}

/// A borrow whose result type is `&&u64` — an extra reference level.
pub fn sh_i9_double<'a>(s: &'a &'a C3) -> &'a u64 {
    &s.b
}

/// A borrow through a DOUBLE deref.
pub fn sh_i10_deref_chain(s: &&C3) -> u64 {
    s.b
}

/// A MUTABLE interior borrow — a different adjustment kind.
pub fn sh_i9_mut_borrow(s: &mut C3) -> &mut u64 {
    &mut s.b
}

/// A raw-pointer interior borrow.
pub fn sh_i9_raw(s: &C3) -> *const u64 {
    &s.b as *const u64
}

/// A borrow of a NESTED field.
pub struct Nest {
    pub inner: One,
}
pub fn sh_i10_nested(s: &Nest) -> &u32 {
    &s.inner.0
}

/// A borrow preceded by an ITEM statement (which declares a separate def and emits nothing).
pub fn sh_i6_item_then_borrow(s: &C3) -> &u64 {
    struct Ignored;
    &s.b
}

/// A borrow preceded by a real statement.
pub fn sh_i6_stmt_then_borrow<'a>(s: &'a C3, w: &mut C3, v: u32) -> &'a u64 {
    w.a = v;
    &s.b
}

// =================================================================================================
// B16 / B24 / B25 / B26 — the branch plan's PREDECESSOR and ROLE-EXCLUSIVITY clauses.
// These need shapes where two branches share an arm or a join, and where an arm has two preds.
// =================================================================================================

/// Two independent `if`s in sequence, each with its own join.
pub fn sh_b_two_ifs(a: u32, b: u32, x: u32, y: u32) -> bool {
    (if a == 0 { x } else { y }) == (if b == 0 { y } else { x })
}

/// A nested `if` in the THEN arm.
pub fn sh_b_nested_then(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if a == 0 { if b == 0 { x } else { y } } else { y }
}

/// A nested `if` in the ELSE arm.
pub fn sh_b_nested_else(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if a == 0 { x } else { if b == 0 { x } else { y } }
}

/// Nested in BOTH arms — two branches whose joins are distinct but whose grandjoin is shared.
pub fn sh_b_nested_both(a: u32, b: u32, c: u32, x: u32, y: u32) -> u32 {
    if a == 0 { if b == 0 { x } else { y } } else { if c == 0 { y } else { x } }
}

/// `&&` — the short-circuit shape whose false edges converge on ONE block.
pub fn sh_b_andand(a: u32, b: u32) -> bool {
    a == 0 && b == 1
}

/// `||`.
pub fn sh_b_oror(a: u32, b: u32) -> bool {
    a == 0 || b == 1
}

/// `&&` chained three deep — two branches sharing the same false target.
pub fn sh_b_andand3(a: u32, b: u32, c: u32) -> bool {
    a == 0 && b == 1 && c == 2
}

/// `||` chained three deep.
pub fn sh_b_oror3(a: u32, b: u32, c: u32) -> bool {
    a == 0 || b == 1 || c == 2
}

/// Mixed `&&`/`||`.
pub fn sh_b_mixed(a: u32, b: u32, c: u32) -> bool {
    (a == 0 && b == 1) || c == 2
}

/// A degenerate `if` with no else — the join IS the else edge.
pub fn sh_b20_no_else(a: u32, w: &mut C3, v: u32) {
    if a == 0 {
        w.a = v;
    }
}

/// The condition is a BARE PARAMETER: built mints no temp (the `param_cond` tripwire).
pub fn sh_b18_param_cond(c: bool, x: u32, y: u32) -> u32 {
    if c { x } else { y }
}

/// The condition is a bare parameter, spelled as a `match`.
pub fn sh_b18_match_bool(c: bool, x: u32, y: u32) -> u32 {
    match c {
        true => x,
        false => y,
    }
}

/// The condition is a FIELD READ — a place, not a marked result.
pub fn sh_b18_field_cond(s: &C3, x: u32, y: u32) -> u32 {
    if s.a == 0 { x } else { y }
}

/// The condition is the NEGATION of a comparison.
pub fn sh_b18_not_cond(a: u32, x: u32, y: u32) -> u32 {
    if !(a == 0) { x } else { y }
}

/// A LOOP: the postorder walk finds a back edge.
pub fn sh_b12_loop(mut a: u32) -> u32 {
    while a > 0 {
        a -= 1;
    }
    a
}

/// An early `return` inside a branch: two `Return` terminators.
pub fn sh_b5_early_return(a: u32, x: u32) -> u32 {
    if a == 0 {
        return x;
    }
    0
}

/// The `if` value is CONSUMED as an operand — the join-parameter rule (B22).
pub fn sh_b22_join_operand(a: u32, b: u32, x: u32, y: u32) -> bool {
    (if a == 0 { x } else { y }) == b
}

/// The `if` value is cast — again an operand use of a join parameter.
pub fn sh_b22_join_cast(a: u32, x: u32, y: u32) -> u64 {
    (if a == 0 { x } else { y }) as u64
}

/// The `if` value is RETURNED — the admitted shape.
pub fn sh_b_ok_returned(a: u32, x: u32, y: u32) -> u32 {
    if a == 0 { x } else { y }
}

/// A branch whose arms are comparisons — the `min_if` shape.
pub fn sh_b_ok_arms_cmp(a: u32, b: u32) -> bool {
    if a == 0 { b == 1 } else { b == 2 }
}

/// A branch whose condition takes a MARKED operand (ordering rule 1).
pub fn sh_b27_marked_operand(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if (a & b) == 0 { x } else { y }
}

/// A branch whose condition has a marked operand on the RIGHT (ordering rule 2).
pub fn sh_b28_right_nested(a: u32, b: u32, c: u32, x: u32, y: u32) -> u32 {
    if a == (b & c) { x } else { y }
}

/// A SHIFT inside a branch (B9).
pub fn sh_b9_shift(a: u32, b: u32, x: u32, y: u32) -> u32 {
    if (a << 2) == b { x } else { y }
}

// =================================================================================================
// O-plan boundary: single-block operand shapes.
// =================================================================================================

/// The canonical `is_null` shape.
pub fn sh_o_ok_field_eq(s: &One) -> bool {
    s.0 == 0
}

/// Left-nested tree — the admitted ordering.
pub fn sh_o_ok_left_nested(a: u32, b: u32, c: u32) -> bool {
    (a & b) == c
}

/// Right-nested tree — ordering rule (2).
pub fn sh_o10_right_nested(a: u32, b: u32, c: u32) -> bool {
    a == (b & c)
}

/// Constant on the left of a right-nested tree — CONSTANT-TOLERANT, must stay admitted.
pub fn sh_o10_const_left(b: u32, c: u32) -> bool {
    0 == (b & c)
}

/// A marked result taking a marked operand — ordering rule (1).
pub fn sh_o9_marked_marked(a: u32, b: u32, c: u32) -> bool {
    ((a & b) | c) == 0
}

/// A SHIFT in a single-block body (O5).
pub fn sh_o5_shift(a: u32, b: u32) -> bool {
    (a << 2) == b
}

/// A shift with no cast, both operands the same type (O5, the reachable half).
pub fn sh_o5_shift_same(a: u32, b: u32) -> u32 {
    a << b
}

/// A value used TWICE (O7).
pub fn sh_o7_dag(a: u32) -> bool {
    (a & a) == a
}

/// A `Load` whose value is returned — takes no marker.
pub fn sh_o_load_returned(p: &u64) -> u64 {
    *p
}

/// A `Load` in operand position — the marked shape.
pub fn sh_o_load_operand(p: &u64) -> bool {
    *p == 0
}

/// A place operand BEFORE a load (`a == *p`) — ordering rule (2) through `Inst::Load`.
pub fn sh_o10_place_then_load(a: u64, p: &u64) -> bool {
    a == *p
}

/// A destructuring parameter — a binding local the scope firewall cannot see (S2).
pub fn sh_s2_ref_param(&l: &u64) -> bool {
    l == 0
}

/// A struct-pattern parameter.
pub fn sh_s2_struct_param(One(k): &One) -> bool {
    *k == 0
}

/// A WILD parameter — admitted, and must stay admitted.
pub fn sh_s2_wild(_: u64, b: u64) -> bool {
    b == 0
}

/// A `mut` binding parameter — still a simple binding.
pub fn sh_s2_mut_param(mut a: u64) -> bool {
    a == 0
}

// =================================================================================================
// S4 / S10 — statements, and struct-literal field order.
// =================================================================================================

/// Declaration order, all same type: invisible permutation baseline.
pub fn sh_s10_decl_order(x: u32, y: u32, z: u32) -> T3 {
    T3 { a: x, b: y, c: z }
}

#[derive(Clone, Copy)]
pub struct T3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}

/// A rotated same-type permutation — invisible.
pub fn sh_s10_rotate(x: u32, y: u32, z: u32) -> T3 {
    T3 { c: z, b: y, a: x }
}

/// A MIXED-width permutation — observable, must stay refused.
pub fn sh_s10_mixed_perm(s: u8, w: u64) -> Mixed {
    Mixed { w, s }
}

/// A mixed-width literal in declaration order — admitted.
pub fn sh_s10_mixed_decl(s: u8, w: u64) -> Mixed {
    Mixed { s, w }
}

/// A permutation with a CONSTANT field between the places.
pub fn sh_s10_const_between(x: u32, z: u32) -> T3 {
    T3 { c: z, b: 7, a: x }
}

/// A `*p` field at declared index 0, permuted.
pub fn sh_s10b_deref_first(p: &u32, y: u32, z: u32) -> T3 {
    T3 { c: z, b: y, a: *p }
}

/// TWO `*p` fields, permuted — the measured refusal.
pub fn sh_s10b_two_derefs(p: &u32, q: &u32, y: u32) -> T3 {
    T3 { c: *q, b: y, a: *p }
}

/// An FRU literal (S6).
pub fn sh_s6_fru(base: T3, x: u32) -> T3 {
    T3 { a: x, ..base }
}

/// The written-out twin of the FRU (must stay admitted).
pub fn sh_s6_written_out(base: T3, x: u32) -> T3 {
    T3 { a: x, b: base.b, c: base.c }
}

/// A statement (assignment) in the body (S4).
pub fn sh_s4_assign_stmt(mut a: u64) -> bool {
    a = a | 1;
    a == 1
}

/// A `let` statement (refused by the scope firewall AND by S4).
pub fn sh_s4_let_stmt(a: u64) -> bool {
    let s = a | 1;
    s == 1
}

/// An ITEM statement only — admitted, and must stay admitted.
pub fn sh_s4_item_stmt(a: u64) -> bool {
    struct Ignored;
    a == 0
}

/// A `match` whose SCRUTINEE is a comparison (S5).
pub fn sh_s5_match_of_cmp(a: u32, b: u32) -> u32 {
    match a == b {
        true => a,
        false => b,
    }
}

/// A `match` on a bare parameter — the admitted sibling of S5.
pub fn sh_s5_match_param(c: bool, a: u32, b: u32) -> u32 {
    match c {
        true => a,
        false => b,
    }
}

// =================================================================================================
// W-plan population: writes, returns, tails.
// =================================================================================================

/// The plain one-write body.
pub fn sh_w_ok_one(w: &mut C3, v: u32) {
    w.a = v;
}

/// Two writes.
pub fn sh_w_ok_two(w: &mut C3, v: u32, u: u8) {
    w.a = v;
    w.c = u;
}

/// A constant write (no operand temp on either side).
pub fn sh_w_ok_const(w: &mut C3) {
    w.a = 7;
}

/// A write then a terminal `return` of a place.
pub fn sh_w_ok_return_place(w: &mut C3, v: u32, r: u64) -> u64 {
    w.a = v;
    return r;
}

/// A write then a terminal `return` of a constant.
pub fn sh_w_ok_return_const(w: &mut C3, v: u32) -> u64 {
    w.a = v;
    return 7;
}

/// A `return` followed by another statement (W7) — unreachable but syntactically present.
pub fn sh_w7_after_return(w: &mut C3, v: u32) -> u64 {
    w.a = v;
    return 7;
}

/// A write whose RHS COMPUTES (W9).
pub fn sh_w9_rvalue_rhs(w: &mut C3, v: u32) {
    w.a = v + 1;
}

/// A write whose RHS is a CAST.
pub fn sh_w9_cast_rhs(w: &mut C3, v: u8) {
    w.a = v as u32;
}

/// A write whose LHS is an INDEX (W8).
pub fn sh_w8_index_lhs(w: &mut [u32], v: u32) {
    w[0] = v;
}

/// A write through a deref chain.
pub fn sh_w8_deref_lhs(w: &mut &mut C3, v: u32) {
    w.a = v;
}

/// A write then a computing tail (W12).
pub fn sh_w12_cmp_tail(w: &mut C3, v: u32, a: u32, b: u32) -> bool {
    w.a = v;
    a == b
}

/// A write then a place tail — admitted.
pub fn sh_w12_place_tail(w: &mut C3, v: u32, p: &u64) -> u64 {
    w.a = v;
    *p
}

/// A write then a `loop { break; }` tail — the exact measured marker-free loop.
pub fn sh_w12_loop_tail(w: &mut C3, v: u32) {
    w.a = v;
    loop {
        break;
    }
}

/// A write then a `while` tail — a wider loop grammar, refused.
pub fn sh_w12_while_tail(w: &mut C3, v: u32, mut n: u32) {
    w.a = v;
    while n > 0 {
        n -= 1;
    }
}

/// A write inside an `if` (W6/S4).
pub fn sh_w6_if_write(w: &mut C3, v: u32, c: bool) {
    if c {
        w.a = v;
    }
}

/// A `let` then a write (W6).
pub fn sh_w6_let_then_write(w: &mut C3, v: u32) {
    let t = v;
    w.a = t;
}

/// A write-free body that the write plan must refuse (W15).
pub fn sh_w15_no_write(a: u32, b: u32) -> bool {
    a == b
}

/// A body whose only statement is an ITEM, and whose tail is a write.
pub fn sh_w13_item_then_wrapped(w: &mut C3, v: u32) {
    struct Ignored;
    {
        w.a = v;
    }
}

/// A destructuring parameter on a write body (W2).
pub fn sh_w2_destructure(One(k): &One, w: &mut C3) {
    w.a = *k;
}
