// Trust (lane MF-ZERO, 2026-08-13) — THE RESIDUAL PROBE.
//
// Every shape here exists to answer ONE question: does the marker plan ever ADMIT a body and then
// emit a marker sequence that is not built's? An admitted-and-wrong body is caught by the oracle
// (`markers_exact: false`, no flip) and costs nothing today — but it is a WRONG DERIVATION the
// plan offered, and the only thing between it and a flip is a comparator. That is debt.
//
// Compile with the trust driver and read both channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=resprobe \
//     -Ztrust-ir-lower=on -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Zdump-mir=all -Zdump-mir-dir=MIR \
//     -Ztrust-dump=ir:IR probes/mf_residual.rs --out-dir OUT
//
// The classification used by the enumeration (see `scratchpad/mfzero/residual.py`):
//
//   markers_exact: true                              -> ADMITTED AND RIGHT
//   markers_exact: false, derived side is EMPTY       -> REFUSED       (`derived <end>` at line 0)
//   markers_exact: false, derived side is NON-EMPTY   -> ADMITTED AND WRONG   <- must be zero
//
// Everything below is `#[inline(never)]` so each shape is its own body, and every operator is
// bitwise/comparison/cast so no body picks up the overflow `Assert` that would split the MIR
// chain and take it out of the single-block class for an unrelated reason.

#[derive(Clone, Copy)]
pub struct Box8(pub u8);
#[derive(Clone, Copy)]
pub struct P2 {
    pub a: u32,
    pub b: u32,
}
#[derive(Clone, Copy)]
pub struct P3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[derive(Clone, Copy)]
pub struct MixedT {
    pub a: u8,
    pub b: u64,
}
#[derive(Clone, Copy)]
pub struct Inner {
    pub x: u32,
    pub y: u32,
}

// =================================================================================================
// GROUP A — ORDERING. Built's `as_operand`->`as_temp` opens the DESTINATION's `StorageLive` and
// only then builds the sub-expression into it, so built's live order is a PREORDER of the
// expression tree. The shim walks the trust-ir instruction list in linear SSA order, which is a
// POSTORDER. They coincide only under two rules:
//
//   (1) a MARKED result may not take a MARKED operand   [landed 2026-08-13, lane N]
//   (2) a MARKED operand may not be preceded by a PLACE operand   [this lane]
//
// Rule (2) must be CONSTANT-TOLERANT: a constant operand folds in place and mints no temp, so it
// constrains nothing. Counting it (as `plan_branch_markers`' rule (2) does) would refuse A2/A7/A11,
// which are correct today and must keep flipping.
// =================================================================================================

// A1 — THE RESIDUAL. `a` is a PLACE operand at position 0 and `(b & c)` a MARKED operand at
// position 1. Built lives `a`'s temp first (`mk b0.1:live s1:u8` for the `&` temp); the shim
// reaches the `&` node first and lives it at `b0.0`. REFUSED by rule (2).
#[inline(never)]
pub fn a1_right_nested(a: u8, b: u8, c: u8) -> bool {
    a == (b & c)
}

// A2 — THE TRAP. Same tree with a CONSTANT in the place position. Built folds `0` in place and
// mints no temp, so built's live order IS the shim's. ADMITTED, exact, and it must stay that way:
// a rule that counted constants would refuse this for nothing.
#[inline(never)]
pub fn a2_const_right_nested(b: u8, c: u8) -> bool {
    0 == (b & c)
}

// A3 — the same defect reached through a FIELD read rather than a bare param.
impl Box8 {
    #[inline(never)]
    pub fn a3_field_right_nested(self, b: u8, c: u8) -> bool {
        self.0 == (b & c)
    }
}

// A4 — the LEFT-nested twin: the marked operand is leftmost, nothing precedes it. ADMITTED, exact.
#[inline(never)]
pub fn a4_left_nested(a: u8, b: u8, c: u8) -> bool {
    (a & b) == c
}

// A5 — TWO marked operands and no place operand. Built opens each sub-expression's temp in operand
// order and the shim reaches them in the same order. ADMITTED, exact.
#[inline(never)]
pub fn a5_both_nested(a: u8, b: u8, c: u8, d: u8) -> bool {
    (a & b) == (c & d)
}

// A6 — rule (2) through `Inst::Load`: a place operand before a marked LOAD.
#[inline(never)]
pub fn a6_place_then_load(a: u64, p: &u64) -> bool {
    a == *p
}

// A7 — the constant-tolerant twin of A6. ADMITTED, exact.
#[inline(never)]
pub fn a7_const_then_load(p: &u64) -> bool {
    0 == *p
}

// A8 — the load leftmost. ADMITTED, exact (this is lane L's `deref_eq0`).
#[inline(never)]
pub fn a8_load_then_const(p: &u64) -> bool {
    *p == 0
}

// A9 — a UNARY consumer of a marked operand: one operand, nothing can precede it. ADMITTED, exact.
#[inline(never)]
pub fn a9_unop_nested(a: u8, b: u8) -> u8 {
    !(a & b)
}

// A10 — a CAST of a marked operand: one operand. ADMITTED, exact.
#[inline(never)]
pub fn a10_cast_nested(a: u8, b: u8) -> u32 {
    (a & b) as u32
}

// A11 — constant-tolerant rule (2) in a plain BinOp (not a comparison). ADMITTED, exact.
#[inline(never)]
pub fn a11_const_then_and(b: u8, c: u8) -> u8 {
    0 | (b & c)
}

// A12 — the place-operand twin of A11. REFUSED by rule (2).
#[inline(never)]
pub fn a12_place_then_and(a: u8, b: u8, c: u8) -> u8 {
    a | (b & c)
}

// A13 — rule (1): a MARKED result taking a MARKED operand. Already refused (lane N); kept here so
// the two rules are visibly independent.
#[inline(never)]
pub fn a13_marked_takes_marked(a: u8, b: u8, c: u8) -> bool {
    ((a & b) | c) == 0
}

// A14/A15 — the same tree as an AGGREGATE FIELD value. Both are already REFUSED in the control,
// and by rule (1) rather than rule (2): the field rvalue `|` is MARKED (its consumer is the
// `InsertField`) and it takes the MARKED `&`. Measured, that refusal is CORRECT for both — built
// opens the outer `|` temp first (`_3`), the linear walk opens the inner `&` first — so the
// constant in A15 buys nothing here. They are kept as the record that rule (1) subsumes rule (2)
// wherever the consumer is itself marked.
#[inline(never)]
pub fn a14_agg_field_right_nested(a: u8, b: u8, c: u8) -> Box8 {
    Box8(a | (b & c))
}
#[inline(never)]
pub fn a15_agg_field_const_nested(b: u8, c: u8) -> Box8 {
    Box8(0 | (b & c))
}

// =================================================================================================
// GROUP B — AGGREGATE FIELD ORDER. `rustc_mir_build`'s `as_rvalue` for `ExprKind::Adt` mints the
// explicit fields' operand temps IN THE ORDER THE USER WROTE THEM ("evaluating them in order
// given by user"), not in field order. The producer likewise lowers field values in source order
// (`for (idx, fexpr) in field_exprs`). The shim, however, mints a PLACE field's temp at the
// aggregate site in FIELD order. So a constructor written out of field order is a live-order
// divergence the field-order rule must catch.
// =================================================================================================

// B1 — PLACE (param) fields written out of field order, with DIFFERENT types so the divergence
// survives `canon_markers`' first-appearance alpha-renaming.
#[inline(never)]
pub fn b1_param_fields_out_of_order(x: u8, y: u64) -> MixedT {
    MixedT { b: y, a: x }
}

// B2 — the in-order twin. ADMITTED, exact.
#[inline(never)]
pub fn b2_param_fields_in_order(x: u8, y: u64) -> MixedT {
    MixedT { a: x, b: y }
}

// B3 — PLACE (field-read) fields written out of field order. Refused TWICE over: the source-form
// gate sees the written order, and `agg_field_order_ok` sees `ef(p,1)` emitted before `ef(p,0)`.
#[inline(never)]
pub fn b3_read_fields_out_of_order(p: MixedT) -> MixedT {
    MixedT { b: p.b, a: p.a }
}

// B4 — INSTRUCTION-valued fields written out of field order. Refused in the control already.
#[inline(never)]
pub fn b4_instr_fields_out_of_order(x: u8, y: u64) -> MixedT {
    MixedT { b: y | 1, a: x | 1 }
}

// =================================================================================================
// GROUP C — FUNCTIONAL RECORD UPDATE. `P { f: v, ..base }` reads every OMITTED field out of
// `base` as `ExtractField{base, i}` — the same instruction `ExprKind::Field` emits for a written
// out `base.f` — but built consumes a base-supplied field as a BARE PLACE with no temp and no
// marker. Two spellings, one instruction stream, two different built bodies: a function of the
// stream cannot be right on both, so the ambiguous ones are refused.
//
// The ambiguity is NOT "any field i fed by a read of field i". The producer appends the base reads
// AFTER every explicit field (`lower_expr(base_expr)` runs after the `field_exprs` loop) and in
// field-index order, so an FRU spelling can only ever put its base reads LAST. A same-index read
// that is NOT last is therefore unreachable by any FRU spelling and is unambiguous.
// =================================================================================================

// C1 — the FRU spelling itself. REFUSED.
#[inline(never)]
pub fn c1_fru(p: P2, x: u32) -> P2 {
    P2 { a: x, ..p }
}

// C2 — the written-out twin of `P2 { b: x, ..p }`: field 0 is the last (and only) instruction
// valued field and it is a same-index read. REFUSED.
#[inline(never)]
pub fn c2_written_out_field0(p: P2, x: u32) -> P2 {
    P2 { a: p.a, b: x }
}

// C3 — same-index read from a DIFFERENT base, still last. The FRU twin is `P2 { a: q.a, ..p }`.
// REFUSED.
#[inline(never)]
pub fn c3_cross_base_same_index(p: P2, q: P2) -> P2 {
    P2 { a: q.a, b: p.b }
}

// C4 — THE OVER-REFUSAL BEING NARROWED. Field 1 is a same-index read, but field 2's value
// (`p.a`) is emitted AFTER it, so no FRU spelling produces this stream: `P3 { a: p.c, c: p.a,
// ..p }` emits the base read LAST (`%3`), this emits it in the middle (`%2`). ADMITTED, exact.
#[inline(never)]
pub fn c4_partial_fru(p: P3) -> P3 {
    P3 { a: p.c, b: p.b, c: p.a }
}

// C5 — no same-index read at all: the indices cross, so no FRU spelling exists. ADMITTED, exact.
#[inline(never)]
pub fn c5_swap_pair(p: P2) -> P2 {
    P2 { a: p.b, b: p.a }
}

// C6 — the same-index read is LAST in field order even though an earlier field is not a base read.
// The FRU twin is `P3 { a: p.b, b: p.a, ..p }`. REFUSED.
#[inline(never)]
pub fn c6_tail_same_index(p: P3) -> P3 {
    P3 { a: p.b, b: p.a, c: p.c }
}

// C7 — a same-index read that is neither last nor first. The FRU twin would have to emit `p.b`
// after `p.a`, and it cannot. ADMITTED, exact.
#[inline(never)]
pub fn c7_middle_same_index(p: P3, x: u32) -> P3 {
    P3 { a: x, b: p.b, c: p.a }
}

// C8 — THE ATTRIBUTION. This is C1 written out: `P2 { a: x, ..p }` and `P2 { a: x, b: p.b }` have
// BYTE-IDENTICAL trust-ir (both: `ef(p,1)`, seed, two `insertfield`s), so no rule that is a
// function of the instruction stream can refuse one and admit the other. C1 is refused and this is
// ADMITTED and exact — which pins the refusal on the source form (`StructTailExpr::Base`) and on
// nothing else.
#[inline(never)]
pub fn c8_written_out_twin_of_c1(p: P2, x: u32) -> P2 {
    P2 { a: x, b: p.b }
}

// =================================================================================================
// GROUP D — PARAMETER PATTERNS. `rustc_mir_build`'s `args_and_body` introduces "no extra copies
// for simple bindings" (`PatKind::Binding { mode: ByRef::No, subpattern: None }`) and mints a
// NAMED BINDING LOCAL, with its own `StorageLive`/`StorageDead`, for every other parameter
// pattern. The producer opens no lexical scope for a parameter pattern, so `func.scopes.is_none()`
// does not see it and the trust-ir instruction stream of `fn f(&l: &u64) { l == 0 }` is
// byte-identical to that of `fn f(p: &u64) { *p == 0 }`. The plan must therefore read the
// parameter patterns themselves.
// =================================================================================================

// D1 — a REFERENCE pattern parameter. Built mints `_2` for the binding `l` AND `_3` for the
// comparison's operand temp; the shim can only see one load. REFUSED.
#[inline(never)]
pub fn d1_pat_deref_eq0(&l: &u64) -> bool {
    l == 0
}

// D2 — the same defect inside a closure (this is `BigNat::is_zero::{closure#0}`'s shape).
#[inline(never)]
pub fn d2_closure_pat_eq0(xs: &[u64]) -> bool {
    xs.iter().all(|&l| l == 0)
}

// D3 — a STRUCT destructuring parameter: two binding locals, no scope table.
#[inline(never)]
pub fn d3_pat_struct(Inner { x, y }: Inner) -> u32 {
    x | y
}

// D4 — a WILDCARD parameter. `declare_bindings` binds nothing, so built mints no binding local.
#[inline(never)]
pub fn d4_wild_param(_: u64, b: u64) -> bool {
    b == 0
}

// D5 — the simple-binding control: identical trust-ir to D1, and correct. ADMITTED, exact.
#[inline(never)]
pub fn d5_simple_deref_eq0(p: &u64) -> bool {
    *p == 0
}

// D6 — a `mut` simple binding is still a simple binding (`ByRef::No`), so the PARAMETER rule does
// not fire here; the STATEMENT rule does. Built assigns the `|` straight into the argument local
// (`_1 = BitOr(move _2, const 1)`) and the shim treats the same `%1` as a marked operand temp.
#[inline(never)]
pub fn d6_mut_param(mut a: u64) -> bool {
    a = a | 1;
    a == 1
}

// D7 — THE ATTRIBUTION for D6. The same expression with no statement. BYTE-IDENTICAL trust-ir to
// D6 (`or; const; icmp; ret` over one `u64` param), so again no function of the instruction stream
// separates them. ADMITTED, exact.
#[inline(never)]
pub fn d7_expr_twin_of_d6(a: u64) -> bool {
    (a | 1) == 1
}

// =================================================================================================
// GROUP E — FIELD WRITE THROUGH A `&mut` PARAMETER, the one defect here NOT owned by a marker plan.
// wave-24's `recognize_field_write` collapses the producer's `load; insertfield; store` triple into
// built's `(*P).k = v` and (wave-24b) reproduces built's operand temp around it. That reproduction
// is right for a PLACE or RVALUE right-hand side and wrong for a CONSTANT one: `stmt_expr`'s
// `ExprKind::Assign` calls `as_local_rvalue(rhs)`, which for `Category::Constant` returns
// `Rvalue::Use(Operand::Constant)` and mints no temp at all.
//
// This group is NOT gated by `source_form_admits` — a field write is a statement, so the marker
// plan is `None` here either way, and these markers come from the field-write arm itself.
// =================================================================================================
pub struct Slot {
    pub f: bool,
    pub g: u32,
}

// E1 — a CONSTANT right-hand side. Built: `((*_1).0: bool) = const true;` — ZERO markers. Until
// 2026-08-13 the shim derived `StorageLive(_3); _3 = const true; ((*_1).0) = move _3;
// StorageDead(_3)` and the oracle read `built <end> vs derived mk b0.0:live s0:bool`. FIXED BY
// EMISSION. The two clean-kernel bodies in this state were
// `LimitedDeserializer::<D>::accept_pending_byte` and
// `<TypedStateHolder<S> as ExtensionStateHolder>::mark_initialized`.
#[inline(never)]
pub fn e1_field_write_const(s: &mut Slot) {
    s.f = true;
}

// E2 — the minimally-different sibling: a PLACE right-hand side, where the temp IS built's. Built:
// `StorageLive(_3); _3 = copy _2; ((*_1).0: bool) = move _3; StorageDead(_3)`. ADMITTED, exact
// before and after — the fix must not take this one's markers away.
#[inline(never)]
pub fn e2_field_write_place(s: &mut Slot, v: bool) {
    s.f = v;
}

// E3 — an RVALUE right-hand side. Built writes the rvalue STRAIGHT into the field place
// (`((*_1).1: u32) = BitOr(move _3, const 1_u32)`) and temps only its operand, which is a third
// shape again. Measured: it never reaches the arm — the body is `unsupported` — so there is
// nothing to be wrong about. Kept as the record that this was checked, not assumed.
#[inline(never)]
pub fn e3_field_write_rvalue(s: &mut Slot, v: u32) {
    s.g = v | 1;
}

// =================================================================================================
// MUST NOT REGRESS — zero markers on both sides, and they stay that way.
// =================================================================================================
#[inline(never)]
pub fn z_unitfn() {}
#[inline(never)]
pub fn z_ident(a: u64) -> u64 {
    a
}
#[inline(never)]
pub fn z_konst() -> u64 {
    7
}
