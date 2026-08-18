// Trust (lane N adversarial review of lane L, 2026-08-13) — the aggregate/`Inst::Load` shapes
// `mf_aggregate_temps.rs` does NOT contain, each measured against a control and a subject driver
// built from the same tree.
//
//   trustc --edition 2021 --crate-type=lib --crate-name=advprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Zcodegen-backend=llvm -Zdump-mir=all -Zdump-mir-dir=MIR \
//     -Ztrust-dump=ir:IR probes/mf_aggregate_adversarial.rs --out-dir OUT
//
// MEASURED (subject driver, -O3): control 1 flip -> subject 13, LOST 0. At -O0 both drivers flip
// the SAME 21 bodies, so nothing here reproduces the `MemoryRegion::new` lost-flip class.
//
// THE THREE SHAPES `agg_field_order_ok` ADMITTED AND STILL GOT WRONG — CLOSED 2026-08-13, and
// this file is now the regression fixture for that closure. All three were refused by the ORACLE
// (`markers_exact: false`, no `-O` flip) and cost nothing measured; they are here because the
// guard's doc used to read as a SUFFICIENT condition and it was not one.
//
// MEASURED at the fix, independently sealed control (352aa0306d) vs subject, `-Copt-level=3` —
// the shim stops offering a WRONG marker sequence and offers NONE:
//
//   nested_field       derived `mk b0.1:live s2:u8`  ->  derived `<end>`   (ordering rule (1))
//   two_instr_nested   derived `mk b0.4:live s5:u8`  ->  derived `<end>`   (ordering rule (1))
//   mk_cast_load       derived `mk b0.0:live s0:u8`  ->  derived `<end>`   (ordering rule (1))
//   fru                derived `mk b0.1:live s1:u32` ->  derived `<end>`   (FRU signature)
//
// Every positive control in this file keeps `markers_exact: true` — including `swap_pair`, whose
// crossed field indices have no FRU spelling, and `from_pair`, whose field rvalue takes only
// PLACE operands. Whole-crate clean-kernel: 0 of 13769 rows moved at either opt level.
//
// `mk_refpair` (section I) is the DEFECT-4 shape and it is NOT observable here: it is
// `unsupported` on both drivers, because `cx.operand` fails a `fwd_ptr_params` field closed
// before any marker question is asked. That unreachability was the whole complaint — the fix is
// pinned by `to_mir::agg_plan_tests`, where the same seed with a `Ty::Ptr` field and with a
// `Ty::Usize` field are told apart by TYPE.
//
//   nested_field / two_instr_nested / mk_cast_load — built's `as_operand`->`as_temp` opens the
//     OUTER (field) temp FIRST and only then the inner one; the shim's LINEAR walk reaches the
//     inner instruction first. Verbatim built MIR for `nested_field`:
//         StorageLive(_4); StorageLive(_5); StorageLive(_6); _6 = copy _1;
//         StorageLive(_7); _7 = copy _2; _5 = BitAnd(move _6, move _7);
//         StorageDead(_7); StorageDead(_6); StorageLive(_8); _8 = copy _3;
//         _4 = BitOr(move _5, move _8); StorageDead(_8); StorageDead(_5);
//         _0 = W8(move _4); StorageDead(_4);
//     `_4` (the field) is live before `_5` (the inner op). Refused at
//     `line 2: built mk b0.0:live s2:u8 vs derived mk b0.1:live s2:u8`.
//
//   fru — FUNCTIONAL RECORD UPDATE. `rustc_mir_build` consumes every BASE-supplied field as a bare
//     place with NO temp and NO marker; only the explicitly-given field goes through `as_operand`:
//         StorageLive(_3); _3 = copy _2;
//         _0 = P3 { a: move _3, b: copy (_1.1: u32), c: copy (_1.2: u32) };
//         StorageDead(_3);
//     The shim mints THREE temps. `agg_field_order_ok` has no notion of a base.
//
// MUST STAY REFUSED BY THE PLAN (derived carries NO markers, `<end>`): place_then_instr2,
// place_instr_place — the `seen_place` rule. And by other walls: mk_outer (nested aggregate),
// mk_zst (unit field), mk_refpair (`&u8` field), mut_deref_eq0 (`&mut` load), mk_neg / deref_add /
// load_shift (overflow-check `Inst::Assert`).
// ---- A. NESTED COMPUTED FIELD ---------------------------------------------------------------
// The outermost field expression is itself an rvalue whose OPERAND is another rvalue.
// built:  SL(T_or); SL(T_and); SL(Ta); Ta=a; SL(Tb); Tb=b; T_and=And; SD(Tb); SD(Ta);
//         SL(Tc); Tc=c; T_or=Or; SD(Tc); SD(T_and); _0=W8(move T_or); SD(T_or)
// shim (linear walk): lives the INNER temp first.  PREDICTION: markers_exact FALSE.
#[derive(Clone, Copy)]
pub struct W8(pub u8);
#[inline(never)]
pub fn nested_field(a: u8, b: u8, c: u8) -> W8 {
    W8((a & b) | c)
}

// ---- B. TWO independent computed fields -------------------------------------------------------
// PREDICTION: markers_exact TRUE (field order == instruction order, one level each).
#[derive(Clone, Copy)]
pub struct Two {
    pub x: u8,
    pub y: u8,
}
#[inline(never)]
pub fn two_instr(a: u8, b: u8, c: u8, d: u8) -> Two {
    Two { x: a & b, y: c ^ d }
}

// ---- C. instr field then place field (the admitted order) ------------------------------------
// PREDICTION: markers_exact TRUE.
#[inline(never)]
pub fn instr_then_place(a: u8, b: u8, c: u8) -> Two {
    Two { x: a & b, y: c }
}

// ---- D. field 1 is NESTED, field 0 is flat ----------------------------------------------------
// PREDICTION: markers_exact FALSE (built opens T1 before the xor temp).
#[inline(never)]
pub fn two_instr_nested(a: u8, b: u8, c: u8, d: u8, e: u8) -> Two {
    Two { x: a & b, y: (c ^ d) | e }
}

// ---- E. place field FIRST (the refused order) -------------------------------------------------
// PREDICTION: plan refuses -> markers_exact FALSE, derived body byte-identical to pre-lane-L.
#[inline(never)]
pub fn place_then_instr2(a: u8, b: u8, c: u8) -> Two {
    Two { x: a, y: b & c }
}

// ---- F. ZST FIELD -----------------------------------------------------------------------------
#[derive(Clone, Copy)]
pub struct WithZst {
    pub v: u32,
    pub u: (),
}
#[inline(never)]
pub fn mk_zst(v: u32) -> WithZst {
    WithZst { v, u: () }
}

// ---- G. NESTED AGGREGATE FIELD ----------------------------------------------------------------
#[derive(Clone, Copy)]
pub struct Inner(pub u32);
#[derive(Clone, Copy)]
pub struct Outer {
    pub i: Inner,
    pub n: u32,
}
#[inline(never)]
pub fn mk_outer(a: u32, b: u32) -> Outer {
    Outer { i: Inner(a), n: b }
}

// ---- H. aggregate built then PARTIALLY OVERWRITTEN (functional record update) -----------------
#[derive(Clone, Copy)]
pub struct P3 {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[inline(never)]
pub fn fru(p: P3, x: u32) -> P3 {
    P3 { a: x, ..p }
}

// ---- I. POINTER FIELD (seed_overwritten_ty seeds Ty::Ptr as Constant::Int(0)) -----------------
// The `every field is scalar` guard reads the SEED's element kinds; a `&u8` field seeds as
// `Int(0)`, i.e. it READS AS SCALAR. Does the plan admit it, and does a ref-typed temp then
// cost what a struct temp cost `MemoryRegion::new`?
pub struct RefPair<'a> {
    pub p: &'a u8,
    pub n: usize,
}
#[inline(never)]
pub fn mk_refpair(p: &u8, n: usize) -> RefPair<'_> {
    RefPair { p, n }
}

// ---- J..M. Inst::Load shapes ------------------------------------------------------------------
#[inline(never)]
pub fn mk_from_load(p: &u32) -> Inner {
    Inner(*p)
}
#[derive(Clone, Copy)]
pub struct TwoU32 {
    pub a: u32,
    pub b: u32,
}
#[inline(never)]
pub fn mk_two_loads(p: &u32, q: &u32) -> TwoU32 {
    TwoU32 { a: *p, b: *q }
}
#[inline(never)]
pub fn mk_cast_load(p: &u8) -> Inner {
    Inner(*p as u32)
}
#[inline(never)]
pub fn two_deref_eq(p: &u64, q: &u64) -> bool {
    *p == *q
}
#[inline(never)]
pub fn deref_add(p: &u64, c: u64) -> u64 {
    *p + c
}
#[inline(never)]
pub fn deref_cast(p: &u32) -> u64 {
    *p as u64
}
// A load whose result feeds a SHIFT — the new shift refusal.
#[inline(never)]
pub fn load_shift(p: &u32) -> u32 {
    *p << 1
}
// A load through &mut, read-only (must refuse at the Load arm).
#[inline(never)]
pub fn mut_deref_eq0(p: &mut u64) -> bool {
    *p == 0
}

// ---- N. tuple with MIXED element types (agg-field-order observability) ------------------------
#[inline(never)]
pub fn mk_tup_mixed(a: u8, b: u64) -> (u8, u64) {
    (a, b)
}

// ---- O. char field ----------------------------------------------------------------------------
#[derive(Clone, Copy)]
pub struct CharBox(pub char);
#[inline(never)]
pub fn mk_char(c: char) -> CharBox {
    CharBox(c)
}

// ---- P. bool-from-compare field then place field ----------------------------------------------
#[derive(Clone, Copy)]
pub struct FlagVal {
    pub f: bool,
    pub v: u32,
}
#[inline(never)]
pub fn mk_flagval(a: u32, v: u32) -> FlagVal {
    FlagVal { f: a == 0, v }
}

// ---- Q. the SAME place used in two fields (block param used twice) ----------------------------
#[inline(never)]
pub fn dag_field(a: u8) -> Two {
    Two { x: a, y: a }
}

// ---- R. UnOp field ----------------------------------------------------------------------------
#[derive(Clone, Copy)]
pub struct I32Box(pub i32);
#[inline(never)]
pub fn mk_neg(a: i32) -> I32Box {
    I32Box(-a)
}

// ---- S. three same-typed fields, one computed in the MIDDLE ----------------------------------
// field 0 place, field 1 instr, field 2 place: the `seen_place` rule must refuse.
#[derive(Clone, Copy)]
pub struct P3b {
    pub a: u32,
    pub b: u32,
    pub c: u32,
}
#[inline(never)]
pub fn place_instr_place(a: u32, b: u32, c: u32) -> P3b {
    P3b { a, b: b ^ 1, c }
}

// ---- T. all-const aggregate (must keep markers_exact, zero markers) ---------------------------
#[inline(never)]
pub fn mk_const() -> P3b {
    P3b { a: 1, b: 2, c: 3 }
}

// ---- U. a field whose operand is a FIELD READ of a struct param -------------------------------
#[derive(Clone, Copy)]
pub struct Pair {
    pub l: u8,
    pub r: u8,
}
#[inline(never)]
pub fn from_pair(p: Pair) -> W8 {
    W8(p.l & p.r)
}

// ---- V. two fields, both field-reads (places) -------------------------------------------------
#[inline(never)]
pub fn swap_pair(p: Pair) -> Pair {
    Pair { l: p.r, r: p.l }
}
