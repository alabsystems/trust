// Trust (LANE PCA, plan-clause audit, 2026-08-17) — the CHECKED-ARITHMETIC-CHAIN (wave-CK) clause
// corpus.
//
// `probes/mf_checked.rs` has twelve bodies and was written by the wave that landed the plan. A
// clause audit cannot use only the corpus the clause's author chose: a clause that never fires on
// its author's corpus reads as "unwitnessed" when it may simply be untested. This file exists to
// give each of wave-CK's eleven clauses a POPULATION on both sides of its boundary.
//
// Naming: `ck_<clause>_<shape>`. Every body is a whole program; none is a fragment.
#![allow(dead_code, clippy::identity_op, clippy::erasing_op, clippy::eq_op)]
#![allow(clippy::unnecessary_cast, clippy::precedence, unused_variables)]

// =================================================================================================
// C3 — `blk.params.is_empty()`. The plan refuses ANY body with a trust-ir entry-block parameter.
// C9+C10 already force every chain leaf to be a CONSTANT, so an admitted body cannot read a
// parameter. These bodies have parameters that no chain leaf can reach.
// =================================================================================================

/// One unused parameter, two-unit chain. Built lowers this identically to `A2_USIZE`.
pub fn ck_c3_unused_one(_a: usize) -> usize {
    256 * 1024 * 1024
}

/// Three unused parameters, two-unit chain.
pub fn ck_c3_unused_three(_a: usize, _b: u32, _c: bool) -> usize {
    256 * 1024 * 1024
}

/// One unused parameter, THREE-unit chain (two marked links).
pub fn ck_c3_unused_three_unit(_a: u64) -> u64 {
    16 * 1024 * 1024 * 1024
}

/// One unused parameter, FOUR-unit chain (three marked links).
pub fn ck_c3_unused_four_unit(_a: u32) -> u32 {
    2 * 3 * 5 * 7 * 11
}

/// An unused parameter of REFERENCE type.
pub fn ck_c3_unused_ref(_p: &u64) -> usize {
    256 * 1024 * 1024
}

/// An unused `_` (wildcard) parameter — no binding is even declared.
pub fn ck_c3_wild_param(_: usize) -> usize {
    256 * 1024 * 1024
}

/// Two unused parameters and a SIGNED chain.
pub fn ck_c3_unused_signed(_a: i32, _b: i32) -> i64 {
    1024 * 1024 - 7 - 9
}

/// An unused parameter and a MIXED-opcode chain.
pub fn ck_c3_unused_mixed(_a: u8) -> u32 {
    2 * 3 * 5 + 7
}

/// The negative control for C3: the parameter IS read, and is a chain leaf. Must stay refused —
/// built mints its operand temp at the consumer and it interleaves with the chain's.
pub fn ck_c3_used_leaf(a: usize) -> usize {
    a * 1024 * 1024
}

/// The parameter is read but not by the chain — it is the OTHER operand of the outermost add.
/// Still a parameter read inside the body, still refused by C9/C10 rather than by C3.
pub fn ck_c3_used_outer(a: usize) -> usize {
    256 * 1024 * 1024 + a
}

// =================================================================================================
// C6 — `is_int(&ty)` on each chain unit. `Inst::Overflow` is minted only by the checked-arithmetic
// lowering, which rustc emits for integer add/sub/mul only. These bodies try every non-integer
// arithmetic the surface language has.
// =================================================================================================

/// A FLOAT chain: no overflow check exists, so no `Inst::Overflow` is minted at all.
pub const CK_C6_FLOAT: f64 = 2.0 * 3.0 * 5.0;

/// A float chain with four factors.
pub const CK_C6_FLOAT4: f32 = 1.5 * 2.5 * 3.5 * 4.5;

/// A BOOL chain — `&&` is not arithmetic and mints no overflow unit.
pub const CK_C6_BOOL: bool = true && false && true;

/// A bitwise chain: `&`/`|`/`^` are unchecked, so no `Inst::Overflow`.
pub const CK_C6_BITAND: u32 = 0xff & 0x0f & 0x03;

/// A SHIFT chain: shifts carry their own (different) check idiom.
pub const CK_C6_SHIFT: u32 = 1 << 4 << 2;

/// `char` arithmetic does not exist; the nearest thing is a cast chain.
pub const CK_C6_CHARCAST: u32 = 'a' as u32 * 2 * 3;

/// A `u128` chain — integer, so C6 admits; the width is what varies.
pub const CK_C6_U128: u128 = 1024 * 1024 * 1024;

/// An `i128` chain.
pub const CK_C6_I128: i128 = -1024 * 1024 * 1024;

/// An `isize` chain.
pub const CK_C6_ISIZE: isize = 512 * 512 * 512;

/// A `u8` chain that stays in range.
pub const CK_C6_U8: u8 = 2 * 3 * 5;

/// An `i8` chain.
pub const CK_C6_I8: i8 = 2 * 3 * 5;

/// A `u16` chain.
pub const CK_C6_U16: u16 = 16 * 16 * 16;

/// An `i16` chain.
pub const CK_C6_I16: i16 = 8 * 8 * 8;

// =================================================================================================
// C7 — `chain.len() >= 2`, and C8 — the chain tail IS the returned value.
// =================================================================================================

/// ONE unit: no non-outermost sub-expression, no temp. Must keep an EMPTY exact sequence.
pub const CK_C7_ONE: usize = 256 * 1024;

/// Two units.
pub const CK_C7_TWO: usize = 256 * 1024 * 4;

/// Three units.
pub const CK_C7_THREE: usize = 256 * 1024 * 4 * 4;

/// Four units.
pub const CK_C7_FOUR: usize = 2 * 3 * 5 * 7 * 11;

/// Five units.
pub const CK_C7_FIVE: u64 = 2 * 3 * 5 * 7 * 11 * 13;

/// Six units.
pub const CK_C7_SIX: u64 = 2 * 3 * 5 * 7 * 11 * 13 * 17;

/// The chain result is CAST before it is returned: the tail is not the chain tail (C8).
pub const CK_C8_CAST_TAIL: u64 = (256u32 * 1024 * 1024) as u64;

/// The chain feeds a comparison, so the return value is a `bool` and not the chain tail (C8).
pub const CK_C8_CMP_TAIL: bool = 256 * 1024 * 1024 > 0;

/// A chain whose result is negated: the outermost node is a `UnOp`, not the chain tail.
pub const CK_C8_NEG_TAIL: i64 = -(2 * 3 * 5);

// =================================================================================================
// C9 / C10 — the chain is LEFT-NESTED and LINEAR (rhs constant, lhs const-or-predecessor).
// =================================================================================================

/// Right-nested: `a * (b * c)`.
pub const CK_C10_RIGHT: usize = 1024 * (256 * 1024);

/// Right-nested three deep.
pub const CK_C10_RIGHT3: usize = 2 * (3 * (5 * 7));

/// Balanced: `(a * b) * (c * d)` — the outermost unit's RHS is a chain result, not a constant.
pub const CK_C9_BALANCED: usize = (2 * 3) * (5 * 7);

/// Left-nested but with a right-nested SUFFIX.
pub const CK_C10_MIXED: usize = 2 * 3 * (5 * 7);

/// Left-nested, all constants: the admitted shape, three units.
pub const CK_C10_LEFT3: usize = 2 * 3 * 5 * 7;

// =================================================================================================
// C11 — every unit result used exactly once.
// =================================================================================================

/// A DAG: the inner product is consumed twice.
pub const fn ck_c11_dag() -> usize {
    let x = 256 * 1024;
    x * x
}

/// A chain link used twice through a `const` item rather than a `let`.
pub const CK_C11_SQ: usize = (256 * 1024) * (256 * 1024);

// =================================================================================================
// C5 — every node is `Inst::Const` or part of a canonical checked unit.
// =================================================================================================

/// A trailing cast after a chain — `Inst::Cast` is outside the modelled set.
pub const CK_C5_TRAILING_CAST: usize = (256u32 * 1024 * 1024) as usize;

/// A leading cast.
pub const CK_C5_LEADING_CAST: u64 = (256u32 as u64) * 1024 * 1024;

/// An unchecked `BinOp` (bit-or) interleaved with a checked chain.
pub const CK_C5_BITOR_MIX: u32 = (2 * 3 * 5) | 1;

/// A DIVISION, which carries the div-by-zero idiom rather than the overflow one.
pub const CK_C5_DIV: u32 = 4096 / 8 / 2;

/// A REMAINDER, same family as division.
pub const CK_C5_REM: u32 = 4096 % 9 % 5;

/// A unary negation inside the chain.
pub const CK_C5_NEG_INNER: i32 = -2 * 3 * 5;

// =================================================================================================
// C1 — the wave-MF `scopes.is_none()` firewall. These are `let`-bearing twins of admitted bodies.
// Deleting C1 admits them, and their built sequences carry the `let`'s own named-local pair.
// =================================================================================================

/// A two-unit chain written through a `let`.
pub const fn ck_c1_let_two() -> usize {
    let inner = 256 * 1024;
    inner * 1024
}

/// A three-unit chain written through two `let`s.
pub const fn ck_c1_let_three() -> u64 {
    let a = 16 * 1024;
    let b = a * 1024;
    b * 1024
}

/// A `let` that binds a bare constant and a chain that ignores it.
pub const fn ck_c1_let_unused() -> usize {
    let _unused = 7;
    256 * 1024 * 1024
}

/// A `let` whose initializer is the whole chain and whose binding is returned.
pub const fn ck_c1_let_whole() -> usize {
    let v = 256 * 1024 * 1024;
    v
}

// =================================================================================================
// C2 / C4 — one block, terminated by a single-value `Return`.
// =================================================================================================

/// A chain inside an `if`: two blocks, so C2 refuses.
pub const fn ck_c2_branchy(c: bool) -> usize {
    if c { 256 * 1024 * 1024 } else { 0 }
}

/// An early `return` before the chain: two `Return`s, and more than one block.
pub const fn ck_c4_early_return(c: bool) -> usize {
    if c {
        return 0;
    }
    256 * 1024 * 1024
}

/// A chain in a body that returns a TUPLE — the `Return` carries one value that is an aggregate.
pub const fn ck_c4_tuple_return() -> (usize, usize) {
    (256 * 1024 * 1024, 4096)
}

/// A unit-returning body whose chain result is discarded.
pub const fn ck_c4_unit_return() {
    let _ = 256 * 1024 * 1024;
}

// =================================================================================================
// The admitted class itself, at width — these must all stay `right`, and any clause whose deletion
// keeps them `right` while ADMITTING more is the profile of an over-refusal.
// =================================================================================================

pub const CK_OK_USIZE_2: usize = 256 * 1024 * 1024;
pub const CK_OK_U64_3: u64 = 16 * 1024 * 1024 * 1024;
pub const CK_OK_U32_2: u32 = 4 * 8 * 16;
pub const CK_OK_I64_SUB: i64 = 1024 * 1024 - 7 - 9;
pub const CK_OK_MIXED: u32 = 2 * 3 * 5 + 7;
pub const CK_OK_ADD3: u32 = 1 + 2 + 3 + 4;
pub const CK_OK_SUB3: i32 = 100 - 1 - 2 - 3;

// =================================================================================================
// C3, THE SECOND HALF — the clause is about trust-ir BLOCK PARAMETERS, and `plan_checked_markers`
// is a trust-ir-only plan: unlike the three source-side plans it never consults
// `hir_params_are_simple_bindings`. A DESTRUCTURING parameter mints a NAMED BINDING LOCAL with its
// own `StorageLive`/`StorageDead` pair that the instruction stream cannot see — so "an admitted
// body cannot read a parameter" (true, by C9+C10) is NOT the same claim as "a parameter cannot
// mint a marker". These bodies separate the two.
// =================================================================================================

/// A REFERENCE-PATTERN parameter. `declare_bindings` + `place_into_pattern` mint a binding local.
pub fn ck_c3_pat_ref(&_l: &u64) -> usize {
    256 * 1024 * 1024
}

/// A TUPLE-PATTERN parameter.
pub fn ck_c3_pat_tuple((_a, _b): (u32, u32)) -> usize {
    256 * 1024 * 1024
}

/// A STRUCT-PATTERN parameter.
pub struct CkOne(pub u32);
pub fn ck_c3_pat_struct(CkOne(_k): CkOne) -> usize {
    256 * 1024 * 1024
}

/// A `ref` binding-mode parameter.
pub fn ck_c3_pat_ref_mode(ref _a: usize) -> usize {
    256 * 1024 * 1024
}

/// A `mut` simple binding — still a simple binding, still no binding local.
pub fn ck_c3_mut_binding(mut _a: usize) -> usize {
    256 * 1024 * 1024
}

/// Three-unit chain behind a destructuring parameter.
pub fn ck_c3_pat_ref_three(&_l: &u64) -> u64 {
    16 * 1024 * 1024 * 1024
}
