// Trust (lane L) — the AGGREGATE-CONSTRUCTION marker fidelity probe, and the `Inst::Load` verdict.
//
// Sibling of `mf_operand_temps.rs` (wave-MF). Compile with the trust driver and read both
// channels:
//
//   trustc --edition 2021 --crate-type=lib --crate-name=aggprobe \
//     -Ztrust-ir-lower -Ztrust-verify=off -Cdebuginfo=0 -Copt-level=3 \
//     -Coverflow-checks=on -Zdump-mir=all -Zdump-mir-dir=MIR \
//     -Ztrust-dump=ir:IR probes/mf_aggregate_temps.rs --out-dir OUT
//
// WHAT BUILT DOES FOR AN AGGREGATE, measured on these shapes: it is `as_operand` one level up.
// The aggregate is the OUTERMOST expression, so it is written straight into `_0` with no temp of
// its own; each NON-CONSTANT field operand goes through `as_operand`->`as_temp` in FIELD order and
// is retired after the aggregate assign in REVERSE field order. A constant field folds in place.

// ---- IN the planned class (expected `markers_exact: true`) ------------------------------------

#[derive(Clone, Copy)]
pub struct AllocationId(pub u64);
impl AllocationId {
    pub const fn is_null(self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Copy)]
pub struct FlatFlags(pub u8);
impl FlatFlags {
    // THE TARGET (clean-kernel `flat::types::FlatFlags::with`). One computed field.
    //   StorageLive(_3);
    //   StorageLive(_4); _4 = copy (_1.0: u8);
    //   StorageLive(_5); _5 = copy (_2.0: u8);
    //   _3 = BitOr(move _4, move _5); StorageDead(_5); StorageDead(_4);
    //   _0 = FlatFlags(move _3); StorageDead(_3);
    #[inline]
    pub const fn with(self, other: FlatFlags) -> Self {
        FlatFlags(self.0 | other.0)
    }
    // wave-MF's own class; must not regress.
    #[inline]
    pub const fn contains(self, other: FlatFlags) -> bool {
        (self.0 & other.0) == other.0
    }
}

#[derive(Clone, Copy)]
pub struct NodeId(pub u32);

// One PLACE field: `StorageLive(_2); _2 = copy _1; _0 = NodeId(move _2); StorageDead(_2)`.
#[inline(never)]
pub fn mk_node(a: u32) -> NodeId {
    NodeId(a)
}

// One CONSTANT field: `_0 = NodeId(const 7_u32)` — ZERO markers on both sides. This body is
// already `markers_exact: true` before lane L; it is here because admitting the aggregate class
// must not cost it that (constants fold in place and take no temp).
#[inline(never)]
pub fn mk_node_const() -> NodeId {
    NodeId(7)
}

#[derive(Clone, Copy)]
pub struct SourcePos {
    pub file_id: u32,
    pub line: u32,
    pub column: u32,
}

// Three PLACE fields: three temps in field order, three deads in reverse field order.
#[inline(never)]
pub fn mk_pos(f: u32, l: u32, c: u32) -> SourcePos {
    SourcePos { file_id: f, line: l, column: c }
}

// A TUPLE return through the same recognizer (wave-L's path).
#[inline(never)]
pub fn mk_pair(a: u32, b: u32) -> (u32, u32) {
    (a, b)
}

// MIXED FIELD TYPES. This one is the observable negative control for
// `-Ztrust-sat-perturb=agg-field-order`, and the reason it has to exist is a MEASURED property of
// the oracle rather than of the shim: `canon_markers` names a local `s{alpha}` by FIRST
// APPEARANCE in the marker stream, so permuting the field temps of an ALL-SAME-TYPE aggregate
// (`mk_pos`, three `u32`s) alpha-renames back to a byte-identical canonical string — measured,
// `mk_pos` stays `markers_exact: true` under `agg-field-order` with `applications=1`. With two
// DIFFERENT field types the permutation shows up in the type column and the channel refuses.
#[derive(Clone, Copy)]
pub struct Mixed {
    pub a: u8,
    pub b: u64,
}
#[inline(never)]
pub fn mk_mixed(a: u8, b: u64) -> Mixed {
    Mixed { a, b }
}

#[derive(Clone, Copy)]
pub struct Flag(pub bool);

// A computed field nested one level: the field's own `as_temp` opens BEFORE the comparison's
// operand temp.
#[inline(never)]
pub fn mk_flag(a: u64) -> Flag {
    Flag(a == 0)
}

// `Inst::Load` — a shared-ref scalar param read. The load IS the operand temp:
//   StorageLive(_2); _2 = copy (*_1); _0 = Eq(move _2, const 0_u64); StorageDead(_2)
#[inline(never)]
pub fn deref_eq0(p: &u64) -> bool {
    *p == 0
}

// ---- OUT of the planned class, each for a named and MEASURED reason ---------------------------
//
// These are the boundary, not a to-do list. Every one must stay `markers_exact: false`.

// place_then_instr: built lives field 0's temp FIRST and only then opens field 1's, while this
// shim's linear instruction walk reaches the `^` before it ever reaches the aggregate. This is
// exactly what `agg_field_order_ok` refuses; without that check the derived marker sequence would
// be wrong (and the oracle would refuse it anyway).
impl SourcePos {
    #[inline(never)]
    pub fn place_then_instr(self) -> Self {
        SourcePos { file_id: self.file_id, line: self.line ^ 1, column: 0 }
    }
    // The real clean-kernel `SourcePos::coalesced`: the `/` mints a div-by-zero assert, which
    // SPLITS the MIR chain, so the body is multi-block and its markers cross a block boundary.
    // That is the multi-block class, not this one.
    #[inline(never)]
    pub fn coalesced(self) -> Self {
        SourcePos { file_id: self.file_id, line: self.line / 10, column: 0 }
    }
}

// pat_deref_eq0 / closure_pat_eq0: THE `Inst::Load` BOUNDARY, and the reason lane L does NOT
// discharge `BigNat::is_zero::{closure#0}`. `|&l| l == 0` lowers to the SAME four-instruction
// trust-ir as `*p == 0` (`load; const; icmp; ret`) but its built body carries FOUR markers, not
// two — the `&l` pattern mints a NAMED BINDING local with its own `StorageLive`/`StorageDead`
// pair, plus an unreachable `FakeRead` block:
//
//   StorageLive(_2); _2 = copy (*_1);          <- the binding `l`
//   StorageLive(_3); _3 = copy _2;             <- the comparison's operand temp
//   _0 = Eq(move _3, const 0_u64); StorageDead(_3); StorageDead(_2);
//
// And it carries NO scope table, so wave-MF's `func.scopes.is_none()` firewall does not see it.
//
// Until 2026-08-13 it was refused by the ORACLE alone — the plan ADMITTED it and offered a
// two-marker sequence against built's four. It is now refused BY THE PLAN: `source_form_admits`
// reads the PARAMETER PATTERNS out of HIR, which is where the difference between `&l: &u64` and
// `p: &u64` actually lives, and refuses every parameter that is not a simple by-value binding
// or `_`. See `probes/mf_residual.rs` group D, whose `d5_simple_deref_eq0` is the byte-identical
// trust-ir sibling that must keep flipping.
#[inline(never)]
pub fn pat_deref_eq0(&l: &u64) -> bool {
    l == 0
}
#[inline(never)]
pub fn closure_pat_eq0(xs: &[u64]) -> bool {
    xs.iter().all(|&l| l == 0)
}

// nonscalar_field: THE ONE PLACE WHERE SATISFYING THE MARKER CHANNEL WAS NOT FREE, kept as a
// permanent record. This is `memory_model::MemoryRegion::new`. Emitting built's field temps here
// is CORRECT — built really does spell `StorageLive(_4); _4 = copy _1` for the struct field, and
// the body did reach `markers_exact: true` — but the derived body then carries a STRUCT temp, and
// the flip fragment gate refuses one: `"struct temp _4 used outside call-dest / whole read /
// scalar field read"`. Measured on the whole crate, that traded a -O0 flip for nothing. So the
// plan declines any aggregate with a non-scalar field and this body keeps its pre-lane-L
// behaviour: `markers_exact: false`, flips at -O0 only. Widening the fragment gate is a different
// change with a different argument.
#[derive(Clone, Copy)]
pub struct Region {
    pub id: AllocationId,
    pub off: usize,
}
#[inline(never)]
pub fn mk_region(id: AllocationId, off: usize) -> Region {
    Region { id, off }
}

// right_nested: wave-MF's permanent record of the evaluation-order boundary — refused by ordering
// rule (2) since 2026-08-13, not by the channel.
#[inline(never)]
pub fn right_nested(a: u8, b: u8, c: u8) -> bool {
    a == (b & c)
}

// ---- MUST NOT REGRESS -------------------------------------------------------------------------
#[inline(never)]
pub fn unitfn() {}
#[inline(never)]
pub fn ident(a: u64) -> u64 {
    a
}
#[inline(never)]
pub fn fieldret(a: AllocationId) -> u64 {
    a.0
}
// A returned load takes NO temp on either side (`_0 = copy (*_1)`).
#[inline(never)]
pub fn deref_ret(p: &u64) -> u64 {
    *p
}
