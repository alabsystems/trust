//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off
//! Trust (vtable slice 15): SCALAR-element fixed arrays are FIRST-CLASS `Ty::Array` on the
//! THIR producer — the MIR oracle's spelling — so a by-value-array signature reaches the real
//! (Array, Array) comparison instead of the slice-12 (Tuple, Array) quarantine, and the
//! construction/const-index/match/destructure lanes ride the format's element ops
//! (`InsertElement`/`ExtractElement` with an integer index constant — `I64` for a construction
//! slot or constant index, `Usize` for a pattern position; `supports_element_ops()` =
//! `Vector | Array`). The repeat lane does not: since trust-ir v50 (2026-09-28) `[x; N]` is ONE
//! `Const(Splat)` or `ArraySplat`, not N element writes. Since 2026-09-23 EVERY fixed array is first-class, aggregate elements
//! included — the tuple spelling was N copies of the element type (see
//! `trust_ir_huge_array_types_first_class.rs`).
//!
//! Each shape below exercises one converted lane; the file existing at all pins "these still
//! compile clean under the flag" (the sweep measured their differential rows the day this
//! landed — see TRUST_IR_V2.md's slice-15 section for the numbers).

// The ctor lane (ExprKind::Array) + by-value-array signature (the quarantine's flip shape).
static CTOR: [isize; 4] = [1, 2, 3, 4];

// The repeat lane: ONE uniform-array value (trust-ir v50 `Constant::Splat`) at every count; the
// count threshold (`REPEAT_COMPACT_MIN`) that once chose a per-slot build below 1024 is gone.
static REPEAT: [isize; 4] = [32; 4];

// A 128-bit element (the issue-101585 shape).
fn min_array() -> [i128; 1] {
    [i128::MIN]
}

// The const-index lane: in-bounds literal index -> Const I64 + ExtractElement, behind the
// #191 bounds gate.
pub fn const_index() -> isize {
    CTOR[2]
}

// The destructure lane (emit_bind Fields over a first-class array).
pub fn destructure() -> isize {
    let [a, b, _, _] = REPEAT;
    a + b
}

// The match lane (the wave-AM positional classifier over the Array spelling).
pub fn array_match(x: bool) -> u8 {
    let arr = [1u8, 2u8];
    match arr {
        [1, b] if x => b,
        [a, _] => a,
    }
}

// A struct FIELD of scalar-element array type: registered def carries `Ty::Array`, the splice
// admits it (def_field_ok + the two-phase types intern), and the seed lane's Array arm fills it.
pub struct Holder {
    pub a: u16,
    pub b: [u8; 3],
}
pub static FIELD: Holder = Holder { a: 1, b: [2, 3, 4] };

// The fat-slice lane: the Alloca slot is now `Ty::Array`-typed (map_ty is the single source of
// truth for the slot spelling).
pub static SLICE: &[isize] = &[1, 2, 3, 4];

// An aggregate-element array — first-class `Ty::Array` of a tuple element now (must still
// compile clean).
pub static PAIRS: [(usize, usize); 2] = [(0, 1), (1, 0)];

fn main() {
    let _ = (min_array(), const_index(), destructure(), array_match(true));
    let _ = (&FIELD, SLICE, &PAIRS);
}
