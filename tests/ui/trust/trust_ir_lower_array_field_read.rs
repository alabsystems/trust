//@ run-pass
//@ dont-check-compiler-stderr
//@ compile-flags: -Ztrust-ir-lower -Ztrust-verify=off
#![allow(unconditional_panic)]
//! Trust (wave-RF2): READ-SIDE AGGREGATE TRANSPORT — the two halves that only work together.
//!
//! `site_a` admits an ARRAY-typed field read (`v.0` on `struct f32x4([f32; 4])`) into the
//! `ExprKind::Field` accept set, as a first-class `ExtractField` of the lane the registered
//! `StructDef` already declares. `site_b` admits `F32`/`F64` as an `ExprKind::Index` element
//! type. Landing `site_b` alone moves the float bodies from `Index(non-scalar element ty)` to
//! `Field(non-scalar field ty)` + `Index(unsupported base)` — still dirty — because the Index
//! arm checks the element type BEFORE it lowers its base. That measured ordering is why the
//! two halves are one commit, and `f_const_simd_f32` below is the fixture that shows it.
//!
//! FIELD ORDER — the confirmed-miscompile mechanism — is answered by construction, not by a
//! check: rustc REORDERS struct fields against declaration order (`struct R { a: u8, b: u64 }`
//! is laid out `b@0, a@8`), but this lane computes NO byte offset. It reads BY INDEX through
//! the registered `StructDef`, whose field list is built from `adt.non_enum_variant().fields`
//! in `FieldIdx` (declaration) order — the same index `name.as_u32()` yields. `reordered`
//! below is the live witness: its array field is DECLARED second and LAID OUT first.
//!
//! ORACLE, stated exactly. `-Ztrust-ir-lower=strict` is STRUCTURALLY BLIND to this lane and
//! grades it neither way: the derived-MIR shim stops at `Const(non int/bool)` (the
//! `Constant::Array` seed) or `non-scalar param type Array(..)` before reaching any element op,
//! `to_mir` has no `Inst::ExtractElement` arm at all, and its `ExtractField` arm refuses a
//! non-scalar field. The oracle that DOES cover the lane is the INTERPRETATION differential,
//! which is live for arrays (an array-from-param body runs `Agreed` on 5 samples, its
//! dynamic-index twin on 25) — so every admitted fixture here takes a SCALAR parameter, and the
//! file is `run-pass` so the values are checked against real execution too.
//!
//! MEASURED BEFORE (subject build `build/snap-lv2-subject`, `-Ztrust-ir-lower`), so the pin has a
//! real "before" and not an assumed one:
//!
//! | fixture             | before                                                    | after |
//! |---------------------|-----------------------------------------------------------|-------|
//! | `a_struct_int`      | `Field(non-scalar field ty)` + `Index(unsupported base)`   | clean |
//! | `b_struct_ref`      | `Field(non-scalar field ty)` + `Index(unsupported base)`   | clean |
//! | `c_tuple_holder`    | `Field(non-scalar field ty)` + `Index(unsupported base)`   | clean |
//! | `d_float_elem`      | `Index(non-scalar element ty)`                             | clean |
//! | `e_float_dynamic`   | `Index(non-scalar element ty)`                             | clean |
//! | `f_const_simd_f32`  | `Index(non-scalar element ty)`                             | clean |
//! | `g_reordered`       | `Field(non-scalar field ty)` + `Index(unsupported base)`   | clean |
//! | `r_zero_len`        | `Field(non-scalar field ty)`                               | UNCHANGED |
//! | `r_agg_elem`        | `Index(non-scalar element ty)` + `Field(unsupported lhs)`  | UNCHANGED |
//! | `r_float_oob`       | `Index(non-scalar element ty)`                             | `Index(const index out of bounds)` |
//!
//! `r_float_oob` is the row that proves the #191 bounds gate is REACHED rather than bypassed:
//! today the element gate refuses first, so the OOB test never runs; after `site_b` the float
//! element is admitted and the body must stop at the bounds gate instead. A `clean` there would
//! be the #191 miscompile back.

#[derive(Copy, Clone)]
pub struct Payload {
    pub k: u32,
}

pub struct Quad(pub [u32; 4]);
pub struct FQuad(pub [f32; 4]);
pub struct Empty(pub [u32; 0]);
pub struct AggArr(pub [Payload; 2]);

/// rustc lays `b` BEFORE `a`; the lane must still read `a` at declaration index 0.
pub struct Reordered {
    pub a: u8,
    pub b: [u64; 2],
}

// ---------------------------------------------------------------- ADMITTED --

// site_a: struct-held int array, constant index, scalar param (the differential samples it).
pub fn a_struct_int(v: u32) -> u32 {
    let s = Quad([v, 2, 3, 4]);
    s.0[1]
}

// site_a through a SHARED receiver — the whole-struct read-through-ref lane already ships
// (`fn(s: &S) -> u32 { s.b }` is clean today), so the array field rides it unchanged.
pub fn b_struct_ref(s: &Quad) -> u32 {
    s.0[0]
}

// site_a with a TUPLE holder: element types come from the same `map_ty`, so they agree by
// construction and the holder check takes its unconditional arm.
pub fn c_tuple_holder(t: ([u32; 2], u32)) -> u32 {
    t.0[1] + t.1
}

// site_b alone: a bare float array, constant index.
pub fn d_float_elem(v: f32) -> f32 {
    let a = [v, 2.0, 3.0];
    a[1]
}

// site_b alone, DYNAMIC index — the bounds `Assert` / `BoundsCheck` obligation path is
// element-type agnostic (index and length are both `Ty::Usize`).
pub fn e_float_dynamic(v: f32, i: usize) -> f32 {
    let a = [v, 2.0, 3.0, 4.0];
    a[i % 4]
}

// site_a AND site_b: the corpus motif (`tests/ui/consts/const-eval/simd/insert_extract.rs`
// reads `V.0[K]` on `#[repr(simd)] struct f32x4([f32; 4])`). Neither half alone lowers it.
pub fn f_const_simd_f32(v: f32) -> f32 {
    let q = FQuad([v, 14.0, 15.0, 16.0]);
    q.0[2]
}

// site_a, FIELD ORDER: `b` is declared second and laid out FIRST. Reading index 1 must yield
// `b`, never `a` — an offset-based lane would return the wrong field here.
pub fn g_reordered(v: u64) -> u64 {
    let r = Reordered { a: 9, b: [v, 77] };
    r.b[1]
}

// ----------------------------------------------------------------- REFUSED --
// Each must keep failing CLOSED with its named tag and push no IR node. `run-pass` is the
// point: failing closed is a lowering refusal, never a compile error — Trust compiles all
// valid Rust identically.

// `Ty::Array(_, 0)` — no element to read. Keeps `Field(non-scalar field ty)`.
pub fn r_zero_len(s: Empty) -> [u32; 0] {
    s.0
}

// An AGGREGATE element type (`Payload`, a struct) is a first-class `Ty::Array` like every
// fixed-size array, but the element READ still refuses: `Index(non-scalar element ty)` — the
// Index arm checks the element type before it lowers its base. The widened gate is
// `seed_constant`'s set, not "anything".
pub fn r_agg_elem(s: AggArr) -> u32 {
    s.0[1].k
}

// The #191 bounds gate is NOT weakened by admitting floats: a constant index that is provably
// out of bounds still fails closed with `Index(const index out of bounds)`, because built MIR
// emits a bounds `Assert` and the function diverges. Never called — the body is lowered anyway,
// which is the whole point (`trust_ir_const_index_oob_fails_closed.rs` is the int-element twin).
const FC: [f32; 2] = [1.0, 2.0];
pub fn r_float_oob() -> f32 {
    FC[7]
}

fn main() {
    assert_eq!(a_struct_int(1), 2);
    assert_eq!(b_struct_ref(&Quad([5, 6, 7, 8])), 5);
    assert_eq!(c_tuple_holder(([10, 20], 3)), 23);
    assert_eq!(d_float_elem(1.0), 2.0);
    assert_eq!(e_float_dynamic(1.0, 0), 1.0);
    assert_eq!(e_float_dynamic(1.0, 3), 4.0);
    assert_eq!(f_const_simd_f32(13.0), 15.0);
    // FIELD ORDER: index 1 is `b` in DECLARATION order; `b[1]` is 77.
    assert_eq!(g_reordered(42), 77);
    let z: [u32; 0] = r_zero_len(Empty([]));
    assert!(z.is_empty());
    assert_eq!(r_agg_elem(AggArr([Payload { k: 1 }, Payload { k: 2 }])), 2);
}
