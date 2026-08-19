//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 2 — producer mirror of d806992cd4; amended by slice 3): the
// trait-object unsize keeps its real DATA lane on the THIR producer, matching the oracle's
// slice-1 spelling — and since slice 3 the vtable lane carries a STABLE SHARED IDENTITY
// where one is mintable.
//
// A `&T -> &dyn Trait` coercion attaches a vtable and leaves the ADDRESS alone, so the fat
// pointer's data lane IS the source pointer. Both sides spell this `PtrFromParts { data:
// <real source pointer>, metadata: <vtable lane> }`. Slice 3 splits the vtable lane by
// whether the `(principal trait def path, concrete source type)` key is mintable
// (`trust_ir::stable_vtable_global_name` + the ONE shared source renderer
// `trust_types::Ty::vtable_source_type_key`, closed structural grammar):
//   * MINTABLE (primitive/tuple/array/ref source pointees): BOTH sides `GlobalAddr`+`Load`
//     the SAME named, value-less external global — the body is NO LONGER SYMBOLIC (the
//     global is not a `symbolic_consts` carrier; that movement is slice 3's deliverable).
//   * UNMINTABLE (nominal source pointees — their generics-erased names would merge
//     distinct vtables): the slice-2 status quo, byte-identically — producer keeps the
//     per-site symbolic carrier (body stays SYMBOLIC), oracle keeps the fresh Ptr havoc.
//
// SCOPE PARITY is the point of this file: every lane below must match the oracle's admitted
// scope exactly, or the differential manufactures a divergence. Each function pins one line
// of that scope, and each must keep COMPILING — a lowering decline is a coverage decision,
// never an error.

trait Speak {
    fn speak(&self) -> u32;
}

struct Dog;
impl Speak for Dog {
    fn speak(&self) -> u32 {
        1
    }
}

// THE PRECISE LANE, NOMINAL SOURCE: `&Dog -> &dyn Speak` — shared ref, concrete sized
// pointee, real principal, but `Dog` is an ADT: its generics-erased name is outside the
// identity renderer's closed grammar, so the key is UNMINTABLE and the vtable lane keeps
// the slice-2 per-site symbolic carrier (body stays SYMBOLIC; never `Inst::Undef`).
fn as_dyn(d: &Dog) -> &dyn Speak {
    d
}

// THE IDENTITY LANE (vtable slice 3): `&i32 -> &dyn Debug` — a PRIMITIVE source pointee is
// inside the closed structural grammar, so both sides mint the SAME named value-less
// global (`__trust_vtable__core::fmt::Debug$i32__`) and the body is NO LONGER SYMBOLIC:
// the metadata lane is a `Load` of a shared identity, not a symbolic-consts carrier.
// (Per-body evidence in the slice-3 commit: symbolic=false, clean=true.)
fn as_dyn_prim(x: &i32) -> &dyn core::fmt::Debug {
    x
}

// Two same-key coercions in ONE body reference ONE global — their metadata lanes are
// structurally read-read equal (the identity claim, true of every real execution: a
// vtable is per-(source type, principal)). A DIFFERENT source type (u8 here) references
// a DIFFERENT global — distinct vtables never merge.
fn two_keys(a: &i32, b: &i32, c: &u8) -> u32 {
    let x: &dyn core::fmt::Debug = a;
    let y: &dyn core::fmt::Debug = b;
    let z: &dyn core::fmt::Debug = c;
    let _ = x;
    let _ = y;
    let _ = z;
    9
}

// The raw sibling, same precise lane: `*const T -> *const dyn Trait` maps to the same
// `FatPtr(TraitObject)` (wave-RD) and the source spells thin, so it gets the same data lane.
// LET position, deliberately: in RETURN position THIR wraps the real thin->fat unsize in an
// OUTER `*dyn -> *dyn` re-coercion node (the raw twin of the reborrow respell the B2-3
// `dyn_identity` pass-through absorbs for `&dyn`), and that outer node's SOURCE is already
// fat — the thin-source gate correctly refuses it, so the whole expression stays on the
// whole-value symbolic global (`as_raw_dyn_ret` below pins that). Extending the identity
// pass-through to raw pointers is a separate lane, not this slice.
fn as_raw_dyn(p: *const Dog) -> u32 {
    let q: *const dyn Speak = p;
    let _ = q;
    7
}

// The return-position raw case: outer `*dyn -> *dyn` THIR node, fat source, thin-source gate
// refuses -> slice-1 status quo (whole-value symbolic). Must keep compiling either way.
fn as_raw_dyn_ret(p: *const Dog) -> *const dyn Speak {
    p
}

// `&mut T -> &mut dyn Trait` STAYS on the whole-value symbolic global: `&mut dyn` maps THIN
// (`Ty::Ptr`) on both sides — no vtable lane to be precise about. Retiring the thin posture
// is the two-sided `&mut` fat-ref lane, not this slice.
fn as_mut_dyn(d: &mut Dog) -> &mut dyn Speak {
    d
}

// PRINCIPAL-LESS `dyn Send` still fails closed on both sides: no def path to hash a
// `trait_id` from, and the oracle keeps its thin `"dyn"` sentinel there. A coverage decline,
// not an error — this must keep compiling.
fn as_send(x: &u32) -> &dyn Send {
    x
}

// The dyn -> dyn IDENTITY pass-through (B2-3), untouched above the slice-2 lane: rustc
// respells a fresh-region reborrow of a `&dyn` value as an `Unsize` coercion, and with the
// SAME principal on both sides the value forwards unchanged — no `PtrFromParts`, no symbolic
// global, no havoc.
fn through(d: &dyn Speak) -> u32 {
    d.speak()
}
fn call_through(d: &dyn Speak) -> u32 {
    through(d)
}

fn main() {
    let d = Dog;
    assert_eq!(as_dyn(&d).speak(), 1);

    let n = 3i32;
    let _ = as_dyn_prim(&n);
    assert_eq!(two_keys(&1, &2, &3u8), 9);

    assert_eq!(as_raw_dyn(&d as *const Dog), 7);
    let rp = as_raw_dyn_ret(&d as *const Dog);
    let _ = rp;

    let mut d2 = Dog;
    assert_eq!(as_mut_dyn(&mut d2).speak(), 1);

    let s = 5u32;
    let _ = as_send(&s);

    assert_eq!(call_through(&d), 1);
}
