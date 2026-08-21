//@ check-pass
//@ compile-flags: -Z trust-ir-lower -Z trust-verify=off

// Trust (vtable slice 12 — the arrays family: THIR-side once-stored-slot value model +
// Array dead seeds + the (Tuple, Array) quarantine): the oracle bridge seeds every array
// literal/repeat with `Undef [T x N]` (LIVE havoc pre-slice), and the producer's slice
// lane spells `&[..]` as an escaping once-stored Alloca. This slice retires both, all
// differential-local: `zero_const`/`undef_is_dead_seed` Array arms (+ the
// InsertField->InsertElement respell the pinned interpreter requires),
// `respell_thir_array_slots_as_globals` (the slice-6 mirror on the side under test,
// ty-scoped to Array/homogeneous-Tuple slots, clone-only), cross-SPELLING pairing arms
// (`promoted_pair_tys_agree` / `promoted_init_content_eq`), and — the load-bearing
// guard — `tys_agree`'s (Tuple, Array) Err QUARANTINE replacing the raw-equality leaf
// that would have manufactured "signature divergence" for every by-value-array body.
//
// Every body below must keep COMPILING (a lowering decline is a coverage decision, never
// an error); each pins one measured lane of the slice.

// THE FAT FLIP (references::BAR / const-vecs-and-slices::y, measured Agreed movers):
// an inline array literal borrowed as a slice. Producer: once-stored Tuple slot +
// PtrFromParts, respelled to `__trust_promoted_0`; oracle: Undef-Array seed + chain +
// slot, dead-seed-substituted then slice-6-respelled; paired cross-spelling, raw data
// lane agreeing on the same named immutable object.
pub const BAR: &[u8] = &[1, 2, 3];

// THE THIN FLIP (const-vecs-and-slices::z): the producer already mints its wave-16
// promoted global here — only the oracle side needed the Array dead-seed + respell.
pub static Z: &'static [u8; 3] = &[1, 2, 3];

// THE ZERO-LENGTH FLIP (issue-40231-2 TEXT_U16): `[T; 0]`'s Undef seed is the type's
// SOLE inhabitant — substitution is exact — and zero-length globals materialize (the
// pre-registered N=0 uncertainty, resolved positive by unit test and measurement).
pub const EMPTY: &[u16] = &[];

// THE INTERNAL-ARRAY FLIP (arithmetic-expr-in-array-len / no_duplicates, group C):
// a signature-array-free body whose repeat chain substitutes; both sides interpret and
// agree on the unit return with no observation gap.
pub fn internal_array() {
    let _foo = [0i32; 8];
}

// THE QUARANTINE HOLD (const-vecs-and-slices::x and the whole by-value group B): an
// array IN THE SIGNATURE is the documented (Tuple, Array) spelling split — held as a
// comparability failure, NEVER published as a signature divergence.
pub static X: [i8; 4] = [1, 2, 3, 4];

// THE POSTURE THAT MUST NOT MOVE (issue-38002 LIST / const-enum-vector C): an array of
// payload-enum elements keeps the flat-enum-model Live seed (uncovered other-variant
// lanes — the slice-11 C family); no Array arm may unlock a lane the construction
// deliberately never wrote.
pub enum E {
    V1(isize),
    V0,
}
pub static C: [E; 3] = [E::V0, E::V1(0xDEADBEE), E::V0];

fn main() {}
