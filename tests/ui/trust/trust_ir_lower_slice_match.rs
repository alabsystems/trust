//@ check-pass
//@ compile-flags: --crate-type=lib -Ztrust-ir-lower -Ztrust-verify=off
//@ forbid-output: final Trust-IR module validation failed
// wave-SL: a `match` on a SLICE with slice patterns — `match s as &[_] {
// [_, x @ .., _] => .., _ => .. }`, the measured `Match(slice scrutinee)`
// population (45 sole rows at wave-full-0901c, whose corpus shape is
// exactly this `as &[_]` cast).
//
// Unlike wave-AR's fixed ARRAY destructure, a slice's arity is not
// static, so the pattern is a runtime TEST: `len >= prefix + suffix` for
// a rest pattern, `len == prefix + suffix` without one. Everything it
// needs already existed — the str-match lane reads a fat pointer's length
// with `PtrMetadata`, `PtrData` gives the data lane, byte-offset `GEP`
// over `Ty::I8` is this file's element-address idiom, and `PtrFromParts`
// builds the subslice. Element size comes from rustc's authoritative
// layout, never hand-computed.
//
// THE SAME TRAP AS wave-AR, hit a second time and recorded here: `x @ ..`
// spells the rest marker as the BINDING'S SUBPATTERN, so matching
// `subpattern: None` silently misses the entire `@`-bound population —
// which is the shape this lane exists for. Measured: the first cut
// declined `mid_len` while accepting the rest-less forms.
//
// FENCES, each a silent fall-through so every declined shape keeps its
// existing tag: exactly two arms with the second irrefutably wild; no
// guards; the scrutinee must map to the slice fat pointer; every
// prefix/suffix subpattern is `_` or a plain binding (which under match
// ergonomics binds `&T` — the GEP pointer this lane hands out); and the
// element type must have a statically known non-zero size.
#[derive(Clone, Copy)]
pub struct N(pub u8);

// A bound REST: its length is `len - prefix - suffix`, computed at
// runtime, and its data pointer is a GEP past the prefix.
pub fn mid_len(a: &[N; 4]) -> usize {
    match a as &[N] {
        [_, x @ .., _] => x.len(),
        _ => 0,
    }
}

// A PREFIX element bind — a static byte offset.
pub fn first_val(a: &[N; 4]) -> u8 {
    match a as &[N] {
        [x, .., _] => x.0,
        _ => 0,
    }
}

// A SUFFIX element bind — offset `(len - ns + j) * size`, so the address
// depends on the runtime length.
pub fn last_val(a: &[N; 4]) -> u8 {
    match a as &[N] {
        [_, .., x] => x.0,
        _ => 0,
    }
}

// No rest: the length test is EXACT (`==`), not `>=`.
pub fn exact_two(a: &[N; 2]) -> u8 {
    match a as &[N] {
        [p, q] => p.0 + q.0,
        _ => 0,
    }
}

fn main() {}
