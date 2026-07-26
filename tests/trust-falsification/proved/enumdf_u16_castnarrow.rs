#![crate_type = "lib"]
// Was MUTANT (pre-9f4b2c8417 the narrowing `e as u8` was refuted as a lossy
// cast). RECLASSIFIED: defined `as` truncation is valid Rust, and this code is
// GENUINELY safe — every discriminant truncates to 0 (0, 256, 512 are all
// ≡ 0 mod 256), so the index is always 0 < 4 (runtime-verified: f(A)/f(B)/f(C)
// all return 10, no panic). NON-VACUOUS: the bounds VC for `a[e as u8 as usize]`
// reports 1 proved / 0 failed.
//
// ✅ SOUNDNESS NOTE (P0 found 2026-07-06 while landing this reclassification;
// FIXED same day): the proof derivation used to carry the discriminant-set
// fact ACROSS the narrowing cast without mod-2^8 truncation and intersect it
// with the u8 type range ({0,256,512} ∩ [0,255] = {0}) — the sibling with
// discriminant 260 (truncates to 4 → OOB on len-4) FALSE-PROVED and panicked
// at runtime. The model now renders the tags' image under the cast
// (`truncate_nonneg_tag_as_int`: {0,256,512} mod 256 = {0} here), so THIS
// fixture proves via the SOUND derivation and the sibling refutes:
// mutant/enumdf_castnarrow_oob.rs.
#[repr(u16)]
pub enum E {
    A = 0,
    B = 256,
    C = 512,
}

pub fn f(e: E) -> u8 {
    let a = [10u8, 20, 30, 40];
    a[e as u8 as usize]
}
