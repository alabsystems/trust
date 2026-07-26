#![crate_type = "lib"]
// MUTANT (P0 enumdisc-narrowing-cast false proof, 2026-07-06): a `#[repr(u16)]`
// enum whose discriminants do NOT all fit in u8, indexed through a NARROWING
// `e as u8` cast into a length-4 array. `E::B` truncates 260 as u8 == 4 → OOB
// (runtime panic, "the len is 4 but the index is 4"). Before the fix the
// discriminant-set fact {0, 260, 512} was carried across the narrowing cast
// UN-MOD'd and intersected with the u8 type range [0, 255], collapsing to {0}
// — a vacuous premise that FALSE-PROVED this guaranteed panic (rc=0,
// "1 proved"). The sound model renders the tags' image under the cast
// ({0, 260, 512} mod 256 = {0, 4}), which keeps index 4 reachable, so this
// MUST refute (exit 1). Accidentally-safe sibling (all tags ≡ 0 mod 256):
// proved/enumdf_u16_castnarrow.rs; fitting-tag sibling (mod is identity):
// proved/enumdf_castnarrow_fits.rs.
#[repr(u16)]
pub enum E {
    A = 0,
    B = 260,
    C = 512,
}

pub fn f(e: E) -> u8 {
    let a = [10u8, 20, 30, 40];
    a[(e as u8) as usize]
}
