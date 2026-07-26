#![crate_type = "lib"]
// COMPLETENESS twin of mutant/enumdf_castnarrow_oob.rs: every discriminant of
// this `#[repr(u16)]` enum FITS in u8 ({0, 1, 5}), so the mod-2^8 fold the
// narrowing-cast fix applies to the tag-set fact is the IDENTITY — the cast
// result is still bounded by `∈ {0, 1, 5}` and the len-6 index proves
// (max index 5 < 6). NON-VACUOUS: the bounds VC reports 1 proved / 0 failed.
// Pins that the P0 fix (fold tags through the cast, never carry them raw) did
// not fail-closed the fitting-discriminant case; the same enum on a len-4
// array correctly refutes (5 >= 4 — checked at fix time, not a fixture: it
// duplicates mutant/enumdf_castnarrow_oob.rs's lane).
#[repr(u16)]
pub enum E {
    A = 0,
    B = 1,
    C = 5,
}

pub fn f(e: E) -> u8 {
    let a = [10u8, 20, 30, 40, 50, 60];
    a[(e as u8) as usize]
}
