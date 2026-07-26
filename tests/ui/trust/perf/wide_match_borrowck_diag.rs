//! Trust: diagnostic-identity regression for the borrowck
//! `is_local_ever_initialized` hybrid scan.
//!
//! `x` has more than LINEAR_SCAN_CAP (16) initialization sites, so the
//! mutability check for the SECOND assignment in the offending arm takes the
//! sparse-state path (few dominating inits at that point, large init list).
//! The E0384 span must still point at the SAME-ARM first assignment — both
//! the init list and the dataflow set iterate ascending `InitIndex`, so the
//! reported `InitIndex` is identical to the original linear scan's.
pub fn f(n: u32) -> u32 {
    let x: u32;
    match n {
        0 => x = 0,
        1 => x = 1,
        2 => x = 2,
        3 => x = 3,
        4 => x = 4,
        5 => x = 5,
        6 => x = 6,
        7 => x = 7,
        8 => x = 8,
        9 => x = 9,
        10 => x = 10,
        11 => x = 11,
        12 => x = 12,
        13 => x = 13,
        14 => x = 14,
        15 => x = 15,
        16 => x = 16,
        17 => {
            // The blessed .stderr asserts the "first assignment" label lands
            // HERE (same-arm), proving the sparse-state path returns the same
            // InitIndex as the linear scan.
            x = 17;
            x = 18; //~ ERROR cannot assign twice to immutable variable `x`
        }
        _ => x = 99,
    }
    x
}

fn main() {}
