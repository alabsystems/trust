//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_standing.rs` and `_standing_holds.rs`:
//! at `seal_dep_measure::util::keep`, a fn that keeps what it is handed
//! where it is (it only measures). Safe, and sound.
#![forbid(unsafe_code)]

pub mod util {
    pub fn keep<T>(a: &mut T, b: &mut T) -> usize {
        std::mem::size_of_val(a) + std::mem::size_of_val(b)
    }
}
