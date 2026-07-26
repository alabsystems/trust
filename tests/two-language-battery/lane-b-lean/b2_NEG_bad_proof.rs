//@ battery-lane: B-lean
//@ battery-expect: reject
//@ battery-flags: -Ztrust-verify=off --crate-type=lib
//! LANE B NEGATIVE CONTROL — the kernel must refuse a bogus proof term.
//!
//! `Nat.le 1 0` is FALSE, and `Nat.le.refl 0` proves `Nat.le 0 0`, not it.
//! If this file compiles, the island lane is decorative: it would mean the
//! kernel is not actually typechecking the terms it is handed, and every
//! Lane B and Lane C pass in this battery would be worthless.
//!
//! This is the single most important file in the battery.

clean {
    theorem bogus : Nat.le 1 0 := Nat.le.refl 0
}

pub fn unreachable_if_kernel_works(x: u64) -> u64 {
    x
}
