//! Part A dependency crate: one Rust `pub fn` with a contract, one `clean { }`
//! island exporting a gate-tier `UInt64` def. Built as an rlib; also emitted as
//! its own trust-ir module so the importer can be linked against it by symbol.
#![crate_type = "rlib"]

pub mod m {
    clean {
        def dep_mix (x : UInt64) (y : UInt64) : UInt64 := x * 3 + y
    }
}

#[inline(never)]
pub fn dep_clamp(x: u64, hi: u64) -> u64
    requires hi >= 1
    ensures result <= hi
{
    if x > hi { hi } else { x }
}
