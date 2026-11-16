#![crate_name = "census_merged"]

mod m {
    clean {
        def cleanWsum (a : UInt64) (b : UInt64) : UInt64 := a + b
    }
}

#[inline(never)]
pub fn calls_clean(x: u64) -> u64 {
    m::cleanWsum(x, 1)
}

#[inline(never)]
pub fn rust_only(x: u64) -> u64 {
    x ^ 0x55
}

#[inline(never)]
pub fn rust_also(x: u64) -> u64 {
    x | 0x100
}
