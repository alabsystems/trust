// FEATURE lean.select — `if`-select, tier structural.
// EXPECT: 44
pub mod m {
    clean {
        def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b
    }
}
pub fn program() -> u64 {
    m::min2(100, 41) + m::min2(3, 8)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
