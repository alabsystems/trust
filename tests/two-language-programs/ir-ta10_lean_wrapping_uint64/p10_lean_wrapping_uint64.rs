// FEATURE lean.wrapping_uint64 — tier gate: wrapping UInt64 +,-,* trees. Rust -> Lean call.
// EXPECT: 92
pub mod m {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
        def addmul (a : UInt64) (b : UInt64) : UInt64 := a * b + a
        def wsub (a : UInt64) (b : UInt64) : UInt64 := a - b
    }
}
pub fn program() -> u64 {
    // wsub(1,2) wraps to u64::MAX; wsum(MAX,3) wraps back to 2.
    m::wsum(40, 2) + m::addmul(6, 7) + m::wsum(m::wsub(1, 2), 3)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
