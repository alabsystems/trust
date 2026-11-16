// FEATURE island_mutant — WS8.8 MUTATION CONTROL, not a feature probe: ir-ta10's p10 with ONE island
// line edited (`addmul`'s trailing `+ a` is `+ b`); the Rust side is byte-identical. The judge requires
// the native value to move (92 -> 93), the mutant's own interpreter-vs-native differential to hold, and
// BOTH cross differentials (mutant module vs original native, original module vs mutant native) to fail.
// EXPECT: 93
pub mod m {
    clean {
        def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b
        def addmul (a : UInt64) (b : UInt64) : UInt64 := a * b + b
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
