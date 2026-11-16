// FEATURE lean.let — `let` bodies (kernel zeta before recognition).
// EXPECT: 22
pub mod m {
    clean {
        def sq_let (x : UInt64) : UInt64 := let y := x + 1; y * y
        def nested_let (x : UInt64) : UInt64 := let y := x; let z := y + 1; z
    }
}
pub fn program() -> u64 {
    m::sq_let(3) + m::nested_let(5)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
