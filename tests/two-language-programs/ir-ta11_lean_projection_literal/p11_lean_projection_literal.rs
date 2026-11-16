// FEATURE lean.projection_literal — parameter projection and an in-range literal.
// EXPECT: 309
pub mod m {
    clean {
        def snd (a : UInt64) (b : UInt64) : UInt64 := b
        def k32 (a : UInt32) : UInt32 := 300
    }
}
pub fn program() -> u64 {
    m::snd(1, 9) + m::k32(0) as u64
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
