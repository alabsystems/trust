// FEATURE lean.bool_cmp — Bool-returning comparison (`decide`).
// EXPECT: 3
pub mod m {
    clean {
        def lt (a : UInt64) (b : UInt64) : Bool := a < b
        def eqf (a : UInt64) (b : UInt64) : Bool := a == b
    }
}
pub fn program() -> u64 {
    (m::lt(3, 9) as u64) + 2 * (m::eqf(7, 7) as u64) + 4 * (m::lt(9, 3) as u64)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
