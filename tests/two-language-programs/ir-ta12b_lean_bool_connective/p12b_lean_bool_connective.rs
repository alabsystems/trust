// FEATURE lean.bool_connective — Bool not / && / ||.
// EXPECT: 3
pub mod m {
    clean {
        def neg (b : Bool) : Bool := not b
        def conj (a : Bool) (b : Bool) : Bool := a && b
        def disj (a : Bool) (b : Bool) : Bool := a || b
    }
}
pub fn program() -> u64 {
    (m::neg(false) as u64) + 2 * (m::conj(true, true) as u64) + 4 * (m::disj(false, false) as u64)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
