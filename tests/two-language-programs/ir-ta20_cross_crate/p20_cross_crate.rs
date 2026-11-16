// FEATURE two_lang.cross_crate — calls into `dep`: its Rust fn AND its Clean def.
// EXPECT: 84
extern crate dep;
pub fn program() -> u64 {
    dep::m::dep_mix(10, 4) + dep::dep_clamp(99, 50)
}

#[cfg(not(parta_lib))]
fn main() {
    println!("{}", program());
}
