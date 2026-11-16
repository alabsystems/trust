//@ trust-ladder: verifies
//! THE SEAL WITHOUT THE WHOLE-PROGRAM BIT. `w3` records that an EXPORTED trait
//! in an rlib is `Open`, and this is its complement: `dyn_trait_sealedness` has
//! three independently-sound routes and only one of them is the final artifact.
//! `T` is not exported, so no downstream crate can name it to implement it, and
//! the impl set is closed in an rlib exactly as it is in an executable.
//!
//! This matters more than it looks: it is the only row where a LIBRARY discharges
//! an open dispatch with no attribute at all. `h5` — the same program with `pub`
//! on the trait — must stay red, and that pair is the whole boundary.
trait T {
    fn m(&self) -> u32;
}
struct A;
impl T for A {
    fn m(&self) -> u32 {
        7
    }
}
fn f(x: &dyn T) -> u32 {
    x.m()
}
pub fn g() -> u32 {
    f(&A)
}
