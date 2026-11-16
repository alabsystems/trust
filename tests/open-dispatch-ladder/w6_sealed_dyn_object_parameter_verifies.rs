//@ trust-ladder: verifies
//@ trust-ladder-crate-type: bin
//! THE C-SEALED ROW. `f` TAKES a trait object, which is the shape ordinary Rust
//! is written in and the one neither existing dyn certificate could serve:
//!
//!   * C-UNIVERSAL wants `#[trust::panic_free]` on `T::m`, and this program has
//!     no attribute anywhere (that pair is `u1`/`r1`);
//!   * C-FLOW enumerates the `Unsize` coercions inside the bundle, and `f`'s own
//!     root has a `dyn`-bearing PARAMETER — which poisons the trait outright, so
//!     no coercion set bounds it. `main` verifies through C-FLOW; `f` did not,
//!     and one refusing root fails the build.
//!
//! The seal is what closes it: `T` is local, has no blanket impl, and this is a
//! whole-program artifact, so `dyn_trait_sealedness` is `Sealed` and the impl
//! set is exactly `{A}` — whose `m` is independently verified. That is rung 2's
//! certificate verbatim, and `w4` is the SAME program with a generic parameter
//! instead of a trait object, green since 2026-09-19. Two call shapes that this
//! module's own header says "range over exactly the same impls" must not
//! disagree.
//!
//! Its rails are `w7` (a sibling impl panics) and `h5` (an exported trait in an
//! rlib, which no seal route reaches).
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
fn main() {
    let a = A;
    let _ = f(&a);
}
