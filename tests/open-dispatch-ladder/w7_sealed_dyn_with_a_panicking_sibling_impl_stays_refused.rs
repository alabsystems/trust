//@ trust-ladder: refuses
//@ trust-ladder-crate-type: bin
//! THE C-SEALED RAIL, and the one that separates it from C-FLOW. `B` is never
//! constructed, so the value-flow enumeration inside `main`'s bundle is `{A}`
//! and C-FLOW discharges `main` — correctly, on a different argument.
//!
//! `f` is a separate root whose `dyn` parameter poisons that enumeration, so it
//! can only be reached by C-SEALED, which quantifies over the IMPL SET. `B::m`
//! is in that set and panics, so the certificate declines and `f` keeps its
//! obligation. A green here would mean C-SEALED had quietly inherited C-FLOW's
//! reachability argument without C-FLOW's premise — the exact confusion `w2`
//! pins for the generic rung.
trait T {
    fn m(&self) -> u32;
}
struct A;
impl T for A {
    fn m(&self) -> u32 {
        7
    }
}
struct B;
impl T for B {
    fn m(&self) -> u32 {
        panic!("boom")
    }
}
fn f(x: &dyn T) -> u32 {
    x.m()
}
fn main() {
    let a = A;
    let _ = f(&a);
}
