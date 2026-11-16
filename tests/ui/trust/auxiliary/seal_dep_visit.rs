//@ edition: 2021
//@ compile-flags: --crate-type=rlib -O -Ztrust-verify=off -A warnings
//@ no-prefer-dynamic
//! A dependency of `clean_island_seal_third.rs` and `_third_holds.rs` (crate
//! B): traits whose bodies are chosen by the type they run at, and a driver.
//! Safe to call, and sound.

/// Settles two values; by default, by swapping them (a PROVIDED method: it
/// runs for a type whose impl does not override it).
pub trait Settle: Sized {
    fn settle(a: &mut Self, b: &mut Self) {
        std::mem::swap(a, b)
    }
}

/// A pair, and a visitor trait with an impl for it that turns the pair round.
pub struct Pair<T> {
    pub a: T,
    pub b: T,
}
pub trait Visit {
    fn visit(&mut self);
}
impl<T> Visit for Pair<T> {
    fn visit(&mut self) {
        std::mem::swap(&mut self.a, &mut self.b)
    }
}

/// Runs whatever visitor it is handed: it did not choose the impl. (Not
/// inlined, so that its caller's body names it.)
#[inline(never)]
pub fn drive<V: Visit>(v: &mut V) {
    v.visit()
}
