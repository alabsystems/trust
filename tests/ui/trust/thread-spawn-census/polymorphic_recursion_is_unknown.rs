//@ revisions: widened bounded
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: through calls and drops
//@[bounded] forbid-output:`UnmodeledThreadSpawnEffect`:
//! Spawn census (design 2026-09-29-spawn-census-by-construction §5.3, §13):
//! the census has no budget. It walks every instance a root reaches, and the
//! one limit is `recursion_limit`: an instance nested deeper than that is an
//! UNKNOWN sink ("not enumerated (no spawn was found)"), never a spawn claim.
//!
//! * `widened`: polymorphic recursion (`poly::<(T,)>` from `poly::<T>`) makes
//!   the instance set infinite, so `poly` and `root` are UNKNOWN. This replaces
//!   `drop_glue_unmeasured_is_not_a_spawn.rs`, whose UNKNOWN rows came from a
//!   drop-glue walk that ran out of budget.
//! * Both revisions: what that budget used to refuse is exact now and quiet,
//!   because nothing here spawns. `drops_wide` drops a value whose glue spans
//!   65 x 65 instantiations through an associated-type projection;
//!   `poly_ref_size` and `poly_box_size` only take the size of a
//!   polymorphically recursive type; `drops_poly_ref` drops one through
//!   `&'static`, whose glue is finite (references are not followed).

#![allow(dead_code)]

pub fn poly<T>(n: u32, t: T) { //[widened]~ NOTE not enumerated (no spawn was found)
    #[cfg(widened)]
    if n > 0 {
        poly(n - 1, (t,));
        return;
    }
    drop(t);
}

pub fn root() { //[widened]~ NOTE not enumerated (no spawn was found)
    poly(3, 0u8)
}

pub trait Proj {
    type Out;
}
impl<const N: usize> Proj for [u8; N] {
    type Out = u8;
}

pub struct G<T: Proj>(String, std::marker::PhantomData<T>, T::Out);

macro_rules! row {
    ($a:literal; ($($b:literal)*)) => { ($(G<[u8; $a * 100 + $b]>,)*) };
}
macro_rules! grid {
    ($($a:literal)*; $bs:tt) => { ($(row!($a; $bs),)*) };
}

pub type Wide = grid!(
    0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
    33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62
    63 64;
    (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
     33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62
     63 64)
);

pub fn drops_wide(_w: Box<Wide>) {}

pub fn wide_caller(w: Box<Wide>) {
    drops_wide(w)
}

pub struct PolyRef<T: 'static> {
    v: T,
    next: Option<&'static PolyRef<(T, T)>>,
}
pub struct PolyBox<T> {
    v: T,
    next: Option<Box<PolyBox<(T, T)>>>,
}
pub struct QuietDrop(u8);
impl Drop for QuietDrop {
    fn drop(&mut self) {}
}

pub fn drops_poly_ref(_n: PolyRef<QuietDrop>) {}

pub fn poly_ref_size(n: &PolyRef<QuietDrop>) -> usize {
    std::mem::size_of_val(n)
}

pub fn poly_box_size(n: &PolyBox<QuietDrop>) -> usize {
    std::mem::size_of_val(n)
}
