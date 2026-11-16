//@ revisions: spawning quiet
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: not a spawn claim
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census (W11 round 3): types that can run no local drop glue are not
//! drop sites, however deep or wide they are, and however they are handed on.
//! The round-2 walk pruned only OWNED drops (`needs_drop`); a SHARED or
//! reachable walk followed every reference and type argument and charged each
//! instantiation to its 4096-pair budget, so handing `&Nested<u32>` (polymorphic
//! recursion through `&'static Nested<(T, T)>`) or a reference to a 65 x 65
//! drop-free type graph to ANY external fn exhausted it: `is_some`, `ptr_eq`,
//! `size_of_val`, `mem::swap`, `black_box`, `Option::filter`, a `PhantomData`
//! fn-pointer output, even a real drop of `Box<Nested<u32>>`, were refused as
//! "could not be enumerated", and their callers as reaching unmeasured drop
//! glue (review probes polyr2.rs / wide2.rs / n4.rs, 2026-09-29).
//!
//! Since P2 (design 2026-09-29-spawn-census-by-construction) the census has no
//! budget: it decomposes each drop glue structurally, per type, and a
//! reference is not followed by drop glue. Every shape below is exact:
//! `drops_wide_quiet` reaches a quiet `Drop` impl (no row) and, in `spawning`,
//! `drops_wide_spawner` the spawning one (an S3 row; its witness names the
//! 4225-type glue cut to 120 characters). No row here may be anything but a
//! spawn claim. What the census cannot enumerate is a polymorphic recursion
//! (`polymorphic_recursion_is_unknown.rs`).

#![allow(dead_code)]

use std::marker::PhantomData;

#[cfg(spawning)]
fn launch() { //[spawning]~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

#[cfg(quiet)]
fn launch() {}

// A spawning `Drop` impl elsewhere in the crate: pruning is per type, not per
// crate.
pub struct Spawner;
impl Drop for Spawner {
    fn drop(&mut self) { //[spawning]~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch()
    }
}

pub struct QuietDrop;
impl Drop for QuietDrop {
    fn drop(&mut self) {}
}

pub struct Nested<T: 'static> {
    v: T,
    inner: Option<&'static Nested<(T, T)>>,
}

pub fn is_some(n: &Nested<u32>) -> bool { n.inner.is_some() }
pub fn ptr_eq(a: &Nested<u32>, b: &Nested<u32>) -> bool { std::ptr::eq(a, b) }
pub fn caller(n: &Nested<u32>) -> bool { is_some(n) }
pub fn caller2(n: &Nested<u32>) -> bool { caller(n) }
pub fn drop_box_nested(_b: Box<Nested<u32>>) {}

pub struct PF<T> {
    v: T,
    p: PhantomData<fn() -> PF<(T, T)>>,
}
pub fn pf_drop(p: PF<String>) { let _ = std::hint::black_box(p); }

pub struct U<T>(u8, PhantomData<T>);
pub struct GS<T>(String, PhantomData<T>);
pub struct GQ<T>(QuietDrop, PhantomData<T>);
pub struct GSp<T>(Spawner, PhantomData<T>);

macro_rules! row {
    ($g:ident; $a:literal; ($($b:literal)*)) => { ($($g<[u8; $a * 100 + $b]>,)*) };
}
macro_rules! grid {
    ($g:ident; $($a:literal)*; $bs:tt) => { ($(row!($g; $a; $bs),)*) };
}
macro_rules! wide {
    ($g:ident) => {
        grid!($g;
            0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30
            31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58
            59 60 61 62 63 64;
            (0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30
             31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58
             59 60 61 62 63 64))
    };
}

pub type WideU = wide!(U);
pub type WideS = wide!(GS);
pub type WideQ = wide!(GQ);
pub type WideSp = wide!(GSp);

pub fn by_ref_eq(a: &WideU, b: &WideU) -> bool { std::ptr::eq(a, b) }
pub fn size_val(a: &WideU) -> usize { std::mem::size_of_val(a) }
pub fn swap(a: &mut WideU, b: &mut WideU) { std::mem::swap(a, b) }
pub fn hint(a: &WideU) -> &WideU { std::hint::black_box(a) }
pub fn opt(a: &WideU) -> Option<&WideU> { Some(a).filter(|_| true) }
pub fn wide_caller(a: &WideU, b: &WideU) -> bool { by_ref_eq(a, b) }

pub fn drops_wide_strings(_w: Box<WideS>) {}
pub fn drops_wide_quiet(_w: Box<WideQ>) {}

#[cfg(spawning)]
pub fn drops_wide_spawner(_w: Box<WideSp>) {} //[spawning]~ NOTE value dropped here has drop glue that may run a local Drop impl that reaches a std thread spawn through calls and drops; drop effect is unmodeled
