//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ forbid-output: value dropped here has drop glue
//@ forbid-output: not a spawn claim
//! Spawn census (W11 round 2): a type whose `Drop::drop` spawns, NAMED but never
//! dropped. The census used to treat every type in a call's generic arguments
//! as possibly dropped by the callee, so `size_of::<Spawner>()` was refused as
//! a drop site, and `size_of::<Nested<u32>>()` (polymorphic recursion through a
//! reference field) exhausted the walk and was refused as unmeasured. A call is
//! now a drop observation only for the operands it HANDS a callee that cannot
//! be seen to drop them, and a value reached only through a shared reference to
//! a `Freeze` type cannot be dropped by the callee. None of the bodies below
//! may carry a drop-glue row (the spawning `Drop::drop` itself still carries
//! its own wrapper row, which is why this test forbids the drop-glue messages
//! rather than every spawn row), nor any row that refuses without a claim
//! (ESCAPES, INDIRECT, UNKNOWN: "not a spawn claim"). Since P2 (design
//! 2026-09-29-spawn-census-by-construction) the census walks each callee's
//! instance, and none of them drops a `Spawner`.

#![allow(dead_code)]

fn launch() { //~ NOTE direct std thread spawn lacks an authenticated execution and race model
    let _handle = std::thread::spawn(|| {});
}

pub struct Spawner;

impl Drop for Spawner {
    fn drop(&mut self) { //~ NOTE local callee reaches a std thread spawn through calls and drops; caller effect is unmodeled
        launch();
    }
}

pub struct Nested<T: 'static> {
    v: T,
    inner: Option<&'static Nested<(T, T)>>,
}

pub fn names_type_only() -> usize { std::mem::size_of::<Spawner>() }

pub fn names_container_type() -> usize { std::mem::size_of::<Vec<Spawner>>() }

pub fn by_shared_ref(s: &Spawner) -> usize { std::mem::size_of_val(s) }

pub fn poly_size() -> usize { std::mem::size_of::<Nested<u32>>() }

pub fn poly_size_caller() -> usize { poly_size() + names_type_only() }
