//@ revisions: spawning quiet
//@ aux-build:const_generic_dep.rs
//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=advisory --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[quiet] forbid-output:UnmodeledThreadSpawnEffect
//! Spawn census: a const-generic body walked at a concrete instance. Its MIR
//! spells the body's own `N`, which the instance's typing environment (the
//! empty one) does not hold, so every question the census asks of a type of
//! that body is asked of the instance's type: the drop of `[Field; N]` in
//! `node::<2>` is a drop of `[Field; 2]`. Asked of `[Field; N]` in the empty
//! environment, `needs_drop` was a compiler panic ("cannot find `N/#0` in
//! param-env"): the ICE the 0.11.0 consumer check met in ty, on
//! `[SmtValue; N]`, which ay-chc spells only in `fn dt<const N: usize>(ctor:
//! &str, fields: [SmtValue; N])`; `node` is that function. A local
//! const-generic body is walked the same way. The answer stays exact: in
//! `spawning`, the array drop in `drop_launchers::<2>` runs the dependency's
//! spawning `Drop` impl, a SPAWNS row at the call; in `quiet`, nothing is
//! refused, so no type was judged at its worst either.

#![allow(dead_code)]

extern crate const_generic_dep;

use const_generic_dep::{Field, drop_fields, node};

// ay-chc's `dt`, from a dependency: the array is dropped where `to_string`
// unwinds.
pub fn pair() -> Field {
    node("pair", [Field::Leaf(1), Field::Leaf(2)])
}

// Dropped on return.
pub fn drops_fields(fields: [Field; 3]) {
    drop_fields(fields)
}

// A local const-generic body at an instance.
pub struct QuietDrop;
impl Drop for QuietDrop {
    fn drop(&mut self) {}
}

fn drop_quiet<const N: usize>(_items: [QuietDrop; N]) {}

pub fn drops_quiet() {
    drop_quiet([QuietDrop, QuietDrop])
}

#[cfg(spawning)]
pub fn drops_launchers(l: [const_generic_dep::Launcher; 2]) { const_generic_dep::drop_launchers(l) } //[spawning]~ NOTE callee reaches a std thread spawn through calls and drops
