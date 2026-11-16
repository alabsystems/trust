//@ needs-trust-verify
//@ edition: 2021
//@ no-prefer-dynamic
//@ aux-crate:b=shared_name_bomb_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib --crate-name shared_name_bomb_dep -C metadata=self
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Review round 77 (2026-10-08). The drop-credit sets are keyed by rendered path,
//! which spells the crate NAME. This crate shares its name with its dependency `b`,
//! so its own no-`Drop` `S` and the dependency's panicking `S` render identically.
//! The first used to credit the second: `f` was PROVED under the default policy and
//! `certify`, and `f(S(vec![]), L(b::S(7)))` panicked. A type whose crate name is
//! shared in the graph now gets no credit.
extern crate b;

pub struct S(pub Vec<u8>);
pub struct L(pub b::S);

pub fn f(x: S, y: L) {
    //~^ ERROR Trust strict verification failed for `shared_name_bomb_dep::f`
    let _p = x;
    let _q = y;
}
