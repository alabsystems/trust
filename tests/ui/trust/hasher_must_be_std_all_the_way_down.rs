//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: panicking_hasher_dep.rs
//@ revisions: map_eq_user_build set_eq_user_build map_eq_bhd query_bhd insert_bhd
//@ revisions: hash_into_box map_eq_std query_std hash_into_std
//@ compile-flags: -Ztrust-verify=on -Ztrust-policy=certify --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[map_eq_user_build] check-fail
//@[set_eq_user_build] check-fail
//@[map_eq_bhd] check-fail
//@[query_bhd] check-fail
//@[insert_bhd] check-fail
//@[hash_into_box] check-fail
//@[map_eq_std] check-pass
//@[query_std] check-pass
//@[hash_into_std] check-pass
//! **A hasher is total only when it is std code all the way down (Trust, 2026-09-28).**
//!
//! The extractor's hash-family totality gates (`HashMap`/`HashSet` `==`, the query, collect
//! and extend gates, and `Hash::hash` of a primitive) either ignored the hasher `S` or
//! checked only its OUTER type's crate. `HashMap::eq` hashes every key through `S`, and
//! std implements `BuildHasher` for `BuildHasherDefault<H>` and `Hasher` for `Box<H>`, so
//! a user `H` runs inside a std-looking type. Without the fix, every revision below builds
//! `certify` rc=0 (measured). The third adversarial audit built certified artifacts of the
//! same shapes, and each panicked in the user hasher (exit 101). Every gate now asks
//! `hasher_ty_is_std_closed` (`crates/trust-mir-extract/src/convert.rs`).
//!
//! * The six negatives are DISCRIMINATING: if a gate credited the user hasher, `f` would
//!   verify and its annotation would go unmatched.
//! * `map_eq_std`, `query_std`, `hash_into_std`: POSITIVE, the std-hasher credit this
//!   must not take away.

extern crate panicking_hasher_dep;

#[allow(unused_imports)]
use panicking_hasher_dep::{PanicBuild, PanicHasher};
#[allow(unused_imports)]
use std::collections::{HashMap, HashSet};
#[allow(unused_imports)]
use std::hash::{BuildHasherDefault, DefaultHasher, Hash};

#[cfg(map_eq_user_build)]
pub fn f(a: &HashMap<u32, u32, PanicBuild>, b: &HashMap<u32, u32, PanicBuild>) -> bool {
    //[map_eq_user_build]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    a == b
}

#[cfg(set_eq_user_build)]
pub fn f(a: &HashSet<u32, PanicBuild>, b: &HashSet<u32, PanicBuild>) -> bool {
    //[set_eq_user_build]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    a == b
}

#[cfg(any(map_eq_bhd, query_bhd))]
pub type M = HashMap<u32, u32, BuildHasherDefault<PanicHasher>>;

#[cfg(map_eq_bhd)]
pub fn f(a: &M, b: &M) -> bool {
    //[map_eq_bhd]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    a == b
}

#[cfg(query_bhd)]
pub fn f(m: &M, k: u32) -> bool {
    //[query_bhd]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    m.contains_key(&k)
}

#[cfg(insert_bhd)]
pub fn f(s: &mut HashSet<u32, BuildHasherDefault<PanicHasher>>, k: u32) -> bool {
    //[insert_bhd]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    s.insert(k)
}

#[cfg(hash_into_box)]
pub fn f(x: u32, state: &mut Box<PanicHasher>) {
    //[hash_into_box]~^ ERROR Trust Level 0 safety verification incomplete for `hasher_must_be_std_all_the_way_down::f`
    x.hash(state)
}

#[cfg(map_eq_std)]
pub fn f(a: &HashMap<u32, u32>, b: &HashMap<u32, u32>) -> bool {
    a == b
}

#[cfg(query_std)]
pub fn f(m: &HashMap<u32, u32>, k: u32) -> bool {
    m.contains_key(&k)
}

#[cfg(hash_into_std)]
pub fn f(x: u32, state: &mut DefaultHasher) {
    x.hash(state)
}
