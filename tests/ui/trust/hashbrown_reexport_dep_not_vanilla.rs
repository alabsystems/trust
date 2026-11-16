//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: hashbrown_reexport.rs
//@ revisions: extend index get_many collect closure_index std_map_beside_ok
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[extend] check-fail
//@[index] check-fail
//@[get_many] check-fail
//@[collect] check-fail
//@[closure_index] check-fail
//@[std_map_beside_ok] check-pass
//! W4 HASHMAP (2026-09-25, redo) — a hashbrown VALUE this crate obtained from a
//! dependency gets none of std's hashbrown credit at this crate's call sites.
//!
//! EVERY check-fail REVISION MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! The policy-B vanilla class credits `hashbrown` — the crate behind
//! `std::collections::HashMap`, identified structurally — but only where STD put
//! the value: as a std/hashbrown DECLARED field (`base: hashbrown::HashMap<..>`),
//! or at a call site inside a bundled std body. A dependency that names the
//! sysroot `hashbrown` under `rustc_private` (`auxiliary/hashbrown_reexport.rs`)
//! can hand this crate a hashbrown table without this crate naming hashbrown, so
//! the loader records no direct load and the credit is NOT withdrawn. Here,
//! hashbrown's OWN API is reachable at this crate's values with no std code in
//! between — its `Extend` (capacity overflow), its `Index` ("invalid key"), its
//! `get_many_mut` (duplicate keys), its `FromIterator`.
//!
//!   * `extend` — `m.extend(repeat(..).take(n))` on the dependency's table. The
//!     first attempt (`w4-hashmap`, stage-1 `f828ea3d9`), which credited hashbrown
//!     at every position, built it rc=0 and a driver passing `n = usize::MAX`
//!     panicked "Hash table capacity overflow" (exit 101). A FALSE ACCEPT, closed.
//!   * `index`, `get_many`, `collect`, `closure_index` — the other hashbrown entry
//!     points (the closure is this crate's own body, verified as its own root).
//!   * `std_map_beside_ok` — check-pass, the POSITIVE control: with the
//!     dependency loaded, a genuine std `HashMap` beside a tolerated `println!`
//!     still verifies.
//!
//! Measured on the baseline (main, stage-1 `7c7e46061`): every check-fail
//! revision refused (and the positive control refused by the old `HashMap`
//! mask).
//!
//! `collect`'s annotation names the refusal, not the gate (2026-10-08,
//! std-absent-callee): with the sysroot panic census on, the std adapters around the
//! call (`repeat`, `take`) are derived panic-free, and the function is refused by the
//! closure-driving-consumer gate ("Trust full verification failed for ... a
//! closure-driving consumer call runs code outside the verified closure and the
//! std/core/alloc TCB") instead of the strict-verification summary. It stays refused.
#![cfg_attr(any(extend, index, get_many, collect), feature(rustc_private))]
#![allow(deprecated)]
extern crate hashbrown_reexport as dep;

#[cfg(extend)]
pub fn extend(m: &mut dep::Map, n: usize) {
    //[extend]~^ ERROR Trust strict verification failed for `hashbrown_reexport_dep_not_vanilla::extend`
    m.extend(std::iter::repeat((1u32, 1u32)).take(n));
}

#[cfg(index)]
pub fn index(m: &dep::Map, k: u32) -> u32 {
    //[index]~^ ERROR Trust strict verification failed for `hashbrown_reexport_dep_not_vanilla::index`
    m[&k]
}

#[cfg(get_many)]
pub fn get_many(m: &mut dep::Map, a: u32, b: u32) {
    //[get_many]~^ ERROR Trust strict verification failed for `hashbrown_reexport_dep_not_vanilla::get_many`
    if let [Some(x), Some(y)] = m.get_many_mut([&a, &b]) {
        std::mem::swap(x, y);
    }
}

#[cfg(collect)]
pub fn collect(n: usize) -> dep::Map {
    //[collect]~^ ERROR verification failed for `hashbrown_reexport_dep_not_vanilla::collect`
    std::iter::repeat((1u32, 1u32)).take(n).collect()
}

#[cfg(closure_index)]
pub fn closure_index(k: u32) -> u32 {
    //[closure_index]~^ ERROR Trust strict verification failed for `hashbrown_reexport_dep_not_vanilla::closure_index`
    dep::with_map(|m| m[&k])
}

#[cfg(std_map_beside_ok)]
pub fn std_map_beside_ok(key: &str, known: &std::collections::HashMap<String, u32>) -> u32 {
    let _ = dep::make;
    println!("looking up {key}");
    known.get(key).copied().unwrap_or(0)
}
