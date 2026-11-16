//@ needs-trust-verify
//@ edition: 2021
// `aux-crate`, not `aux-build`: the aux's crate name is `hashbrown`, so a bare
// `-L` search leaves `extern crate hashbrown` ambiguous against the sysroot's
// own `hashbrown` (E0464 "multiple candidates") before any Trust check runs.
//@ aux-crate: hashbrown=hashbrown.rs
//@ revisions: dep_call_beside_std_map dep_value_in_std_map dep_call_alone namesake_loaded_std_map_ok
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[dep_call_beside_std_map] check-fail
//@[dep_value_in_std_map] check-fail
//@[dep_call_alone] check-fail
//@[namesake_loaded_std_map_ok] check-pass
//! W4 HASHMAP (2026-09-25; redo) — a DEPENDENCY NAMED `hashbrown` gets none of the
//! sysroot `hashbrown`'s vanilla-class credit.
//!
//! EVERY check-fail REVISION MUST STAY REFUSED. Fix the compiler, never this file.
//!
//! The policy-B vanilla class now credits `hashbrown` — the crate behind
//! `std::collections::HashMap` — and it is also an ordinary crates.io name
//! (reached through `indexmap`, `dashmap`, ...). A credit keyed on the crate
//! NAME would hand a verify-off dependency called `hashbrown` the sysroot's
//! standing: X1 measured exactly that for the destructor credit (a namesake
//! `raw::RawTable` whose `Drop` panics, dropped beside a real `HashMap`: rc=0,
//! exit 101 — `xcrate_drop_glue_sysroot_name_shadowed_not_credited.rs`). This
//! credit is keyed on STRUCTURE (`trust_mir_extract::
//! def_is_in_std_hash_table_crate`: the crate that defines the ADT std's
//! `HashMap`/`HashSet` field is declared as, resident in the compiler's own
//! library directory), so the namesake is never that crate.
//!
//! The aux (`auxiliary/hashbrown.rs`, crate name `hashbrown`, built the way
//! `targo` builds every dependency: verify-off, MIR encoded) defines
//! `hashbrown::map::HashMap` — the sysroot type's own path — whose `insert`
//! PANICS on key 7, and `hashbrown::raw::RawTable`, whose `Drop` panics on 7.
//!
//!   * `dep_call_beside_std_map` — the namesake's `insert` called in the same
//!     function as a genuine `std::collections::HashMap` insert and a tolerated
//!     `println!`: the sysroot `hashbrown` callees in that function ARE vanilla
//!     now, and the namesake must not borrow their verdict.
//!   * `dep_value_in_std_map` — the namesake's `RawTable` as the VALUE type of a
//!     genuine std `HashMap`, dropped with it: the map's glue runs the namesake's
//!     panicking `Drop`, so the std type over it is not foundational.
//!   * `dep_call_alone` — CONTROL: the namesake call with no std map anywhere.
//!   * `namesake_loaded_std_map_ok` — check-pass, the POSITIVE control: the
//!     namesake is loaded but unused, and a genuine std `HashMap` beside a
//!     tolerated `println!` still verifies. The credit follows the sysroot
//!     crate's IDENTITY, so a crates.io `hashbrown` elsewhere in the graph costs
//!     it nothing (unlike a name-keyed credit, which would have to be withdrawn
//!     from every program that merely depends on `indexmap`).
//!
//! Measured on the baseline (main, stage-1 `7c7e46061`): all four refused (the
//! positive control by the old `HashMap` mask).
extern crate hashbrown;

#[cfg(dep_call_beside_std_map)]
pub fn dep_call_beside_std_map(k: u64, x: u64) -> u64 {
    //[dep_call_beside_std_map]~^ ERROR Trust strict verification failed for `hashbrown_namesake_dep_not_vanilla::dep_call_beside_std_map`
    println!("inserting {k}");
    let mut real: std::collections::HashMap<u64, u64> = std::collections::HashMap::new();
    real.insert(k, x);
    let mut fake = hashbrown::map::HashMap { k: 0, v: 0 };
    fake.insert(k, x).unwrap_or(0)
}

#[cfg(dep_value_in_std_map)]
pub fn dep_value_in_std_map(k: u64, x: u32) -> usize {
    //[dep_value_in_std_map]~^ ERROR verification failed for `hashbrown_namesake_dep_not_vanilla::dep_value_in_std_map`
    let mut real: std::collections::HashMap<u64, hashbrown::raw::RawTable> =
        std::collections::HashMap::new();
    real.insert(k, hashbrown::raw::RawTable(x));
    let n = real.len();
    drop(real);
    n
}

#[cfg(dep_call_alone)]
pub fn dep_call_alone(k: u64, x: u64) -> u64 {
    //[dep_call_alone]~^ ERROR Trust strict verification failed for `hashbrown_namesake_dep_not_vanilla::dep_call_alone`
    let mut fake = hashbrown::map::HashMap { k: 0, v: 0 };
    fake.insert(k, x).unwrap_or(0)
}

#[cfg(namesake_loaded_std_map_ok)]
pub fn namesake_loaded_std_map_ok(key: &str, known: &std::collections::HashMap<String, u32>) -> u32 {
    println!("looking up {key}");
    known.get(key).copied().unwrap_or(0)
}
