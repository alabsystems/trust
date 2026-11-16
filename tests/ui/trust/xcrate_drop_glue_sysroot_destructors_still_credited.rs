//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! **WAS RED 2026-09-26 on `btree`; FIXED the same day.** The cause was NOT this
//! fixture's subject. `BTreeMap`'s `Drop` is `drop(self.into_iter())`
//! (library/alloc/src/collections/btree/map.rs:206), so the map's own glue never
//! appears — only `alloc::collections::btree::map::IntoIter`'s does, and the audited
//! total-drop container list credited the map but not that iterator, which made the
//! map's entry unreachable. Measured: `BTreeMap::new()` + `drop` verified, ONE `insert`
//! did not. Fixed in `crates/trust-mir-extract/src/convert.rs` with a path-exact
//! delegated-drop arm; negative control
//! `btree_intoiter_drop_credit_declines_panicking_element.rs`; write-up
//! `docs/issues/2026-09-26-btree-intoiter-drop-credit-CLOSED.md`.
//!
//! Two things the red taught, recorded because both cost time: the
//! "direct typed trust_mc CHC/PDR input required ..." line it appeared to fail on is
//! printed unconditionally on green builds too and diagnoses nothing; and the sysroot
//! residency arm was never involved — `map` stayed green throughout, which is the
//! fixture's own stated canary.
//!
//! X1 (2026-09-23) — THE POSITIVE CONTROL for
//! `xcrate_drop_glue_dep_destructor_not_credited.rs`.
//!
//! The X1 fix narrows foreign-destructor admission to the compiler's own
//! sysroot. It must not take away any sysroot credit, and the one that is easy
//! to lose is the one whose crate is NOT named `core`/`alloc`/`std`:
//! `HashMap`'s glue runs `hashbrown::raw::RawTable`'s destructor, and
//! `hashbrown` is a sysroot-internal crate. It stays admitted because its
//! artifacts are loaded from the compiler's own target library directory
//! (`trust_mir_extract::def_is_in_sysroot_resident_crate`), not because of its
//! name. If this file turns red on `map`, the residency arm is not matching the
//! way this toolchain lays out its sysroot — fix the arm, do not delete the row.
//!
//! Every function drops through `core::mem::drop::<T>`, which is the exact
//! shape X1 leaked through (a drop INSIDE a bundled sysroot body), so each row
//! exercises the admission this fix changed. Measured BEFORE the fix on stage-1
//! `trustc` at `fa6661d85e`: all six build clean, with admitted destructor sets
//! `{alloc::vec::Vec, alloc::raw_vec::RawVec}` (vec, string),
//! `{alloc::boxed::Box}`, `{alloc::rc::Rc, alloc::rc::Weak}`,
//! `{hashbrown::raw::RawTable}` and the btree set.

pub fn vec(x: u8) -> u8 {
    let m = vec![x];
    drop(m);
    x
}

pub fn string(x: u8) -> u8 {
    let m = String::from("a");
    drop(m);
    x
}

pub fn boxed(x: u8) -> u8 {
    let m = Box::new(x);
    drop(m);
    x
}

pub fn rc(x: u8) -> u8 {
    let m = std::rc::Rc::new(x);
    drop(m);
    x
}

pub fn map(x: u8) -> u8 {
    let mut m: std::collections::HashMap<u8, u8> = std::collections::HashMap::new();
    m.insert(x, x);
    drop(m);
    x
}

pub fn btree(x: u8) -> u8 {
    let mut m = std::collections::BTreeMap::new();
    m.insert(x, x);
    drop(m);
    x
}
