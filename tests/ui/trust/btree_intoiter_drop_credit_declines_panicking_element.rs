//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: WARN

//! **NEGATIVE CONTROL for the `btree::map::IntoIter` drop credit** (2026-09-26,
//! `crates/trust-mir-extract/src/convert.rs`, `is_audited_total_drop_std_container`).
//!
//! WHAT THE CREDIT IS. `BTreeMap`'s own `Drop` is, verbatim
//! (`library/alloc/src/collections/btree/map.rs:206`):
//!
//! ```text
//! fn drop(&mut self) { drop(unsafe { ptr::read(self) }.into_iter()) }
//! ```
//!
//! so the map's glue never appears on its own — only the iterator's does. The audited
//! container list credited `BTreeMap` and not `alloc::collections::btree::map::IntoIter`,
//! which made the `BTreeMap` entry unreachable: `drop glue for
//! alloc::collections::btree::map::IntoIter has unproven panic-freedom` failed closed and
//! took the whole function with it. Measured before the fix: `BTreeMap::new()` + `drop`
//! exit 0, but ONE `insert` — which is what puts a node in the tree for the iterator to
//! walk — exit 1.
//!
//! WHAT THIS FIXTURE PINS: that the credit is about the CONTAINER'S OWN glue and nothing
//! else. Both functions below put a value carrying a USER `Drop` into the map, and a user
//! `Drop` runs arbitrary, possibly-panicking code. Both must be REFUSED. If this file ever
//! compiles, the delegated-drop arm stopped recursing into the concrete type arguments and
//! is crediting element glue it never audited — which is a false proof, not a widening.
//!
//! Measured 2026-09-26 on a stage1 built from the fix: both exit 1, each with
//! `Trust strict verification failed`. The POSITIVE side is
//! `xcrate_drop_glue_sysroot_destructors_still_credited.rs`, whose `btree` case this fix
//! turned green; keep the two in step.
//!
//! The KEY position is covered as well as the VALUE position because they reach the
//! iterator's drop by different routes — `dying_next` hands back a key/value pair and
//! `drop_key_val` drops both — and a fix that recursed into only one of the two type
//! arguments would still pass a value-only control.

pub struct Boom(u8);

impl Drop for Boom {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("boom")
        }
    }
}

pub fn btree_panicking_value(x: u8) -> u8 {
    //~^ ERROR Trust strict verification failed
    let mut m = std::collections::BTreeMap::new();
    m.insert(x, Boom(x));
    drop(m);
    x
}

pub struct BoomKey(u8);

impl Drop for BoomKey {
    fn drop(&mut self) {
        if self.0 == 7 {
            panic!("boom")
        }
    }
}

impl PartialEq for BoomKey {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl Eq for BoomKey {}
impl PartialOrd for BoomKey {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BoomKey {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

pub fn btree_panicking_key(x: u8) -> u8 {
    //~^ ERROR Trust strict verification failed
    let mut m = std::collections::BTreeMap::new();
    m.insert(BoomKey(x), x);
    drop(m);
    x
}
