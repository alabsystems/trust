//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
#![crate_type = "lib"]
//! The other half of `hashmap_through_hashbrown_is_vanilla.rs`: std's private
//! `hashbrown` joins the vanilla class only at FOUNDATIONAL types. Instantiated
//! at a user key or a user `BuildHasher`, `entry` hashes through user code (both
//! of which panic on 7 here), so the hashbrown callee is NOT vanilla and its
//! absent-callee row stays a fail-closed assumption panic. A green `user_key` or
//! `user_hasher` would be a false verify: `f(&mut m, 7)` panics.
use std::collections::HashMap;
use std::hash::{BuildHasher, Hash, Hasher};

#[derive(PartialEq, Eq)]
pub struct Key(pub u32);

impl Hash for Key {
    fn hash<H: Hasher>(&self, h: &mut H) {
        if self.0 == 7 {
            panic!("boom");
        }
        h.write_u32(self.0);
    }
}

pub fn user_key(m: &mut HashMap<Key, u32>, k: u32) { //~ ERROR Trust strict verification failed for `hashmap_non_foundational_stays_closed::user_key`
    let e = m.entry(Key(k)).or_insert(0);
    *e = e.saturating_add(1);
}

pub struct State;
pub struct Sip(u64);

impl Hasher for Sip {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        if bytes.first() == Some(&7) {
            panic!("boom");
        }
        self.0 = self.0.wrapping_add(bytes.len() as u64);
    }
}

impl BuildHasher for State {
    type Hasher = Sip;
    fn build_hasher(&self) -> Sip {
        Sip(0)
    }
}

pub fn user_hasher(m: &mut HashMap<u32, u32, State>, k: u32) { //~ ERROR Trust strict verification failed for `hashmap_non_foundational_stays_closed::user_hasher`
    let e = m.entry(k).or_insert(0);
    *e = e.saturating_add(1);
}
