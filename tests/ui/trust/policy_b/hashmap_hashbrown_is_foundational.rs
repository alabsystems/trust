//@ needs-trust-verify
//@ edition: 2021
//@ revisions: inventory inventory_release_std invert fifo dedup print_lookup sorted_keys certify certify_census
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[certify] compile-flags: -Ztrust-policy=certify
//@[certify] rustc-env:TRUST_NO_SYSROOT_CENSUS=1
//@[certify_census] compile-flags: -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[inventory] check-pass
//@[inventory] needs-std-debug-assertions (pinned by `inventory_release_std`)
//@[inventory_release_std] check-fail
//@[inventory_release_std] ignore-std-debug-assertions (pinned by `inventory`)
//@[invert] check-pass
//@[fifo] check-pass
//@[dedup] check-pass
//@[print_lookup] check-pass
//@[sorted_keys] check-fail
//@[certify] check-fail
//@[certify_census] check-fail
//! W4 HASHMAP (2026-09-25, redo) — `std::collections::HashMap`/`HashSet` are
//! FOUNDATIONAL: the crate behind them (`hashbrown`) is credited, identified
//! STRUCTURALLY, and it is the only crate outside `core`/`alloc`/`std` that is.
//!
//! # The over-refusal
//!
//! `std::collections::HashMap`'s only field is `hashbrown::HashMap`. The policy-B
//! vanilla class admitted ADTs from `core`/`alloc`/`std` alone, so the field
//! walk made every `HashMap`/`HashSet` non-foundational, with three effects:
//! every call on one was a MASKED fail-closed source (withdrawing the vanilla
//! grace from every co-resident tolerated gap — a `VecDeque` op, a `String`
//! push, a `Vec::sort`); every `hashbrown` callee of a bundled `HashMap::entry`
//! body was a NOT-IN-LEDGER absent callee; and `<HashMap<..> as Default>::
//! default` was NOT-VANILLA.
//!
//! # The ruling (lead, owner-delegated; docs/TCB.md "hashbrown behind HashMap")
//!
//! Credit ONLY hashbrown, identified by structure, never by name: the crate that
//! defines the ADT std's `HashMap`/`HashSet` FIELD is declared as
//! (`trust_mir_extract::def_is_in_std_hash_table_crate`), resident in the
//! compiler's own target library directory, and not named directly by the crate
//! being compiled. std's other dependencies (`libc`, `std_detect`, ...) are not
//! credited. And even hashbrown counts only where STD put it: at a user call
//! site a hashbrown type counts only as a std/hashbrown DECLARED field, and a
//! hashbrown callee only at a call site inside a bundled std body
//! (`HashTableCredit` in `trust_verify.rs`).
//!
//! # What each revision pins
//!
//! Every check-pass revision was REFUSED on the baseline (main, stage-1
//! `7c7e46061`, rc=1) with the `HashMap`/`HashSet` call as the masked
//! fail-closed source or a NOT-IN-LEDGER hashbrown callee:
//!
//!   * `inventory` — unaimed d1/p07: `#[derive(Default)]` over a `HashMap`,
//!     `entry().or_insert()`, `get_mut`;
//!   * `invert`    — unaimed d1/p10: `for (k, v) in &map`, `entry().or_default()
//!     .push()`, `values_mut`, a `sort` per value;
//!   * `fifo`      — unaimed d1/p12: `HashMap::insert`/`remove` beside
//!     `VecDeque::push_back`/`pop_front`;
//!   * `dedup`     — `HashSet::insert` beside `Vec::push`;
//!   * `print_lookup` — `HashMap::get` beside a tolerated `println!`;
//!   * `sorted_keys`  — `keys().cloned().collect()` then a tolerated `Vec::sort`.
//!
//! `certify` compiles the same functions under `-Ztrust-policy=certify` and
//! must REFUSE them: the check-pass revisions pass as REPORTED, runtime-checked
//! rows, never as proofs.
//!
//! `certify` runs with the sysroot panic census withheld (`TRUST_NO_SYSROOT_CENSUS=1`,
//! 2026-10-08, std-absent-callee), which keeps that statement exactly as measured.
//! `certify_census` is the same file with the census on: every function stays
//! refused except `Inventory::add`, whose one unproved row was the absent
//! `Entry::or_insert` call. The census derives it panic-free from std's MIR at its
//! instance (`Occupied` returns the slot; `Vacant` is `insert_no_grow` into the
//! capacity `entry` reserved: no panic site on a release-like std), so `add` is
//! proved by that derivation together with the lanes that already discharge
//! `to_string` and `HashMap::entry` here — a proof, not a reported row
//! (`tests/ui/trust/sysroot_census/certify_total_sysroot_callees.rs` pins the
//! `or_insert` derivation on its own).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14; DECISION_QUEUE D103): `sorted_keys`
//! now REFUSED (`check-fail`), measured on the merged stage 1. Each was accepted on
//! main through a grant the merge conjoined with the soundness line's fail-closed gate
//! for the same call, and that gate refuses it: the bounded-source capacity grant
//! also needs D93 (a)'s upfront-reservation fit on the per-allocation axiom (a hash
//! table or a widening destination over a slice, a `BTreeMap`/`LinkedList` source held
//! in many allocations, and `extend` into a live hash table are charged:
//! `bounded-source-destination-may-overflow` / `count-not-derivable`), a tuple
//! receiver is not a receiver whose length memory bounds (`receiver-length-not-bounded`),
//! and an `Arc` or a local `Drop` key in a bundled std body keeps its drop-glue row.
//! A capability loss of the conjunction, recorded; each is a correct program, and none
//! of these refusals is a refutation.

#[cfg(any(inventory, inventory_release_std, certify, certify_census))]
pub mod inventory {
    use std::collections::HashMap;

    #[derive(PartialEq)]
    pub enum StockError {
        UnknownItem,
        Insufficient { available: u32 },
    }

    #[derive(Default)]
    pub struct Inventory {
        stock: HashMap<String, u32>,
    }

    impl Inventory {
        pub fn add(&mut self, item: &str, qty: u32) {
            //[certify]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::inventory::Inventory::add`
            // `inventory`: CAPABILITY RETURNED on the 1.101 toolchain
            // (2026-10-18, measured: builds under the default policy with the
            // absent-callee row carried runtime-checked; `certify` above
            // still refuses). Was: CAPABILITY LOSS, re-pinned 2026-10-15
            // (ZERO-ROW-GATE: the body published no row of its own, and its
            // `HashMap::entry` call into BUNDLED std bodies was discharged
            // by no registry the gate reads). See
            // `hashmap_through_hashbrown_is_vanilla.rs` for the mechanism.
            let e = self.stock.entry(item.to_string()).or_insert(0);
            *e = e.saturating_add(qty);
        }

        pub fn remove(&mut self, item: &str, qty: u32) -> Result<u32, StockError> {
            let available = self.stock.get_mut(item).ok_or(StockError::UnknownItem)?;
            if *available < qty {
                return Err(StockError::Insufficient { available: *available });
            }
            *available -= qty;
            Ok(*available)
        }
    }
}

#[cfg(any(invert, certify, certify_census))]
pub mod invert {
    use std::collections::HashMap;

    /// Invert a map from user to team into a map from team to its users.
    pub fn invert(assignments: &HashMap<String, String>) -> HashMap<String, Vec<String>> {
        //[certify,certify_census]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::invert::invert`
        let mut by_team: HashMap<String, Vec<String>> = HashMap::new();
        for (user, team) in assignments {
            by_team.entry(team.clone()).or_default().push(user.clone());
        }
        for users in by_team.values_mut() {
            users.sort();
        }
        by_team
    }
}

#[cfg(any(fifo, certify, certify_census))]
pub mod fifo {
    use std::collections::{HashMap, VecDeque};

    /// A tiny least-recently-inserted cache: evicts the oldest key when full.
    pub struct FifoCache {
        map: HashMap<u64, String>,
        order: VecDeque<u64>,
        cap: usize,
    }

    impl FifoCache {
        pub fn new(cap: usize) -> Self {
            FifoCache { map: HashMap::new(), order: VecDeque::new(), cap }
        }

        pub fn get(&self, key: u64) -> Option<&String> {
            self.map.get(&key)
        }

        pub fn put(&mut self, key: u64, value: String) {
            //[certify,certify_census]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::fifo::FifoCache::put`
            if self.map.insert(key, value).is_some() {
                return;
            }
            self.order.push_back(key);
            while self.order.len() > self.cap {
                if let Some(old) = self.order.pop_front() {
                    self.map.remove(&old);
                }
            }
        }
    }
}

#[cfg(any(dedup, certify, certify_census))]
pub mod dedup {
    use std::collections::HashSet;

    /// Remove duplicates while keeping the first occurrence of each item.
    pub fn dedup_stable(items: &[u32]) -> Vec<u32> {
        //[certify,certify_census]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::dedup::dedup_stable`
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        for &x in items {
            if seen.insert(x) {
                out.push(x);
            }
        }
        out
    }
}

#[cfg(any(print_lookup, certify, certify_census))]
pub mod print_lookup {
    use std::collections::HashMap;

    pub fn lookup(key: &str, known: &HashMap<String, u32>) -> u32 {
        //[certify,certify_census]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::print_lookup::lookup`
        println!("looking up {key}");
        known.get(key).copied().unwrap_or(0)
    }
}

#[cfg(any(sorted_keys, certify, certify_census))]
pub mod sorted_keys {
    use std::collections::HashMap;

    pub fn sorted_keys(known: &HashMap<String, u32>) -> Vec<String> {
        //[certify,certify_census]~^ ERROR Trust strict verification failed for `hashmap_hashbrown_is_foundational::sorted_keys::sorted_keys`
        let mut keys: Vec<String> = known.keys().cloned().collect();
        keys.sort();
        keys
    }
}

