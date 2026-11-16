//! R19 FRONT A runtime canaries for the btree/hash map-iterator `next` admission.
//!
//! K2 (genuinely TRUE): the admitted claim — `BTreeMap`/`BTreeSet` `Iter::next` runs NO
//! user code — witnessed against a key whose `Ord::cmp` and `Drop` PANIC once armed.
//! Building the map runs `cmp`; iterating it must not.
//!
//! K1 (would be FALSE if admitted): the nearest shapes the gate must DECLINE — a
//! `Filter`/`Map` adapter over the same btree iterator. Their `next` DOES drive user
//! code and DOES panic; `#[should_panic]` executes the witness.
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

thread_local! { static ARMED: Cell<bool> = const { Cell::new(false) }; }

#[derive(Debug, PartialEq, Eq)]
struct BoobyKey(u32);

impl PartialOrd for BoobyKey {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for BoobyKey {
    fn cmp(&self, o: &Self) -> Ordering {
        if ARMED.with(|a| a.get()) {
            panic!("BoobyKey::cmp ran");
        }
        self.0.cmp(&o.0)
    }
}
impl Drop for BoobyKey {
    fn drop(&mut self) {
        if ARMED.with(|a| a.get()) {
            panic!("BoobyKey::drop ran");
        }
    }
}

#[derive(Debug)]
struct BoobyVal(u32);
impl Clone for BoobyVal {
    fn clone(&self) -> Self {
        if ARMED.with(|a| a.get()) {
            panic!("BoobyVal::clone ran");
        }
        BoobyVal(self.0)
    }
}
impl Drop for BoobyVal {
    fn drop(&mut self) {
        if ARMED.with(|a| a.get()) {
            panic!("BoobyVal::drop ran");
        }
    }
}

fn build() -> BTreeMap<BoobyKey, BoobyVal> {
    let mut m = BTreeMap::new();
    for i in 0..64u32 {
        m.insert(BoobyKey(i), BoobyVal(i * 3));
    }
    m
}

// ---------- K2: the admitted claim, genuinely true ----------

#[test]
fn k2_btreemap_iter_next_runs_no_user_code() {
    let m = build();
    ARMED.with(|a| a.set(true));
    let mut n = 0u32;
    let mut sum = 0u64;
    // The EXACT shape the gate now admits: `<btree::map::Iter as Iterator>::next`.
    for (k, v) in m.iter() {
        n += 1;
        sum += u64::from(k.0) + u64::from(v.0);
    }
    ARMED.with(|a| a.set(false));
    assert_eq!(n, 64);
    assert_eq!(sum, (0..64u64).map(|i| i + i * 3).sum::<u64>());
    std::mem::forget(m); // keep the armed Drop out of teardown
}

#[test]
fn k2_btreeset_iter_next_runs_no_user_code() {
    let mut s = BTreeSet::new();
    for i in 0..64u32 {
        s.insert(BoobyKey(i));
    }
    ARMED.with(|a| a.set(true));
    let n = s.iter().fold(0u32, |acc, k| acc + k.0);
    ARMED.with(|a| a.set(false));
    assert_eq!(n, (0..64u32).sum::<u32>());
    std::mem::forget(s);
}

#[test]
fn k2_keys_values_enumerate_run_no_user_code() {
    let m = build();
    ARMED.with(|a| a.set(true));
    let mut c = 0usize;
    for (i, k) in m.keys().enumerate() {
        c += i + k.0 as usize;
    }
    for v in m.values() {
        c += v.0 as usize;
    }
    ARMED.with(|a| a.set(false));
    assert!(c > 0);
    std::mem::forget(m);
}

// ---------- K1: shapes the gate must DECLINE (they really do panic) ----------

#[test]
#[should_panic(expected = "user filter predicate panicked")]
fn k1_filter_over_btree_iter_really_panics() {
    let m = build();
    // `Filter<btree::map::Iter>` is a CLOSURE adapter: its `next` drives user code.
    // The gate lists no `Filter` arm, so it stays fail-closed — this witness shows
    // what admitting it would have certified away.
    let _n = m
        .iter()
        .filter(|(k, _)| {
            if k.0 == 7 {
                panic!("user filter predicate panicked");
            }
            true
        })
        .count();
    std::mem::forget(m);
}

#[test]
#[should_panic(expected = "user map closure panicked")]
fn k1_map_over_btree_iter_really_panics() {
    let m = build();
    let _s: u32 = m
        .iter()
        .map(|(k, _)| {
            if k.0 == 9 {
                panic!("user map closure panicked");
            }
            k.0
        })
        .sum();
    std::mem::forget(m);
}

#[derive(Debug)]
struct CloneBomb(u32);
impl Clone for CloneBomb {
    fn clone(&self) -> Self {
        panic!("CloneBomb::clone ran");
    }
}

#[test]
#[should_panic(expected = "CloneBomb::clone ran")]
fn k1_cloned_over_btree_values_really_panics() {
    // `Cloned<btree::map::Values>` runs `V::clone` inside `next` — also absent from the
    // gate. Uses a benign-Drop bomb so the witness unwinds cleanly.
    let mut m: BTreeMap<u32, CloneBomb> = BTreeMap::new();
    for i in 0..8u32 {
        m.insert(i, CloneBomb(i));
    }
    let _v: Vec<CloneBomb> = m.values().cloned().collect();
    unreachable!();
}

#[derive(Debug, PartialEq, Eq)]
struct CmpBomb(u32);
impl PartialOrd for CmpBomb {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for CmpBomb {
    fn cmp(&self, o: &Self) -> Ordering {
        if CMP_ARMED.with(|a| a.get()) {
            panic!("CmpBomb::cmp ran");
        }
        self.0.cmp(&o.0)
    }
}
thread_local! { static CMP_ARMED: Cell<bool> = const { Cell::new(false) }; }

#[test]
#[should_panic(expected = "CmpBomb::cmp ran")]
fn k1_insert_does_run_user_cmp() {
    // CONTROL. Without this, K2 could be vacuous — passing because the user `Ord` is
    // never callable at all rather than because `next` avoids it. Insert DOES reach it.
    let mut m: BTreeMap<CmpBomb, u32> = BTreeMap::new();
    for i in 0..8u32 {
        m.insert(CmpBomb(i), i);
    }
    CMP_ARMED.with(|a| a.set(true));
    m.insert(CmpBomb(999), 0);
    unreachable!();
}

#[test]
fn k2_cmpbomb_iteration_is_clean_after_insert_control() {
    // The K2 claim restated on the CONTROL's own key type: same map, same armed `cmp`,
    // iteration completes.
    let mut m: BTreeMap<CmpBomb, u32> = BTreeMap::new();
    for i in 0..64u32 {
        m.insert(CmpBomb(i), i);
    }
    CMP_ARMED.with(|a| a.set(true));
    let n: u32 = m.iter().map(|(k, _)| k.0).sum();
    CMP_ARMED.with(|a| a.set(false));
    assert_eq!(n, (0..64u32).sum::<u32>());
}
