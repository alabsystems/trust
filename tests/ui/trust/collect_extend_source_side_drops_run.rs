//@ run-fail
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: source_side_drops_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=off
//@ check-stdout
//@ error-pattern: hasher drop bomb
//@ error-pattern: hash_set_hasher: hasher drop bomb
//@ error-pattern: result_err: err drop bomb
//@ error-pattern: take_remainder: item drop bomb
//@ error-pattern: skip_discard: item drop bomb
//@ error-pattern: filter_discard: item drop bomb
//@ error-pattern: skip_ref_discard: item drop bomb
//@ error-pattern: stepby_ref_discard: item drop bomb
//@ error-pattern: zip_remainder: item drop bomb
//@ error-pattern: chain_ref_take: item drop bomb
//@ error-pattern: into_keys_discard: item drop bomb
//@ error-pattern: scan_state: item drop bomb
//@ error-pattern: collect_into_keys: item drop bomb
//@ error-pattern: collect_filter_capture: item drop bomb
//@ ignore-emscripten no processes
//! The WITNESS for `collect_extend_source_side_drops.rs` (SOURCE-SIDE-DROP-CERTIFY-1):
//! the same function shapes, built with verification OFF, run with the
//! auxiliary's bombs armed (field `7`). Each `extend`/`collect` panics INSIDE the
//! std call, in a drop the source side performs: the hasher `HashMap::into_iter`
//! and `HashSet::into_iter` drop, the `Err` payload `Result::into_iter` drops, a
//! `Take`/`Zip` remainder, an item `Skip`/`StepBy`/`Filter` passes over (through
//! `&mut` too), the first half a borrowed `Chain` drops when it runs dry, the
//! value `IntoKeys` drops, a `Scan` state and a by-move capture. Every shape but the
//! last is caught and reported on stdout as `<shape>: <message>`; the last, the
//! `HashMap` hasher, panics out of `main` (exit 101).
//! (`check-stdout`: compiletest matches a run-fail `error-pattern` against stderr
//! only unless asked, and the `<shape>: <message>` lines are on stdout.)
//!
//! Built with verification OFF, so it passes before and after the fix alike: it
//! pins that each drop really runs inside the call, not the verdict (the check-fail
//! fixture refuses these shapes after the fix). Measured 2026-10-13 on the stage 1
//! at `scratchpad/stage1-w25f` and on stock `rustup run stable rustc`: the auxiliary
//! built `-Ztrust-verify=off` and this file built `-Ztrust-verify=off` (stock: no
//! `-Z` flag) exit 101 and print every pattern above.

extern crate source_side_drops_unverified_dep as dep;

use dep::{Bomb, DropBuild, ErrBomb};
use std::collections::{btree_map, BTreeMap, HashMap, HashSet};
use std::iter::{Chain, Skip, StepBy, Take, Zip};
use std::ops::Range;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::vec::IntoIter;

#[inline(never)]
pub fn hash_map_hasher(v: &mut Vec<(u32, u8)>, m: HashMap<u32, u8, DropBuild>) {
    v.extend(m)
}

#[inline(never)]
pub fn hash_set_hasher(v: &mut Vec<u32>, s: HashSet<u32, DropBuild>) {
    v.extend(s)
}

#[inline(never)]
pub fn result_err(v: &mut Vec<u32>, r: Result<u32, ErrBomb>) {
    v.extend(r)
}

#[inline(never)]
pub fn take_remainder(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    v.extend(src.into_iter().take(1))
}

#[inline(never)]
pub fn skip_discard(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    v.extend(src.into_iter().skip(1))
}

#[inline(never)]
pub fn filter_discard(v: &mut Vec<Bomb>, src: Vec<Bomb>) {
    v.extend(src.into_iter().filter(|b| b.0 != 7))
}

#[inline(never)]
pub fn skip_ref_discard(v: &mut Vec<Bomb>, it: &mut Skip<IntoIter<Bomb>>) {
    v.extend(it)
}

#[inline(never)]
pub fn stepby_ref_discard(v: &mut Vec<Bomb>, it: &mut StepBy<IntoIter<Bomb>>) {
    v.extend(it)
}

#[inline(never)]
pub fn zip_remainder(v: &mut Vec<(Bomb, u32)>, it: Zip<IntoIter<Bomb>, Range<u32>>) {
    v.extend(it)
}

#[inline(never)]
pub fn chain_ref_take(v: &mut Vec<Bomb>, it: &mut Chain<Take<IntoIter<Bomb>>, IntoIter<Bomb>>) {
    v.extend(it)
}

#[inline(never)]
pub fn into_keys_discard(v: &mut Vec<u32>, it: btree_map::IntoKeys<u32, Bomb>) {
    v.extend(it)
}

#[inline(never)]
pub fn scan_state(v: &mut Vec<u32>, it: IntoIter<u32>, st: Bomb) {
    v.extend(it.scan(st, |_, x| Some(x)))
}

#[inline(never)]
pub fn collect_into_keys(it: btree_map::IntoKeys<u32, Bomb>) -> HashSet<u32> {
    it.collect()
}

#[inline(never)]
pub fn collect_filter_capture(it: IntoIter<(u32, u8)>, cap: Bomb) -> HashMap<u32, u8> {
    it.filter(move |p| {
        let _c = &cap;
        p.0 != 7
    })
    .collect()
}

/// Runs one armed shape, which must panic; prints `<shape>: <message>`.
fn witness(shape: &str, run: impl FnOnce()) {
    let payload = catch_unwind(AssertUnwindSafe(run)).expect_err(shape);
    let msg = payload.downcast_ref::<&str>().copied().unwrap_or("<non-str payload>");
    println!("{shape}: {msg}");
}

fn bombs(a: u8, b: u8) -> Vec<Bomb> {
    vec![Bomb(a), Bomb(b)]
}

fn main() {
    // Every vector a shape fills holds only unarmed items, so it drops normally.
    witness("hash_set_hasher", || {
        let mut s = HashSet::with_hasher(DropBuild(7));
        s.insert(3u32);
        hash_set_hasher(&mut Vec::new(), s);
    });
    witness("result_err", || result_err(&mut Vec::new(), Err(ErrBomb(7))));
    witness("take_remainder", || take_remainder(&mut Vec::new(), bombs(0, 7)));
    witness("skip_discard", || skip_discard(&mut Vec::new(), bombs(7, 0)));
    witness("filter_discard", || filter_discard(&mut Vec::new(), bombs(7, 0)));
    witness("skip_ref_discard", || {
        let mut it = bombs(7, 1).into_iter().skip(1);
        skip_ref_discard(&mut Vec::new(), &mut it);
    });
    witness("stepby_ref_discard", || {
        let mut it = bombs(1, 7).into_iter().step_by(2);
        stepby_ref_discard(&mut Vec::new(), &mut it);
    });
    witness("zip_remainder", || zip_remainder(&mut Vec::new(), bombs(1, 7).into_iter().zip(0..1)));
    witness("chain_ref_take", || {
        let mut it = bombs(1, 7).into_iter().take(1).chain(Vec::new());
        chain_ref_take(&mut Vec::new(), &mut it);
    });
    witness("into_keys_discard", || {
        let m = BTreeMap::from([(1u32, Bomb(7))]);
        into_keys_discard(&mut Vec::new(), m.into_keys());
    });
    witness("scan_state", || scan_state(&mut Vec::new(), vec![1, 2].into_iter(), Bomb(7)));
    witness("collect_into_keys", || {
        let m = BTreeMap::from([(1u32, Bomb(7))]);
        collect_into_keys(m.into_keys());
    });
    witness("collect_filter_capture", || {
        collect_filter_capture(vec![(1, 2)].into_iter(), Bomb(7));
    });
    // The last shape panics out of `main`.
    let mut m = HashMap::with_hasher(DropBuild(7));
    m.insert(1u32, 2u8);
    hash_map_hasher(&mut Vec::new(), m);
    println!("unreachable: the hasher drop did not run inside the call");
}
