//@ needs-trust-verify
//@ edition: 2021
//@ revisions: wc_set wc_set_opt wc_map wc_map_string itermap_wc_set resmap_wc_set map_or_else_wc_set impl_fn_wc_set wc_guarded_big from_iter_set from_iter_map collect_set iter_from_iter_set iter_collect_map from_iter_range wc_vec from_iter_vec impl_fn_wc_vec from_iter_range_vec wc_min_clamped bounded_zip_map bounded_map_map bounded_extend_map bounded_map_vec bounded_extend_vec values_sum_duration values_sum_duration_vec bounded_chain_cost itermap_sum_set itermap_count_set itermap_sum_map itermap_sum_vec
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[wc_set_opt] compile-flags: -O
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! W4 HASHMAP r3 (2026-09-29) — the FALSE ACCEPTS the redo's round-2 build
//! (`w4-hashmap-redo` `b9288112d`, stage-1 snapshot `snap-w4f-hashmap-r2`) built
//! rc=0 and that then exited 101 at run time, found by its adversarial prober
//! (probe round r2, LAND-WITH-CHANGES: 17 new false accepts in three classes),
//! plus the `Vec` twins of the same classes, which main built rc=0 as well.
//!
//! EVERY REVISION MUST STAY REFUSED. Each program panics at run time for some
//! input (`wc_min_clamped` excepted: see below). Fix the compiler, never this
//! file. MEASURED (every revision compiled the way compiletest does; see the
//! commit message for the table): rc=0 on the round-2 compiler
//! (`snap-w4f-hashmap-r2`, `b9288112d`) and refused on the round-3 build.
//!
//!   * `wc_*`, `*map_wc_set`, `map_or_else_wc_set`, `impl_fn_wc_*`,
//!     `*from_iter_*`, `*collect_*` — a sysroot BULK-ALLOCATION fn ITEM handed
//!     to a higher-order function (`Option::map`, `Result::map`,
//!     `Option::map_or_else`, `Iterator::map`, an `impl Fn`). The item runs
//!     inside the callee, where no `[unbounded_allocation]` row is minted, and
//!     the compiler admitted it as a vanilla sysroot item because vcgen's
//!     call-site panic families (`callee_has_call_site_panic_family`) had no
//!     allocation member. "Hash table capacity overflow" / "capacity overflow"
//!     at `n = usize::MAX` (`wc_guarded_big`: behind `n < 2^28`, a
//!     `2^35`-byte element). The `*_vec` revisions are the `Vec` twins —
//!     accepted on main (`296873da6`) too, closed by the same change.
//!   * `wc_min_clamped` — a DISCLOSED OVER-REFUSAL, pinned:
//!     `Some(n.min(1024)).map(HashSet::with_capacity)` never panics, but the
//!     fn-item gate is by the item's NAME and cannot see the argument. Main
//!     refuses it too; round 2 accepted it.
//!   * `bounded_*` — the BOUNDED-SOURCE grant counted the source and ignored the
//!     destination: a 2^28-byte `&[u8]` mapped (or zipped) to a
//!     `MaybeUninit<[u8; 1 << 35]>` element and collected into a `HashMap` (or a
//!     `Vec`, or `extend`ed into either) asks for 2^63 bytes. Now the grant needs
//!     the destination to fit the live source's count
//!     (`trust_types::live_source_bound`), in the extractor's TOTAL-sentinel
//!     licence and in vcgen's skip alike. `bounded_map_map`, `bounded_extend_map`
//!     and the `*_vec` twins were accepted on main too.
//!   * `values_sum_duration*` — `HashMap::values().copied().sum::<Duration>()`
//!     panics "overflow in iter::sum over durations"; closed by main's
//!     `numeric_panic` (`1f3b181649`, `Sum<Duration>`), merged into round 3.
//!   * `bounded_chain_cost` — a DISCLOSED OVER-REFUSAL, pinned (added after
//!     the round-3 review, measured rc=0 on `snap-w4f-hashmap-r2` and on the
//!     round-3 dev build, refused on `snap-w4f-hashmap-r3`; main refuses it
//!     too, `HashMap` being non-foundational there): a `chain` of two
//!     one-byte sources into a 41-byte table element never panics on real
//!     hardware, but a chain's sides are bounded each on its own (they may walk
//!     ONE buffer: `v.iter().chain(v.iter())`), and `2 * 2^56` items of 41 bytes
//!     do not fit hashbrown's bucket layout, so the grant is withheld and the
//!     collect is a visible Unknown. A single such source fits up to 62 bytes, a
//!     chain of two up to 30 (docs/TCB.md, the W4 HASHMAP cost paragraph).
//!   * `itermap_*` — found at the LANDING of round 3 (2026-09-29): the same
//!     fn-item class through `Iterator::map` when the chain ENDS in `sum` or
//!     `count`. Those consumers' std members carry an `Overflow(Add)` Assert, and
//!     the round-3 build still had the policy-B tolerance on the lowering-failure
//!     path of `abort_on_full_verification_failure`, which admitted the function
//!     as "the only undischarged obligation is a bundled std member's Assert"
//!     BEFORE the fn-item type-argument gate ran. MEASURED: rc=0 on
//!     `snap-w4f-hashmap-r3` (`2b5f15e9c`), "Hash table capacity overflow" /
//!     "capacity overflow" at `n = usize::MAX`; the `HashSet`/`HashMap` forms
//!     refused on main `fb9f57688` (non-foundational there), the `Vec` twin
//!     accepted there too. Closed by main's `de66170e69` (that tolerance removed;
//!     the runtime-checked std-member disposition is judged on the success path,
//!     where the gate runs), merged before landing: refused on the merged build.

use std::collections::{HashMap, HashSet};
use std::time::Duration;

type Big = std::mem::MaybeUninit<[u8; 1 << 35]>;

#[cfg(any(wc_set, wc_set_opt))]
pub fn wc_set(n: usize) -> Option<HashSet<u64>> {
    //[wc_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_set`
    //[wc_set_opt]~^^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_set`
    Some(n).map(HashSet::with_capacity)
}

#[cfg(wc_map)]
pub fn wc_map(n: usize) -> Option<HashMap<u64, u64>> {
    //[wc_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_map`
    Some(n).map(HashMap::with_capacity)
}

#[cfg(wc_map_string)]
pub fn wc_map_string(n: usize) -> usize {
    //[wc_map_string]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_map_string`
    Some(n).map(HashMap::<String, Vec<u8>>::with_capacity).map_or(0, |m| m.capacity())
}

#[cfg(itermap_wc_set)]
pub fn itermap_wc_set(n: usize) -> Option<HashSet<u64>> {
    //[itermap_wc_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::itermap_wc_set`
    std::iter::once(n).map(HashSet::with_capacity).last()
}

#[cfg(resmap_wc_set)]
pub fn resmap_wc_set(r: Result<usize, u8>) -> Result<HashSet<u64>, u8> {
    //[resmap_wc_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::resmap_wc_set`
    r.map(HashSet::with_capacity)
}

#[cfg(map_or_else_wc_set)]
pub fn map_or_else_wc_set(n: Option<usize>) -> usize {
    //[map_or_else_wc_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::map_or_else_wc_set`
    n.map_or_else(HashSet::<u64>::new, HashSet::with_capacity).capacity()
}

#[cfg(impl_fn_wc_set)]
fn make_set() -> impl Fn(usize) -> HashSet<u64> {
    HashSet::with_capacity
}

#[cfg(impl_fn_wc_set)]
pub fn impl_fn_wc_set(n: usize) -> usize {
    //[impl_fn_wc_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::impl_fn_wc_set`
    make_set()(n).capacity()
}

#[cfg(wc_guarded_big)]
pub fn wc_guarded_big(n: usize) -> usize {
    //[wc_guarded_big]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_guarded_big`
    if n < (1 << 28) {
        Some(n).map(HashMap::<u32, Big>::with_capacity).map_or(0, |m| m.capacity())
    } else {
        0
    }
}

#[cfg(from_iter_set)]
pub fn from_iter_set(n: usize) -> Option<HashSet<u64>> {
    //[from_iter_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::from_iter_set`
    Some(std::iter::repeat(1u64).take(n)).map(HashSet::from_iter)
}

#[cfg(from_iter_map)]
pub fn from_iter_map(n: usize) -> Option<HashMap<u64, u64>> {
    //[from_iter_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::from_iter_map`
    Some(std::iter::repeat((1u64, 2u64)).take(n)).map(HashMap::from_iter)
}

#[cfg(collect_set)]
pub fn collect_set(n: usize) -> Option<HashSet<u64>> {
    //[collect_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::collect_set`
    Some(std::iter::repeat(1u64).take(n)).map(Iterator::collect::<HashSet<u64>>)
}

#[cfg(iter_from_iter_set)]
pub fn iter_from_iter_set(n: usize) -> usize {
    //[iter_from_iter_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::iter_from_iter_set`
    vec![std::iter::repeat(1u64).take(n)]
        .into_iter()
        .map(HashSet::from_iter)
        .map(|s: HashSet<u64>| s.len())
        .fold(0, usize::wrapping_add)
}

#[cfg(iter_collect_map)]
pub fn iter_collect_map(n: usize) -> usize {
    //[iter_collect_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::iter_collect_map`
    vec![std::iter::repeat((1u64, 2u64)).take(n)]
        .into_iter()
        .map(Iterator::collect::<HashMap<u64, u64>>)
        .map(|m| m.len())
        .fold(0, usize::wrapping_add)
}

#[cfg(from_iter_range)]
pub fn from_iter_range(n: u64) -> usize {
    //[from_iter_range]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::from_iter_range`
    Some(0..n).map(HashSet::<u64>::from_iter).map_or(0, |s| s.len())
}

#[cfg(wc_vec)]
pub fn wc_vec(n: usize) -> Option<Vec<u64>> {
    //[wc_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_vec`
    Some(n).map(Vec::with_capacity)
}

#[cfg(from_iter_vec)]
pub fn from_iter_vec(n: usize) -> Option<Vec<u64>> {
    //[from_iter_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::from_iter_vec`
    Some(std::iter::repeat(1u64).take(n)).map(Vec::from_iter)
}

#[cfg(impl_fn_wc_vec)]
fn make_vec() -> impl Fn(usize) -> Vec<u64> {
    Vec::with_capacity
}

#[cfg(impl_fn_wc_vec)]
pub fn impl_fn_wc_vec(n: usize) -> usize {
    //[impl_fn_wc_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::impl_fn_wc_vec`
    make_vec()(n).capacity()
}

#[cfg(from_iter_range_vec)]
pub fn from_iter_range_vec(n: u64) -> usize {
    //[from_iter_range_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::from_iter_range_vec`
    Some(0..n).map(Vec::<u64>::from_iter).map_or(0, |s| s.len())
}

// DISCLOSED OVER-REFUSAL (never panics; refused on main too): see the header.
#[cfg(wc_min_clamped)]
pub fn wc_min_clamped(n: usize) -> usize {
    //[wc_min_clamped]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::wc_min_clamped`
    Some(n.min(1024)).map(HashSet::<u64>::with_capacity).map_or(0, |s| s.capacity())
}

#[cfg(bounded_zip_map)]
pub fn bounded_zip_map(v: &[u8]) -> usize {
    //[bounded_zip_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_zip_map`
    v.iter().copied().zip(std::iter::repeat_with(Big::uninit)).collect::<HashMap<u8, Big>>().len()
}

#[cfg(bounded_map_map)]
pub fn bounded_map_map(v: &[u8]) -> usize {
    //[bounded_map_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_map_map`
    v.iter().map(|&b| (b, Big::uninit())).collect::<HashMap<u8, Big>>().len()
}

#[cfg(bounded_extend_map)]
pub fn bounded_extend_map(m: &mut HashMap<u8, Big>, v: &[u8]) -> usize {
    //[bounded_extend_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_extend_map`
    m.extend(v.iter().map(|&b| (b, Big::uninit())));
    m.len()
}

#[cfg(bounded_map_vec)]
pub fn bounded_map_vec(v: &[u8]) -> usize {
    //[bounded_map_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_map_vec`
    v.iter().map(|&b| (b, Big::uninit())).collect::<Vec<(u8, Big)>>().len()
}

#[cfg(bounded_extend_vec)]
pub fn bounded_extend_vec(m: &mut Vec<(u8, Big)>, v: &[u8]) -> usize {
    //[bounded_extend_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_extend_vec`
    m.extend(v.iter().map(|&b| (b, Big::uninit())));
    m.len()
}

#[cfg(values_sum_duration)]
pub fn values_sum_duration(m: &HashMap<u32, Duration>) -> Duration {
    //[values_sum_duration]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::values_sum_duration`
    m.values().copied().sum::<Duration>()
}

#[cfg(values_sum_duration_vec)]
pub fn values_sum_duration_vec(v: &Vec<Duration>) -> Duration {
    //[values_sum_duration_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::values_sum_duration_vec`
    v.iter().copied().sum::<Duration>()
}

// DISCLOSED OVER-REFUSAL (never panics on real hardware): see the header.
#[cfg(bounded_chain_cost)]
pub fn bounded_chain_cost(v: &[u8]) -> usize {
    //[bounded_chain_cost]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::bounded_chain_cost`
    v.iter().chain(v.iter()).map(|&b| (b, [0u8; 40])).collect::<HashMap<u8, [u8; 40]>>().len()
}

#[cfg(itermap_sum_set)]
pub fn itermap_sum_set(n: usize) -> usize {
    //[itermap_sum_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::itermap_sum_set`
    std::iter::once(n).map(HashSet::<u64>::with_capacity).map(|s| s.capacity()).sum()
}

#[cfg(itermap_count_set)]
pub fn itermap_count_set(n: usize) -> usize {
    //[itermap_count_set]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::itermap_count_set`
    std::iter::once(n).map(HashSet::<u64>::with_capacity).count()
}

#[cfg(itermap_sum_map)]
pub fn itermap_sum_map(n: usize) -> usize {
    //[itermap_sum_map]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::itermap_sum_map`
    std::iter::once(n).map(HashMap::<u64, u64>::with_capacity).map(|m| m.capacity()).sum()
}

#[cfg(itermap_sum_vec)]
pub fn itermap_sum_vec(n: usize) -> usize {
    //[itermap_sum_vec]~^ ERROR Trust strict verification failed for `hashmap_fn_item_alloc_and_bounded_source_refused::itermap_sum_vec`
    std::iter::once(n).map(Vec::<u8>::with_capacity).map(|v| v.capacity()).sum()
}
