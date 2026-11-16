//@ needs-trust-verify
//@ edition: 2021
//@ revisions: gio_str_upper gio_str_upper_opt gio_str_upper_o3 gio_str_lower gio_char_upper gio_char_upper_o3 gio_u8_upper gio_bytes_upper gio_wrapper gio_to_owned wcah_in_map wcah_in_map_opt wcah_in_set wcah_in_set_o3 wcah_in_system wcah_in_guard collect_into_set collect_into_set_opt collect_into_map collect_into_range collect_into_vec map_wc_large_value map_wc_large_value_opt map_wcah_large_value set_wc_const set_wc_const_o3 map_wc_const extend_reserve_const
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[gio_str_upper_opt] compile-flags: -O
//@[gio_str_upper_o3] compile-flags: -Copt-level=3
//@[gio_char_upper_o3] compile-flags: -Copt-level=3
//@[wcah_in_map_opt] compile-flags: -O
//@[wcah_in_set_o3] compile-flags: -Copt-level=3
//@[collect_into_set_opt] compile-flags: -O
//@[map_wc_large_value_opt] compile-flags: -O
//@[set_wc_const_o3] compile-flags: -Copt-level=3
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! W4 HASHMAP r2 (2026-09-28, salvaged after the 2026-09-27 crash) — the FALSE
//! ACCEPTS the redo's round-1 build (`w4-hashmap-redo` `9eadf44e0`, stage-1
//! snapshot `snap-w4f-hashmap-r1`) built rc=0 and that then exited 101 at run
//! time, found by its adversarial prober (LAND-WITH-CHANGES, 25 false accepts in
//! five classes). The baseline (main `7c7e46061`) refused every one of them only
//! because `HashMap`/`HashSet` were non-foundational.
//!
//! EVERY REVISION MUST STAY REFUSED. Each program panics at runtime for some
//! input (the `gio_to_owned` revision excepted: see below). Fix the compiler,
//! never this file. MEASURED 2026-09-28 (every revision, compiled the way
//! compiletest does): rc=0 on the round-1 compiler (`snap-w4f-hashmap-r1`,
//! `9eadf44e0`); rc=1 on main (`7c7e46061`, and `296873da69` the round-2 merge
//! base) except `collect_into_vec`, rc=0 there too (the pre-existing `Vec` twin).
//!
//!   * `gio_*` — the KEY-EQUIVALENCE assert. `HashSet::get_or_insert_with(q, f)`
//!     (nightly `hash_set_entry`) hands the caller's `f(q)` to hashbrown's
//!     `VacantEntryRef::insert_entry_with_key`, which asserts "key used for Entry
//!     creation is not equivalent to the one used for insertion" (hashbrown 0.17.1
//!     `map.rs:4735`). A sysroot fn item as `f` made the root call vanilla, and
//!     the hashbrown callee was credited at the std call site without its body
//!     ever being walked. Now std's `HashSet::get_or_insert_with` (by the
//!     `HashSet` diagnostic item) and hashbrown's `get_or_insert_with` /
//!     `insert_with_key` / `insert_entry_with_key` / `replace_key` / `index` (by
//!     structural identity + the pinned census in
//!     `trust_vcgen::std_hash_table_census`) are excluded from the vanilla class.
//!   * `gio_to_owned` — a DISCLOSED OVER-REFUSAL, pinned: `str::to_owned` IS
//!     key-equivalent, so this program never panics, but the exclusion is by the
//!     callee's identity and cannot see `f`. It is refused on main too.
//!   * `wcah_in_*` — nightly `allocator_api` `with_capacity_and_hasher_in(n, ..)`
//!     was known to neither vcgen's bulk-allocation recognizer nor the extractor's
//!     sink list: no allocation row at all, "Hash table capacity overflow" at a
//!     large `n` (`wcah_in_guard`: behind `n <= 2^59`).
//!   * `collect_into_*` — nightly `Iterator::collect_into(&mut E)` is
//!     `E::extend(self)`, the same `size_hint().0` reservation as `collect`; it was
//!     not an allocation sink. `collect_into_vec` is the `Vec` twin, a
//!     pre-existing false accept on main closed by the same change.
//!   * `map_wc_large_value*` / `map_wcah_large_value` — the table's element size
//!     was stamped from `K` alone (`HashMap::<u8, [u8; 1 << 50]>` read as 1 byte).
//!     A hash-table sink now carries the table token (`(K, V)` / `T`), and a
//!     hash-table allocation without it fails closed.
//!   * `set_wc_const*` / `map_wc_const` / `extend_reserve_const` — BUCKET
//!     INFLATION: `with_capacity(4097)` of a `2^50`-byte element passed the
//!     constant skip (`4097 * 2^50 < isize::MAX`), but hashbrown rounds 4097 up
//!     to 8192 buckets (`2^63` bytes).
//!     The capacity term and the constant skip now use a sound bound on
//!     hashbrown's bucket layout (`hash_table_capacity_overflow_term`).
#![cfg_attr(
    any(
        gio_str_upper,
        gio_str_upper_opt,
        gio_str_upper_o3,
        gio_str_lower,
        gio_char_upper,
        gio_char_upper_o3,
        gio_u8_upper,
        gio_bytes_upper,
        gio_wrapper,
        gio_to_owned
    ),
    feature(hash_set_entry)
)]
#![cfg_attr(
    any(wcah_in_map, wcah_in_map_opt, wcah_in_set, wcah_in_set_o3, wcah_in_system, wcah_in_guard),
    feature(allocator_api)
)]
#![cfg_attr(
    any(
        collect_into_set,
        collect_into_set_opt,
        collect_into_map,
        collect_into_range,
        collect_into_vec
    ),
    feature(iter_collect_into)
)]
#![cfg_attr(extend_reserve_const, feature(extend_one))]
#![allow(unused_imports)]

use std::collections::{HashMap, HashSet};
use std::hash::RandomState;

// ---- 1. key-equivalence assert (get_or_insert_with) ----

#[cfg(any(gio_str_upper, gio_str_upper_opt, gio_str_upper_o3))]
pub fn gio_str_upper(set: &mut HashSet<String>, q: &str) -> usize {
    //[gio_str_upper]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_str_upper`
    //[gio_str_upper_opt]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_str_upper`
    //[gio_str_upper_o3]~^^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_str_upper`
    set.get_or_insert_with(q, str::to_ascii_uppercase).len()
}

#[cfg(gio_str_lower)]
pub fn gio_str_lower(set: &mut HashSet<String>, q: &str) -> bool {
    //[gio_str_lower]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_str_lower`
    set.get_or_insert_with(q, str::to_lowercase).is_empty()
}

#[cfg(any(gio_char_upper, gio_char_upper_o3))]
pub fn gio_char_upper(set: &mut HashSet<char>, c: char) -> char {
    //[gio_char_upper]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_char_upper`
    //[gio_char_upper_o3]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_char_upper`
    *set.get_or_insert_with(&c, char::to_ascii_uppercase)
}

#[cfg(gio_u8_upper)]
pub fn gio_u8_upper(set: &mut HashSet<u8>, b: u8) -> u8 {
    //[gio_u8_upper]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_u8_upper`
    *set.get_or_insert_with(&b, u8::to_ascii_uppercase)
}

#[cfg(gio_bytes_upper)]
pub fn gio_bytes_upper(set: &mut HashSet<Vec<u8>>, q: &[u8]) -> usize {
    //[gio_bytes_upper]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_bytes_upper`
    set.get_or_insert_with(q, <[u8]>::to_ascii_uppercase).len()
}

#[cfg(gio_wrapper)]
pub struct Interner {
    pub set: HashSet<String>,
}

#[cfg(gio_wrapper)]
impl Interner {
    pub fn intern(&mut self, q: &str) -> usize {
        //[gio_wrapper]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::Interner::intern`
        self.set.get_or_insert_with(q, str::to_uppercase).len()
    }
}

// The disclosed over-refusal: `str::to_owned` is key-equivalent (never panics).
#[cfg(gio_to_owned)]
pub fn gio_to_owned(set: &mut HashSet<String>, q: &str) -> usize {
    //[gio_to_owned]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::gio_to_owned`
    set.get_or_insert_with(q, str::to_owned).len()
}

// ---- 2. with_capacity_and_hasher_in ----

#[cfg(any(wcah_in_map, wcah_in_map_opt))]
pub fn wcah_in_map(n: usize) -> usize {
    //[wcah_in_map]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_map`
    //[wcah_in_map_opt]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_map`
    let m: HashMap<u64, u64, RandomState, std::alloc::Global> =
        HashMap::with_capacity_and_hasher_in(n, RandomState::new(), std::alloc::Global);
    m.len()
}

#[cfg(any(wcah_in_set, wcah_in_set_o3))]
pub fn wcah_in_set(n: usize) -> usize {
    //[wcah_in_set]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_set`
    //[wcah_in_set_o3]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_set`
    let s: HashSet<u64, RandomState, std::alloc::Global> =
        HashSet::with_capacity_and_hasher_in(n, RandomState::new(), std::alloc::Global);
    s.len()
}

#[cfg(wcah_in_system)]
pub fn wcah_in_system(n: usize) -> usize {
    //[wcah_in_system]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_system`
    let m: HashMap<u32, u32, RandomState, std::alloc::System> =
        HashMap::with_capacity_and_hasher_in(n, RandomState::new(), std::alloc::System);
    m.len()
}

#[cfg(wcah_in_guard)]
pub fn wcah_in_guard(n: usize) -> usize {
    //[wcah_in_guard]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::wcah_in_guard`
    if n > (1usize << 59) {
        return 0;
    }
    let m: HashMap<u64, u64, RandomState, std::alloc::Global> =
        HashMap::with_capacity_and_hasher_in(n, RandomState::new(), std::alloc::Global);
    m.len()
}

// ---- 3. Iterator::collect_into ----

#[cfg(any(collect_into_set, collect_into_set_opt))]
pub fn collect_into_set(s: &mut HashSet<u64>, n: usize) -> usize {
    //[collect_into_set]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::collect_into_set`
    //[collect_into_set_opt]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::collect_into_set`
    std::iter::repeat(1u64).take(n).collect_into(s).len()
}

#[cfg(collect_into_map)]
pub fn collect_into_map(m: &mut HashMap<u32, u32>, n: usize) -> usize {
    //[collect_into_map]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::collect_into_map`
    std::iter::repeat((1u32, 1u32)).take(n).collect_into(m).len()
}

#[cfg(collect_into_range)]
pub fn collect_into_range(s: &mut HashSet<u64>, n: u64) -> usize {
    //[collect_into_range]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::collect_into_range`
    (0..n).collect_into(s).len()
}

// The `Vec` twin: a pre-existing false accept on main, closed by the same sink.
#[cfg(collect_into_vec)]
pub fn collect_into_vec(v: &mut Vec<u64>, n: usize) -> usize {
    //[collect_into_vec]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::collect_into_vec`
    std::iter::repeat(1u64).take(n).collect_into(v).len()
}

// ---- 4. the table element is (K, V), not K ----

#[cfg(any(map_wc_large_value, map_wc_large_value_opt))]
pub fn map_wc_large_value(n: usize) -> usize {
    //[map_wc_large_value]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::map_wc_large_value`
    //[map_wc_large_value_opt]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::map_wc_large_value`
    if n >= (1 << 20) {
        return 0;
    }
    HashMap::<u8, [u8; 1 << 50]>::with_capacity(n).len()
}

#[cfg(map_wcah_large_value)]
pub fn map_wcah_large_value(n: usize) -> usize {
    //[map_wcah_large_value]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::map_wcah_large_value`
    if n >= (1 << 20) {
        return 0;
    }
    HashMap::<u8, [u8; 1 << 50], RandomState>::with_capacity_and_hasher(n, RandomState::new()).len()
}

// ---- 5. bucket inflation of a constant count ----

#[cfg(any(set_wc_const, set_wc_const_o3))]
pub fn set_wc_const() -> usize {
    //[set_wc_const]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::set_wc_const`
    //[set_wc_const_o3]~^^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::set_wc_const`
    HashSet::<[u8; 1 << 50]>::with_capacity(4097).len()
}

#[cfg(map_wc_const)]
pub fn map_wc_const() -> usize {
    //[map_wc_const]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::map_wc_const`
    HashMap::<[u8; 1 << 50], u8>::with_capacity(4097).len()
}

// ---- 6. the constant-count bucket bound through a trait sink ----
//
// `extend_reserve` (nightly `extend_one`) of a constant 4097 on a `2^50`-byte table:
// `4097 * 2^50 < isize::MAX`, so only the bucket-layout bound charges it. It holds no
// element value. (Round 2's other candidates — `collect` / `from_iter` / `extend` /
// `unzip` / tuple `extend` of `[0u8; 1 << 50]` values — are deliberately NOT here: a
// literal of that size makes the compiler itself allocate tens of GB before the
// verifier runs, measured 2026-09-28: killed at 24.5 GB RSS and still growing.)
#[cfg(extend_reserve_const)]
pub fn extend_reserve_const(s: &mut HashSet<[u8; 1 << 50]>) {
    //[extend_reserve_const]~^ ERROR Trust strict verification failed for `hashmap_key_equivalence_and_bucket_layout_refused::extend_reserve_const`
    <HashSet<[u8; 1 << 50]> as Extend<[u8; 1 << 50]>>::extend_reserve(s, 4097)
}
