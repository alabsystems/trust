//@ revisions: hashmap_eq_bad_hasher hashset_eq_bad_hasher
//@ revisions: vec_clone_ref_bomb_alloc vec_clone_ref_bomb_alloc_certify
//@ revisions: hashmap_get_dep_query
//@ revisions: option_eq_dep_payload option_eq_dep_payload_certify
//@ revisions: collect_string_dealloc_bomb collect_string_dealloc_bomb_certify
//@ revisions: hashmap_entry_global_dep_value
//@ revisions: option_unwrap_dep_payload hashmap_len_dep_value vec_pop_dep_elem
//@ revisions: hashmap_get_insert_dep_value hashmap_entry_string_global hashmap_entry_string_global_release_std
//@ needs-trust-verify
//@ edition: 2021
//@ aux-build: sysroot_call_reach_unverified_dep.rs
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[vec_clone_ref_bomb_alloc_certify] compile-flags: -Ztrust-policy=certify
//@[option_eq_dep_payload_certify] compile-flags: -Ztrust-policy=certify
//@[collect_string_dealloc_bomb_certify] compile-flags: -Ztrust-policy=certify
//@[hashmap_eq_bad_hasher] check-fail
//@[hashset_eq_bad_hasher] check-fail
//@[vec_clone_ref_bomb_alloc] check-fail
//@[vec_clone_ref_bomb_alloc_certify] check-fail
//@[hashmap_get_dep_query] check-fail
//@[option_eq_dep_payload] check-fail
//@[option_eq_dep_payload_certify] check-fail
//@[collect_string_dealloc_bomb] check-fail
//@[collect_string_dealloc_bomb_certify] check-fail
//@[hashmap_entry_global_dep_value] check-fail
//@[option_unwrap_dep_payload] check-pass
//@[hashmap_len_dep_value] check-pass
//@[vec_pop_dep_elem] check-pass
//@[hashmap_get_insert_dep_value] check-pass
//@[hashmap_entry_string_global] check-pass
//@[hashmap_entry_string_global] needs-std-debug-assertions (pinned by `hashmap_entry_string_global_release_std`)
//@[hashmap_entry_string_global_release_std] check-fail
//@[hashmap_entry_string_global_release_std] ignore-std-debug-assertions (pinned by `hashmap_entry_string_global`)
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! CALL-REACH-1 phase 1 and the interim H1-H3 stopgaps (docs/DECISION_QUEUE.md
//! CALL-REACH-1; design: docs/design/2026-10-10-call-reach-1-instance-type-arguments.md).
//! MEASURED 2026-10-10 on stage 1 with the D1-D5 amendments (design, "Amendment
//! (2026-10-10, measured)"): every revision below as annotated, and each check-fail
//! revision's refusal is the deny arm's own (`TRUST_CALL_REACH_DEBUG=1` prints its
//! `[CALL_REACH_DENY]` line naming the dependency body reached).
//!
//! An absent sysroot callee is credited by many lanes on one belief, "a sysroot
//! callee runs only sysroot code". That belief is about the sysroot's code, not about
//! the code the call's TYPE ARGUMENTS choose, which the std body then runs inside the
//! credited call. Each shape below credits such a call today (design §2.1, read, not
//! measured), and the auxiliary's code panics inside it once armed:
//!
//!  * H1 (`hashmap_eq_bad_hasher`, `hashset_eq_bad_hasher`): `a == b` on a hash
//!    collection at `BuildHasherDefault<dep::BadHasher>`. The extractor's PartialEq
//!    sentinel (`tcx_derived_trait_is_total`) asked the key and value, never the
//!    hasher, though `eq` calls `other.get(k)` for every entry. Closed by the interim
//!    stopgap (`hasher_ty_is_sysroot_throughout` and
//!    `audited_container_allocators_are_sysroot` in that arm); the call then reaches
//!    the bridge, where CALL-REACH-1's deny arm also withdraws it.
//!  * H2 (`vec_clone_ref_bomb_alloc`, `_certify`): `<Vec<u8, &'static
//!    dep::BombAlloc> as Clone>::clone`. `tcx_clone_is_total` asked the allocator's
//!    CLONE (a `&A` passed outright), not whether its `allocate` runs dependency code.
//!    Closed by the interim stopgap (`audited_container_allocators_are_sysroot` in its
//!    container arms).
//!  * H3 (`hashmap_get_dep_query`): `HashMap<u32, u8>::get(&q)` with `q: dep::Q`,
//!    whose `Hash` panics, through the dependency's orphan-legal `impl Borrow<Q> for
//!    u32`. The hash-query sentinel read the impl's `K`, `S` and `A`, never the
//!    method's own `Q`. Closed by the interim stopgap (`Q` must be `K` or a
//!    `tcx_key_is_std_total` key).
//!  * H4 (`option_eq_dep_payload`, `_certify`): `a == b` on `Option<dep::Bomb>`, whose
//!    `eq` panics. The bridge models the tags (`eq_unit_variant_model_plan`) and
//!    credits the payload's `eq`. Closed by CALL-REACH-1 phase 1: the compiler's
//!    call-reach walk reaches `<dep::Bomb as PartialEq>::eq` and the bridge's deny arm,
//!    at the head of its call chain, withdraws every credit for the call.
//!  * H5 (`collect_string_dealloc_bomb`, `_certify`): `v.iter().map(|&x|
//!    dep::mk(x)).collect::<String>()`, where `mk` returns `Box<str, dep::DeallocBomb>`
//!    and `String: FromIterator<Box<str, A>>` drops every item. Closed by phase 1 with
//!    amendment (a): the type walk now asks a local closure's SIGNATURE, so the
//!    pre-filter no longer holds the call, and the walk reaches
//!    `DeallocBomb::deallocate`. Its refusal may be the generic "Trust strict
//!    verification failed" or the closure-driving consumer's "Trust full verification
//!    failed", so its annotation names only the common part.
//!
//! COST (phase 1; owed to phase 2), RE-PINNED 2026-10-13 after the 2026-10-10 control
//! claim did not reproduce: `hashmap_entry_global_dep_value`, `HashMap<String,
//! dep::Plain>::entry` + `Entry::or_insert` at std's `Global` allocator and `RandomState`.
//! It runs no `Plain` code on any path, but the default policy refuses it, and NOT
//! through CALL-REACH-1: the walk closes both root calls (`[CALL_REACH] closed(walk)`, no
//! `[CALL_REACH_DENY]`). std's `HashMap::entry` and `Entry::or_insert` are bundle
//! members, so the C2 std-map stamp (which fires only in the bridge's absent-callee arm
//! on the ROOT call) is never consulted. Their bodies' calls into hashbrown
//! (`rustc_entry::<.., dep::Plain, RandomState>` and `RustcVacantEntry::insert`) are
//! absent, and policy B tolerates an absent callee only at foundational type arguments;
//! `dep::Plain` is a dependency's type, so each row is NOT-VANILLA and the generic
//! absent-callee assumption-panic row keeps `add_dep` fail-closed. MEASURED 2026-10-13
//! (`TRUST_VANILLA_DEBUG=1`): the same refusal and the same NOT-VANILLA rows on five
//! stage 1s of one machine, two of them older than CALL-REACH-1 (preview2, 2026-10-05;
//! preview3 `ed578e1a5`), then preview4 `35a39d5c74`, preview5 `9fb13bb9e8` and main
//! `825437bfeb`. The "did not occur" measurement of `a33353a38a` does not reproduce
//! (docs/DECISION_QUEUE.md CALL-REACH-1-ENTRY-COST). Phase 2's closed-world walk is the
//! recorded recovery; if this revision starts to build, find WHICH lane credited it
//! before flipping it back to `check-pass`.
//!
//! CONTROLS that must stay accepted (the type rule flags each, the walk clears it):
//! `option_unwrap_dep_payload` (`Option<dep::Plain>::unwrap` behind a `Some` guard: the
//! model arm keeps its proof), `hashmap_len_dep_value` (`HashMap<u32, dep::Plain>::len`,
//! the F5 table), `vec_pop_dep_elem` (`Vec<dep::Plain>::pop`, EXACT_TOTAL),
//! `hashmap_get_insert_dep_value` (`get`/`insert` at `Global` and `RandomState`, the
//! SP-1 sentinel, unchanged), and `hashmap_entry_string_global` (`HashMap<String,
//! u32>::entry`, the `Inventory::add` shape: sysroot types only, so the pre-filter
//! holds it and nothing is walked).
//!
//! NOT HERE: H6 (a by-value hash source's hasher drop) is pinned in
//! `collect_extend_source_side_drops.rs` (`hash_map_hasher`, `hash_set_hasher`, whose
//! auxiliary's hasher builder has a `Drop` of its own), stopgapped by
//! SOURCE-SIDE-DROP-CERTIFY-1 until phase 2. A local `unsafe impl Allocator` control is
//! not possible: UNSAFE-IMPL-PROMISE-1 refuses such a crate as a whole.
//!
//! Ordinary Rust programs: the auxiliary is a plain verify-off dependency
//! (`auxiliary/sysroot_call_reach_unverified_dep.rs`); this crate names its
//! allocator-carrying types only through aliases and constructors, so it needs no
//! feature gate.

extern crate sysroot_call_reach_unverified_dep as dep;

#[allow(unused_imports)]
use std::collections::{HashMap, HashSet};

// ---- H1: hash-collection equality hashes through the hasher ----

#[cfg(hashmap_eq_bad_hasher)]
pub fn eq_map_bh(a: &HashMap<u32, u8, dep::BadBuild>, b: &HashMap<u32, u8, dep::BadBuild>) -> bool {
    //[hashmap_eq_bad_hasher]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::eq_map_bh`
    a == b
}

#[cfg(hashset_eq_bad_hasher)]
pub fn eq_set_bh(a: &HashSet<u32, dep::BadBuild>, b: &HashSet<u32, dep::BadBuild>) -> bool {
    //[hashset_eq_bad_hasher]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::eq_set_bh`
    a == b
}

// ---- H2: `Clone` allocates through the allocator behind a `&'static` ----

#[cfg(any(vec_clone_ref_bomb_alloc, vec_clone_ref_bomb_alloc_certify))]
pub fn clone_bv(v: &dep::BombVec) -> dep::BombVec {
    //[vec_clone_ref_bomb_alloc,vec_clone_ref_bomb_alloc_certify]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::clone_bv`
    v.clone()
}

// ---- H3: a hash query's own type argument ----

#[cfg(hashmap_get_dep_query)]
pub fn get_q(m: &HashMap<u32, u8>, q: &dep::Q) -> Option<u8> {
    //[hashmap_get_dep_query]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::get_q`
    m.get(q).copied()
}

// ---- H4: `Option == Option` runs the payload's `eq` ----

#[cfg(any(option_eq_dep_payload, option_eq_dep_payload_certify))]
pub fn eq_opt_bomb(a: &Option<dep::Bomb>, b: &Option<dep::Bomb>) -> bool {
    //[option_eq_dep_payload,option_eq_dep_payload_certify]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::eq_opt_bomb`
    a == b
}

// ---- H5: `collect` drops what its destination's `from_iter` is handed ----

#[cfg(any(collect_string_dealloc_bomb, collect_string_dealloc_bomb_certify))]
pub fn collect_mk(v: &[u8]) -> String {
    //[collect_string_dealloc_bomb,collect_string_dealloc_bomb_certify]~^ ERROR verification failed for `sysroot_call_reach_type_arguments::collect_mk`
    v.iter().map(|&x| dep::mk(x)).collect()
}

// ---- cost: C2 at `Global` with a dependency value type (refused; phase 2 owes it) ----

#[cfg(hashmap_entry_global_dep_value)]
pub fn add_dep(m: &mut HashMap<String, dep::Plain>, item: &str, qty: u32) {
    //[hashmap_entry_global_dep_value]~^ ERROR Trust strict verification failed for `sysroot_call_reach_type_arguments::add_dep`
    let e = m.entry(item.to_string()).or_insert(dep::Plain(0));
    e.0 = e.0.saturating_add(qty);
}

// ---- controls that stay accepted: a dependency type that is only moved ----

#[cfg(option_unwrap_dep_payload)]
pub fn unwrap_dep(o: Option<dep::Plain>) -> u32 {
    if let Some(_) = o { o.unwrap().0 } else { 0 }
}

#[cfg(hashmap_len_dep_value)]
pub fn len_dep(m: &HashMap<u32, dep::Plain>) -> usize {
    m.len()
}

#[cfg(vec_pop_dep_elem)]
pub fn pop_dep(v: &mut Vec<dep::Plain>) -> Option<dep::Plain> {
    v.pop()
}

#[cfg(hashmap_get_insert_dep_value)]
pub fn get_dep(m: &HashMap<u32, dep::Plain>, k: &u32) -> Option<dep::Plain> {
    m.get(k).copied()
}

#[cfg(hashmap_get_insert_dep_value)]
pub fn insert_dep(m: &mut HashMap<u32, dep::Plain>, k: u32, v: dep::Plain) -> Option<dep::Plain> {
    m.insert(k, v)
}

#[cfg(any(hashmap_entry_string_global, hashmap_entry_string_global_release_std))]
pub fn add(m: &mut HashMap<String, u32>, item: &str, qty: u32) {
    // CAPABILITY RETURNED 2026-10-18 (the 1.101 toolchain migration), lane
    // identified before flipping (the header's instruction): hashbrown 0.17
    // routes `entry` through `hashbrown::rustc_entry`, which the bundler
    // declines, so the body publishes one runtime-checked absent-callee row
    // for it — vanilla sysroot at foundational types (`String`, `u32`,
    // `RandomState`, `Global`), reported and built under the default
    // policy, NOT a zero-row mint (the zero-obligation gate still answers
    // NONE for the `entry` call itself). The 2026-10-15 D103(i) refusal was
    // the bundled-bodies shape: zero rows, gate refuses.
    let e = m.entry(item.to_string()).or_insert(0);
    *e = e.saturating_add(qty);
}
