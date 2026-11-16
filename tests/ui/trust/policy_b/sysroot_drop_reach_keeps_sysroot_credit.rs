//@ needs-trust-verify
//@ aux-build: sysroot_drop_reach_dep.rs
//@ revisions: box_u32 rc_u32 arc_u32 rc_string option_box hash_map
//@ revisions: rc_dep_plain box_dep_named mutex_guard rwlock_read_guard
//@ revisions: rwlock_write_guard option_box_global hash_map_box_u32
//@ revisions: vec_u8_strict string_strict vec_dep_plain_strict btree_map_strict
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on -Ztrust-verify-output=json --error-format=human
//@ compile-flags: -Copt-level=0 --crate-type lib
//@[box_u32] compile-flags: -Ztrust-policy=certify
//@[rc_u32] compile-flags: -Ztrust-policy=certify
//@[arc_u32] compile-flags: -Ztrust-policy=certify
//@[rc_string] compile-flags: -Ztrust-policy=certify
//@[option_box] compile-flags: -Ztrust-policy=certify
//@[hash_map] compile-flags: -Ztrust-policy=certify
//@[rc_dep_plain] compile-flags: -Ztrust-policy=certify
//@[box_dep_named] compile-flags: -Ztrust-policy=certify
//@[mutex_guard] compile-flags: -Ztrust-policy=certify
//@[rwlock_read_guard] compile-flags: -Ztrust-policy=certify
//@[rwlock_write_guard] compile-flags: -Ztrust-policy=certify
//@[option_box_global] compile-flags: -Ztrust-policy=certify
//@[hash_map_box_u32] compile-flags: -Ztrust-policy=certify
//@[vec_u8_strict] compile-flags: -Ztrust-policy=strict
//@[string_strict] compile-flags: -Ztrust-policy=strict
//@[vec_dep_plain_strict] compile-flags: -Ztrust-policy=strict
//@[btree_map_strict] compile-flags: -Ztrust-policy=strict
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@[box_u32] check-pass
//@[rc_u32] check-pass
//@[arc_u32] check-pass
//@[rc_string] check-pass
//@[option_box] check-pass
//@[hash_map] check-pass
//@[rc_dep_plain] check-pass
//@[box_dep_named] check-pass
//@[mutex_guard] check-fail
//@[rwlock_read_guard] check-fail
//@[rwlock_write_guard] check-fail
//@[option_box_global] check-pass
//@[hash_map_box_u32] check-pass
//@[vec_u8_strict] check-pass
//@[string_strict] check-pass
//@[vec_dep_plain_strict] check-pass
//@[btree_map_strict] check-pass
//! (2026-10-02) Each control but `mutex_guard` can free memory when it drops its
//! value (the allocator walk reaches `__rust_dealloc` from each, from `RwLock`'s
//! unlock path too), so in this rlib it also
//! carries the allocator premise row (`contract:global-alloc-dealloc-panic-free`,
//! DISCHARGED: the final link chooses the global allocator) and is no longer counted
//! verified; an explicit `drop(v)` is a call to `mem::drop`, which the name-keyed
//! drop charge did not see, so origin/main counted these 1 of 1 while a final link
//! whose `dealloc` panics panicked in `drop(v)` (measured on the `box_u32` shape).
//! What this file pins is unchanged: the drop-glue credit is KEPT — the build is
//! `certify`-clean, the panic-freedom row is the one proved row, and the only other
//! row is that premise (the two `RAW` pins per revision below; the summary's
//! `total_unknown` is the JSON's documented legacy aggregate, which counts a
//! skipped row too).
//!
//! The positive control for `sysroot_drop_reaches_dependency_code.rs`: the
//! drop-glue credit that change must KEEP (2026-09-29).
//!
//! Its rule withdraws sysroot drop-glue credit only where the concrete glue can
//! reach code outside the sysroot. A sysroot owner of plain data, of another
//! sysroot owner, or of a DEPENDENCY type with no destructor of its own
//! (`Rc<dep::Plain>`, `Box<dep::Named>`, `Vec<dep::Plain>`) reaches none — a
//! destructor-less type's glue is a compiler shim, not a body — so these stay
//! exactly as they were. The poisoning guards (`MutexGuard`, `RwLockWriteGuard`)
//! reach `std::thread::panicking()`, whose thread-local accessor is an indirect
//! call; it is followed through the constant key rather than refused (see
//! `trust_verify/sysroot_drop_reach.rs`). `RwLockReadGuard` does not poison, so
//! it reaches no accessor: it pins the plain unlock path, not the follow.
//!
//! `option_box_global` and `hash_map_box_u32` pin the total-drop stamp's
//! allocator rule (`sysroot_drop_reach_allocator_behind_owner.rs`): an audited
//! container at `Global` — spelled explicitly, or by default under a stamped
//! owner — keeps the stamp.
//!
//! MEASURED on stage 1 of origin/main `fbb9fa383d2` (m3's debug std) and on the
//! change, identically: every `certify` revision builds exit 0 with
//! `functions_verified` 1 of 1, and every `_strict` revision builds exit 0 with
//! `functions_verified` 0 of 1 (on the change: `runtime_checked` rows, disclosed).
#![cfg_attr(option_box_global, feature(allocator_api))]

extern crate sysroot_drop_reach_dep as rdep;

#[cfg(box_u32)]
pub fn p(t: u8, v: Box<u32>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(rc_u32)]
pub fn p(t: u8, v: std::rc::Rc<u32>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(arc_u32)]
pub fn p(t: u8, v: std::sync::Arc<u32>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(rc_string)]
pub fn p(t: u8, v: std::rc::Rc<String>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(option_box)]
pub fn p(t: u8, v: Option<Box<u32>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(hash_map)]
pub fn p(t: u8, v: std::collections::HashMap<u8, u8>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(rc_dep_plain)]
pub fn p(t: u8, v: std::rc::Rc<rdep::Plain>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(box_dep_named)]
pub fn p(t: u8, v: Box<rdep::Named>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(mutex_guard)]
pub fn p(t: u8, g: std::sync::MutexGuard<'_, u32>) -> u8 {
    // CAPABILITY LOSS, re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
    // "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
    // `drop(g)` of a lock guard now carries the counted panic-freedom aggregate of the call
    // into the bundled body, which the native lane leaves `runtime_checked`; `certify` refuses
    // that row (before, the drop-glue credit left one proved row and the build was clean).
    // Fail-closed: refused, never proved. Flip back to `check-pass` when it returns.
    let c = if t == 0 { 1 } else { 2 };
    drop(g);
    c
}

#[cfg(rwlock_read_guard)]
pub fn p(t: u8, g: std::sync::RwLockReadGuard<'_, u32>) -> u8 {
    // See `mutex_guard` (CAPABILITY LOSS, re-pinned 2026-10-15).
    let c = if t == 0 { 1 } else { 2 };
    drop(g);
    c
}

#[cfg(rwlock_write_guard)]
pub fn p(t: u8, g: std::sync::RwLockWriteGuard<'_, u32>) -> u8 {
    // See `mutex_guard` (CAPABILITY LOSS, re-pinned 2026-10-15).
    let c = if t == 0 { 1 } else { 2 };
    drop(g);
    c
}

#[cfg(option_box_global)]
pub fn p(t: u8, v: Option<Box<u32, std::alloc::Global>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(hash_map_box_u32)]
pub fn p(t: u8, v: std::collections::HashMap<u8, Box<u32>>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(vec_u8_strict)]
pub fn p(t: u8, v: Vec<u8>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(string_strict)]
pub fn p(t: u8, v: String) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(vec_dep_plain_strict)]
pub fn p(t: u8, v: Vec<rdep::Plain>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

#[cfg(btree_map_strict)]
pub fn p(t: u8, v: std::collections::BTreeMap<u8, u8>) -> u8 {
    let c = if t == 0 { 1 } else { 2 };
    drop(v);
    c
}

//[mutex_guard]~? RAW "functions_verified":0,"total_proved":0,"total_failed":0,"total_unknown":0,"total_timed_out":0,"total_skipped":0,"total_runtime_checked":1,"total_obligations":1
//[box_u32,rc_u32,arc_u32,rc_string,option_box,hash_map]~? RAW "total_proved":1,"total_failed":0,"total_unknown":1,"total_timed_out":0,"total_skipped":1,"total_runtime_checked":0,"total_obligations":2
//[box_u32,rc_u32,arc_u32,rc_string,option_box,hash_map]~? RAW "kind":"contract:global-alloc-dealloc-panic-free",
//[rc_dep_plain,box_dep_named]~? RAW "total_proved":1,"total_failed":0,"total_unknown":1,"total_timed_out":0,"total_skipped":1,"total_runtime_checked":0,"total_obligations":2
//[rc_dep_plain,box_dep_named,rwlock_read_guard]~? RAW "kind":"contract:global-alloc-dealloc-panic-free",
//[option_box_global,hash_map_box_u32]~? RAW "total_proved":1,"total_failed":0,"total_unknown":1,"total_timed_out":0,"total_skipped":1,"total_runtime_checked":0,"total_obligations":2
//[rwlock_write_guard,option_box_global,hash_map_box_u32]~? RAW "kind":"contract:global-alloc-dealloc-panic-free",
// CAPABILITY LOSS (certify), re-pinned 2026-10-15 (the merge of 2026-10-14; docs/KNOWN_HAZARDS.md
// "OPEN 2026-10-15 — correct programs the merge of 2026-10-14 refuses", DECISION_QUEUE D103(i)):
// the three lock-guard revisions are refused, on the counted aggregate's `runtime_checked` row
// (see `mutex_guard`'s note above).
//[rwlock_read_guard,rwlock_write_guard]~? RAW "total_proved":0,"total_failed":0,"total_unknown":1,"total_timed_out":0,"total_skipped":1,"total_runtime_checked":1,"total_obligations":2
//[mutex_guard,rwlock_read_guard,rwlock_write_guard]~? RAW error: Trust strict verification failed for `sysroot_drop_reach_keeps_sysroot_credit::p`
