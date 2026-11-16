//@ needs-trust-verify
//@ edition: 2021
//@ revisions: guarded_read guarded_write nonempty collected closure_owner view_len unguarded wrong_vec stale_pop owned_move_alias view_len_wrong range_index
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[guarded_read] check-pass
//@[guarded_write] check-pass
//@[nonempty] check-pass
//@[collected] check-pass
//@[closure_owner] check-fail
//@[view_len] check-pass
//@[unguarded] check-fail
//@[wrong_vec] check-fail
//@[stale_pop] check-fail
//@[owned_move_alias] check-fail
//@[view_len_wrong] check-fail
//@[range_index] check-fail
//! **`v[i]` on a `Vec` (VEC-AS-SLICE, Trust 2026-09-25).**
//!
//! `v[i]` is `<Vec<T> as Index<usize>>::index(&v, i)`. Its bundled body forwards to
//! `<usize as SliceIndex<[T]>>::index`, whose bounds `Assert` reached the root only
//! through that FOREIGN member, so the bundled-member Assert gate refused EVERY
//! bundle that indexed a `Vec` ("refused Assert-bearing transitive member
//! `<usize as SliceIndex<[u32]>>::index` … not owned"). The charge now lives in the
//! caller's own owned-`Vec` index row, which the gate regenerates and matches
//! (`trust_verify/vec_index_forwarder.rs`; premise in docs/TCB.md). That row had
//! itself been silent since `Vec` became `Ty::Seq`; it is live again, and so is its
//! length-stability gate, now asked over the base's whole alias closure.
//!
//! # Before (stage 1 `0.10.0+gb4bc7cdf9`, 2026-09-25)
//!
//! EVERY revision was rc=1 with the same refusal — the six check-pass revisions
//! included: `native TrustIr bundle for … refused Assert-bearing transitive member
//! `<usize as core::slice::index::SliceIndex<[..]>>::index`: no exact direct root
//! call can carry its derived precondition; the site(s) in `<alloc::vec::Vec<..> as
//! core::ops::index::Index<usize>>::index` are not owned`. (`view_len` and
//! `view_len_wrong` index an ARRAY, so theirs was the enumerate row instead:
//! `[bounds] FAILED`, the iterated slice length unrelated to `v.len()`.)
//!
//! # After
//!
//! The check-pass revisions build; each check-fail revision is refused ON ITS
//! BOUNDS ROW (`[slice] FAILED` / `[bounds] FAILED`), never on the gate — a gate
//! refusal here would mean the charge is no longer being matched — except
//! `owned_move_alias` and `stale_pop` (see its own comment), refused on the
//! never-provable `container-index-unstable-len` row. `owned_move_alias` is the
//! hole the alias closure closes: `w = v` moves the `Vec`, `w.clear()` borrows
//! `&mut w` (never `&mut v`), and the index on `w` resolves to `v`'s length.
//! MEASURED with the closure disabled (a temporary env-gated ablation of
//! `guards::base_alias_closure`, same source otherwise): this revision built rc=0,
//! `2 proved`, and `moved_then_cleared(vec![1, 2, 3])` panicked "index out of bounds:
//! the len is 0 but the index is 2". If it ever goes green, treat it as that false
//! accept until shown otherwise.
//! `range_index` (`&v[a..b]`, a different `SliceIndex` impl, not a forwarder) is
//! refused by the range lane's own row, never by the gate: the `Vec` receiver's
//! length is not recovered for a range. Pinned so this change is seen NOT to widen
//! the range index. That row was the always-violated `Bool(true)` as a refutable
//! `[slice] FAILED`, an arbitrary model on a GUARDED index (`a <= b && b <=
//! v.len()`, which does not panic). Since RANGE-DECLINE (docs/DECISION_QUEUE.md,
//! `c888f21ea31`) it is the declined UNKNOWN `slice-range-len-unresolved`, which
//! strict counts as a build error; re-pinned 2026-10-13 (RANGE-DECLINE-UI-REPIN).
//!
//! RE-PINNED 2026-10-15 (the merge of 2026-10-14): `guarded_read`, `guarded_write` and
//! `nonempty` now read `1 proved ... 0 runtime-checked out of 1` (measured on the merged
//! stage 1): the bundled std index member that carried the `runtime_checked` row is no
//! longer in their bundle, so the forwarded charge is the only row and it is proved.

#[cfg(guarded_read)]
pub fn get(v: &Vec<u32>, i: usize) -> u32 {
    //[guarded_read]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if i < v.len() { v[i] } else { 0 }
}

#[cfg(guarded_write)]
pub fn set(v: &mut Vec<u32>, i: usize, x: u32) {
    //[guarded_write]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if i < v.len() {
        v[i] = x;
    }
}

#[cfg(nonempty)]
pub fn first(v: &Vec<u32>) -> u32 {
    //[nonempty]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    if !v.is_empty() { v[0] } else { 0 }
}

#[cfg(collected)]
pub fn outer_len(s: &str) -> usize {
    //[collected]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
    let parts: Vec<&str> = s.split(',').collect();
    if parts.len() != 3 {
        return 0;
    }
    parts[0].len() + parts[2].len()
}

// PINNED PRECISION COST (CALL-HAVOC-ESCAPE-2, 2026-10-06; docs/KNOWN_HAZARDS.md): the
// closure reads `v` through its captured reference `(*_1).0`, a reference STORED IN
// MEMORY (the closure's own field), never retagged. Every call now havocs the memory
// behind such a reference, and the `Vec` (with its length, named on `_1*.0`) is behind
// it, so `j < v.len()` does not survive the `len` call into the index. This was
// `1 proved, 0 failed, .., 1 runtime-checked` and check-pass before; it flips back only
// with a reviewed argument that a closure's capture cannot carry raw-pointer bits.
#[cfg(closure_owner)]
pub fn via_closure(v: &Vec<u32>, i: usize) -> u32 {
    let get = |j: usize| if j < v.len() { v[j] } else { 0 };
    //[closure_owner]~^ NOTE [slice] FAILED
    get(i)
}

// The deref'd slice's length IS the `Vec`'s: `i < 3` from `parts.len() == 3`.
#[cfg(view_len)]
pub fn fill(s: &str) -> u32 {
    //[view_len]~^ NOTE Trust verification: 3 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 5 obligation(s)
    let parts: Vec<&str> = s.split('.').collect();
    if parts.len() != 3 {
        return 0;
    }
    let mut nums = [0u32; 3];
    for (i, p) in parts.iter().enumerate() {
        nums[i] = p.len() as u32;
    }
    nums[0]
}

#[cfg(unguarded)]
pub fn get_any(v: &Vec<u32>, i: usize) -> u32 {
    //[unguarded]~^ NOTE [slice] FAILED
    v[i]
}

#[cfg(wrong_vec)]
pub fn get_other(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> u32 {
    //[wrong_vec]~^ NOTE [slice] FAILED
    if i < a.len() { b[i] } else { 0 }
}

// The index row, refused fail-honest (VEC-LEN-PARAM-COPY-1, `192c1c23d2`, 2026-10-07):
// `v.pop()` is `Vec::pop(copy _1)`, so the length oracle answers "may resize" and the
// row is the never-provable `container-index-unstable-len` (`Bool(true)`), not a
// `[slice]` row over a length the pop has changed. The `[slice] FAILED` this pinned
// until then was a row over a length the oracle wrongly called stable across the pop
// (it saw no `&mut (*_1)` reborrow), refuted by the call havoc of the `&mut` parameter
// alone; that havoc also "refuted" an in-bounds twin (`opaque_then_rw`). A model of
// `pop`'s new length would win the refutation back; it is not taken (DECISION_QUEUE
// VEC-LEN-PARAM-COPY-1, VEC-POP-REPIN-1).
// What this revision pins: refused on the index row, never accepted, never proved.
#[cfg(stale_pop)]
pub fn last_after_pop(v: &mut Vec<u32>) -> u32 {
    //[stale_pop]~^ NOTE unsupported MIR `container-index-unstable-len`
    let n = v.len();
    v.pop();
    if n > 0 { v[n - 1] } else { 0 }
}

#[cfg(owned_move_alias)]
pub fn moved_then_cleared(v: Vec<u32>) -> u32 {
    //[owned_move_alias]~^ NOTE unsupported MIR `container-index-unstable-len`
    let n = v.len();
    let mut w = v;
    w.clear();
    if n > 0 { w[n - 1] } else { 0 }
}

// Four parts, a three-slot array: `i == 3` is reachable.
#[cfg(view_len_wrong)]
pub fn fill_short(s: &str) -> u32 {
    //[view_len_wrong]~^ NOTE [bounds] FAILED
    let parts: Vec<&str> = s.split('.').collect();
    if parts.len() != 4 {
        return 0;
    }
    let mut nums = [0u32; 3];
    for (i, p) in parts.iter().enumerate() {
        nums[i] = p.len() as u32;
    }
    nums[0]
}

#[cfg(range_index)]
pub fn window(v: &Vec<u32>, a: usize, b: usize) -> usize {
    //[range_index]~^ NOTE unsupported MIR `slice-range-len-unresolved`
    if a <= b && b <= v.len() { v[a..b].len() } else { 0 }
}
