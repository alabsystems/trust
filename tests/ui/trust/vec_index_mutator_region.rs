//@ needs-trust-verify
//@ edition: 2021
//@ revisions: rotate insert_sorted remove_guarded insert_guarded owned_local unguarded off_by_one pop_first remove_twice other_vec search_other_vec helper_clear
//@ revisions: twophase_push_then_remove twophase_truncate twophase_insert twophase_is_empty twophase_as_slice twophase_retain twophase_trait_method twophase_tuple_def
//@ revisions: twophase_break_out twophase_returned_ref twophase_compound_assign
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: ERROR
//@[rotate] check-pass
//@[insert_sorted] check-pass
//@[remove_guarded] check-pass
//@[insert_guarded] check-pass
//@[owned_local] check-pass
//@[unguarded] check-fail
//@[off_by_one] check-fail
//@[pop_first] check-fail
//@[remove_twice] check-fail
//@[other_vec] check-fail
//@[search_other_vec] check-fail
//@[helper_clear] check-fail
//@[twophase_push_then_remove] check-pass
//@[twophase_truncate] check-fail
//@[twophase_insert] check-fail
//@[twophase_is_empty] check-fail
//@[twophase_as_slice] check-fail
//@[twophase_retain] check-fail
//@[twophase_trait_method] check-fail
//@[twophase_tuple_def] check-fail
//@[twophase_break_out] check-fail
//@[twophase_returned_ref] check-fail
//@[twophase_compound_assign] check-fail
//! (2026-10-02) The "1 skipped" in a summary below is the allocator premise this
//! rlib's allocating functions now carry (`contract:global-alloc-dealloc-panic-free`,
//! DISCHARGED: the final link chooses the global allocator; see
//! `policy_b/global_allocator_is_chosen_by_the_final_link.rs`). It is not this file's
//! subject; every other count is unchanged.
//!
//! **`Vec::{remove, swap_remove, insert}` inside the base's pre-mutation region
//! (VEC-INSERT, Trust 2026-09-25).**
//!
//! The index mutators panic on `i >= len` (`i > len` for `insert`). Their call row
//! was an unconditional `UnsupportedMir` ("vec-panic-method-index-unmodeled" /
//! "Call::remove::panic-freedom-unverified") that no guard could discharge, and the
//! compiler refused the callee as "panics on a caller-supplied value". vcgen now
//! states the real precondition over `L0`, the base's length on entry to its
//! pre-mutation region (`trust-vcgen/src/generate/vec_region.rs`), and the compiler
//! drops the caller-value exclusion at exactly the charged call block
//! (`def_is_std_vec_index_mutator`). See docs/TCB.md.
//!
//! # Before (stage 1 `0.10.0+gb4bc7cdf9`, 2026-09-25)
//!
//! Every revision was rc=1. The check-pass ones were refused on the unconditional
//! row, measured on `rotate` (sweep `t22`): `unsupported MIR
//! `Call::remove::panic-freedom-unverified``, and `[VANILLA_ROW] tolerated=false
//! NOT-VANILLA callee=`alloc::vec::Vec::<u32>::remove``.
//!
//! # After
//!
//! The check-pass revisions build. Each check-fail revision is refused on its own
//! row: the index precondition `[slice] FAILED` where the region reaches the call,
//! and the old unconditional row where it does not (`pop_first`, `remove_twice`,
//! `helper_clear`: a mutation of the base precedes the call on some path).
//!
//! # The definition block's two-phase reservation (W4 fix round 3, 2026-09-29)
//!
//! The `twophase_*` check-fail revisions are adversarial round r2's false accepts
//! (probes v2p01, v2p05, v2p06, v2p09, v2p12, x04, x08). Each takes a two-phase autoref
//! `&mut v` in `v`'s DEFINITION block (`v.truncate({ black_box(0); k = v.len(); 0 })`),
//! reads the length inside the argument after a block split, and then indexes by the
//! PRE-shrink length. The definition block was exempt from the region's taint as a
//! whole, and the activating call names only the reservation temp, so `k == L0` was
//! minted at the pre-shrink length. Every one built rc=0 on stage 1
//! `0.10.0+g81274d5b9` (snapshot snap-w4g-vecslice-r2), with the mutator's
//! `SliceBoundsCheck` PROVED, and panicked (`f(vec![1, 2, 3], 1)`: "removal index (is
//! 1) should be < len (is 0)"). After the fix, the blocks between the reservation and
//! its activation are outside the region, so no length fact is minted there: the
//! mutator is still charged after a single activation, and with no fact to relate `k`
//! to `L0` it is `[slice] FAILED` (measured on stage 1 `0.10.0+ga1032a22f`).
//! `twophase_push_then_remove` is the control: `v.push(v.len() as u32)`, then a guarded
//! remove, still builds, because the region resumes after the single activation.
//! `twophase_break_out`, `twophase_returned_ref` and `twophase_compound_assign` are the
//! fixer's own probes of that rule (r3 self-probes a02, a04, a05), each also rc=0 with
//! the remove proved on `0.10.0+g81274d5b9`: a labeled `break` out of the reservation's
//! argument skips the activation on one path (that path stays outside the region); the
//! activation returns `&mut Self` and the base is cleared through it (the returned
//! borrow is followed, so the activation is not the last use); and a two-phase
//! compound assignment (`v += Wipe(..)`, a local `AddAssign` that clears).
//!
//! # Only a sysroot inherent callee resumes the region (VEC-REGION-DEF-BLOCK-STASH-1, 2026-10-13)
//!
//! An activation (or any call handed the definition block's borrow) is now credited
//! with keeping no alias of `v` past its return only when it is a sysroot inherent
//! callee handed only references to `v` and otherwise pointer-free data
//! (`vec_region::call_cannot_retain_borrow`, `call_args_admit_no_alias`); any other
//! callee leaves NO region for `v`. `twophase_trait_method` (a local trait method),
//! `twophase_compound_assign` (`<Vec<u32> as AddAssign<Wipe>>::add_assign`, a user impl
//! under core's trait `DefId`) and `twophase_retain` (`Vec::retain` handed a closure) lose
//! the region, so their `remove` is no longer charged and each is refused on the old
//! unconditional row instead of `[slice] FAILED`: still check-fail, by a different row.
//! Measured at the trust-vcgen level on their MIR dumped by `scratchpad/stage1-w25f`
//! (`vec_mutator_charged_blocks`: `[bb4]` before, `[]` after); the compiler-level row is
//! predicted, not built in the lane. `twophase_returned_ref` was already uncharged; it
//! loses only a true fact in its window. Every other revision is unchanged.

#[cfg(rotate)]
pub fn rot(v: &mut Vec<u32>) {
    //[rotate]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if !v.is_empty() {
        let f = v.remove(0);
        v.push(f);
    }
}

#[cfg(insert_sorted)]
pub fn insert_sorted(v: &mut Vec<i64>, value: i64) -> bool {
    //[insert_sorted]~^ NOTE Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 4 obligation(s)
    match v.binary_search(&value) {
        Ok(_) => false,
        Err(pos) => {
            v.insert(pos, value);
            true
        }
    }
}

#[cfg(remove_guarded)]
pub fn take(v: &mut Vec<u32>, i: usize) -> u32 {
    //[remove_guarded]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 1 obligation(s)
    // Re-pinned 2026-10-15 (the merge of 2026-10-14): one row, proved and kernel-certified. The
    // guarded `remove` is the sole-resize precondition row (`i < len`), the only way
    // `Vec::remove` panics; its body is no longer bundled, so the runtime-checked member row
    // it owed is gone with it.
    if i < v.len() { v.remove(i) } else { 0 }
}

#[cfg(insert_guarded)]
pub fn put(v: &mut Vec<u32>, i: usize, x: u32) {
    //[insert_guarded]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    if i <= v.len() {
        v.insert(i, x);
    }
}

#[cfg(owned_local)]
pub fn tail_len(xs: &[u32]) -> usize {
    //[owned_local]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let mut v = xs.to_vec();
    if !v.is_empty() {
        v.swap_remove(0);
    }
    v.len()
}

#[cfg(unguarded)]
pub fn take_any(v: &mut Vec<u32>, i: usize) -> u32 {
    //[unguarded]~^ NOTE [slice] FAILED
    v.remove(i)
}

#[cfg(off_by_one)]
pub fn take_upto(v: &mut Vec<u32>, i: usize) -> u32 {
    //[off_by_one]~^ NOTE [slice] FAILED
    if i <= v.len() { v.remove(i) } else { 0 }
}

// `pop` shrinks the base before the call: the call is outside the region.
#[cfg(pop_first)]
pub fn pop_then_remove(v: &mut Vec<u32>) {
    //[pop_first]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    if !v.is_empty() {
        v.pop();
        v.remove(0);
    }
}

#[cfg(remove_twice)]
pub fn remove_twice(v: &mut Vec<u32>) {
    //[remove_twice]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    if v.len() >= 2 {
        v.remove(1);
        v.remove(1);
    }
}

#[cfg(other_vec)]
pub fn take_other(a: &Vec<u32>, b: &mut Vec<u32>, i: usize) -> u32 {
    //[other_vec]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    // Since DECISION_QUEUE D101 (2026-10-15) an `&mut Vec` parameter beside another
    // argument that is not a pure value (here a `&Vec`) gets no `Vec` region, so the
    // call keeps the fail-honest Unknown instead of the region's refuted row: still
    // refused, no longer refuted (measured on the stage 1 of that change).
    if i < a.len() { b.remove(i) } else { 0 }
}

#[cfg(search_other_vec)]
pub fn insert_elsewhere(a: &Vec<i64>, b: &mut Vec<i64>, x: i64) {
    //[search_other_vec]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    // Since DECISION_QUEUE D101 (2026-10-15) an `&mut Vec` parameter beside another
    // argument that is not a pure value (here a `&Vec`) gets no `Vec` region, so the
    // call keeps the fail-honest Unknown instead of the region's refuted row: still
    // refused, no longer refuted (measured on the stage 1 of that change).
    match a.binary_search(&x) {
        Ok(_) => {}
        Err(p) => b.insert(p, x),
    }
}

#[cfg(helper_clear)]
fn shrink(v: &mut Vec<u32>) {
    v.clear()
}

#[cfg(helper_clear)]
pub fn cleared_then_removed(v: &mut Vec<u32>) {
    //[helper_clear]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    if !v.is_empty() {
        shrink(v);
        v.remove(0);
    }
}

#[cfg(twophase_push_then_remove)]
pub fn push_len_then_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_push_then_remove]~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 1 runtime-checked, 1 skipped out of 3 obligation(s)
    let mut v = w;
    v.push(v.len() as u32);
    if i < v.len() { v.remove(i) } else { 0 }
}

#[cfg(twophase_truncate)]
pub fn truncate_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_truncate]~^ NOTE [slice] FAILED
    let mut v = w;
    let k;
    v.truncate({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_insert)]
pub fn truncate_then_stale_insert(w: Vec<u32>, i: usize) -> usize {
    //[twophase_insert]~^ NOTE [slice] FAILED
    let mut v = w;
    let k;
    v.truncate({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    if i <= k {
        v.insert(i, 7);
    }
    v.len()
}

#[cfg(twophase_is_empty)]
pub fn truncate_then_stale_nonempty(w: Vec<u32>) -> u32 {
    //[twophase_is_empty]~^ NOTE [slice] FAILED
    let mut v = w;
    let e;
    v.truncate({
        std::hint::black_box(0u8);
        e = v.is_empty();
        0
    });
    if !e { v.remove(0) } else { 0 }
}

#[cfg(twophase_as_slice)]
pub fn truncate_then_stale_view(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_as_slice]~^ NOTE [slice] FAILED
    let mut v = w;
    let k;
    v.truncate({
        std::hint::black_box(0u8);
        k = v.as_slice().len();
        0
    });
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_retain)]
pub fn retain_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_retain]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    let mut v = w;
    let k;
    v.retain({
        std::hint::black_box(0u8);
        k = v.len();
        |_: &u32| false
    });
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_trait_method)]
pub trait Shrink {
    fn shrink_arg(&mut self, x: usize);
}

#[cfg(twophase_trait_method)]
impl Shrink for Vec<u32> {
    fn shrink_arg(&mut self, _x: usize) {
        self.clear()
    }
}

#[cfg(twophase_trait_method)]
pub fn local_shrink_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_trait_method]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    let mut v = w;
    let k;
    v.shrink_arg({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_tuple_def)]
pub fn tuple_def_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_tuple_def]~^ NOTE [slice] FAILED
    let (mut v, _z) = (w, 0u8);
    let k;
    v.truncate({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_break_out)]
pub fn break_out_then_stale_remove(w: Vec<u32>, i: usize, c: bool) -> u32 {
    //[twophase_break_out]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    let mut v = w;
    let k;
    'a: {
        v.truncate({
            std::hint::black_box(0u8);
            k = v.len();
            if c {
                break 'a;
            }
            0
        });
    }
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_returned_ref)]
pub trait ShrinkRet {
    fn shrink_ret(&mut self, x: usize) -> &mut Self;
}

#[cfg(twophase_returned_ref)]
impl ShrinkRet for Vec<u32> {
    fn shrink_ret(&mut self, _x: usize) -> &mut Self {
        self
    }
}

#[cfg(twophase_returned_ref)]
pub fn returned_ref_cleared_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_returned_ref]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    let mut v = w;
    let k;
    let r = v.shrink_ret({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    r.clear();
    if i < k { v.remove(i) } else { 0 }
}

#[cfg(twophase_compound_assign)]
pub struct Wipe(pub usize);

#[cfg(twophase_compound_assign)]
impl std::ops::AddAssign<Wipe> for Vec<u32> {
    fn add_assign(&mut self, _w: Wipe) {
        self.clear()
    }
}

#[cfg(twophase_compound_assign)]
pub fn compound_assign_then_stale_remove(w: Vec<u32>, i: usize) -> u32 {
    //[twophase_compound_assign]~^ NOTE unsupported MIR `vec-panic-method-index-unmodeled`
    let mut v = w;
    let k;
    v += Wipe({
        std::hint::black_box(0u8);
        k = v.len();
        0
    });
    if i < k { v.remove(i) } else { 0 }
}
