//@ needs-trust-verify
//@ edition: 2021
//@ revisions: bounded zst wide
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[bounded] check-pass
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! Collecting a slice's `chunks`/`chunks_exact`/`rchunks`/`windows` allocates at
//! most one destination element per source element, exactly as collecting
//! `iter()` does, so the unbounded-allocation lane grants it (ordsweep2
//! collections/c06). Before 2026-10-03 every such collect reported
//! `UnboundedAllocation::Iterator::collect::count-not-derivable` and failed the
//! build. The remaining advisories are the bundled `Chunks::size_hint` member's own
//! guarded assert (policy B).
//!
//! The `zst` revision keeps the zero-sized-element refusal: `[(); 1 << 61]` costs
//! no memory, so its length bounds nothing and the collect stays charged.
//!
//! The `wide` revision is review round 52's false proof, fixed 2026-10-06 by
//! `docs/DECISION_QUEUE.md` D12 option (a): a bounded source does not bound what the
//! destination reserves per item. `huge_chunks` panicked "capacity overflow" on an
//! 8 MiB input and was reported verified; `huge_extend` was reported `1 proved`.
//! A destination item more than twice the source item's bytes (`&[i32]` views of
//! `i32`s) is charged too. The `bounded` revision's items stay within that factor.
//!
//! Re-pinned 2026-10-15 (the merge of 2026-10-14): `huge_chunks`, `huge_extend` and
//! `unit_chunks` are refused on their charged rows ("strict verification failed") instead
//! of on a lowering failure ("full verification failed"): the bundle of the collect's
//! member is now kept (for `huge_extend`, since `ChunksExact::size_hint`'s unrooted divisor
//! is a runtime-checked std member again, DECISION_QUEUE D103(f)). Same functions, same
//! refusal.
#![allow(dead_code)]

#[cfg(bounded)]
pub fn chunk_lens(v: &[i32]) -> Vec<usize> {
    v.chunks(3).map(|c| c.len()).collect()
}

#[cfg(bounded)]
pub fn exact_lens(v: &[u32]) -> Vec<usize> {
    v.chunks_exact(4).map(|c| c.len()).collect()
}

#[cfg(bounded)]
pub fn rchunk_lens(v: &[u64]) -> Vec<usize> {
    v.rchunks(2).map(|c| c.len()).collect()
}

#[cfg(wide)]
pub fn window_views(v: &[i32]) -> Vec<&[i32]> {
    //[wide]~^ ERROR Trust Level 0 safety verification incomplete
    //[wide]~| ERROR Trust strict verification failed
    v.windows(2).collect()
}

#[cfg(wide)]
pub fn huge_chunks(v: &[u8]) -> Vec<core::mem::MaybeUninit<[u8; 1 << 40]>> {
    //[wide]~^ ERROR Trust Level 0 safety verification incomplete
    //[wide]~| ERROR Trust strict verification failed
    v.chunks(1).map(|_| core::mem::MaybeUninit::uninit()).collect()
}

/// Review round 53: `FromIterator::from_iter` carried `size_of::<Self>()` (24 for any
/// `Vec`) as its per-item size, so this one stayed open through `from_iter`.
#[cfg(wide)]
pub fn huge_from_iter(
    v: &[[u64; 2]],
) -> Vec<Result<[[u64; 2]; 1 << 36], core::array::TryFromSliceError>> {
    //[wide]~^^^ ERROR Trust Level 0 safety verification incomplete
    //[wide]~| ERROR Trust strict verification failed
    Vec::from_iter(v.windows(1).map(<[[u64; 2]; 1 << 36]>::try_from))
}

#[cfg(wide)]
pub fn huge_extend(out: &mut Vec<core::mem::MaybeUninit<[u8; 1 << 40]>>, v: &[u8]) {
    //[wide]~^ ERROR Trust Level 0 safety verification incomplete
    //[wide]~| ERROR Trust strict verification failed
    out.extend(v.chunks_exact(1).map(|_| core::mem::MaybeUninit::uninit()));
}

#[cfg(zst)]
pub fn unit_chunks(v: &[()]) -> Vec<usize> {
    //[zst]~^ ERROR Trust Level 0 safety verification incomplete
    //[zst]~| ERROR Trust strict verification failed
    v.chunks(1).map(|c| c.len()).collect()
}
