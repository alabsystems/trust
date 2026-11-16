//@ revisions: on off
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[off] compile-flags: -Ztrust-no-adapter-yield
//@[on] check-pass
//@[off] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//! D2 tier 1 (2026-09-24): `ADAPTER_YIELD` through a LAZY adapter, on the shape
//! of ordinary-rust sweep `s19`
//! (`v.windows(2).filter(|w| w[0] <= w[1]).count()`).
//!
//! `filter` hands its predicate `&Self::Item`, so the item is `*_2` (a
//! `&&[u32]` parameter). The `Filter` value carries the closure; it is admitted
//! only because it is written once by `filter` and MOVED once into core's
//! `Iterator::count`, which has no generic parameters of its own — nothing else
//! can reach the predicate.
//!
//! Every `w[i]` through `&&[u32]` makes rustc mint a fresh auto-deref copy
//! (`_k = copy (*_2)`) whose index row reads `_k`'s own length; vcgen carries
//! the premise onto each such single-assignment copy (a definitional
//! consequence, see `stable_copy_slice_lens`). Without that, the two load rows
//! stay refuted with `_14__slice_len#s1_0 = 0` even under the premise — the
//! same gap that refutes plain `fn g(s: &&[u32]) -> u32 { s[0] }` today.
//!
//! BEFORE (stage-1 snapshot 4e9fe36bf = the `off` revision): rc=1, the closure
//! refused with `0 proved, 4 failed` (`w*__slice_len = 1`, `= 2` with
//! `_16__slice_len#s2_0 = 0`, …); the parent carries a bundled-std advisory
//! warning.
//!
//! Trust (2026-09-29): the PARENT is now refused in both revisions, and that is
//! the bundled std-member fix, not this premise. `count()` bundles core's
//! `<usize as Sum>::sum::{closure#0}`, whose inherited `Overflow(Add)` Assert the
//! admission lane refuses. That refusal used to DISCARD the parent's whole native
//! bundle, and the lowering-failure tolerance then accepted `windows2` on a
//! verdict with no rows behind it. The bundle is now kept (the member's Assert is
//! a `runtime_checked` row), and the kept bundle carries a fail-closed
//! `[trust-drop-glue-assumption]` row for `core::slice::iter::Windows`'s drop
//! inside core's `count` — exactly the row the success path already refuses for
//! `v.windows(2).filter(..).for_each(..)`, which has no refused member (measured
//! on origin/main `f6773df328e`, release-like std: rc=1, "drop glue for
//! `core::slice::iter::Windows` has unproven panic-freedom"). A capability loss,
//! recorded in docs/KNOWN_HAZARDS.md ("CLOSED 2026-09-29 — the bundled std-member
//! tolerance …"). The CLOSURE's premise and verdict — what this file is for — are
//! unchanged and still pinned.
//!
//! Trust (2026-10-03): `off` now reports `2` Level 0 obligations not proved, not `4`.
//! bbfec0ee70 (the index lane conjoins its own block's slice-length ties at the use
//! point) proves each LOAD row (`(*_14)[_4]`, `(*_16)[_9]`) from its dominating bounds
//! `Assert` (`_7`, `_12`) plus the copy's tie `_14__slice_len = w*__slice_len` (a copy of
//! `*_2` through an immutable `&&[u32]`): reaching the load means that Assert held. The
//! two Asserts themselves still FAIL without the premise, as they must, and the closure
//! is still refused with `[slice] FAILED`.
//!
//! 2026-09-28 (W-D2a/W-D2b, local line; the same result as main's bbfec0ee70 above,
//! reached independently by cb97b9547f4): `off` is still refused, but on `2 proved,
//! 2 failed`. The two loads through the auto-deref copies now read their copy's
//! same-block length tie, so each is discharged by the native `BoundsCheck` assert
//! that runs before it. The two asserts stay refuted, on windows of length 1 and 0,
//! since without the premise the window length is unknown. The refusal is exactly
//! the real one.

pub fn windows2(v: &[u32]) -> usize {
    // Re-pinned 2026-10-15 (the merge of 2026-10-14, DECISION_QUEUE D103(d)): `on` builds. The
    // parent publishes no row of its own: `count()` over this `Filter` is decided total by the
    // drive-only consumer lane (the closure's own verdict below), and `windows(2)` by its
    // non-zero constant size (CONST-CHUNK-SIZE-ZERO-ROW-PARITY), so ZERO-ROW-GATE, which
    // refused it on the merged stage 1 for the `windows` call, now reads those decisions.
    v.windows(2).filter(|w| w[0] <= w[1]).count()
    //[on]~^ NOTE Trust verification: 4 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked out of 4 obligation(s)
    //[on]~| NOTE Trust modeled fact ADAPTER_YIELD: core `Iterator::filter` over `<[T]>::windows(2)` invokes this closure only on items it yields; assumed: item parameter `*_2` has slice length 2
    //[off]~^^^ ERROR Trust Level 0 safety verification incomplete for `windows_filter_count::windows2::{closure#0}`: 2 obligation(s) were not proved
    //[off]~^^^^ ERROR Trust strict verification failed for `windows_filter_count::windows2::{closure#0}`: 4 obligation(s) were not fully verified
    //[off]~^^^^^ NOTE [slice] FAILED
}
