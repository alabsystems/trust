#![crate_type = "lib"]
// THE POSITIVE TWIN of `mutant/option_map_or_default_div_zero.rs`. Same
// `map_or` shape, both hazards guarded: the eagerly evaluated default divides
// by `d.max(1)` (never zero) and the `Some` closure uses `saturating_add`
// (never overflows). It must PROVE (exit 0).
// Runtime oracle (stock rustc 1.96.0, -O -C debug-assertions=on,
// #[inline(never)], black_box, catch_unwind, silent hook): 0 panics / 245 runs,
// sweep `a x b` over {0, 1, 2, 3, 7, u64::MAX-1, u64::MAX} squared x
// `d in {0, 1, 2, 3, u64::MAX}` — `d == 0` is IN the sweep on purpose, since it
// is the input that faults in the mutant twin.
//
// THIS ROW IS THE ONE POSITIVE THE COMBINATOR LANE COULD ACTUALLY EARN, and it
// was added only after being MEASURED green. Two-column measurement under
// `-Ztrust-policy=certify`, same worktree, sequential:
//
//   measurement parent  1 proved, 0 failed, 0 unknown, 1 runtime-checked / 2 -> FAIL
//   candidate           2 proved, 0 failed, 0 unknown, 0 runtime-checked / 2,
//                       of which 2 kernel-certified by the clean CIC kernel   -> PASS
//
// (The two commits below this one name and fingerprint both columns.)
//
// The DENOMINATOR IS 2 IN BOTH COLUMNS. The row moves from runtime-checked to
// statically proved; no obligation was deleted to make the total look better.
//
// Five further combinator positives were probed and are NOT here because they
// are not green on the tip: an `and_then` with an in-bounds `% 3` index, an
// all-checked `and_then`/`map` chain, the `is_some_and` in-bounds twin, and
// a3d's own `range_in_bounds` all answer `incomplete` — the direct-call
// summary now reaches them, but the proof-grade admission layer rejects the
// CHC evidence, which is the NEXT wall and is not closed here. A sixth,
// `x.map_or(1, |v| v | 1)` followed by `n / d`, answers `refuted` with the
// counterexample `d = 0` on BOTH columns — a false refutation, since `v | 1`
// is odd for every `v`. A `proved/` row that does not verify is a
// false-refutation failure, not a control, so none of the six was shipped.
pub fn map_or_guarded(a: u64, b: u64, d: u64) -> u64 {
    a.checked_mul(b).map_or(100 / d.max(1), |v| v.saturating_add(1))
}
