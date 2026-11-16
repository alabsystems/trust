//! THE FIRST ALab-DERIVED BATTERY ROW. Every other row in this battery is a
//! program written to exercise the compiler; this one is the scalar core of
//! code the owner already ships, converted to the two-language surface and put
//! through the AUTHENTICATED lane (`targo trust check main.rs`) — the same lane
//! `r29` pins, with `r32` as its close negative twin.
//!
//! ============================================================================
//! SOURCE, AND WHAT WAS SIMPLIFIED
//! ============================================================================
//! Source file: `a3d/crates/a3d-kernel/src/lib.rs` in the sibling a3d checkout
//! (read-only for this lane; nothing in that checkout was modified). a3d-kernel is a3d's proved
//! geometry/metrology core — straight-line integer code, no loops, no floats,
//! written for exactly this fragment, and the survey measured 179/191
//! obligations proved on the sealed pack.
//!
//! `end_within_file` is the scalar core of
//!
//!     pub fn range_in_bounds(off: u64, len: u64, file_len: u64) -> bool {
//!         match off.checked_add(len) {
//!             Some(end) => end <= file_len,
//!             None => false,
//!         }
//!     }                                    // a3d-kernel/src/lib.rs:238
//!
//! SIMPLIFIED: the `checked_add` / `match` overflow wrapper is dropped and the
//! already-summed `end` is taken as a parameter. `Option` and `match` are
//! outside the admitted fragment today (measured: the E6 recognizer admits a
//! projection, a select from bare params, a comparison-to-bool, and
//! `wrapping_*`, and nothing else).
//!
//! WHAT THAT COSTS, SAID PLAINLY. The `end <= file_len` COMPARISON is verbatim,
//! at the same `u64` width, and is what this row proves agrees with its Lean
//! model. The overflow guard is the other half of a3d's function, and it is the
//! half a3d's own suite pins — `assert!(!range_in_bounds(u64::MAX, 1,
//! u64::MAX)); // overflow -> false` (`a3d-kernel/src/lib.rs:582`). It is
//! outside the fragment and outside this contract, which can neither state nor
//! refuse it. This row therefore proves agreement with the model on
//! ALREADY-SUMMED inputs; it is not a proof that a byte range is safe to read,
//! and a caller that computes `end` by wrapping addition satisfies it.
//!
//! `min_span` is the two-ary core of
//!
//!     fn min4(a: i64, b: i64, c: i64, d: i64) -> i64 {
//!         let ab = if a < b { a } else { b };
//!         let cd = if c < d { c } else { d };
//!         if ab < cd { ab } else { cd }
//!     }                                    // a3d-kernel/src/lib.rs:500
//!
//! SIMPLIFIED twice: (1) the 4-ary chain is reduced to one of its three
//! identical 2-ary selects, because a sibling-call chain is not admitted
//! (measured); (2) the carrier is `u64`, not a3d's `i64`. A signed carrier is
//! admitted, but the island must then be written over `BitVec 64` under the
//! sign-flip order key (`Nat.xor (BitVec.toNat v) 9223372036854775808`), and no
//! signed bound theorem has been measured through the publication boundary. The
//! select itself is a3d's, character for character.
//!
//! ============================================================================
//! WHAT THIS ROW PINS
//! ============================================================================
//! Both Lean→Rust routes, on real code, through the lane that PUBLISHES:
//!
//!   * `end_within_file` — an UNCITED `ensures` that calls a Clean island
//!     definition and discharges by kernel definitional equality (wire solver
//!     `clean-kernel-defeq`). The Lean side says what "in bounds" means; the
//!     kernel checks that the Rust body IS that.
//!   * `min_span` — a CITED `ensures` whose Lean theorem is re-checked against
//!     the compiler-elaborated goal (wire solver `clean-kernel-citation`). The
//!     Lean side says why the body satisfies a bound it does not state.
//!
//! `row_targo_file … published` requires BOTH solver labels to appear as
//! `[PROVED]`, no `[UNKNOWN]` row, and `Publication boundary: … (0 withheld)` —
//! so a compiler that discharges these and then withholds them for want of a
//! `clean_cic` artifact fails this row, which is the regression r29 exists for.
//!
//! MEASURED on a stage1 built from this branch, not predicted:
//! `Gate: PASS [strict lane, exit 0]`, `5 obligation(s) passed the compiler,
//! all 5 published (0 withheld)`, `cited=3 defeq=2`. `r33` is this row with the
//! island moved verbatim into a `clean mod` unit file and publishes the
//! identical counts.
//!
//! COMMENTS INSIDE THE ISLAND ARE LEAN COMMENTS. `--` and `/- … -/`; `//`
//! lexes and then fails to parse (`Parse error: parser recovery produced raw
//! declaration: SlashSlash …`). This row's first draft used `//` and the whole
//! island was rejected.
//!
//! The two functions are kept on SEPARATE surfaces on purpose: r32 mutates the
//! Lean model behind `end_within_file` only, and `min_span`'s citation must go
//! on publishing there, so that a refusal cannot be collateral damage. (A MIXED
//! surface — one cited and one uncited clause on ONE function — also works
//! after round 1; it is pinned by
//! `tests/ui/trust/e9_mixed_cited_and_island_defeq_discharge.rs` and is not
//! used here because it would give r32 a second source of defeq rows.)

clean {
    -- a3d `range_in_bounds`, its overflow wrapper removed: the half-open byte
    -- range `[off, end)` is inside a blob of `f` bytes exactly when `e <= f`.
    -- `<=` at an unsigned carrier goes through Clean's own `instLEUInt64` /
    -- `instDecidableUInt64Le`, which is why the decision spells as plain
    -- `decide (e <= f)`.
    def within_isl (e : UInt64) (f : UInt64) : Bool := decide (e <= f)

    -- a3d `min4`'s two-ary core.
    def min2_isl (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b

    -- Why the body satisfies a bound its text never mentions: the minimum of
    -- two values is at most the first of them. This is the fact a3d's
    -- `IntervalI64::mul` relies on when it takes `min4` of the four endpoint
    -- products as the interval's lower bound.
    theorem min2_isl_le_left (a b : UInt64) : min2_isl a b <= a := by
      unfold min2_isl
      split <;> omega
}

/// a3d `range_in_bounds`, scalar core: is the (already summed) end offset
/// inside a file of `file_len` bytes?
///
/// UNCITED: the clause names the island definition, and the kernel closes it by
/// definitional equality against the E6 import of this body. The
/// `result == (file_len >= end)` conjunct pairs the author's own operator with
/// the island's `decide`: `>=` normalizes by swapping operands, so both
/// conjuncts land on the same decided term and the clause states the stronger
/// thing — that the two are the SAME term, not merely equal at every input.
pub fn end_within_file(end: u64, file_len: u64) -> bool
    ensures result == (file_len >= end) && result == within_isl(end, file_len)
{
    end <= file_len
}

/// a3d `min4`'s two-ary core, at the unsigned carrier.
///
/// CITED: the clause is a bound the body does not state, and the Lean theorem
/// proves it. Nothing here is uncited, so this function contributes only
/// `clean-kernel-citation` rows — which is what lets r32 attribute its refusal
/// to the mutated model.
pub fn min_span(a: u64, b: u64) -> u64
    ensures result <= a by min2_isl_le_left
{
    if a < b { a } else { b }
}

fn main() {
    // A 4096-byte header read out of a 1 MiB scan file is in bounds; the same
    // read one byte past the end is not.
    let ok = end_within_file(4096, 1048576);
    let bad = end_within_file(1048577, 1048576);
    let lo = min_span(7, 41);
    let _ = (ok, bad, lo);
}
