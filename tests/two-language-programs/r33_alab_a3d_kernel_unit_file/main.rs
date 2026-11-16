//! `r31` WITH THE ISLAND OUT OF LINE — the tree's only measurement of a Rust
//! CONTRACT discharged from a `clean mod` unit file.
//!
//! WHY THIS ROW EXISTS. `docs/TWO_LANGUAGE_CONVERSION_GUIDE.md` §1b tells a
//! converter to put anything longer than a few lines in a unit file, and §8
//! builds its only cross-crate answer on one. Before this row, **no file in the
//! tree paired `clean mod` with `ensures` at all**: every contract that
//! discharges through Lean — r15, r29..r32, every `e9_*` and every
//! `e6-fragment-probe` — used an INLINE island, and the one unit/island
//! equivalence control (`tests/ui/trust/clean_unit_island_equivalence.rs`) runs
//! under `-Z trust-verify=off` and pins the CALL path only. The guide was
//! recommending an unmeasured spelling for the work it exists to enable.
//!
//! WHAT IT PINS. Byte-for-byte the same as `r31` except that the island lives in
//! `bounds.lean` and `clean mod bounds;` stands in its place: the same two
//! functions, the same uncited-defeq and cited-theorem clauses, the same
//! `targo trust check main.rs`. `row_targo_file … published` therefore requires
//! the identical publication facts — `Gate: PASS`, `(0 withheld)`, both kernel
//! solver labels `[PROVED]`, no `[UNKNOWN]` — and a divergence from r31 on the
//! same compiler is attributable to the unit-file spelling and to nothing else.
//! Read the two rows as a pair; r31's header carries the a3d provenance and
//! every simplification.
//!
//! MEASURED, not predicted, on a stage1 built from this branch: `5 obligation(s)
//! passed the compiler, all 5 published (0 withheld)`, `cited=3 defeq=2` —
//! identical to r31's counts.

clean mod bounds;

/// a3d `range_in_bounds`, scalar core. UNCITED: closed by definitional equality
/// against the E6 import of this body.
pub fn end_within_file(end: u64, file_len: u64) -> bool
    ensures result == (file_len >= end) && result == within_isl(end, file_len)
{
    end <= file_len
}

/// a3d `min4`'s two-ary core. CITED: the clause is a bound the body does not
/// state, and the unit file's theorem proves it.
pub fn min_span(a: u64, b: u64) -> u64
    ensures result <= a by min2_isl_le_left
{
    if a < b { a } else { b }
}

fn main() {
    let ok = end_within_file(4096, 1048576);
    let bad = end_within_file(1048577, 1048576);
    let lo = min_span(7, 41);
    let _ = (ok, bad, lo);
}
