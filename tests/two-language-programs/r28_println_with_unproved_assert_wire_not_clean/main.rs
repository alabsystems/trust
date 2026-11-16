// r09's SECOND negative control, for the CLASS itself. Same program plus one
// user `assert!` whose operand the verifier cannot ground (`black_box`). The
// user's panic site and std's `_print` panic site FOLD into the one
// whole-function panic-freedom row, and that row is named after the first
// marked site — `_print`. Under the default policy the crate still COMPILES and
// RUNS (a user assertion keeps its runtime check; policy B), so this cannot be a
// refusal row. What the row pins is the wire: the compiler must attest the
// print class only when the print backend is the aggregate's SOLE panic source,
// so this program's row carries NO `gap_class`, the print tolerance does not
// cover it, and the grader reads `clean=no` naming an UNCLASSED
// `runtime_checked:assert`. Measured 2026-09-17 on a HEAD stage1 before this
// pin existed: the row was classed and graded clean=yes — the vacuous green
// this row exists to keep out.
fn double(x: i32) -> i32
    requires x > 0
    requires x < 1000
    ensures result == x * 2
{ x * 2 }
fn main() { assert!(std::hint::black_box(1) == 1); println!("{}", double(21)); }
