// Source for `entry_sentinel_unranged_overflow_tied_control.json` — the NEGATIVE
// CONTROL for `entry_sentinel_unranged_overflow.rs`.
//
// Identical code with the `String` (and therefore every cleanup block) deleted, so
// `entry_sentinel_tie_is_sound`'s mint-side clause PASSES and the tie `Eq(n#e, n)`
// IS emitted. Its `n#e` is connected through the tie rather than through the
// versioned-parameter range, which is what makes it the control: the range repair
// must leave this row's verdict untouched.
//
// It is also the honest CEILING for the sibling fixture. This row is `Unknown` —
// with the tie, with a fully-connected `n#e` — so the residual obstacle on both is
// the solver's integer-division reasoning, not a missing hypothesis. `Unknown`, not
// `Proved`, is what the repair can deliver.
pub fn h(mut n: u32, b: bool, c: bool) -> u32 {
    n /= 3;
    let mut t: u32 = 0;
    if b { t = 1; } else { t = 2; }
    if c && t > 0 { n * 3 } else { 0 }
}
