// Source for `entry_sentinel_unranged_overflow.json`.
//
// Captured with:
//   trustc --crate-type lib -Ztrust-dump=mir:<dir> -Ztrust-verify=on \
//          -Ztrust-policy=advisory -O --edition 2021 <this file> -o /dev/null
//
// SAFE for every `u32`: `u32::MAX / 3 * 3 == 4294967295` exactly, so the `n * 3`
// cannot overflow.
//
// Two ingredients put the entry sentinel `n#e` on its own:
//   * the `String` makes `bb8 Drop unwind=Cleanup(11)` / `bb9 Resume` /
//     `bb10 Drop unwind=Terminate`. Those cleanup blocks have an EMPTY
//     entry-version map, so `entry_sentinel_tie_is_sound`'s mint-side clause
//     refuses the tie for the WHOLE function — `n#e` gets no `Eq(n#e, n)`.
//   * the `if b {…} else {…}` diamond weakens the bare-read sibling def away, so
//     the pinned `n#s0_5 == n#e / 3` is the only carrier left.
//
// `conjoin_arg_type_ranges` bounded only the BARE `n`, so `n#e` floated free on
// `Sort::Int` and the solver picked `n#e = 4294967298` — three above `u32::MAX` —
// falsely REFUTING this. See `entry_sentinel_unranged_overflow_realmir.rs`.
pub fn h(mut n: u32, b: bool, c: bool) -> u32 {
    let s = String::new();
    n /= 3;
    let mut t: u32 = 0;
    if b { t = 1; } else { t = 2; }
    let r = if c && t > 0 { n * 3 } else { 0 };
    drop(s);
    r
}
