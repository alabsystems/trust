#![crate_type = "lib"]
// SIGNED SWITCH LABEL (raw two's-complement). `match n { -1 => x + 1, _ => 0 }`
// adds 1 to a `u8` on the `-1` arm and returns 0 everywhere else. IT FAULTS: at
// `n == -1, x == 255` the `x + 1` overflows and panics under debug assertions.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 1 panic / 1792 runs, sweep
// `n in -3..=3` x `x in 0..=255` (7*256), the single panicking point being
// exactly (-1, 255).
//
// WHY IT IS A GATE FIXTURE. A MIR `SwitchInt` label crosses the extraction
// boundary as a raw `u128`. Unsign-extended, the `-1` arm's label is
// 2^32-1 while `n: i32` ranges over the SIGNED interval, so the arm's path
// condition is UNSAT and every obligation on it — including this overflow —
// discharges vacuously. The verifier MUST refute this.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `proved` (SURVIVING MUTANT — the false proof); `campaign-integration`
// answers `refuted`. The fixture discriminates.
pub fn switch_neg_label_add(n: i32, x: u8) -> u8 {
    match n {
        -1 => x + 1,
        _ => 0,
    }
}
