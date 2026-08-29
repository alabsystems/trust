#![crate_type = "lib"]
// MUTANT (parameter-accumulator soundness twin): the accumulator is a by-value PARAMETER
// whose const init is CONDITIONAL, so on the `!c` path the caller's own `t` survives into
// the reduction and `t += x as u64` GENUINELY OVERFLOWS. `certify` MUST refute (exit 1).
//
// This is the twin of proved/wide_unsigned_accumulator.rs::u64_acc — byte-identical
// reduction, and the ONLY difference is that its accumulator is a parameter rather than a
// local. That one difference is the whole point: a parameter is defined implicitly AT
// ENTRY and `body.blocks` never carries that definition, so `accumulator_init_const` used
// to count only the `t = 0` store and the self-add, score `def_count == 2`, and admit the
// bound `t <= 0 + 64*255` over a value the caller chooses. The path condition then went
// UNSAT and BOTH obligations discharged AND kernel-certified.
//
// Measured before the fix (main @ 86ed2d4cd6 / 1d457f875e, `-Ztrust-policy=certify`):
//   "Trust verification: 2 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked"
//   "of which 2 kernel-certified by the clean CIC kernel"
// against a stock-rustc runtime oracle (overflow-checks=on, at -O and without, identical)
// sweeping t in {0, 1, 1000, 2^32, MAX-16320, MAX-16319, MAX-1, MAX} x fill in
// {0x00, 0x01, 0xff} x c in {false, true} = 48 cases: 5 of 48 PANIC. Pins that the
// reduction bound is withheld once the accumulator's entry value is unaccounted for.
pub fn f(mut t: u64, a: &[u8; 64], c: bool) -> u64 {
    if c {
        t = 0;
    }
    for &x in a {
        t += x as u64;
    }
    t
}
