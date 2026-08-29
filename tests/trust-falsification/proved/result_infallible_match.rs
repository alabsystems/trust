#![crate_type = "lib"]
// FALSE-REFUTATION GUARD: matching a `Result<u8, Infallible>` and discharging
// the error arm with the empty match `match e {}`. `Infallible` is uninhabited,
// so the `Err` variant cannot be constructed and the empty match is the standard
// way to say so. IT DOES NOT FAULT: only `Ok` exists, and the body just returns
// its payload.
// Runtime oracle (stock rustc, -O -C debug-assertions=on, #[inline(never)],
// black_box, catch_unwind, silent hook): 0 panics / 256 runs, sweep
// `Ok(v)` for `v in 0..=255` — the whole inhabited input domain, since no `Err`
// value exists to sweep.
//
// WHY IT IS A GATE FIXTURE. If the uninhabited variant's tag stays in the
// published tag set, the unreachability obligation on the `Err` arm is
// refutable and a total function is accused of reaching a `match e {}`.
//
// Two-column measurement, `-Ztrust-policy=certify`: pristine `70a7534fd1`
// answers `refuted` with `[unreach] FAILED ... __trust_mir__discr_r = 0` — the
// solver selecting the uninhabited variant. `campaign-integration` answers
// `proved`. The fixture discriminates.
use core::convert::Infallible;
pub fn result_infallible_match(r: Result<u8, Infallible>) -> u8 {
    match r {
        Ok(v) => v,
        Err(e) => match e {},
    }
}
