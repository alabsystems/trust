// loop-wellformed-corpus — ADVERSARIAL (but REAL-trustc-MIR-reachable) loop-counter /
// accumulator well-formedness probes for the 2026-07-05 recognizer soundness campaign
// (see reports/recognizer-wellformedness-campaign-2026-07-05.md). Every function here is
// a LEGITIMATE Rust program a recognizer must NOT falsely certify: the loop/accumulator
// local is written by an ADDITIONAL `Statement::Assign` beyond its recognized {init,
// update} pair — an off-back-edge body-spine write, a pre-header double overwrite, a
// post-loop write on the exit->return path, or an off-spine COPY/CONST write to an
// accumulator — each dropped by a §6 loop extractor that models the local from only the
// header/back-edge shape blocks (or a linear body-spine walk), never inspecting every
// REACHABLE write.
//
// Deliberately BARE (no `#[core::contracts::ensures]`): the native contracts attribute
// wraps the function body in an ensures-checker closure whose return commit is a
// `Terminator::Call` (`std::intrinsics::contract_check_ensures`), not a direct
// `Statement::Assign(_0, ...)` — that indirection is an ORTHOGONAL, already-tracked
// "Call-dest value-injection" class (see the campaign report's class 2), and would
// confound these probes (the extractors under test here never even reach the
// contract-wrapper's `_0`). Bare functions (matching `count_up`/`count_to`'s style in
// `fixtures/real-spec-corpus/SOURCE.rs`) give a direct `_0 := Copy(local)` return commit,
// isolating exactly the write-count gates this corpus exercises: `extract_loop_shape`
// (via `resolve_counter_update`/`resolve_guard_counter_update`) and
// `collect_loop_body_updates`. These probes are tested via the extraction-level
// recognizers (`extract_synth_loop_function`, `extract_accum_loop_function`), which do
// not require a postcondition to be present.
//
// Dump with:
//   trustc -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> \
//     --crate-type=lib SOURCE.rs
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
#![allow(unused)]

// PROBE 1 — OFF-BACK-EDGE body-spine write to the loop counter. The back-edge block's
// `i = i + 1` is the ONLY update `resolve_counter_update`/`extract_loop_shape` inspects;
// the `if i > 3 { i = i + 5; }` arm ALSO writes `i` on a body-spine block the header/
// back-edge-only shape scan never visits. Real per-iteration behavior can push `i` well
// past `n` (e.g. `n = 4`: guard lets `i = 3` in, the `+5` bump lands at `i = 9`, `9 > 4`),
// so a claimed `ret <= n` would be genuinely FALSE for real inputs — a real false
// certification if the recognizer does not decline.
pub fn off_spine_counter_write(n: i64) -> i64 {
    let mut i: i64 = 0;
    while i < n {
        if i > 3 {
            i = i + 5;
        }
        i = i + 1;
    }
    i
}

// PROBE 2 — PRE-HEADER const OVERWRITE of the counter. TWO pre-loop writes to `i`:
// `i = 100` (dead) then `i = 0` (the LIVE init the loop actually starts from).
// `counter_init_const` takes the FIRST `i := Use(Constant)` in program order — the DEAD
// `100`, not the live `0` — so a (pre-fix) recognizer would synthesize `100 <= i` and
// could falsely certify `ret >= 100`, even though the REAL returned value (e.g. `n = 1`
// ⇒ `ret = 1`) is nowhere near 100.
pub fn pre_header_double_init(n: i64) -> i64 {
    let mut i: i64 = 100;
    i = 0;
    while i < n {
        i = i + 1;
    }
    i
}

// PROBE 3 — POST-LOOP write to the counter on the exit→return path. After the loop exits,
// `i` is reset to `0` before the return. `return_reads_counter` sees the `_0 := Copy(i)`
// and (pre-fix) reports "the return reads the counter" without noticing the intervening
// post-loop write — so a certified `ret <= n` claim would describe the LOOP's halting
// value of `i`, not the actual returned `0`. At `n < 0` the real returned `0` VIOLATES
// `ret <= n` (`0 <= -1` is false) — a genuine counterexample.
pub fn post_loop_counter_overwrite(n: i64) -> i64 {
    let mut i: i64 = 0;
    while i < n {
        i = i + 1;
    }
    i = 0;
    i
}

// PROBE 4 — body-spine COPY/CONST write to the ACCUMULATOR, dropped by
// `collect_loop_body_updates`/`resolve_block_commits`. Every iteration first CLOBBERS `s`
// back to `100` (a `Use(Constant)` write — neither of `resolve_block_commits`'s two
// recognized commit forms), then bumps it by `s = s + 1`. `resolve_block_commits` only
// recognizes the SECOND statement as a commit, so the collected model is `s := s + 1`
// (accumulating from 0) when the REAL per-iteration transform unconditionally resets `s`
// to `101` every time — the real returned value is always `101` (for any `n >= 1`), a
// clear divergence from the modeled accumulation.
pub fn off_spine_accumulator_write(n: i64) -> i64 {
    let mut i: i64 = 0;
    let mut s: i64 = 0;
    while i < n {
        s = 100;
        s = s + 1;
        i = i + 1;
    }
    s
}
