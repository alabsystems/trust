//@ needs-trust-verify
//@ compile-flags: -Ztrust-verify=on --crate-type lib -Ztrust-policy=certify
//@ dont-check-compiler-stderr
//@ dont-require-annotations: ERROR
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ check-fail
//! Trust (postcondition composition — the VACUITY guard on the positive test).
//!
//! Byte-for-byte the bodies of `postcondition_composition_at_call_site.rs`,
//! with the callee's `ensures` weakened to its UPPER half. `clamp_low` still
//! proves its own (weaker) postcondition, and the caller still assumes it — but
//! `result <= 1000000` says nothing about how negative `y` may be, so `y * 3`
//! does not FOLLOW from the clause, and this obligation must NOT prove.
//!
//! State that claim precisely, because this file used to overstate it and said
//! `y * 3` was "still a real underflow". It is not. `clamp_low`'s body clamps to
//! `[0, 1000000]` and never returns a negative, so no input makes `triple`
//! overflow — measured 2026-09-17 against stage1 with debug assertions on:
//! `triple(i32::MIN) == 0`, and the largest value `triple` ever produces is 297.
//! What this file asserts is DERIVABILITY, not the presence of a bug: a modular
//! caller knows only the clause, the clause admits negatives, and a lane that
//! reports this row proved has either used a fact it was not given or stopped
//! emitting the row at all.
//!
//! Without this file, the positive test cannot distinguish "the caller USED the
//! postcondition" from "the caller-side lane stopped emitting the obligation".
//! Composition that proves regardless of what the clause SAYS is not
//! composition, it is suppression.
//!
//! POLICY RE-PINNED 2026-09-16. This file read its answer off the DEFAULT lane's
//! exit code, which stopped being the same question on 2026-09-14, when policy B
//! landed as ruled (docs/design/2026-07-25-completeness-gap-policy-ruling.md): an
//! unproved arithmetic row that keeps rustc's runtime check is REPORTED and the
//! build SUCCEEDS. `-Ztrust-policy=certify` is the lane where full static
//! discharge IS the contract, so that is where this question belongs and that is
//! what the flag above selects.
//!
//! OUTCOME RE-PINNED 2026-09-17, after `first-party/ay` moved to c187eb99d
//! (reports/2026-09-17-nine-ui-reds-follow-the-ay-pin-move.md establishes by A/B
//! that the VC formula is byte-identical across that move and only the solver's
//! ANSWER changed). The row was `runtime-checked`; the stronger solver decides it
//! now and returns a refutation with a model.
//!
//! The guard's discriminating power is unchanged — the row is still emitted and
//! still does not prove, which is the whole of what it ever asked — and the model
//! is a better witness than the old shrug, because the value it picks SATISFIES
//! the assumed clause. It shows the caller reasoning inside the contract it was
//! actually given and still unable to close the obligation, which is precisely
//! "the upper bound is not enough".
//!
//! Read the word `counterexample` in that row narrowly, though, and do not carry
//! it into any claim about the code. It is a model of the MODULAR ENCODING, in
//! which `clamp_low`'s result is any value the clause admits. The program cannot
//! produce that value and `triple` has no overflowing execution at all. The
//! compiler states this standard itself — not in THIS file's report, which was
//! checked on 2026-09-17 and contains no such row, but in the companion fixtures
//! that do carry one (`postcondition_composition_needs_proved_ensures.rs` and
//! `..._attribute_needs_proved_ensures.rs`, on their `bad` / `bad_pre`
//! postcondition rows) — when it demotes a refutation of an over-approximation:
//! a satisfying
//! model may assign a value the program can never produce, so it refutes the
//! ENCODING, not the program. Here the encoding is refuted and the code is fine.
//! The obligation is genuinely open — that is what this file pins — and nothing
//! in that row is a defect in `clamp_low` or `triple`.
//!
//! A refuted row also fails the default lane, so `certify` no longer decides this
//! file's exit code, and with no runtime-checked row left in `triple` the flag is
//! currently inert here. Keep it: it is the lane this question belongs in, and it
//! is what would catch the row sliding back to runtime-checked-and-tolerated. The
//! `NOTE` pin below carries that duty at row level — it asserts the row EXISTS
//! and did not prove, whichever policy decides the exit code.
//!
//! RE-PINNED 2026-09-28 (MEASURED on the Track B stage 1). The D5-A
//! call-destination screen now lets a solver model over a same-crate call
//! result stand only where an injected clause DETERMINES that result with no
//! `requires` guard (`trust_vcgen::generate::summary_pins_result`). Here
//! `result <= 1000000` bounds `y` only from above, so the `[overflow:mul]` model picks a
//! value the contract admits but no execution of `clamp_low` returns (MEASURED
//! shape: `p_falsefail::dead_else_s`). The row is therefore HELD — `UNKNOWN`
//! naming `clamp_low`, a fail-closed gap with no runtime-check tolerance — where it
//! read `FAILED`. It still does not prove and the build still fails, which is
//! the whole of what this file asks.

pub fn clamp_low(x: i32) -> i32
    ensures result <= 1000000
{
    if x < 0 {
        0
    } else if x > 1000000 {
        1000000
    } else {
        x
    }
}

pub fn triple(x: i32) -> i32 {
//~^ ERROR Trust Level 0 safety verification incomplete for `postcondition_composition_upper_bound_only::triple`
//~| ERROR Trust strict verification failed for `postcondition_composition_upper_bound_only::triple`
//~| NOTE generic solver counterexample withheld: query depends on the unmodeled return of same-crate `postcondition_composition_upper_bound_only::clamp_low`
    let y = clamp_low(x);
    if y < 100 { y * 3 } else { 0 }
}
