//@ revisions: advisory certify
//@ needs-trust-verify
//@ edition: 2021
//@ compile-flags: -Ztrust-verify=on --crate-type lib
//@[advisory] compile-flags: -Ztrust-policy=advisory
//@[certify] compile-flags: -Ztrust-policy=certify
//@[advisory] check-pass
//@[certify] check-fail
//@ dont-check-compiler-stderr
//@ dont-require-annotations: NOTE
//@ dont-require-annotations: WARN
//@ dont-require-annotations: HELP
//! SELF-GUARDED-LITERAL-OPERAND-1 (2026-10-12): a checked operation over a LITERAL
//! operand kept a vacuous statement-lane row beside its assert's own row, and that
//! row was kernel-certified at the span of an operation that panics.
//!
//! * A signed division or remainder with a literal dividend (`100 / x`): rustc
//!   checks the divisor, then `Eq(x, -1) & Eq(const 100, const i32::MIN)`, then
//!   divides. The zero-divisor chain bound that second conjunct with a binder that
//!   refuses a literal (trust-vcgen `checked_vcs.rs`,
//!   `v2_divzero_signed_chain_binds_operation`), so the statement-lane `divzero` /
//!   `remzero` row survived under the zero assert's own guard: `x != 0 && x == 0`,
//!   `proved`, clean-kernel `Certified`, beside the assert lane's FAILED row.
//! * A literal negation under `#![allow(arithmetic_overflow)]` (`-i32::MIN`): the
//!   assert-lane builder refused a literal (a `RecognizedSafetyAssertProofGap`), and
//!   the statement row — self-guarded, and built at the i64 that `operand_ty` gives
//!   `i32::MIN` — was the function's only `negation` row, kernel-certified.
//!
//! Every function below panics for some input (`div_lit(0)`, `n32()` on every
//! run), so no zero-divisor or negation row of any of them may read proved.
//!
//! Each function is pinned by the human-format `Trust verification: N proved, M failed,
//! ...` note at its span (both revisions) and, under `certify`, by its `summary:` note
//! and errors. The vacuous row was one more PROVED (and certified) row, so each count
//! moves by exactly one. The lane first pinned the rows' `-Ztrust-verify-output=json`
//! spellings with `forbid-output`; compiletest keeps only the first 512 KiB of a test's
//! output, and this file's JSON is about 2 MB (`e4`'s record alone is 1.3 MB), so every
//! pattern past `div_lit` was read in no run, before or after. Do not reintroduce a
//! JSON `forbid-output` here without checking where the row lands in the capture.
//!
//! BEFORE (the wave-25 probe stage 1, `scratchpad/stage1-w25probe`, integ7 after wave
//! 24; each revision's flags plus `--cfg <revision> --emit=metadata`): `advisory` exits
//! 0 and `certify` 1. `div_lit`, `rem_lit`, `e2` read `3 proved, 1 failed` and `summary:
//! 0 trusted, 3 certified, 1 failed, … out of 4`, `e4` `5 proved, 1 failed` (`5
//! certified`), `div_min_lit` `1 proved, 2 failed` (`1 certified`), and `n32` `1 proved,
//! 0 failed, 1 unknown` (its only `negation` row the certified one, at `Int { width: 64
//! }`, beside a `RecognizedSafetyAssertProofGap(OverflowNeg)`). No pin below matched.
//!
//! AFTER (measured 2026-10-13, the integ/wave25 stage 1): each zero-divisor and negation
//! check keeps exactly one row, the assert lane's, FAILED (`n32`'s at `Int { width: 32
//! }`, now also a guaranteed violation under `certify`); each count and certify summary
//! loses exactly the vacuous certified row; the `overflow:*` rows are unchanged.
//!
//! LITERAL-DIVISOR FOLLOW-UP (2026-10-13, the wave-25 adversarial review). The same lie
//! held for a LITERAL zero divisor (`x / 0`, `x % 0`, `a % 0u8`, `a / 0u32`, `100 / 0`,
//! `(false as u8) % 0u8`; every one panics on every call): its zero check is `Eq(const
//! 0, const 0)` and, signed, the chain's divisor conjunct `Eq(const 0, const -1)`, and the
//! zero-divisor binding refused a literal on both, so the statement-lane row, under the
//! zero assert's own guard, shipped kernel-certified beside the FAILED one. The fix
//! above did not reach it. BEFORE (the integ/wave25 stage 1 at `392246d0c4`,
//! `scratchpad/stage1-w25`; the wave-24 probe reads the same): the signed four read
//! `3 proved, 1 failed` (certify `3 certified, 1 failed`) and the unsigned ones `1
//! proved, 1 failed` (`1 certified, 1 failed`). AFTER: one proved and certified row
//! fewer each. No count pin of the six matches BEFORE.
//!
//! SELF-GUARDED-LITERAL-OPERAND-2 (2026-10-13, the wave-26 scouts). Two literal shapes of
//! the same family remained, each a clean-kernel `Certified` PROVED row beside the
//! FAILED one at the span of an operation that panics on every call:
//! * a SIGNED-literal shift amount (`x << 40`: the amount defaults to `i32`, and the
//!   assert compares the cast temporary `_t = const 40 as u32`), which the shift binder
//!   refused (`v2_shift_amount_cast_source` admitted no literal source), so the
//!   statement-lane `shift:*` row, under the assert's own guard, survived beside the
//!   assert lane's generic `overflow` row;
//! * a signed `/` or `%` over TWO width-less literals (`i32::MIN / -1`), whose overflow
//!   row and its suppression took the i64 `int_op_type` fabricates for a literal pair
//!   (LITERAL-PAIR-WIDTH-1, `literal_pair_width.rs`), so the cond's `Eq(const MIN, const
//!   MIN)` never bound and the statement row read `MIN == i64::MIN`, UNSAT.
//! BEFORE (stage1-w25f, integ7's stage 1 of wave 25 at `a971311ee2`; each revision's
//! flags plus `--cfg <revision> -Zui-testing -Zdeduplicate-diagnostics=no -A unused
//! --emit=metadata`): every function below this point read `1 proved, 1 failed, 0
//! unknown, 0 timed out, 0 runtime-checked out of 2 obligation(s)` and, under certify,
//! `summary: 0 trusted, 1 certified, 1 failed`, and `ok_shl` read `2 proved, 0 failed`.
//! The division shapes also reported "1 guaranteed Level 0 safety violation(s)" under certify (the
//! assert lane's row, unchanged by the fix); the shifts did not. AFTER (FIX PREPARED
//! 2026-10-13, not built; predicted): each keeps exactly one row, FAILED, and loses the
//! certified one; `ok_shl` keeps one PROVED `shift:left` row (the generic `overflow` row
//! and the statement row were one proposition). `div_lit_lit0` above does not move: its
//! cond's conjuncts `Eq(const 0, const -1)` and `Eq(const 100, const i32::MIN)` compare
//! two different literals, which the direct suppression's binder still refuses (its
//! literal side is the left one), so its TRUE statement-lane `overflow:div` row stays,
//! now built at `i32`. No count pin below matches BEFORE.
#![allow(arithmetic_overflow, unconditional_panic)]

pub fn div_lit(x: i32) -> i32 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    100 / x
}

pub fn rem_lit(x: i32) -> i32 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    100 % x
}

// `i32::MIN / x`: its overflow rows were already deduplicated (the direct
// suppression admits `Eq(const MIN, const MIN)`); its zero-divisor rows were not.
pub fn div_min_lit(x: i32) -> i32 {
    //~^ NOTE Trust verification: 0 proved, 2 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 2 failed, 0 unknown,
    i32::MIN / x
}

pub fn e2(z: i16) -> i16 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    (-15i16) / z
}

// Two divisions: the first by a nonzero literal, the second a literal dividend over
// the first's result, which is 0 for `b < 255`.
pub fn e4(b: u8) -> i16 {
    //~^ NOTE Trust verification: 4 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 4 certified, 1 failed, 0 unknown,
    let z = (b as i16) / 32766i16;
    7i16 / z
}

pub fn n32() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    -i32::MIN
}

// Re-pinned 2026-10-15 (FORCED-OWN-EQ-1, docs/KNOWN_HAZARDS.md): a literal-zero divisor or
// an over-wide literal shift panics on EVERY run whatever `x` is, and trust-router now reads
// that: `x` appears only in its type-range hypothesis, so it no longer blocks the ground
// violation from folding (`bind_isolated_range_witnesses`). Each of the eight functions
// below that does so now carries the "guaranteed" error; before, only the all-literal ones
// did.
// ---- the literal-DIVISOR follow-up: the zero check is `Eq(const 0, const 0)` ----

pub fn div_x0(x: i32) -> i32 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x / 0
}

pub fn rem_x0(x: i32) -> i32 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x % 0
}

pub fn rem_u8_0(a: u8) -> u8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    a % 0u8
}

pub fn div_u32_0(a: u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    a / 0
}

// Two width-less literals: the chain reads `INT_MIN` at the destination's width.
pub fn div_lit_lit0() -> i32 {
    //~^ NOTE Trust verification: 2 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 2 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    100 / 0
}

pub fn rem_cast_0() -> u8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    (false as u8) % 0u8
}

// ---- SELF-GUARDED-LITERAL-OPERAND-2: a signed-literal shift amount ----

pub fn shl_lit(x: u32) -> u32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x << 40
}

pub fn shr_lit(x: i64) -> i64 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x >> 64
}

pub fn shl_u8x(x: u8) -> u8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x << 8
}

pub fn shl_i32c(x: u64) -> u64 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    x << 64i32
}

// The safe twin: one honest PROVED row instead of two copies of one proposition.
pub fn ok_shl(x: u32) -> u32 {
    //~^ NOTE Trust verification: 1 proved, 0 failed, 0 unknown, 0 timed out, 0 runtime-checked
    x << 8
}

// ---- SELF-GUARDED-LITERAL-OPERAND-2: a signed `/` or `%` over two literals ----

pub fn d_minm1() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    i32::MIN / -1
}

pub fn r_minm1() -> i32 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    i32::MIN % -1
}

pub fn d8() -> i8 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    (-128i8) / -1
}

pub fn r16() -> i16 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    i16::MIN % -1
}

pub fn d128() -> i128 {
    //~^ NOTE Trust verification: 0 proved, 1 failed, 0 unknown, 0 timed out, 0 runtime-checked
    //[certify]~^^ ERROR Trust Level 0 safety verification incomplete
    //[certify]~| ERROR Trust strict verification failed
    //[certify]~| NOTE summary: 0 trusted, 0 certified, 1 failed, 0 unknown,
    //[certify]~| ERROR 1 guaranteed Level 0 safety violation(s)
    i128::MIN / -1
}
