# Real extracted-MIR fixtures for the self-guarded-obligation regression guards

Every `*.json` here is the compiler's OWN verification input — a serialized
`trust_types::VerifiableFunction` — captured verbatim with

```sh
trustc --edition 2021 --crate-type lib -Ztrust-dump=mir:<dir> <source>.rs
```

so `tests/divzero_canary_real_mir.rs`, `tests/shift_canary_real_mir.rs` and
`tests/coroutine_resume_state_global_fact_real_mir.rs` exercise the real lowering
rather than a hand-built approximation of it. Absolute paths in the `span.file`
fields were rewritten to stable repo-relative names; nothing else was edited.

## Zero-divisor family

| fixture | source |
|---|---|
| `sentinel_div_by_zero_must_not_prove` | `clean/tests/trust_verify/vacuity_sentinel.rs` — `x / (n - n)` |
| `sentinel_remainder_by_zero_must_not_prove` | `clean/tests/trust_verify/vacuity_sentinel.rs` — `x % (n - n)` |
| `two_distinct_divisors` | `pub fn two_distinct_divisors(x: u64, n: u64, m: u64) -> u64 { (x / n) ^ (x / m) }` |
| `unguarded_call_division` | `pub fn unguarded_call_division(a: i64, b: i64) -> i64 { a.div_euclid(b) }` |
| `provably_safe_division` | `pub fn provably_safe_division(x: u64, n: u64) -> u64 { x / (n \| 1) }` |

## Coroutine-resume / path-collapse family

| fixture | source |
|---|---|
| `coroutine_resume_zero_await_widen` | `pub async fn f(x: u8) -> u16 { (x as u16) + 1 }` — the resume body, DEDICATED `Unreachable` |
| `coroutine_resume_merged_unreachable` | `pub async fn f(x: Option<u8>) -> u16 { match x { Some(v) => (v as u16) + 1, None => 0 } }` — rustc MERGES the dispatch's and the match's `otherwise` into one `Unreachable` |
| `coroutine_resume_saturated_unreachable` | the same with SEVEN sequential `Option` matches (`t = t \| match a_k { .. }`), whose merged `Unreachable` is reached by more than `MAX_PATHS_PER_BLOCK` routes — the path-cap cliff |
| `path_budget_nonasync_merged_unreachable` | `pub fn f(b0: bool, .., b12: bool, x: Option<u8>) -> u16` — thirteen `if b_i { .. }` followed by an exhaustive `Option` match; its path walk outruns the GLOBAL STEP BUDGET. A plain `fn`: the budget-trip collapse is not coroutine-specific |
| `path_budget_async_sentinel` | the `Option`-match `async fn` with THIRTEEN matches — its path walk outruns the GLOBAL STEP BUDGET (`BudgetTripped`), which is the SECOND collapse cliff — `coroutine_resume_saturated_unreachable` is the first. Carries a `ResumedAfter*` sentinel row as well as the merged `Unreachable` |
| `switch_arms_shared_target_mul_overflow` | `pub fn f(sel: u32, x: u32, y: u32) -> u32 { match sel { 0 \| .. \| 64 => { let c = x ^ y; let d = c \| 7; d * x } _ => 0 } }` — 65 arms share ONE target holding three arithmetic statements, so the target saturates AND carries a GENUINE `Mul` overflow. The COST side of the collapse repair: restoring the in-edge disjunction onto a row that has its own violation condition multiplies the formula by the in-degree and demotes the refutation to a decline. See `tests/path_guard_collapse_cost_real_mir.rs` |

The coroutine fixtures are all `{closure#0}`, the async fn's resume body: the
`async fn` item itself carries no obligations. Their value is the SHAPE named in
the table — dedicated `Unreachable`, merged `Unreachable`, path-cap saturated,
step-budget tripped; if a rustc update changes it, the fixture must be
re-captured rather than patched. The block count, step cap and collapse mode of
every collapse fixture is asserted by name in
`src/generate/path_guard_collapse_tests.rs::walk_arithmetic`, so a drift fails
there rather than passing vacuously somewhere else.

## Shift family

The source is committed beside the dumps as [`shift_arms.rs`](shift_arms.rs), so
every row can be re-derived rather than trusted. All six were produced by ONE
invocation of the command above on that file, and the `span.file` fields name it.

| fixture | source (`shift_arms.rs`) |
|---|---|
| `sentinel_shift_overflow_must_not_prove` | `clean/tests/trust_verify/vacuity_sentinel.rs` — `1u32 << (x \| 64)` |
| `sentinel_shr_overflow_must_not_prove` | `x >> (x \| 64)` — the `Shr` member of the family |
| `two_distinct_shift_amounts` | `(x << s) ^ (x << t)` |
| `provably_safe_shift` | `x << (s & 31)` |
| `unguarded_shift` | `x << s` |
| `constant_amount_shift` | `x << 8` |

MEASURED while collecting these, and worth knowing before adding a fixture for
it: `-C overflow-checks=off -C debug-assertions=off` does **not** strip a shift's
`Overflow(Shl)` assert. Shifting by at least the bit width is UB, not overflow,
so the guard is unconditional — there is no "bare `Shl` statement, no assert"
shape to extract from real source. `constant_amount_shift` was the only shape the
compiler emits where a shift statement had no assert bound to it, because the
assert guards a cast temporary (`_2 = 8 as u32`) while the shift reads the
constant directly. Since SELF-GUARDED-LITERAL-OPERAND-2 (2026-10-13) the binder
admits that literal cast source by value, so it is bound too: its one `shift:left`
row is now the assert lane's (see "Literal pair width family" below).

To regenerate, compile the source shown with the flag above and copy the dumped
JSON whose `"name"` matches.

## Projected-operand `Overflow(Div|Rem)` family

The source is committed beside the dumps as
[`divrem_projected_arms.rs`](divrem_projected_arms.rs), and all fifteen came from
ONE invocation of the command above on that file.

Under overflow checks the value rustc compares against `INT_MIN`/`-1` and then
divides is `_3.0` — the value field of a `CheckedAdd`/`CheckedSub` tuple — so the
compared value is PROJECTED. Pretty-printed `--emit=mir` renders that as a plain
local and hides the whole family; only the extracted input shows it.

| fixture | source (`divrem_projected_arms.rs`) |
|---|---|
| `projected_dividend_div` | `let a = x + 1; a / b` — the defect |
| `projected_divisor_div` | `let b = y + 1; a / b` |
| `projected_both_div` | `let a = x + 1; let b = y - 1; a / b` |
| `projected_both_rem` | the `Rem` twin |
| `two_distinct_projected_divisors` | `(a / b) ^ (a / c)` — operand exactness |
| `plain_dividend_deep_div` | `let a = x << s; a / b` — CONTROL, plain local |
| `provably_safe_projected_dividend_div` | `let a = (x & 1) + 1; a / b` — safe, keeps one real row |
| `provably_safe_projected_div` | `a / 3` — const/const cond, two rows before AND after |
| `const_min_dividend_div` / `_rem` | `i32::MIN / y` — the CONSTANT compared value, suppressed today |
| `nonmin_const_dividend_div` | `7 / y` — const identity mismatch, two rows |
| `projected_unsigned_div` | no signed overflow obligation exists |
| `unguarded_call_projected_div` | `a.div_euclid(b)` — no assert to bind to |
| `deref_operand_div` | `*p / *q` — the `&i32` base the `Deref` forged arm retargets onto |
| `index_operand_div` | `a[i] / a[j]` — the `[i32; 4]` base the `Index` forged arm retargets onto |

The last two compile to the ordinary plain-local shape: rustc copies a
deref/element read into a projection-free temporary before comparing it. They are
here because a forged `_1[_2]` or `(*_1)` compared value only TYPES when the base
local really is an array or a reference, and a forged arm whose refusal comes from
an unrelated type failure could never go red.

SELF-GUARDED-LITERAL-OPERAND-1 (2026-10-12): `nonmin_const_dividend_div` and
`const_min_dividend_div` / `_rem` are also the LITERAL-DIVIDEND fixtures of the
signed zero-divisor chain. Their intervening conjunct is `Eq(const L, const
INT_MIN)`, a literal on both sides, which the chain's literal-refusing binder never
bound, so each carried TWO zero-divisor rows, one of them vacuous. The guards are
the literal-dividend arms of `signed_divzero_chain_tests` in
`src/generate/checked_vcs.rs` and `tests/self_guarded_literal_operand_real_mir.rs`;
nothing in the dumps changed.

## Symbolic-constant operand family (SELF-GUARDED-CONST-OPERAND-1)

The source is committed beside the dumps as
[`const_operand_arms.rs`](const_operand_arms.rs), and all twelve came from ONE
invocation, run inside this directory on 2026-10-11 by the stage 1 of `5911b1325f`:

```sh
rustc --edition 2021 --crate-type lib -C debug-assertions=on -Ztrust-dump=mir:<dir> const_operand_arms.rs
```

Each `const_operand_<fn>.json` is the dump whose `"name"` is `<fn>`, re-indented to
two spaces and otherwise byte-for-byte; the spans were already file-relative. The
checked operand is a CONSTANT on both sides of the chain (`Eq(const N, const 0)`,
then `Div(x, const N)`), which no exact-binding suppressor admitted before. The
guards are `tests/self_guarded_const_operand_real_mir.rs` and the
`symbolic_constant_identity_tests` module of `src/generate/checked_vcs.rs`.

| fixture | source (`const_operand_arms.rs`) |
|---|---|
| `const_operand_neg_c` | `-N`, `N: i32` — the headline: its only negation row was the vacuous one |
| `const_operand_neg_c8` / `_neg_c64` | the width sweep |
| `const_operand_neg_c128` | `N: i128` — no BV rendering, so both lanes take the Int constructors |
| `const_operand_div_c` / `_rem_c` | `x / N`, `x % N`, unsigned |
| `const_operand_sdiv_c` / `_srem_c` | signed: zero assert, then the intervening `Overflow` assert |
| `const_operand_sdiv_c_dividend` | `N / -1` — the const generic as the dividend |
| `const_operand_shl_c` / `_shr_c` | `x << N`, `x >> N` |
| `const_operand_div_a` | `x / T::U` — a KEYED opaque scalar (`OpaqueOrigin::Const`) |

## Shift-binder residues (SHIFT-BINDER-RESIDUE-1)

The source is committed beside the dumps as
[`shift_amount_arms.rs`](shift_amount_arms.rs), and all ten came from ONE
invocation, run on 2026-10-11 by the stage 1 of `999b006b87` (`integ/wave23`):

```sh
rustc --edition 2021 --crate-type lib -C debug-assertions=on -Ztrust-dump=mir:<dir> shift_amount_arms.rs
```

Each `shift_amount_<fn>.json` is the dump whose `"name"` is `<fn>`, byte for byte
plus a trailing newline; the spans were already file-relative. These are the two
canonical rustc shift chains the shift assert binder refused after
SELF-GUARDED-CONST-OPERAND-1, so a self-guarded statement row survived beside a
generic `overflow` row: two shifts of different widths sharing a widthless shifted
constant and one amount (the by-operands width was the MINIMUM of the two), and a
SIGNED amount, which rustc checks through a same-width `as uW` cast temporary.
The guard is `tests/shift_amount_residue_real_mir.rs`.

| fixture | source (`shift_amount_arms.rs`) |
|---|---|
| `shift_amount_rev_c` / `_rev_p` | `(1i64 << N, 1i8 << N)`, const-generic and place: the wide shift first |
| `shift_amount_fwd_p` | `(1i8 << s, 1i64 << s)`: the narrow shift first, which dominates the wide one |
| `shift_amount_shl_ci` / `_shl_s` | `x << N` / `x << s` over an `i32` amount: the cast temporary |
| `shift_amount_shr_ci8` / `_shl_s64` / `_shl_s128` | the same over an `i8`, an `i64` and an `i128` amount |
| `shift_amount_rev_c_guarded` / `_shl_s_guarded` | the safe twins: no row may be refuted |

## Literal operand family (SELF-GUARDED-LITERAL-OPERAND-1)

The source is committed beside the dumps as
[`literal_operand_arms.rs`](literal_operand_arms.rs), and all five came from ONE
invocation, run inside this directory on 2026-10-12 by the stage 1 of `46e9afaf95`
(`scratchpad/stage1-w25probe`):

```sh
rustc --edition 2021 --crate-type lib -C debug-assertions=on -Ztrust-dump=mir:<dir> literal_operand_arms.rs
```

Each `literal_<fn>.json` is the dump whose `"name"` is `<fn>`, byte for byte plus a
trailing newline; the spans were already file-relative. Under
`#![allow(arithmetic_overflow)]` rustc keeps the checked `Neg` of a LITERAL
(`Eq(const MIN, const MIN); assert(!_, OverflowNeg); Neg(const MIN)`), which the
assert-lane negation builder refused, so the self-guarded statement row, built at the
i64 `operand_ty` gives the literal, was the only `negation` row. The guards are
`tests/self_guarded_literal_operand_real_mir.rs` and the `literal_negation_tests` and
`signed_divzero_chain_tests` modules of `src/generate/checked_vcs.rs`.

| fixture | source (`literal_operand_arms.rs`) |
|---|---|
| `literal_neg_min` | `-i32::MIN`: the headline, panics on every run |
| `literal_neg_min8` | `-i8::MIN`: the narrow width (`operand_ty` says i64) |
| `literal_neg_max` | `-i32::MAX`: the safe twin, keeps one honest row |
| `literal_neg_min128` | `-i128::MIN`: both lanes take the bitvector constructors |
| `literal_div_cast_divisor` | `7i16 / (b as i16)`: a literal dividend over a one-definition divisor, for the rewrite-window forged arm |

## Literal divisor family (SELF-GUARDED-LITERAL-OPERAND-1, literal-divisor follow-up)

The source is committed beside the dumps as
[`literal_divisor_arms.rs`](literal_divisor_arms.rs), and all seven came from ONE
invocation, run in a directory holding only that file on 2026-10-13 by the stage 1
of `integ/wave25` at `392246d0c4` (`scratchpad/stage1-w25`; the extraction is
compiler-side, so the vcgen fix does not change it):

```sh
rustc --edition 2021 --crate-type lib -C debug-assertions=on -Ztrust-dump=mir:<dir> literal_divisor_arms.rs
```

Each `literal_divisor_<fn>.json` is the dump whose `"name"` is `<fn>`, byte for byte plus
a trailing newline; the spans were already file-relative. Under
`#![allow(unconditional_panic)]` rustc keeps the zero check of a LITERAL divisor as
`Eq(const 0, const 0)` (and, signed, the chain's `Eq(const 0, const -1)` conjunct), which
the zero-divisor binding refused, so the self-guarded statement-lane row shipped
kernel-certified beside the assert lane's FAILED one. The guards are
`tests/self_guarded_literal_operand_real_mir.rs` and the `signed_divzero_chain_tests`
module of `src/generate/checked_vcs.rs`.

| fixture | source (`literal_divisor_arms.rs`) |
|---|---|
| `literal_divisor_div_x0` / `_rem_x0` | `x / 0`, `x % 0` (`i32`): the signed chain |
| `literal_divisor_rem_u8_0` / `_div_u32_0` | `a % 0u8`, `a / 0` (`u32`): the one hop |
| `literal_divisor_rem_cast_0` | `(false as u8) % 0u8`: a cast dividend, the scout corpus's shape |
| `literal_divisor_div_lit_lit0` | `100 / 0` (`i32`): two width-less literals, `INT_MIN` read at the destination's width |
| `literal_divisor_div_x5` | `x / 5`: the control, no statement-lane zero-divisor row and one TRUE assert-lane row |

## Literal pair width family (LITERAL-PAIR-WIDTH-1, SELF-GUARDED-LITERAL-OPERAND-2)

The source is committed beside the dumps as
[`literal_pair_width_arms.rs`](literal_pair_width_arms.rs), and all twenty-seven came from
ONE invocation, run in a directory holding only that file on 2026-10-13 by
`scratchpad/stage1-w25f` (integ7's stage 1 of wave 25 at `a971311ee2`; the extraction is
compiler-side, so the vcgen fix does not change it):

```sh
rustc --edition 2021 --crate-type lib -C debug-assertions=on -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> --emit=metadata literal_pair_width_arms.rs
```

Each `literal_pair_<fn>.json` is the dump whose `"name"` is `<fn>`, byte for byte plus a
trailing newline; the spans were already file-relative. A width-less signed literal
(`ConstValue::Int`) carries no type, so when BOTH operands of a signed `Div`/`Rem`, or both
arguments of an `unchecked_*` method call, are literals, no operand carries the operation's
width, and `int_op_type` answered the i64 `operand_ty` fabricates. A signed-literal shift
amount (`x << 40`) is checked through the cast temporary `_t = const 40 as u32`, which the
shift binder refused. The guards are `tests/literal_pair_width_real_mir.rs` and the
`literal_pair_width_tests` module of `src/generate/checked_vcs.rs`.

| fixture | source (`literal_pair_width_arms.rs`) |
|---|---|
| `literal_pair_ud8` / `_ud16` / `_ud32` / `_ud128` / `_ur8` | `unchecked_div(MIN, -1)` (`unchecked_rem` for `ur8`): a bare `Div` with no assert, the function's only obligation |
| `literal_pair_ctl_ud64` / `_ctl_ud_px` / `_ctl_ud_py` | controls: `i64` (the widths coincide), a place dividend, a place divisor |
| `literal_pair_cd8` / `_cd32` / `_cr16` / `_cd128` | `i8::MIN / -1`, `i32::MIN / -1`, `i16::MIN % -1`, `i128::MIN / -1`: the checked chain |
| `literal_pair_ctl_cd64` / `_ctl_cdsize` | controls: `i64::MIN / -1`, `isize::MIN / -1` (the verifier lane spells `isize` `Int { width: 64 }`) |
| `literal_pair_ok_cd32` | `100 / 7`: the safe twin |
| `literal_pair_ua8` / `_um8` / `_ok_ua8` | `i8::MAX.unchecked_add(1)`, `100i8.unchecked_mul(2)`, and the safe `100i8.unchecked_add(27)` |
| `literal_pair_shl_lit` / `_shr_lit` / `_shl_u8x` / `_shl_i32c` / `_shl_neg` | `x << 40` (`u32`), `x >> 64` (`i64`), `x << 8` (`u8`), `x << 64i32` (`u64`), `x << -1` (`u32`) |
| `literal_pair_ok_shl` | `x << 8` (`u32`): the safe twin |
| `literal_pair_ctl_shl_u8` / `_ctl_shl_u64` / `_ctl_shl_usize` | controls: an UNSIGNED literal amount, compared directly with no cast temporary |
