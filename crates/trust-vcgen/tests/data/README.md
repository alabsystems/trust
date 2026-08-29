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
shape to extract from real source. `constant_amount_shift` is the only shape the
compiler emits where a shift statement has no assert bound to it, because the
assert guards a cast temporary (`_2 = 8 as u32`) while the shift reads the
constant directly.

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
