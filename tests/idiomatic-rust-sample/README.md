# The idiomatic-Rust sample

Fourteen small programs written from a list of TASKS a developer would write —
an error enum, a list of defaults, a sort, a formatted message, a parse with a
fallback — **not** from the failure list, and measured only after all fourteen
existed. Untouched since.

## Why it exists

`tests/ordinary-rust-sweep/` contains **no `vec![a, b, c]` and no
`#[derive(Debug)]`**: zero of its eighty programs, measured 2026-09-20. So two of
the five rows on the project's decision queue are
invisible to it, and "sweep 69 of a possible 73" undercounts the daily-driver gap
for that reason. A corpus that cannot see an item is not evidence about it.

**Reproduced on a second toolchain, 2026-09-20:** the installed pack
(`~/trust-packs/379912412b1`, cut from a different commit than the stage1 below)
gives the **same 8 / 14, the same six programs failing, with the same causes**.
The gap is a property of the compiler's fragment, not of one build.

## Re-measured 2026-09-25, D1 increment 2 build: 13 / 14

`i04` verifies since the transitive-member `Assert` gate credits a site owned by a
local body's own accepted run (wave 3), and `i01` — a `#[derive(Debug)]` error enum
— verifies as a writer-relative CONDITIONAL pass since D1 increment 2 (`certify`
still refuses it). Still failing: `i07`, a correct refusal (the fold can overflow).

> **What "verifies" means in that count (2026-09-27, stage 1 `6387144780e`):** it
> means the build exits 0 under the default policy, not that every row is proved.
> `i04`'s closure is fully proved (`2 proved`), but its root `evens` still has
> `1 runtime-checked` row: the `[assert]` panic-freedom aggregate. That row is deferred
> to trust-mc's whole-function transport. On `6387144780e` the transport refused to admit
> it ("block #1 instruction 0 executes Undef"). That was fixed in `58218475038`, and the
> transport now stops at a declined call summary, the `ValidBorrow` stamp that D5-C's
> bundle-wide conjunct 3 withholds. Later the same day conjunct 3 was re-scoped to the
> lowered module, and `i04` now PASSES `certify`: the closure has 2 rows proved and `evens`
> has 1 proved, with 0 runtime-checked. See `docs/DECISION_QUEUE.md` D5.

## Re-measured 2026-09-25 (stage 1 `50bc1adc4`, the wave-2 build): 11 / 14

`i10` now verifies as a CONDITIONAL pass under D1 increment 1 (the
writer-relative class: its only unproved rows are its own `Formatter`'s writer,
discharged at the `println!` sink; `certify` still refuses it). `i13` verifies
under D2 tier 1 (`ADAPTER_YIELD`, disclosed as a modeled fact). `i02` was already
fixed (vec![] drop-glue stamp, W3). Still failing: `i01` (a derived `Debug` on an
error enum — later D1 increments), `i04` (closure fixed by D5-C; its ROOT is
refused by the transitive-member `Assert` gate — addressed 2026-09-25, see
below, awaiting a build), `i07` (a correct refusal).

## The measurement (2026-09-20, stage1 `5fc1c43f64`)

**8 / 14 verify.** The six failures, each traced to its cause rather than named
by its symptom:

| program | cause | queue row |
|---|---|---|
| `i01_error_enum_with_debug` | `<dyn fmt::Write>::write_str` | **D1** |
| `i10_newtype_display` | `<dyn fmt::Write>::write_str` | **D1** |
| `i02_vec_literal_of_defaults` | `MaybeUninit` union projection | *work* (ay L6) |
| `i13_slice_windows_check` | closure root, unconstrained parameter | **D2** (tier 1, 2026-09-24: the `ADAPTER_YIELD` modeled fact; re-measure) |
| `i07_fold_a_total` | `[overflow:add]` — a CORRECT refusal | — |
| `i04_filter_collect` | closure: `Load` with no `ValidBorrow` in a B-lane member (D5-C, fixed 2026-09-24); root: the transitive-member `Assert` gate | **D5** |

**Three of the six are queued decisions**, one is work (the union projection: the
tree's own test says a union fails closed *until* trust-ir has a union
representation, so it is an IR gap, not a ruling). One is a correct refusal:
`v.iter().fold(0u64, |a, &x| a + x as u64)` really can overflow `u64` — it needs
about 2^32 elements, which is 16 GiB of `u32`, large but not unreachable.

**The sixth was unnamed and now is not.** `i04`'s diagnostic says only that some
construct would not lower. Named behaviourally, without a build, by asking what
distinguishes it from a neighbour that lowers:

```
filter(|x| x % 2 == 0)    &u32 % u32,  Rem BRANCHES (div-by-zero)   -> does not lower
filter(|&x| x % 2 == 0)   destructured to a value                   -> lowers
filter(|x| *x % 2 == 0)   explicit deref                            -> lowers
filter(|x| x & 1 == 0)    &u32 & u32,  BitAnd is straight-line       -> lowers
```

So it is not reference arithmetic — it is a BRANCHING callee body, which needs a
phi the bridge does not have, so the value goes through `Alloca`/`Store`/`Load`
and `try_direct_call_summary` declines on the `Load`. That is the same item as
sweep `s03`, now **D5**, not a new one.

**The workaround is real and cheap:** `|&x|` or `|*x|` both verify. It belongs in
the diagnostic, which currently names neither the construct nor the fix.

**Corrected 2026-09-24 (D5-C).** The table above has the right rows and the
wrong reason. `filter(|x| x & 1 == 0)` declines on the SAME `Load` under
`-Ztrust-policy=certify`. It passes by default only because the policy tolerates
the row, and because `bitand` has no `Assert` for the ROOT's transitive-member
gate to refuse. The `Load` is `*self` through the operator impl's reference
parameter. It declined because monomorphic-foreign members were never classified
for `ValidBorrow`, and that is now fixed
(`compiler/rustc_mir_transform/src/trust_verify/bundled_borrow_provenance.rs`).
What still refuses `i04`'s root is
`ensure_bundled_member_asserts_exactly_charged`: `rem` carries an `Assert` and is
reached only through the closure.

**2026-09-25 (implemented, not yet measured).** That gate now credits the
closure's call site to the closure's own accepted run, which charged and proved
its exact `Precondition` row (`trust_verify/member_assert_ownership.rs`). BEFORE,
on stage 1 `43b8fe6ab`: **11 / 14**, `i04` refused by that gate. PREDICTED after:
**12 / 14**. The prediction rests on `filter(|x| x & 1 == 0).collect()`, whose
bundle has the same 38 members with a member that has no `Assert`, and which
builds rc=0 on that snapshot with the root's aggregate row `runtime-checked`.
Re-measure before quoting it.

## What D1 costs, made concrete here

`i10` is a hand-written `Display` whose whole body is `f.write_str("port")`. It is
blocked on the same callee as `#[derive(Debug)]`. So D1 does not gate *the
derive* — it gates **writing anything at all** from a `Display`/`Debug` impl,
which is most formatting code a daily driver would meet.

## Reading it honestly

Fourteen programs chosen by one author in one sitting is a small sample and its
composition reflects that choice. It is not a replacement for the eighty-program
sweep; it is the complement the sweep cannot provide. **Do not add a program to
it because that program fails** — that is the curated-probe defect this repo has
already recorded twice, and it would make the count meaningless.

Runner: `scripts/idiomatic_rust_sample.sh`.
