# W16 monomorphic-instance harvest — 2026-07-25

**OBSERVATIONAL ONLY.** These dumps carry no proof authority. The mono hook that
produced them is documented as emitting "no proof, changes no verdict, and grants no
transport credit" (`reports/w16-monomorphic-extraction-2026-07-16.md` §0), and that is
unchanged here.

## What this is

A fresh harvest of CONCRETE monomorphic instances of GENERIC stdlib functions — the
population W16 blocks. It exists to answer one question with data: *does monomorphizing
generic stdlib bodies actually make them provable?*

## Generation

```
TRUST_DUMP_MONO=1 build/aarch64-apple-darwin/stage2/bin/trustc probe.rs \
  -O --crate-type bin -o <out> \
  -Ztrust-dump-mir=<dir> -Ztrust-verify-survey
```

- `trustc` = `rustc 1.99.0-dev (ad0719550 2026-07-21) (trustc)`, the in-tree stage2
  build. **NOTE THE VERSION SKEW:** that toolchain predates this repo HEAD. Trust's
  version stamp embeds HEAD, so these dumps and a HEAD-built harness do NOT share a
  commit. That is acceptable *only* because this set is observational; it must never be
  promoted to a certification artifact without a HEAD-matched re-harvest.
- The `-o /dev/null` form fails late with a temp-dir error, which trips the hook's
  no-errors precondition. Use a real output path.
- Requires real codegen (the hook checks `output_types.should_codegen()`), so
  `--emit=metadata` / `-Zno-codegen` will silently produce nothing.

## Measured result (per-function, each body isolated in its own process)

23 bodies; **17 inhabited, 0 kernel_rejected**. The monomorphic stdlib instances that
PROVE:

| body | status |
|---|---|
| `<i32 as Ord>::min` / `::max` | **inhabited** |
| `<u8 as Ord>::min` / `::max` | **inhabited** |
| `core::cmp::impls::<impl PartialOrd for i32>::lt` | **inhabited** |
| `core::cmp::impls::<impl PartialOrd for u8>::lt` | **inhabited** |
| `core::fmt::num::<impl Debug for i32>::fmt` | **inhabited** |
| `core::cmp::impls::<impl Ord for i32>::clamp` | **not_grounded** (W-NESTED-SELECT) |
| `probe::generic_id` / `generic_add` (the un-monomorphized generics) | not_grounded — correct |

**This is the W16 thesis demonstrated:** the same `cmp` family that is 0-of-12 when
extracted generically (`stdlib-leaf-cmp-2026-07-16/dumps`) proves once monomorphized.
The recognizers were ready; extraction was the blocker.

**An update to the 2026-07-16 report:** it recorded `PartialOrd::lt` as rejected
(`W-DEREF-CMP-LEAF` — "empty body with an undefined return place after extraction").
Under this newer toolchain `lt` extracts with a real body and **inhabits**. That item
appears closed by later extraction work; re-verify before citing it as open.

## The remaining blocker — CORRECTED 2026-07-25

`clamp` is `not_grounded`. Its shape is a 3-way nested select over primitive comparisons plus a
diverging panic arm:

```
bb0: _4 = Le(min,max);  switchInt -> bb2(panic) | bb1
bb1: _7 = Lt(self,min); switchInt -> bb4 | bb3(_0 = min)
bb4: _8 = Gt(self,max); switchInt -> bb6(_0 = self) | bb5(_0 = max)
bb2: build core::fmt::Arguments -> call panic_fmt (target: null, DIVERGING)
```

### The blocker is the DIVERGING PANIC ARM, not the nested select

Two experiments settle it:

1. **`ctl_clamp_i32`** (`cmp-monomorphic-2026-07-16/controls/`) is a hand-authored 3-arg nested
   select with no panic arm. Measured: **inhabited**. So the nested-select shape already proves.
2. Take the REAL harvested `clamp`, replace bb2 with a bare `Unreachable` block — CFG shape
   preserved, both switch edges still distinct — and drop the fmt-only locals. Measured:
   **inhabited**.

⇒ The nested select is fine. What blocks `clamp` is the panic arm: its `core::fmt::Arguments`
construction and ~20 unsupported locals (`fmt::rt::Argument`, `FnPtr`, `RawPtr`, `NonNull`), all
of which exist ONLY on a path that provably never returns.

### CORRECTION — an earlier version of this file claimed the opposite

The first commit of this fixture stated the panic-arm hypothesis was *refuted*, on the strength of
an experiment that deleted bb2 and redirected its predecessor edge to bb1. **That experiment was
invalid:** it left bb0's `SwitchInt` with `targets [0 -> bb1] otherwise bb1`, i.e. both edges to
the same block — a degenerate switch that declines for its own reasons, unrelated to the panic
arm. The corrected experiment above preserves the CFG shape and reverses the conclusion. The
2026-07-16 report's `W-NESTED-SELECT` diagnosis is therefore ALSO superseded for this body: the
select is not what stops it.

## Next increment (scoped) — DIVERGING-ARM ELISION, not a select recognizer

The real gap is general and worth far more than `clamp`: **a block that provably never returns
must not force its locals or statements to be groundable.** `clamp`'s panic arm ends in a `Call`
with `target: null`; nothing on that path can contribute to `_0`, yet its `fmt` machinery
currently sinks the whole body.

Every Rust function carrying an `assert!`, a bounds check, an arithmetic overflow check, or any
`panic!` has exactly this shape, so closing it reaches far beyond the `cmp` family.

Soundness requirements this must meet, inherited from the 2026-07-16 ruling on this area:
- divergence must be **proven structurally** (`Call` with `target: None`, or `Unreachable`), never
  assumed from a callee name;
- the elided block must be shown to contribute NO value to `_0` on any path that reaches `Return`
  — exact reaching-definition accounting, not a predecessor-count heuristic (that heuristic was
  explicitly rejected because "overwrites and intervening effects can forge its shape");
- unwind/cleanup edges must be accounted for: `cfg_reachable_from` does not walk them, so a
  cleanup block that writes `_0` must not become invisible.
