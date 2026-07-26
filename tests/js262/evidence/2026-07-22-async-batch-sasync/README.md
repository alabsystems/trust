# Evidence — S-async batch (first measured-async slice), 2026-07-22

First calibration of the **S-async** slice (S0 rules with `require_flags=["async"]`,
5,401 cases; `tests/js262/S-async.toml`, list_sha256 `46ce5905...`), four heads
(Node v24.5.0, Bun 1.3.14, `sem`, `trustjs`), driver_sha256
`f83dea475e4a05f6...` (byte-identical to the S0 driver — the async completion-marker
normalization lives in the Rust trace layer, not the driver JS).

## Totals

| head | covered | equal | divergent | no_coverage |
|---|---|---|---|---|
| sem     | 1,431 | 1,431 | **0** | 9,138 |
| trustjs |   839 |   839 | **0** | 9,730 |

Both in-house heads are **zero-divergent** — every covered async case is trace-equal to
Node; every uncovered case is a sound `NoCoverage` refusal (`equal == covered`). The
faithful tier emits no wrong async trace. `sem_audit_ok = true`, `trustjs_audit_ok = true`.

Node vs Bun: 9,996 / 10,571 runs trace-equal = **94.56%** (up from 92.50% before the
async completion-marker normalization removed 218 message-only divergences).

## Why gate.pass = false (honest)

`gate.pass = false` because the **Node-vs-Bun** comparison has 319 unclassified
divergent cases (`unclassified_ok = false`, `ratio_ok = false`). These are real
cross-engine differences — overwhelmingly Node `Error` vs Bun `ResolveMessage` on
failed dynamic `import()` — not in-house bugs. The S-async Node-vs-Bun
divergence-audit ledger is not yet written; classifying these is the next S-async task.
Until then this evidence asserts only the in-house zero-wrong-traces coverage recorded
in `tests/js262/coverage-async.toml`, and makes **no green-gate claim** for S-async.

## What this batch fixed

The measure-first S-async run surfaced 59 faithful-tier async bugs (all fixed:
interp async divergences 59 → 0) and a `projection_too_strong` marker flaw invisible to
S0 (the async failure marker leaked engine-divergent message text; fixed in the
projection via `normalize_async_completion_markers`). It also caught two soundness bugs
— a throwing `finally` overriding an `Abrupt::Fatal` refusal, and a poisoned-Array
setter driver-artifact — both now sound refusals (the documented S0 60,799 → 60,743
soundness decrease).
