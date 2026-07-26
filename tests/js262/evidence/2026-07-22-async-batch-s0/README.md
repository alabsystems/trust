# Evidence — S0 batch after the async correctness batch, 2026-07-22

Re-gate of the **S0** slice (68,547 cases) after the async correctness batch, to prove
the async fixes and the completion-marker normalization leave S0 sound and
byte-identical where it must be. Four heads (Node v24.5.0, Bun 1.3.14, `sem`,
`trustjs`), driver_sha256 `f83dea475e4a05f6...`.

## Totals

| head | covered | equal | divergent | no_coverage |
|---|---|---|---|---|
| sem     | 46,327 | 46,327 | **0** | 22,220 |
| trustjs | 60,743 | 60,743 | **0** |  7,804 |

`gate.pass = true`. Both in-house heads zero-divergent, zero panics; all engine
divergences classified.

## Documented soundness decrease: trustjs 60,799 → 60,743

The async batch converts a handful of previously-covered-but-**fabricated** S0 cases to
sound `NoCoverage` refusals — this is a soundness improvement, not a regression:

- **try/finally Fatal-swallow fix.** A throwing `finally` block no longer overrides an
  `Abrupt::Fatal` refusal from its `try`. Previously a Fatal refusal could be masked by
  the `finally`'s own completion, fabricating a trace; now the refusal propagates.
- **poisoned-Array-setter driver artifact.** Cases that trip the trace driver's own
  event recorder via a poisoned indexed setter on `Array.prototype` now sound-refuse
  rather than emit a driver-contaminated trace.

`divergent == 0` and `equal == covered` still hold on both heads. Landed with
`trust-js-differential ratchet --check --allow-soundness-decrease` (see the documented
entry `cov-trustjs-2026-07-22-asyncbatch` in `tests/js262/coverage.toml`). The
`--allow-soundness-decrease` flag warns rather than hard-fails a coverage decrease
**only** when the sound invariants (`divergent == 0`, `equal == covered`) still hold —
a decrease that also broke an invariant would still fail the ratchet.
