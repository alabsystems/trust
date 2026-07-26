# Evidence — S-async gate closure, 2026-07-23

The S-async slice (async core) re-gated on the **proposal-corrected slice**
(5,279 files / 10,325 runs) after the double-`$DONE` truncation fix, with the
Node-vs-Bun divergence audit applied. Four heads (Node v24.5.0, Bun 1.3.14,
`sem`, `trustjs`), driver_sha256 `f83dea475e4a05f6…`.

## Totals

| head | covered | equal | divergent | no_coverage |
|---|---|---|---|---|
| sem     | 1,401 | 1,401 | **0** | 8,924 |
| trustjs |   809 |   809 | **0** | 9,516 |

Both in-house heads **zero-divergent** — every covered async case is trace-equal
to Node, every uncovered case a sound `NoCoverage` refusal (`equal == covered`).
`sem_audit_ok = true`, `trustjs_audit_ok = true`.

## Node-vs-Bun classification: 237 of 238 cases

`ledger_ok = true` (every audit entry well-formed, **no `projection_too_strong`
resting waiver**). The 238 divergent cases (443 runs) are classified in
`tests/js262/divergence-audit.toml` (S-async section, 2026-07-23) by a
classify + **adversarial-verify** workflow — each verdict independently
re-derived against ECMA-262 and re-run on both engines:

- **219 paths / 419 runs — benign_host_defined**: a failed dynamic `import()`
  rejects with Node `Error` vs Bun `ResolveMessage`; the error constructor for a
  `HostLoadImportedModule` failure is host-defined (both permitted).
- **17 paths / 20 runs — bun_bug**: for-await-of object-destructuring identifier
  resolution order (TDZ); `yield*` delegated-value non-unwrap / microtask order;
  `for await (async of …)` LHS parse. Node conforms, Bun deviates.
- **1 path / 2 runs — node_bug**: `await using` invalid-assignment target must
  throw (immutable-binding `SetMutableBinding`, 9.1.1.1.5); Node lets it succeed.

## The one deferred case — `gate.pass = false`, honestly

`unclassified_divergent_cases = 1`:
`test/language/expressions/dynamic-import/import-errored-module.js`. This is a
**confirmed harness limitation** (`projection_too_strong`), not a real engine
divergence: the script-eval driver indirect-evals the test body, so its relative
`import('./…_FIXTURE.js')` resolves against `trace_driver.mjs` rather than the
test directory. Node's not-found `Error` spuriously satisfies the test's
`assert.throwsAsync(Error, …)` while Bun's `ResolveMessage` fails — a
harness-induced pass/fail split. `projection_too_strong` is **never** a resting
waiver (it would break `ledger_ok`), so this row is intentionally left
unclassified and is resolved by the **S-module module-goal driver** (correct
import base URL + module-load settle), not by a waiver. The gate is therefore
classified on every runnable S-async row but this one.

## What the audit bought (vs. rubber-stamping)

The adversarial-verify pass turned a naive "waive 573 divergences benign" into
four real findings: a **slice-contract bug** (proposal-feature exclusion missed
10 of 16 proposals — 432 S0 / 122 S-async files wrongly admitted; fixed
separately), a **projection over-count** (double-`$DONE`; fixed), a **confirmed
harness base-URL bug** (`import-errored-module`; deferred to S-module), and the
**correct direction** on 8 eval-code cases the first pass had backwards.
