# Evidence — module-goal driver change, S0/S-async re-bless proof (2026-07-23)

The module-goal execution driver (increment 2) added a `manifest.kind === 'module'`
branch to `crates/trust-js-trace/js/trace_driver.mjs` (evaluate the test as an ES
module via `await import(pathToFileURL(source))` instead of `indirectEval(body)`).
This changed `driver_sha256`:

```
f83dea475e4a05f60ff88a1437c103eea361d8d97d8f48d3b6a7db15f7d47f50   (old)
2b50648a91f56e8e86e03b2c630970448a31c58fdd66349f7222628c63c9c5b0   (new)
```

The module branch is entered ONLY for `kind === 'module'`; the script-goal path
(`indirectEval(body)`, bare/strict prefix) is byte-identical. This is proven here:
S0 and S-async were fully re-run with the new driver and **every total** compared
against the committed baseline evidence.

- `s0-scorecard.json` (new driver) vs `../2026-07-23-s0-proposal-rebless/scorecard.json`:
  **all 20 totals identical** — cases 34,914, runs 67,717, sem covered 46,189,
  trustjs covered 60,160, both 0 divergent, 0 harness errors, ratio 0.98642881…,
  gate.pass=true.
- `sasync-scorecard.json` (new driver) vs `../2026-07-23-sasync-close/scorecard.json`:
  **all 20 totals identical** — sem covered 1,401, trustjs covered 809, both 0
  divergent, runs 10,327, divergent_runs 443, unclassified 1.

Only `driver_sha256` differs. The committed S0/S-async coverage ledgers therefore
stand unchanged; the live `tests/js262/dashboard.md` is re-stamped to the new
`driver_sha256`. The historical evidence dirs (produced under the old driver) are
left immutable — they accurately record what was measured at the time.
