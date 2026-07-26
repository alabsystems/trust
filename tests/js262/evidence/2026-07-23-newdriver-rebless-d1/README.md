# Evidence — DEFECT-1 driver change, S0/S-async re-bless proof (2026-07-23)

The module-goal async-settle + uncaught-TLA-capture fix (increment 2 hardening)
changed the module branch of trace_driver.mjs; driver_sha256 2b50648a… → 5996b07b….
The changes are entered ONLY for `kind === 'module'` (the real-event-loop settle
for `async` cases + the unhandledRejection/uncaughtException capture, both scoped
to the module branch; the pre-firewall setTimeout capture at module top is unused
by the script path). So the script goal is byte-identical — proven by re-running
S0 and S-async under the new driver and comparing EVERY total:

- s0-scorecard.json vs ../2026-07-23-s0-proposal-rebless/scorecard.json: ALL TOTALS
  IDENTICAL (cases 34,914, sem 46,189, trustjs 60,160, both 0 divergent, gate.pass).
- sasync-scorecard.json vs ../2026-07-23-sasync-close/scorecard.json: ALL TOTALS
  IDENTICAL (sem 1,401, trustjs 809, both 0 divergent, unclassified 1).

Only driver_sha256 differs. Coverage ledgers stand unchanged; the live
dashboard.md is re-stamped to 5996b07b….
