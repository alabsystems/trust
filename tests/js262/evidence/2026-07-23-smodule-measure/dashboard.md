# TrustJS S-module calibration dashboard

The published dashboard is the only permitted conformance claim.

- Generated: 2026-07-23T05:34:50Z
- Corpus: `9e61c12835c5e4a3bdba93850427e6742c4f64c4` (slice sha256 `77efc64a11dcb682c65f91424b13fb6b9400d26bd4e0f8e5b25f29830daa5dde`)
- Node: `/home/ayates/.local/opt/node-v24.5.0/bin/node` (v24.5.0)
- Bun: `/home/ayates/.local/opt/bun-1.3.14/bun` (1.3.14)
- Driver sha256: `5996b07b1da62b4989c8b6591f721720e5fa44a851c51382f71054ff6ad308e9`

| metric | value |
|---|---|
| cases | 693 |
| runs | 693 |
| trace-equal runs | 455 |
| divergent runs | 238 |
| divergent cases | 238 |
| classified divergent cases | 238 |
| unclassified divergent cases | 0 |
| harness errors (= tool failures) | 0 |
| failed | 0 |

**Gate**: unclassified_ok true, sem_audit_ok true, trustjs_audit_ok true, ledger_ok true => **pass: true** — Node==Bun agreement measured 0.656566 (the design doc's >=99.9% hypothesis is reported, not gated: hypothesis_met=false)

## Sem coverage

- sem cases: 693 — covered 0, equal 0, divergent 0, no-coverage 693

Top no-coverage reasons (top 10):

- 693 × module execution (out of slice)

## TrustJS coverage (faithful tier)

- trustjs cases: 693 — covered 0, equal 0, divergent 0, no-coverage 693

Top no-coverage reasons (top 20):

- 693 × module execution (out of slice)

## Divergences

238 divergent runs (0 unclassified). Full list: divergences.jsonl.
