# TrustJS S-module calibration dashboard

The published dashboard is the only permitted conformance claim.

- Generated: 2026-07-23T12:24:46Z
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

- trustjs cases: 693 — covered 225, equal 225, divergent 0, no-coverage 468

Top no-coverage reasons (top 20):

- 233 × top-level `await` (async module, out of slice)
- 39 × dynamic `import()` (module loader, out of slice)
- 34 × `export … from` re-export (out of slice)
- 25 × module body parse: import attributes (with clause)
- 21 × `export *` re-export (out of slice)
- 14 × global-object property miss `test262` (engine global surface unmodeled)
- 12 × top-level `for await` (async module, out of slice)
- 10 × `export … from` re-export (module loader, out of slice)
- 5 × `import.meta` (module meta object, out of slice)
- 5 × module body parse: module export name string with a lone surrogate
- 2 × exported binding `x` is reassigned (live binding, out of slice)
- 2 × module body parse: annexB html-close-comment --> (out of slice)
- 2 × string module-export-name (out of slice)
- 2 × top-level `await using` declaration (async module, out of slice)
- 2 × using declaration in a scope without an active DisposeCapability (explicit resource management, out of slice)
- 1 × dependency module threw during evaluation (out of slice)
- 1 × exported binding `fn` is reassigned (live binding, out of slice)
- 1 × module body parse: annexB html-open-comment <!-- (out of slice)
- 1 × module top-level `this` (is `undefined`, not `globalThis`)
- 1 × self-import (`./Symbol.iterator.js`)

## Divergences

238 divergent runs (0 unclassified). Full list: divergences.jsonl.
