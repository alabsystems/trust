# TrustJS S-async calibration dashboard

The published dashboard is the only permitted conformance claim.

- Generated: 2026-07-23T11:59:15Z
- Corpus: `9e61c12835c5e4a3bdba93850427e6742c4f64c4` (slice sha256 `4b6f31207c4688a7a463d45f07013b116ae53255ae67087660dffc3259d0f12e`)
- Node: `/home/ayates/.local/opt/node-v24.5.0/bin/node` (v24.5.0)
- Bun: `/home/ayates/.local/opt/bun-1.3.14/bun` (1.3.14)
- Driver sha256: `5996b07b1da62b4989c8b6591f721720e5fa44a851c51382f71054ff6ad308e9`

| metric | value |
|---|---|
| cases | 5279 |
| runs | 10327 |
| trace-equal runs | 9882 |
| divergent runs | 443 |
| divergent cases | 238 |
| classified divergent cases | 237 |
| unclassified divergent cases | 1 |
| harness errors (= tool failures) | 2 |
| failed | 1 |

**Gate**: unclassified_ok false, sem_audit_ok true, trustjs_audit_ok true, ledger_ok true => **pass: false** — Node==Bun agreement measured 0.956909 (the design doc's >=99.9% hypothesis is reported, not gated: hypothesis_met=false)

## Sem coverage

- sem cases: 10325 — covered 1401, equal 1401, divergent 0, no-coverage 8924

Top no-coverage reasons (top 10):

- 3951 × body parse: async generator method (async generators out of slice)
- 3012 × body parse: async generator function (async generators out of slice)
- 758 × body parse: expected `(`, found Ident("await")
- 296 × body parse: `import` statement (out of slice)
- 253 × body parse: reserved word `import` as expression
- 144 × unimplemented intrinsic property `fromAsync` (intrinsic host statics)
- 48 × unresolved identifier `AsyncDisposableStack` (unmodeled global or real ReferenceError)
- 46 × body parse: new.target (out of slice)
- 42 × body parse: expected `;`, found Ident("x") (no ASI opportunity)
- 30 × body parse: expected `;`, found Ident("_") (no ASI opportunity)

## TrustJS coverage (faithful tier)

- trustjs cases: 10325 — covered 4987, equal 4987, divergent 0, no-coverage 5338

Top no-coverage reasons (top 20):

- 2313 × for-await-of (async, M2)
- 1612 × async generator yield* delegation (out of slice)
- 613 × import() (M2, out of slice)
- 176 × unimplemented intrinsic property `fromAsync`
- 125 × yield in an unsupported expression position (out of slice)
- 94 × await using declaration (async explicit resource management, out of slice)
- 62 × Promise combinator with a patched resolve/then protocol (out of slice)
- 60 × sloppy-function legacy `caller` own surface (engine magic slots)
- 58 × unresolved identifier `AsyncDisposableStack` (unmodeled realm global or context-restricted binding)
- 48 × global-object property miss `arguments` (engine global surface unmodeled)
- 32 × async generator .return() (out of slice)
- 22 × Promise combinator over an element with an observable custom `then` (out of slice)
- 12 × Promise subclass @@species (out of slice)
- 10 × AsyncGeneratorFunction constructor (eval-like, out of slice)
- 10 × Promise.prototype.finally on a non-intrinsic-promise receiver (out of slice)
- 10 × await using declaration in a for-statement head (explicit resource management, out of slice)
- 10 × global-object property miss `Symbol.unscopables` (engine global surface unmodeled)
- 9 × sloppy-function legacy `arguments` own surface (engine magic slots)
- 8 × Promise.prototype.finally: observable `then` on the intermediate promise (out of slice)
- 8 × sloppy block-level function declaration (Annex B, out of slice)

## Divergences

443 divergent runs (2 unclassified). Full list: divergences.jsonl.

Top unclassified divergences:

- `test/language/expressions/dynamic-import/import-errored-module.js` [bare] fp `1610861449e3060f`: event[0]: stdout(1 args): [{"t":"str","v":"Test262:AsyncTestComplete"}] vs stdout(1 args): [{"t":"str","v":"Test262:AsyncTestFailure:Test262Error"}]
- `test/language/expressions/dynamic-import/import-errored-module.js` [strict] fp `ee322ef9f572035d`: event[0]: stdout(1 args): [{"t":"str","v":"Test262:AsyncTestComplete"}] vs stdout(1 args): [{"t":"str","v":"Test262:AsyncTestFailure:Test262Error"}]

## Harness errors (2)

- test/language/statements/await-using/syntax/await-using-invalid-assignment-next-expression-for.js [bare]: node: trace extraction failed: no trace sentinel in engine stdout (tail: "") (stderr tail: "")
- test/language/statements/await-using/syntax/await-using-invalid-assignment-next-expression-for.js [strict]: node: trace extraction failed: no trace sentinel in engine stdout (tail: "") (stderr tail: "")
