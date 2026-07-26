# TrustJS S0 calibration dashboard

The published dashboard is the only permitted conformance claim.

- Generated: 2026-07-23T08:37:38Z
- Corpus: `9e61c12835c5e4a3bdba93850427e6742c4f64c4` (slice sha256 `a8ee2a3fac84c4a5f350aa545fee14dfa09adf764fd63c40a0972f0570d78224`)
- Node: `/home/ayates/.local/opt/node-v24.5.0/bin/node` (v24.5.0)
- Bun: `/home/ayates/.local/opt/bun-1.3.14/bun` (1.3.14)
- Driver sha256: `5996b07b1da62b4989c8b6591f721720e5fa44a851c51382f71054ff6ad308e9`

| metric | value |
|---|---|
| cases | 34914 |
| runs | 67717 |
| trace-equal runs | 66798 |
| divergent runs | 917 |
| divergent cases | 551 |
| classified divergent cases | 551 |
| unclassified divergent cases | 0 |
| harness errors (= tool failures) | 0 |
| failed | 0 |

**Gate**: unclassified_ok true, sem_audit_ok true, trustjs_audit_ok true, ledger_ok true => **pass: true** — Node==Bun agreement measured 0.986429 (the design doc's >=99.9% hypothesis is reported, not gated: hypothesis_met=false)

## Sem coverage

- sem cases: 67715 — covered 46189, equal 46189, divergent 0, no-coverage 21526

Top no-coverage reasons (top 10):

- 1135 × body parse: async generator method (async generators out of slice)
- 996 × length-tracking typed array on a resizable buffer (out of slice)
- 830 × body parse: async generator function (async generators out of slice)
- 750 × loop iteration cap exceeded
- 732 × unresolved identifier `Iterator` (unmodeled global or real ReferenceError)
- 560 × body parse: invalid assignment target
- 502 × unresolved identifier `x` (unmodeled global or real ReferenceError)
- 448 × unresolved identifier `w` (unmodeled global or real ReferenceError)
- 300 × body parse: `with` statement (out of slice)
- 294 × Set-methods combinator (union/intersection/... out of slice)

## TrustJS coverage (faithful tier)

- trustjs cases: 67715 — covered 61155, equal 61155, divergent 0, no-coverage 6560

Top no-coverage reasons (top 20):

- 750 × loop iteration cap exceeded
- 242 × Promise static method on a subclass receiver (out of slice)
- 202 × unimplemented intrinsic property `toString`
- 179 × for-in over an object with unmodeled enumerable surface
- 178 × unresolved identifier `DisposableStack` (unmodeled realm global or context-restricted binding)
- 152 × with statement (out of slice)
- 144 × global-object property miss `arguments` (engine global surface unmodeled)
- 144 × unresolved identifier `AsyncDisposableStack` (unmodeled realm global or context-restricted binding)
- 134 × include[2] parse: regex: class-escape range bound (annexB)
- 129 × sloppy-function legacy `caller` own surface (engine magic slots)
- 120 × global-object property miss `p1` (engine global surface unmodeled)
- 108 × import() (M2, out of slice)
- 88 × unimplemented intrinsic property `flatMap`
- 86 × nested yield in a yield operand (out of slice)
- 86 × unimplemented intrinsic property `zipKeyed`
- 82 × unimplemented intrinsic property `toLocaleString`
- 74 × eval body needs caller context (out of slice): 'super' call outside of derived-class constructor
- 74 × unimplemented intrinsic property `filter`
- 74 × unimplemented intrinsic property `zip`
- 72 × unimplemented intrinsic property `map`

## Divergences

917 divergent runs (0 unclassified). Full list: divergences.jsonl.

## Harness errors (2)

- test/built-ins/RegExp/property-escapes/generated/strings/RGI_Emoji.js [bare]: node: timeout (excepted: js262-rgi-emoji-node-timeout)
- test/built-ins/RegExp/property-escapes/generated/strings/RGI_Emoji.js [strict]: node: timeout (excepted: js262-rgi-emoji-node-timeout)
