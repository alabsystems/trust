# TrustJS S-async calibration dashboard

The published dashboard is the only permitted conformance claim.

- Generated: 2026-07-22T23:37:00Z
- Corpus: `9e61c12835c5e4a3bdba93850427e6742c4f64c4` (slice sha256 `46ce5905cb6a69fc22f301734ac0b8f98b74c214a343e4cbb3aab40db5896ffe`)
- Node: `/home/ayates/.local/opt/node-v24.5.0/bin/node` (v24.5.0)
- Bun: `/home/ayates/.local/opt/bun-1.3.14/bun` (1.3.14)
- Driver sha256: `f83dea475e4a05f60ff88a1437c103eea361d8d97d8f48d3b6a7db15f7d47f50`

| metric | value |
|---|---|
| cases | 5401 |
| runs | 10571 |
| trace-equal runs | 9996 |
| divergent runs | 573 |
| divergent cases | 319 |
| classified divergent cases | 0 |
| unclassified divergent cases | 319 |
| harness errors (= tool failures) | 2 |
| failed | 319 |

**Gate**: unclassified_ok false, sem_audit_ok true, trustjs_audit_ok true, ledger_ok true => **pass: false** — Node==Bun agreement measured 0.945606 (the design doc's >=99.9% hypothesis is reported, not gated: hypothesis_met=false)

## Sem coverage

- sem cases: 10569 — covered 1431, equal 1431, divergent 0, no-coverage 9138

Top no-coverage reasons (top 10):

- 3951 × body parse: async generator method (async generators out of slice)
- 3028 × body parse: async generator function (async generators out of slice)
- 758 × body parse: expected `(`, found Ident("await")
- 370 × body parse: `import` statement (out of slice)
- 287 × body parse: reserved word `import` as expression
- 144 × unimplemented intrinsic property `fromAsync` (intrinsic host statics)
- 82 × read of engine-specific error message text
- 48 × unresolved identifier `AsyncDisposableStack` (unmodeled global or real ReferenceError)
- 46 × body parse: new.target (out of slice)
- 42 × body parse: expected `;`, found Ident("x") (no ASI opportunity)

## TrustJS coverage (faithful tier)

- trustjs cases: 10569 — covered 839, equal 839, divergent 0, no-coverage 9730

Top no-coverage reasons (top 20):

- 4158 × async class method (M2, out of slice)
- 3421 × async generator function (out of slice)
- 770 × for-await-of (async, M2)
- 651 × import() (M2, out of slice)
- 164 × unimplemented intrinsic property `fromAsync`
- 84 × using declaration (out of slice)
- 82 × read of engine-specific synthetic message text
- 62 × Promise combinator with a patched resolve/then protocol (out of slice)
- 52 × unresolved identifier `AsyncDisposableStack` (unmodeled realm global or context-restricted binding)
- 48 × global-object property miss `arguments` (engine global surface unmodeled)
- 34 × Promise static method on a subclass receiver (out of slice)
- 32 × body parse: import.defer (deferred imports)
- 31 × yield in an unsupported expression position (out of slice)
- 22 × Promise combinator over an element with an observable custom `then` (out of slice)
- 20 × sloppy-function legacy `caller` own surface (engine magic slots)
- 18 × unimplemented intrinsic property `dispose`
- 12 × unimplemented intrinsic property `asyncDispose`
- 10 × await using declaration in a for-statement head (explicit resource management, out of slice)
- 10 × global-object property miss `Symbol.unscopables` (engine global surface unmodeled)
- 8 × Promise.prototype.finally: observable `then` on the intermediate promise (out of slice)

## Divergences

573 divergent runs (573 unclassified). Full list: divergences.jsonl.

Top unclassified divergences:

- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-func-decl-declare-arguments-and-assign.js` [bare] fp `432e254e7d647a13`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-func-decl-declare-arguments.js` [bare] fp `b81bd3e18492cd1c`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-lex-bind-declare-arguments-and-assign.js` [bare] fp `b2bf044b7ac906c6`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-lex-bind-declare-arguments.js` [bare] fp `a9458bd2688b209f`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-var-bind-declare-arguments-and-assign.js` [bare] fp `f8423bc377d005c7`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-fn-body-cntns-arguments-var-bind-declare-arguments.js` [bare] fp `c3d6ec7b9ffce9e0`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-no-pre-existing-arguments-bindings-are-present-declare-arguments-and-assign.js` [bare] fp `186b86268e8c7936`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-decl-no-pre-existing-arguments-bindings-are-present-declare-arguments.js` [bare] fp `a29dcbd92c795a71`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-func-decl-declare-arguments-and-assign.js` [bare] fp `5f1aadd756d6fa8c`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-func-decl-declare-arguments.js` [bare] fp `6c6db3ddfa35dac2`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-lex-bind-declare-arguments-and-assign.js` [bare] fp `d5d17fdc296fa03a`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-lex-bind-declare-arguments.js` [bare] fp `b5dd0b69d2ede1b7`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-var-bind-declare-arguments-and-assign.js` [bare] fp `19471d3186f08a24`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-fn-body-cntns-arguments-var-bind-declare-arguments.js` [bare] fp `eea9591515d34f20`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-no-pre-existing-arguments-bindings-are-present-declare-arguments-and-assign.js` [bare] fp `5fae713bc7252d0d`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-named-no-pre-existing-arguments-bindings-are-present-declare-arguments.js` [bare] fp `963f4998453f3a94`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-func-decl-declare-arguments-and-assign.js` [bare] fp `268e959e3b57a831`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-func-decl-declare-arguments.js` [bare] fp `c79ccd5083ae2f9f`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-lex-bind-declare-arguments-and-assign.js` [bare] fp `54f16cfac258a906`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-lex-bind-declare-arguments.js` [bare] fp `d6463b4335590ea1`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-var-bind-declare-arguments-and-assign.js` [bare] fp `0b6370cd7e61bff1`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-fn-body-cntns-arguments-var-bind-declare-arguments.js` [bare] fp `5e838a444b369267`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-no-pre-existing-arguments-bindings-are-present-declare-arguments-and-assign.js` [bare] fp `1fe46c86a86a6ffa`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-func-expr-nameless-no-pre-existing-arguments-bindings-are-present-declare-arguments.js` [bare] fp `52bb12dbebb8e717`: event count: 2 vs 1 (left head has 2)
- `test/language/eval-code/direct/async-meth-fn-body-cntns-arguments-func-decl-declare-arguments-and-assign.js` [bare] fp `91de2969f56f2b7e`: event count: 2 vs 1 (left head has 2)

## Harness errors (2)

- test/language/statements/await-using/syntax/await-using-invalid-assignment-next-expression-for.js [bare]: node: trace extraction failed: no trace sentinel in engine stdout (tail: "") (stderr tail: "")
- test/language/statements/await-using/syntax/await-using-invalid-assignment-next-expression-for.js [strict]: node: trace extraction failed: no trace sentinel in engine stdout (tail: "") (stderr tail: "")
