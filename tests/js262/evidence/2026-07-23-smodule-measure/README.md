# Evidence — S-module measurement (module-goal execution), 2026-07-23

Calibration of the **S-module** slice (module-goal core, 693 tests;
`tests/js262/S-module.toml`) with the module-goal execution driver, **after the
module-goal-detection fix** (below). Four heads (Node v24.5.0, Bun 1.3.14,
`sem`, `trustjs`), driver_sha256 `2b50648a91f56e8e…`. Each test runs from its
real corpus location (`await import(pathToFileURL(source))`) so relative imports
(siblings, self, `_FIXTURE`) resolve.

## The module-goal-detection fix

A first, unfixed run measured only 49.35% Node-vs-Bun agreement — but ~93 of
those "divergences" were a **harness bug**, caught by the divergence-audit
workflow's adversarial pass (classified `projection_too_strong`, never waived).
Root cause: the driver imports the real corpus `.js`, but with no
`package.json {"type":"module"}` at the pinned corpus root, Node's ESM loader
uses CommonJS-first source detection for a `.js` file that lacks
import/export/top-level-await — so a `flags:[module]` test relying purely on
module SEMANTICS (top-level `return`/`this`/`new.target`, module early errors)
was spuriously run in the **Script goal** by Node while Bun used the **Module
goal**. Empirically confirmed: a top-level `return` file runs clean under Node
(CommonJS) but throws `SyntaxError` under Bun (module); with a corpus
`package.json {"type":"module"}` both throw `SyntaxError` (module).

Fix (`crates/trust-js-differential/src/calibrate.rs`, driver unchanged): each
calibration self-configures the corpus goal from its slice kind — S-module writes
`<corpus>/package.json {"type":"module"}` (forcing the Module goal on both
engines for every `.js` under it, while importing the real file preserves
self-import identity), S0/S-async ensure it is ABSENT (their raw lane runs corpus
`.js` script tests directly). Result: agreement 49.35% → **62.77%**.

## Totals (after the fix)

| head | covered | NoCoverage | divergent |
|---|---|---|---|
| sem     | 0 | 693 | **0** |
| trustjs | 0 | 693 | **0** |

Both in-house heads **soundly refuse** module execution (not yet implemented —
Fatal → `NoCoverage`), ZERO wrong module traces. Making `trustjs` cover modules
(link + evaluate) is increment 2b.

### A second module-driver fix: async dynamic-import settle + uncaught-TLA capture

The divergence-audit workflow's adversarial pass then caught TWO more harness
defects (classified `projection_too_strong`, never waived): (1) **async
dynamic-import under-drain** (20 cases) — the module path drained only 64 virtual
microtask ticks, but a file-based inner `import('./x')` settles on a real host/IO
turn the virtual timers never pump, so on Bun the async `$DONE` landed after
`emit()` (0 events) vs Node's 1; and (2) it exposed that a module whose top-level
await REJECTS surfaces engine-asymmetrically — Node rejects the `import()`
promise, Bun reports an uncaught exception and exits without a completion (a
spurious harness error). Fixed in `crates/trust-js-trace/js/trace_driver.mjs`:
for `async` module cases the driver now settles real dynamic-import jobs on the
real event loop (a pre-firewall `setTimeout`, bounded, stopping at the completion
marker), and captures an uncaught top-level-await rejection on the real process
(scoped to the module branch — the script goal's `process` semantics and
determinism are untouched, proven by S0/S-async re-running byte-identical). The
`is_async` flag is threaded from the frontmatter into the manifest.

Node vs Bun: 693 cases, **0 harness errors**, 455 trace-equal, **238 divergent**
(65.66%, up from 62.77% — the ~22 async-under-drain event-count rows converged,
and the two top-level-await `fulfillment-order` tests are now cleanly captured as
real divergences rather than harness errors). **`gate.pass=true`** — all 238 Node-vs-Bun divergences are now classified in
`tests/js262/divergence-audit.toml` (S-module section) by a classify +
adversarial-verify workflow: **175 benign_host_defined** (host-defined module
error object + Bun bare-specifier auto-install), **50 bun_bug** ($DONOTEVALUATE
bodies run instead of the mandated early error, TDZ/namespace-exotic
ReferenceErrors, import.meta, JSON default-only export, top-level-await
[[AsyncEvaluationOrder]], ...), **13 node_bug** (circular/ambiguous ResolveExport,
super-access-TDZ TypeError, and static import with an unsupported attribute where
Node throws TypeError but ES2025 16.2.1.5.1.1 mandates SyntaxError). ZERO
projection_too_strong, ZERO deferred. Both in-house heads still soundly refuse
module execution (0 covered / 693 NoCoverage) — making `trustjs` COVER modules is
increment 2b.

### Divergence families (Node vs Bun) — to be classified next

| runs | family | note |
|---|---|---|
| 166 | `SyntaxError` (node) vs `BuildMessage` (bun) | module parse/early/resolution error — error OBJECT is host-defined (likely benign) |
| 52 | throw (node) vs normal (bun), or vice versa | real module-semantics splits (ambiguous star-export, ResolveExport) |
| 23 | event count 1 vs 0 | all `dynamic-import/catch/*eval-script-code-target*` — async completion of import()-ing a script-code target |
| 9 | other vs `BuildMessage` | mixed |
| 8 | `SyntaxError` (node) vs `AggregateError` (bun) | Bun wraps in AggregateError — host-defined |

The `BuildMessage`/`AggregateError` bulk (183) is very likely
`benign_host_defined` (the concrete error object of a module load/parse failure
is host-defined); the throw-vs-normal (52) and event-count (23) families need
per-family spec judgment (classify + adversarial-verify) — not pre-judged here.
