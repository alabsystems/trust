<!--
tests/js262/README.md — the js262 calibration ledger directory.
Author: Andrew Yates
Copyright 2026 Andrew Yates | License: MIT OR Apache-2.0
-->

# tests/js262 — TrustJS M0 calibration ledgers

This directory is the **M0 calibration discipline** for TrustJS
(the internal 2026-07-20 TrustJS M0 scope note,
deliverables D3 + D5): the committed, payload-external evidence that the
`ObservableTrace` differential harness (`crates/trust-js-trace` +
`crates/trust-js-differential`) measures the right observables at the right
strength — proven by pointing it at two independent mature engines (Node, Bun)
**before any in-house engine exists**. It clones the `tests/upstream-rust/`
ledger discipline for the Test262 suite.

## Files

| File | Role |
|---|---|
| `corpus-pin.json` | `trust.js262.corpus-pin.v1`: the pinned Test262 revision + sha256 of every `harness/*.js` payload + `manifest_hash`. The corpus itself is payload-external (fetched, never committed). |
| `S0.toml` | The frozen "modern sync core" slice: selection rules + derived `count`/`list_sha256`. Re-derivable from the pinned corpus; drift fails closed. |
| `baseline.toml` | Seed calibration baseline. All entries are `status = "unknown"` until a real calibration scorecard populates them — never hand-edit a status. |
| `test-exceptions.toml` | Per-test expiring waivers (mandatory owner/reason/`reviewed_on`/`expires_on`). |
| `divergence-audit.toml` | Classification of every residual head-vs-head divergence, pinned by `{path, mode, fingerprint}`. |

## The corpus pin

Test262 is pinned at commit
`9e61c12835c5e4a3bdba93850427e6742c4f64c4`
(`https://github.com/tc39/test262.git`, snapshot 2026-07-21) into
`build/js262/test262-<sha>`. Fetch + verify (idempotent, fail-closed on any
revision or payload-checksum drift):

```bash
scripts/js262/fetch_corpus.sh
```

which is equivalent to `git init; git remote add origin <repo>; git fetch
--depth 1 origin <sha>; git checkout FETCH_HEAD` followed by a `rev-parse`
check against the pin and a sha256 check of every `corpus-pin.json` payload.

## The S0 slice

A test file is IN S0 iff **all** of: its corpus-relative path starts with
`test/language/` or `test/built-ins/`; it does not start with
`test/intl402/`, `test/staging/`, `test/annexB/`, or
`test/built-ins/Temporal/`; the filename ends `.js` and not `_FIXTURE.js`;
its frontmatter `flags` contain none of `async`, `module`, `CanBlockIsTrue`,
`CanBlockIsFalse`; the raw content does not contain the substring `$262.`;
its frontmatter `features` contain none of `Atomics`,
`SharedArrayBuffer`, `Temporal`, `tail-call-optimization`, `IsHTMLDDA`,
`cross-realm`, `host-gc-required`, nor any feature containing `Intl`;
its `features` contain no **proposal-stage** feature, where the proposal set
is read from the pinned corpus's own `features.txt`
"`## Proposed language features`" section (pin-derived, so this rule can
never be tuned to observed engine agreement); and its frontmatter `includes`
name no harness file whose content contains `$262.` (e.g.
`detachArrayBuffer.js` — assembling those would test the harness stub, not
the engines). The sorted list's count and sha256 are frozen in
`S0.toml [derived]`; the full path list is re-derived, never committed.

## Running the calibration gate

```bash
# thin wrapper (fetch + verify + run):
scripts/js262/calibrate.sh

# or directly, from the crates/ workspace:
cd crates && RUSTC_BOOTSTRAP=1 cargo run -j 4 -p trust-js-differential -- \
  calibrate \
  --corpus ../build/js262/test262-9e61c12835c5e4a3bdba93850427e6742c4f64c4 \
  --slice ../tests/js262/S0.toml --sem
```

Engines are pinned: Node v24.5.0 and Bun 1.3.14, resolved from `PATH` (or
`--node`/`--bun`, or `TRUST_JS_NODE` / `TRUST_JS_BUN` for an install outside
`PATH`). Every route asserts the pin and aborts on a mismatch: the divergence
ledgers classify trace text produced by *these* builds, so a run against
another engine is not evidence about anything they describe. The resolved
version and binary sha256 are part of the scorecard's evidence identity. Never
run unbounded parallel builds — keep `-j 4`.

## Fail-closed rules

- Corpus revision or payload-checksum drift ⇒ fetch/verify exits nonzero; no
  run happens on a drifted corpus.
- `S0.toml [derived]` mismatch (count or `list_sha256`) ⇒ gate exits 1.
- An `active` exception with `expires_on` ≤ the validation date
  (`TRUST_JS262_VALIDATION_DATE`, default today) ⇒ gate exits 1.
- Any unclassified divergence, nonzero failed/tool-failure totals, or an
  incomplete artifact set ⇒ gate exits 1.
- `projection_too_strong` is **never waivable**: it is a harness bug — fix
  `crates/trust-js-trace` and re-run; it cannot rest in any ledger as an
  accounted divergence.

## Gate semantics and the 99.9% hypothesis

The M0 design doc's "Node and Bun are trace-equal on ≥99.9% of the slice"
figure is a **hypothesis the calibration measures and reports** — it is not a
pass condition. The gate passes when the apparatus is calibrated: every
divergence carries an active classification (none of them
`projection_too_strong`), the sem coverage audit equation holds
(`covered + no_coverage == cases`, zero sem divergences), the ledgers
validate, and the run is complete. The measured agreement ratio and whether
the hypothesis held are first-class scorecard fields — reported, never
hidden, never gated on.

Two projection-strength rulings from the 2026-07-21 calibration are part of
the trace contract: engine-incidental own properties on Error instances
(V8's `stack` accessor; JSC's `line`/`column`/`sourceURL`/`originalLine`/
`originalColumn`) are filtered from the deep print, and the Normal-completion
witness is **opt-in** per case manifest (V8 and JSC genuinely diverge on
spec-corner eval completion values; no test relies on them — the witness
remains available for engine-vs-sem differential work).

## Conformance claims

**The published dashboard emitted by the calibration scorecard is the only
permitted conformance claim.** No pass percentage, trace-equality rate, or
"supported subset" statement may be quoted from anywhere else — not from ad
hoc runs, not from these seed ledgers, and not from intuition. Statuses in
`baseline.toml` are populated exclusively from a real scorecard run against
the pinned revision.
