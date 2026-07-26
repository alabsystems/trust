# real-spec-corpus — provenance

> The dump flags were spelled `-Ztrust-dump-mir` / `-Ztrust-dump-only` when
> these bytes were produced; they are one `-Ztrust-dump=<what>:<dir>` option now.
> The recipe below is the current spelling, so it reproduces against today's
> compiler rather than the pinned one.

Classification (honesty ledger `reports/honesty-and-ladder-2026-07-07.md` §1.4):
**SYNTHETIC_EXTRACT** — every dump here is genuine, unmodified `TRUST_DUMP_MIR`
output from `trustc` ("real" = real compiler MIR), but the *source* is authored
micro-fixture Rust, **not** published-crate code. Nothing in this corpus is
real-code coverage.

## How the dumps were produced

All JSONs are `trust_types::VerifiableFunction` dumps emitted by the
`TRUST_DUMP_MIR=<dir>` hook (`compiler/rustc_mir_transform/src/trust_verify.rs`,
Trust #941) while compiling small scratch files with a stage2 `trustc`
(`--crate-type lib`, default flags — see the byte-verified command below).

**Layout caveat (honest):** the checked-in `SOURCE.rs` is a *consolidated*
documentation file containing the source text of the corpus functions. The
dumps themselves were made from **per-function / per-batch scratch files**
(e.g. `count_up.rs`, `NEWSHAPES.rs` — visible in each JSON's `span.file`), so
the file names and line numbers embedded in the JSONs do **not** match
`SOURCE.rs`, and compiling `SOURCE.rs` does not byte-reproduce the JSONs. The
function *text* is the same; the span metadata is not. The original scratch
files were not checked in at dump time.

## count_to.json — reconstructed generating source (2026-07-07)

`count_to.json` (commit `98f116b930`) predated this file and had **no**
checked-in source at all — the weakest provenance in the project per the
2026-07-07 honesty audit (§2 item 7). Its generating source was reconstructed
from the spans + MIR embedded in the checked-in JSON (the fn text at
`count_to.rs` lines 23–31 is exactly pinned by the recorded spans; the 22-line
header preamble is *not* pinned and is authored) and is checked in here as
**`count_to.rs`**.

**Verification (2026-07-07):** re-dumping the reconstruction with the stage2
`trustc` (`rustc 1.96.0-dev (340e45e50 2026-06-22) (trustc)`):

```
cd <dir containing count_to.rs>
LIBRARY_PATH=/opt/homebrew/lib \
  trustc --crate-type lib -Ztrust-dump=mir-only:<out> \
  -Ztrust-policy=advisory count_to.rs -o count_to.rlib
cmp <out>/count_to.json fixtures/real-spec-corpus/count_to.json
```

→ **BYTE-IDENTICAL.** `regenerate.sh` reruns exactly this.

Two honest notes from the verification:

- The dump must be made without the now-retired `-Zcontract-checks=yes`
  legacy exec projection. With
  that projection active in the historical upstream-compatibility lane, the
  requires/ensures checker closures stay live and the dumped
  MIR carries their scaffolding locals (14 locals / 8 blocks, `_0` unnamed) —
  semantically the same function, but **not** byte-identical to the checked-in
  fixture (9 locals / 5 blocks, `_0` named `__ret`). The contracts are
  extracted into `contracts`/`spec` either way.
- Only `count_to.rs` has this byte-level regeneration guarantee. The other
  fixtures' original scratch files were never recovered; their source of truth
  is the consolidated `SOURCE.rs` text plus the JSONs themselves.

## What the corpus is for

Meaningful specifications (`#[core::contracts::requires/ensures]`) + non-trivial
auto safety VCs + deliberate negative controls, to measure true verification
depth rather than contract inhabitation on spec-free one-liners. See the
`SOURCE.rs` header and `DEPTH-REPORT.md`.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
