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

→ **BYTE-IDENTICAL** *at that date*. `regenerate.sh` reruns exactly this, with
one mechanical change forced on it since: since `2c9fdb1dd5` (2026-07-10) the
compiler writes every dump **content-addressed** — `mir_dump_filename` emits
`trust-mir-<fingerprint>.json`, never `<fn>.json` — so the filenames in this
directory are a *corpus convention*, not compiler output. The script selects the
fresh dump by its own `def_path` and writes it back under the corpus name.

### Drift ledger — the 2026-08-05 re-publish

The 2026-07-07 bytes are no longer reproducible. Five differences separate them
from what today's stage2 emits for the same `count_to.rs`; each was established
independently before the regenerated dump was published, and the checked-in
`count_to.json` is now the fresh one. `git show b1aa9d5426:...count_to.json`
retrieves the 2026-07-07 bytes.

1. **Spans move by exactly one line** — `span` 25–31 → 26–32, the `Requires`
   span line 23 → 24, the `Ensures` span line 24 → 25. **Not toolchain drift:**
   `a86f5ada72` grew `count_to.rs`'s own "Dump with:" header note from one line
   to two, and every recorded span is an absolute line number. `git log -p --
   count_to.rs` shows the edit; the fn text itself is untouched.
2. **`def_path`: `count_to` → `count_to::count_to`** — `bd2d6ed1fc`
   (2026-07-13) renders def paths crate-qualified and definition-site under
   `with_resolve_crate_name!` / `with_no_visible_paths!`, whose stated
   requirement is that the string "must neither omit the local crate nor select
   a context-dependent visible re-export". The crate is `count_to` because the
   file is compiled as `count_to.rs`.
3. **Type and closure paths requalify the same way** — `std::option::Option` →
   `core::option::Option` (definition site, not the re-export), and the ensures
   closure `count_to::{closure#1}` → `count_to::count_to::{closure#1}`.
4. **Locals `__ret` / `__requires_checker` / `__ensures_checker` lose their
   names** (`"name": null`). `source_contract_synthetic_name_collision`
   (`crates/trust-types/src/spec_parse.rs`) reserves the entire `__` family as
   `GeneratedMetadata` — "Trust's MIR/Formula producers reserve `__` for
   generated metadata … reserve the whole family rather than chasing a
   perpetually incomplete prefix list" — and `build_debug_name_map`
   (`crates/trust-mir-extract/src/lib.rs`) drops every debug name in it, so a
   source binding can never collide with a generated Formula symbol. No
   information is lost: those locals keep their injective `_N` MIR spelling, and
   the body is structurally identical to the 2026-07-07 fixture — still **9
   locals / 5 blocks**, same types, same statements.
5. **`preconditions` gains one conjunct**, `n >= i32::MIN AND n <= i32::MAX`.
   An always-true type-range fact for the `i32` parameter; purely additive
   (the source `requires(n >= 0)` is still the first conjunct, unchanged).

**Measured on the regenerated bytes, 2026-08-05** (stage2 `build/host/stage2`):
`--test real_spec_corpus_depth` 3/3, `--test specfree_baseline_compare` 1/1,
`--test either_discriminant_guard` 1/1, and all 24 `trust-clean` lib tests that
read this corpus — including
`prove::tests::real_count_to_synthesizes_guard_aware_upper_bound_modulo_3` and
the two `trustir_anchor` `count_to` tests — pass. The depth scorecard is
identical to the one the old bytes produce, line for line, except that the
per-function breakdown now prints the qualified `count_to::count_to`; the proven
set, the 27/35 fully-faithful depth and every discharge count are unchanged.

**Not a cause, and not hidden:** on the current stage2 a `-Ztrust-dump=mir:`
(solve-and-dump) run of `count_to.rs` reports `2x [postcond] FAILED
(trust-full-verifier); counterexample: verified_counterexample = true`. That is a
real regression in the postcondition lane, *not* a fixture problem and not the
reason the old script failed (it failed on the filename, cause above). It
reproduces with no fixture involved — `fn f(n: i32) -> i32 { let mut i = 0;
while i < n { i = i + 1; } i }` with `ensures(*ret >= 0)` and **no** `requires`
is refuted the same way — and the 2026-07-16 stage2 still on disk at
`build/aarch64-apple-darwin/stage2-restored` proves the obligation the current
one refutes. `regenerate.sh` uses the documented `mir-only:` mode, which
publishes the extracted inputs and stops, because dumping is its job and solving
is not.

Two honest notes from the original 2026-07-07 verification:

- The dump must be made without the now-retired `-Zcontract-checks=yes`
  legacy exec projection. With
  that projection active in the historical upstream-compatibility lane, the
  requires/ensures checker closures stay live and the dumped
  MIR carries their scaffolding locals (14 locals / 8 blocks) — semantically the
  same function, but **not** byte-identical to the checked-in fixture (9 locals
  / 5 blocks, which is still the shape today). The contracts are extracted into
  `contracts`/`spec` either way. (In 2026-07-07 the distinguishing marker was
  also that `_0` was named `__ret` here and unnamed there; drift-ledger cause 4
  since removed that name from both, so use the local/block counts.)
- Only `count_to.rs` has this byte-level regeneration guarantee. The other
  fixtures' original scratch files were never recovered; their source of truth
  is the consolidated `SOURCE.rs` text plus the JSONs themselves.

## What the corpus is for

Meaningful specifications (`#[core::contracts::requires/ensures]`) + non-trivial
auto safety VCs + deliberate negative controls, to measure true verification
depth rather than contract inhabitation on spec-free one-liners. See the
`SOURCE.rs` header and `DEPTH-REPORT.md`.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
