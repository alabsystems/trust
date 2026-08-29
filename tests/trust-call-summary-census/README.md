# Call-summary census — committed control corpus

Four real `-Ztrust-dump=native-bundle` dumps, kept so
`scripts/call_summary_census.sh` has a **positive control** it can run with no
`trustc`, no build of the compiler, and no scratchpad.

The census refuses to report a green it cannot back up: it fails when it
observes zero summaries or zero declines, because a silent instrument reads
exactly like a clean result. That check needs a corpus that provably contains
both. These four are it — each was picked as the *smallest* bundle in a
2,592-bundle sweep exhibiting one distinct outcome:

| bundle (`trust-native-bundle-…`) | root body | what it controls |
|---|---|---|
| `43fc80276288ff94-402ac604e80a5104` | `proc_macro2::imp::<impl From<proc_macro::Span> for Span>::from` | a call that **summarizes** — the success side |
| `427553eced0cd00c-6291c22189d88220` | `proc_macro2::fallback::Span::mixed_site` | declines at `unmodeled_instruction` |
| `dab8f0a0f42ec297-ecc64d9c2a9c897b` | `serde_core::de::value::<impl IntoDeserializer for f32>::into_deserializer` | declines at `signature_param_ty_unsupported` |
| `a2773eecdb558e6a-b9b73e924c71e025` | `serde_core::ser::impls::<impl Serialize for OsStr>::serialize` | declines at `signature_return_ty_unsupported` |

They are ordinary dependency bodies, not hand-written fixtures: the census is a
statement about real code, and a control built only from synthetic IR would not
be evidence that the interpreter behaves this way on any.

Passing the same directory twice is a supported (and mutation-proved) control:
bundles are deduped by **module digest**, the duplicates are named in the
report, and the `dedup` self-check fails if the tallied population and the
distinct-module count ever disagree.

## Provenance

Produced by `trustc -Ztrust-verify=on -Ztrust-dump=native-bundle:<dir>` over
`tests/ui/trust/*.rs` (the recipe `scripts/call_summary_census.sh --dump-corpus`
runs), trust-ir producer version `0.6.0`. Each file carries its own
`provenance` and `trust_ir_module_digest` blocks — read those rather than this
table if the two ever disagree.

## Regenerating a full corpus

```bash
scripts/call_summary_census.sh --dump-corpus /path/to/corpus --out /path/to/out
scripts/call_summary_census.sh --dump-corpus /tmp/c --dump-max-files 40   # bounded
```

That compiles every `tests/ui/trust/*.rs` with the dump flag under a per-file
wall-clock cap and refuses to continue past a disk floor. Budget ~45–60 min for
the full 299-fixture sweep; `--dump-max-files N` bounds it.

### The guard keys on DUMPS, not on exit codes — and that is a correction

This recipe used to **fail on its own healthy output**. The guard refused a sweep
in which a majority of compilations exited nonzero, and on this corpus a majority
of them *do*, by design:

* 100 fixtures are `check-fail`, 3 are `build-fail`, 4 are `run-crash`, and more
  carry `error-pattern` — a nonzero exit is what the fixture asserts;
* the recipe deliberately overrides each fixture's own `//@ compile-flags` with
  `-Ztrust-verify=on --crate-type lib`, so fixtures written for
  `-Ztrust-policy=advisory` or for a `//@ revisions` `--cfg` fail under it.

Measured 2026-08-29 over the whole suite: **57% exited nonzero while 82% produced
at least one bundle.** A nonzero exit is uncorrelated with instrument health —
verification failures are emitted *after* the dump — so the old predicate refused
a working recipe, which is exactly the "committed control whose regeneration
recipe does not run" failure this corpus exists to end.

What the guard was built to catch is a dump lane producing **nothing** — the
`timeout`-binary failure that once had a census reporting "zero obligations
across 361 fixtures" because every invocation exited 127. That is a statement
about dumps, and it is now measured as one:

* zero bundles from a nonempty sweep → **FAIL**;
* fewer than `--dump-floor-pct` (default 30%) of compilations producing a bundle
  → **FAIL**.

Exit codes are still counted and printed, and `<out>/dump-index.tsv` records
`fixture / rc / dumps / expect` per fixture so the two can be read apart.

Two fixture classes are **skipped and reported**, not counted as failures:
`//@ aux-build:` (needs a companion crate compiletest builds; a bare `trustc`
gets `E0463` and dumps nothing) and `//@ ignore-test`.
