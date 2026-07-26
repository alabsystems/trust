# Examples

This directory is organized as a tiered verification corpus.

Current baseline:

- `targo trust check` is the verifier front door
- native compiler-backed runs depend on a discoverable Trust compiler, usually a
  locally built Trust sysroot whose `bin` directory is on `PATH`
- compiler-backed example checks are regression diagnostics only; neither a
  live match nor metadata-only header validation is proof or release evidence
- crate-based `trust::` examples still pair most honestly with
  `targo trust check --standalone`

For toolchain or release evidence, use the canonical Trust entrypoints in the
selected sysroot: `trustc`, `targo`, `targo-trust`, `trustdoc`, `trustfmt`,
`tippy`, `targo-tippy`, `tippy-driver`, `trust-analyzer`, and optional
`trust-miri`/`targo-miri` when
Miri ships. Inherited `rustc`/`cargo`-family names do not count as Trust
toolchain evidence.

## Tier 0: Fast Smoke

Use these first when you want a quick compiler-backed verification experiment:

- `midpoint.rs`
- `binary_search.rs`
- `binary_search_fixed.rs`
- `demo/`

These are intended to be the smallest end-to-end examples for observing a
known bug and its expected safe counterpart on the native compiler-backed
path. `targo trust verify examples --trustc <stage2 trustc> --json-output
<report>` compares each declared `VcKind STATUS` assertion with the structured
compiler rows. It does not check every possible property or require that every
output row was declared. Its v2 report is deliberately a regression diagnostic:
it does not authenticate the example source and compiler build provenance
together and is neither proof nor release evidence. Stage1 is an explicitly
developer-only version of the same diagnostic.

## Tier 1: Enforced L0 Regression Suite

These files are the machine-enforced single-file corpus:

- `verify_*.rs`
- `verify_*_safe.rs`

They encode the intended L0 story: overflow, divide-by-zero, bounds,
assertions, and closely related verifier obligations. The headers are
machine-checked by the metadata diagnostic; the live compiler-backed run checks
the expected output rows but is still only a regression diagnostic.

Notes:

- The top-of-file comments are part of the corpus metadata.
- Every `verify_*.rs` file must declare at least one structured regression assertion as
  `// Expected: VcKind STATUS`. The accepted statuses are `PROVED`, `FAILED`,
  `RUNTIME-CHECKED`, `UNKNOWN`, `TIMEOUT`, and `ABSENT`; prose such as “not
  proved” is invalid and never defaults to a verdict.
- `ABSENT` is a VC-generation assertion: the structured compiler report must
  contain no row for that kind. It is deliberately distinct from `PROVED`,
  requires a valid structured report, and cannot turn missing verifier output
  into success.
- `targo trust verify examples` is the live corpus diagnostic: it requires a built
  `trustc` (or `TRUSTC_BIN=/path/to/trustc`), compiles every `verify*.rs`
  example with verifier JSON output enabled, and checks that each parsed
  `Expected:` obligation/status pair is reflected in the verifier output. Its
  durable report always records `proof_evidence=false` and
  `release_evidence=false`: source/tool provenance is unauthenticated and a
  stage2 run does not promote the diagnostic into evidence. Use `targo trust verify examples
  --metadata-only` only to check headers on machines without `trustc`.
- Some contract-oriented files in this tier still use legacy contracts syntax.
  They are kept that way because the single-file regression path still targets
  the native compiler-backed verifier, not the crate-based `trust::` surface
  with `trust-spec`.

## Tier 2: Public L1 Contract Corpus

Use these when you want the public-facing contract surface:

- `contracts/basic-contracts/`

This tier is crate-based and uses:

- `Cargo.toml`, including its `[trust]` policy table
- `trust-spec`
- `#[trust::requires(...)]` / `#[trust::ensures(...)]`

Today this tier is best paired with `targo trust check --standalone`, which
recognizes the namespaced attrs and reports spec coverage honestly. Treat it as
contract-surface inventory, not as the main proof-artifact path.

## Tier 3: Workflow and Artifact Corpus

Use these when you want a repeatable local walkthrough:

- `demo/`

This is where to learn report generation, proof diffs, and cache behavior on
the compiler-backed path when a discoverable Trust compiler is available.

## Tier 4: Hardened Lab Corpus

Use this when you want the current hardened boundary fixture set:

- `hardened/`

The hardened lab is a crate-based corpus for exercising hardened reporting over
intentionally risky path, bytes, error, panic, permission, compatibility,
process/SIGPIPE, trust-domain, unsafe-operation, and FFI-boundary surfaces.

Run the curated lab wrapper:

```sh
targo trust hardened-lab --manifest-path examples/hardened/Cargo.toml
```

Run the raw standalone hardened analyzer and emit JSON:

```sh
targo trust check --standalone --hardened --format json --manifest-path examples/hardened/Cargo.toml
```

Treat this as hardened lab source-inventory/walkthrough coverage, not as a
claim that the fixture program is secure or that standalone output is
compiler-backed proof evidence.

## Tier 5: Research and Showcase

These examples are useful for orientation, but they are not yet the stable
front door:

- `showcase/`

Expect a mix of L0-oriented demonstrations, roadmap sketches, and future-facing
material.

## Unsafe-Operation Coverage Demos

- `unsafe-coverage/`

Single-file demo fixtures for the unsafe-operation coverage gate: every
user-expressible unsafe-operation kind is caught fail-closed (inline asm,
union field access, mutable statics, unmodeled unsafe calls, target-feature
calls), with discriminating controls that must NOT be flagged, plus the HIGH-2
proved-unsafe demos (`high2_demo.rs`, `copy_nonoverlapping_proved.rs`, the
`aterm_*` mmap set). `scripts/check-unsafe-coverage.sh` runs the stage2
`trustc` over this directory and asserts the catch/control matrix.

## Tier 6: Compile/Verify Benchmark Index

Use this when you want the single-file good/flawed matrix for comparing
compiler slots:

- `bench/program_index/`

The index covers paired known-good and known-flawed programs across upstream
`rustc`, Trust noverify, Trust verification, and experimental trust-cg slots. The
safe runner is:

```sh
targo trust benchmark program-index --list
```

Real compiler slots are opt-in through `--slot-bin SLOT=PATH` or environment
discovery. trust-cg is report-only by default because it is still experimental.
Use `targo trust benchmark program-index` for the benchmark implementation.
