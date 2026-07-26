# stdlib-leaf-cmp-2026-07-16 — provenance

This fixture is the fourth P1 stdlib leaf harvest. It measures the scalar
`core::cmp` min/max/clamp regime as it is available in a per-DefId
`library/core` extraction. The published result remains deliberately red:
**0/12 real bodies are FULLY_FAITHFUL**.

The narrative report is
`reports/p1-leaf-harvest-cmp-2026-07-16.md`. Machine expectations are in
`results.tsv`, `controls.tsv`, `wrappers.tsv`, and `forgeries.tsv`; each records
every FF-gate field and every census field.

## Current measured result

- Real core family: **0/12 FULLY_FAITHFUL**, all `SHAPE_GAP`, all
  `not_grounded=1`, `kernel_rejected=0`, `declined=0`.
- Monomorphic controls: **5/5 FULLY_FAITHFUL**. The four single-select min/max
  controls and the nested clamp are accepted by both FF-gate diagnostic lanes;
  census selects `via_trustir=1` for each.
- Intent wrappers: **0/7 FULLY_FAITHFUL**. Each body contains an opaque call to
  the core callee, so compiling a downstream probe does not expose the callee's
  MIR.
- Adversarial probes: C1–C4 decline `SHAPE_GAP`, C5 declines `SAFETY_GAP`, and
  the unmutated C6 control is `FULLY_FAITHFUL`. No row is kernel-rejected.

The pinned stage1 extraction changed several old diagnostic counts without
changing the headline. In the current corpus, only `cmp::Ord::clamp` and the
three `NonZero<T>` rows carry one census safety obligation; the other eight real
rows carry zero. The controls carry zero census safety obligations. Those exact
values replace the larger stale counts from the superseded corpus.

`declined` above is the named census output column; it is distinct from the
FF-gate's fail-closed `SHAPE_GAP`/`SAFETY_GAP` classification.

## Exact 12-body family

The recursive slicer requires exactly these crate-relative identities:

- `cmp::{min,max,min_by,max_by,min_by_key,max_by_key}`;
- `cmp::Ord::{min,max,clamp}`;
- `<num::nonzero::NonZero<T> as cmp::Ord>::{min,max,clamp}`.

It rejects a missing or duplicate target and requires its recursive JSON scan
count to equal the authenticated extraction count. Float, SIMD, iterator, and
collection folds are different semantic regimes and are not silently mixed into
this family.

The 12 available bodies are generic. Integer `min` and `max` use the generic
`Ord` defaults; compiling core as a library emits one polymorphic body per DefId,
not concrete `<i32 as Ord>` instances. Free min/max helpers and the `NonZero<T>`
implementations are likewise generic or contain opaque trait calls. Census
therefore reports `not_grounded=1` for every real row. This is the existing W16
monomorphization/extraction wall, not evidence that a generic theorem was proved.

There is also a separate extraction observation for primitive `clamp`.
`ord_impl!` authors concrete primitive overrides, but the pinned 27,547-body raw
inventory contains only the three `clamp::do_panic{,::compiletime,::runtime}`
leaves for each of 13 `{char,i*,u*}` implementations—39 leaves total—and no
parent primitive clamp body. The `const_assert!` promotion is the observed
discriminator. This fixture names that extraction residue
W-CONSTASSERT-ELIDE; it does not patch a certified clamp body to manufacture a
green result.

## Controls and wrappers

`SOURCE/src/lib.rs` contains two disjoint groups, extracted by the same compiler:

- Five hand-inlined, monomorphic controls. The four single guarded selects
  (`ctl_{min,max}_{i32,u8}`) and the nested two-select `ctl_clamp_i32` certify.
  W-NESTED-SELECT is closed by an ordered convergence-spine recognizer: a leaf
  may be followed only by exact stepwise pass-throughs of that leaf's value to
  the return join. A pass-through before the leaf, a leaf-to-leaf overwrite, or
  a mixed assign-arm overwrite declines. Current census reports zero open
  safety obligations for every control.
- Seven intent wrappers that call real `core::cmp` functions or methods. Their
  fresh call identities include `<i32 as core::cmp::Ord>::min` and
  `core::cmp::min::<i32>`. All seven remain opaque-call `SHAPE_GAP`s. They show
  why a downstream probe is not a substitute for extracting core itself.

Controls demonstrate lane reach; they are not counted as certified stdlib.

## Fail-closed probes

`prepare_corpus.py` derives every forgery deterministically from the freshly
extracted `ctl_min_i32` body and asserts the base control's exact select shape
before mutating it:

| probe | mutation | current FF-gate result | census safety |
|---|---|---|---|
| C1 | comparison reads nonexistent local `_9` | SHAPE_GAP | 0/0 |
| C2 | Bool return/type lie populated by integer Add | SHAPE_GAP | 0/0 |
| C3 | one arm divides by zero | SHAPE_GAP | 1/2 |
| C4 | one arm becomes `Call evil::opaque_oracle` | SHAPE_GAP | 0/0 |
| C5 | one arm performs unchecked `a + i32::MAX` | SAFETY_GAP | 0/1 |
| C6 | unmutated valid select | FULLY_FAITHFUL | 0/0 |

C5 is the direct no-shape-only-promotion witness:
`via_mirsem_shape=true` while straight-line safety discharge and
`fully_faithful` remain false. C2 is no longer described as that witness because
the current gate rejects its shape outright.

## Reproducibility and authentication

`regenerate.sh` is checkout-relative by default and has two modes:

```text
./regenerate.sh                 # extract, derive, validate, then publish
./regenerate.sh --validate-only # validate committed bytes without publication
```

The workflow is fail-closed:

1. `SOURCE.sha256` authenticates the relevant core sources, SOURCE crate,
   workaround target, and exact workaround patch before extraction.
2. `TOOLCHAIN.sha256` pins the stage1 launcher version and bytes, its exact
   adjacent `rustc_driver` dylib and bytes, host, and expected dump counts. The
   script also requires exactly one linked driver and exactly one
   `@loader_path/../lib` RPATH with all DYLD overrides removed.
   `LIBRARY_PATH` comes from an explicit `TRUST_LIBRARY_PATH` or from
   `$(brew --prefix)/lib`; no machine-specific prefix is checked in.
3. Core is copied to a temporary tree and the unrelated `int_log10` optimizer
   hint workaround is applied once with forward-only `patch`. The compiler is
   run from the temporary directory so its delayed-ICE attachment cannot dirty
   the checkout.
4. The pinned compiler's one recorded post-dump NonZero metadata-normalization
   ICE is accepted only with exit 101, exactly one `error:`/ICE, the observed
   `::ptr::metadata::Pointee::Metadata`, `num::nonzero::NonZero<T/#0>`, and
   `NormalizationResult` substrings exactly once, both delayed-bug notes exactly
   once, the exact `27,553 warnings emitted` summary exactly once, empty stdout,
   and exactly **27,547 recursive JSON bodies**. The crate disambiguator before
   the projection is intentionally not hard-coded. Any other diagnostic, exit,
   or inventory is fatal.
5. SOURCE extraction must succeed with exactly **12 JSON bodies**. Recursive
   selection is exact; identity normalization strips only the authenticated
   local `core::` or `stdlib_leaf_cmp_source::` crate tokens from identity-bearing
   `def_path`, call `func`, and type/ADT `name` fields.
6. `canonicalize_dump_paths.py` rewrites only recognized core/SOURCE span paths
   to checkout-relative paths and rejects residual `/Users`, `/private`, `/tmp`,
   `/var/folders`, or Windows-drive paths anywhere in JSON.
7. `ARTIFACTS.sha256` must cover exactly all 30 JSON bodies and all four TSVs.
   Missing, extra, duplicate, or changed publications fail validation.
8. Release FF-gate and census tools are rebuilt `--locked` and offline from the
   current checkout into an isolated target. Every output column, schema, and
   row is checked. Any analyzer warning is fatal, and tool bytes are rehashed
   after validation.
9. A fixture-local lock prevents concurrent regeneration. Candidate artifacts
   are published only after all checks pass; directory backups are restored on
   a failed or interrupted publication. There is no `|| true`, hard-coded other
   worktree, or pre-validation deletion of the committed corpus.

The compiler records a historical source point because that is the code encoded
in its binary. The analyzers intentionally do not record historic executable
hashes: regeneration builds and checks the current checkout's release tools.

## Published files

```text
dumps/                    12 real generic core bodies
controls/                  5 fresh monomorphic controls
wrappers/                  7 fresh intent wrappers
forgeries/                 6 deterministic adversarial/positive probes
results.tsv                complete real-family tool outputs + wall
controls.tsv               complete control tool outputs + wall
wrappers.tsv               complete wrapper tool outputs
forgeries.tsv              complete forgery tool outputs
SOURCE/                    wrapper/control Rust input
SOURCE.sha256              exact input hashes
ARTIFACTS.sha256           exact publication inventory and hashes
TOOLCHAIN.sha256           compiler/driver/extraction identity
canonicalize_dump_paths.py constrained path normalizer
prepare_corpus.py          exact slicer and forgery derivation
validate_results.py        complete analyzer-output checker
regenerate.sh              locked transactional workflow
```

No certified cmp source is edited. The only core change occurs in the temporary
copy and removes two unrelated `int_log10` optimizer hints needed to let the
dump complete far enough to publish this honest 0/12 measurement.
