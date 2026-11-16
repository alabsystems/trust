# Schema-5 overflow-mode protocol fixture

This fixture is prepared for a matching fresh Root compiler/std/private closure.
It has not yet executed against that SDK. It never builds or relabels an SDK.

`rmake.rs` compiles the actual producing crate with overflow checks on and off,
then compiles a canonical consumer in both modes for each producer. The existing
`-Ztrust-instance-flip-probe=*` channel-C route reaches
`rmeta_entry::upstream_entry_column`, which supplies the actual consuming
session's `tcx.sess.overflow_checks()` to `decode_entry_for_overflow`.

Each cell requires real schema-5 `mix` and `identity` entries. Matching modes
require the ordinary entry diagnostic; opposite modes require the exact named
`overflow-check-mode` refusal. A real local `#[rustc_inherit_overflow_checks]`
identity function must compile normally but have the distinct producer-recorded
`inherited-overflow-checks` no-entry reason in every cell. Missing evidence for
either required R subject is always failure; the intentional no-entry subject
cannot count as a metadata positive.

The accompanying runner also builds the maintained read-only Rustc-private probe
from `crates/trust-thir-lower/probes/rmeta_overflow_mode.rs`. Four separate actual
consuming sessions load the real producer bytes through Rust's crate store.
Their actual session mode reaches both decoder routes. Runner-declared modes
are independent assertions, never decoder or official-evidence selectors. The
producer's retained mode is compared with its producing invocation flag, never
inferred from its IR. Both actual entry blobs and all rows/diagnostics are kept.

Prepare an honest execution plan without SDK inputs:

```sh
python3 run_matrix.py --plan --out /owned/new-matrix-plan
```

Execute once Root supplies its completed matching SDK, immutable source/build
record. The exact local inherited-overflow guard
`7e98e8115cde1c5205b646f195e5537b652c6900` is always required as an ancestor:

```sh
build-slot -- python3 run_matrix.py \
  --out /owned/new-matrix-run \
  --sdk-root "$MATRIX_SDK_ROOT" \
  --compiler-source "$MATRIX_COMPILER_SOURCE" \
  --compiler-commit "$MATRIX_COMPILER_COMMIT" \
  --guard-commit "$MATRIX_GUARD_COMMIT" \
  --build-receipt "$MATRIX_BUILD_RECEIPT"
```

The source checkout must be clean and name the supplied compiler's actual full
commit; both protocol and guard commits must be ancestors. The actual canonical
driver and private SDK driver hashes must agree. The genuine supplied Targo,
private dependencies, source, binaries, flags, modes and every command/result
are recorded. The output path must be new, and every native step waits to exit
before the next starts. Old compilers cannot be treated as schema-5 executions.

This tests protocol and custody. It creates no F1 admission token, makes no
trust-cg selection and establishes no machine-code, ABI/NoUB or kernel proof.
The strict F1 consumer/codegen matrix belongs to the importer qualification.
