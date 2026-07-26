# trust-thir-lower — Rust/THIR directly to TrustIR

`trust-thir-lower` is the Rust structural frontend for the canonical typed
TrustIR pipeline. It lowers rustc THIR directly into `trust_ir::Module`; it
does not lower through MIR. Trust-CG consumes TrustIR for native codegen, and
the TrustIR-to-MIR direction is only a secondary LLVM-compatibility path.

Design context, in short: the P1 "IR inversion" makes typed TrustIR the
canonical pipeline IR — Rust is lowered THIR-first into TrustIR, and the
TrustIR-to-MIR direction survives only as an LLVM-compatibility path — and the
fusion design folds the verifier and codegen onto that one IR spine.

## Current status and authority boundary

This is a wired `rustc_private` frontend, not a scaffold. Batteries-on trustc
invokes the per-body lowering at the `mir_built` seam, records results in a
Session-owned registry, and finalizes one deterministic crate-level module at
the `rustc_interface` analysis seam. `-Ztrust-dump=ir:<dir>` publishes:

- `<crate>.trust-ir.bin` — canonical binary TrustIR;
- `<crate>.trust-ir.txt` — canonical text TrustIR;
- `<crate>.coverage.json` — deterministic per-body lowering, splice, call,
  unsupported-reason, and typed differential evidence. Coverage schema v2
  keeps interpreter `agreed`, `mismatch`, `unsupported`, and `not-run` states
  distinct, records the derived-MIR compatibility verdict, and gives every
  deferred call-bearing body an explicit resolved crate-seam outcome.

These files are published transactionally. `coverage.json` is the last-renamed
commit marker and carries domain-separated SHA-256 bindings for the exact
binary/text bytes. Missing-marker, partial, and mixed-generation sets are
invalid. Publication requires a nonempty, valid explicit `--crate-name`; source
and injected crate-name attributes must agree with it. Direct publication cannot
use `@response-files`: expanded tokens do not retain sufficiently strong origin
information to authenticate option/value ownership. With a complete literal
outer identity, the ordinary evidence-capable driver acquires and invalidates
that target before opening the response file, so missing, malformed-shell, and
non-UTF-8 files still clear a preceding generation. A readable response file is
rejected after invalidating every unambiguous, fully known target. Without a
response file, the driver invalidates after typed option validation and before
`--explain`, input-count selection, or stdin reads. No/multiple-input, read,
UTF-8 decoding, eager tokenization, syntax, expansion, type, borrow-check,
lowering, validation, serialization, and write failures in an accepted
publication attempt therefore invalidate the preceding generation. Typed
pre-parse exits invalidate without publishing a replacement; raw help/version
modes that return before typed target validation reject `-Ztrust-dump=ir:` as an
incompatible request when no response file is present.

Coverage JSON is rendered only after crate assembly and the linked seam
differential. The finalizer requires exactly one seam result for each deferred
body and none for any other body; missing, duplicate, unexpected, or internally
inconsistent results abort publication. The artifact never serializes the
producer's ambiguous `equal` boolean, so a comparison that did not run cannot
be consumed as agreement.

One pre-input lease serializes each crate target across processes until Session
finalization or failure. Within one compiler process, the pre-open guard
serializes the whole dump directory because case-folding or Unicode-normalizing
filesystems can alias differently spelled sentinel names before their shared
inode can safely be opened. Its hidden
`.<crate>.coverage.json.trustc-publish.lock` sentinel is persistent (never
unlinked), opened without following links, verified as the same regular-file
identity after locking and at every commit boundary, and released by the OS on
process death. Unix publication uses `openat`/`renameat` operations through a
stable directory descriptor. Windows pins the selected directory and every
ancestor with no-delete-share handles, compares full 128-bit `FILE_ID_INFO`
identities (including on ReFS), and uses replacement-capable, write-through
Win32 renames. The requested path is revalidated against the opened directory
identity throughout the transaction, so a rename or redirect cannot publish
under an unrelated lock. Unsupported identity queries and hosts fail closed.
Under the lease, abandoned per-artifact temporary files are enumerated through
the directory anchor and removed without following non-regular entries.

Custom drivers must call the pre-input acquire API before input I/O and install
that exact lease into the Session before parsing; the parser fallback alone
cannot cover earlier failures. Publication failures roll back only while the
locked sentinel identity remains valid. If an external actor replaces that
entry, rollback stops rather than deleting a replacement lock owner's files.
A dump directory writable by a hostile actor is not a filesystem security
boundary. Identity is checked at each operation boundary, but parent handles
and advisory locks do not make checks and later sibling namespace changes one
indivisible operation.

The direct lane is deliberately `structural-parity-only-v1`. Its sidecar says
`proof_authority: false` and `native_verification_requests: false`. Source
contracts, state epochs, typed formulas, and obligation ownership are not yet
bound to the direct module's SSA values, so an empty direct obligation table
can never mean “verified.” Authenticated MIR-derived evidence remains temporary
compatibility and differential scaffolding while that binding and verdict
parity are completed; MIR is not the canonical semantics or end-state
frontend.

## Implementation map

- `src/lib.rs` lowers the supported THIR body subset to typed TrustIR and
  records every unsupported construct fail-closed.
- `src/crate_module.rs` assembles deterministic crate modules, remaps typed
  tables and call identities, publishes artifacts, and enforces the direct
  authority marker.
- `src/differential.rs` and `src/mir_differential.rs` compare the direct module
  with the authenticated MIR-derived compatibility oracle.
- `src/flip.rs` and `src/flip_registry.rs` guard the structural compatibility
  flip; they do not mint proof authority.
- `src/to_mir.rs` is the derived TrustIR-to-MIR compatibility direction.

## Build and test

The crate is a root workspace member so its unit tests are reachable through
bootstrap. It remains excluded from the separate `crates/Cargo.toml` stable
development workspace because its rustc-private dependencies require a staged
compiler.

```text
./x test --stage 2 --set build.submodules=false crates/trust-thir-lower
./x test --stage 2 --set build.submodules=false \
  tests/run-make/trust-thir-enum-differential \
  tests/run-make/trustc-verifier-options \
  tests/incremental/trust-mir-snapshot-after-green-ensure.rs
```

The enum-differential run-make test requires end-to-end interpreter agreement
for the supported enum parameter, discriminant, payload, reassignment, and
nested-value cases, and rejects any typed mismatch. The dedicated publication
run-make test checks commit-marker bindings,
generation replacement, the persistent lock control entry, raw-mode exclusion,
response-file failure and exclusion, typed pre-parse exits,
no/multiple inputs, stdin and file decoding, parser/type/borrow failures, and
source/injected identity disagreement. Unit tests additionally exercise
phase-by-phase rollback, in-process and
cross-process writer exclusion, crash lock release, stale temporary cleanup,
symlink/hardlink rejection, lock replacement, and directory path swaps. The
broader artifact test retains the non-authoritative capability, coverage,
provenance, and green-query replay checks.

## Remaining canonical-frontend work

The structural lowering continues to expand fail-closed THIR coverage, but the
authority milestone is stricter: bind source contracts, state epochs, formulas,
and obligation ownership to exact TrustIR SSA identities; replay that binding;
then demonstrate semantic and verdict parity before retiring MIR-derived
compatibility evidence.

Mark Trust-specific edits with `// Trust:` per the repository's upstream
discipline convention.
