# `trust-dump`

The tracking issue for this feature is internal to Trust.

------------------------

`-Z trust-dump=<what>:<directory>` publishes one Trust verification artifact to
an explicit, non-empty directory. Repeat the option to request more than one
sink; requesting the same sink twice is rejected rather than silently taking the
last value. Every sink is dependency-tracked and artifact-only, so it
invalidates the current compiler invocation without changing the downstream
crate hash.

| `<what>` | publishes |
|---|---|
| `mir` | each extracted MIR verification input |
| `mir-only` | the same inputs, then stops before solver/certifier dispatch |
| `native-bundle` | each finalized native TrustIr verification bundle |
| `ir` | the assembled crate-level TrustIr lowering artifacts |

`mir`, `mir-only`, and `native-bundle` require batteries-on Trust verification.
`ir` requires either batteries-on verification or `-Z trust-ir-lower`.

The retired `TRUST_DUMP_ONLY` and `TRUST_IR_DUMP` environment variables are
ignored and scrubbed from compiler and Targo child processes, so ambient state
cannot change solver dispatch or incremental reuse.

## `mir-only:<directory>`

Extracts and writes the verifier MIR without dispatching those inputs to a
solver or the clean certificate kernel. It is intended for reproducible compiler
and corpus-census workflows, not as a proof mode, so it additionally requires
`-Z trust-policy=advisory`: every dumped function is reported as unproved/unknown.

```text
trustc -Ztrust-dump=mir-only:mir-inputs \
       -Ztrust-policy=advisory \
       crate.rs
```

Dump-only output is evidence input, not verification evidence, and never earns
proof credit.

## `ir:<directory>`

Publishes the crate-level TrustIr artifacts assembled by `-Z trust-ir-lower`:

- `<crate>.trust-ir.bin`
- `<crate>.trust-ir.txt`
- `<crate>.coverage.json`

`--emit=trust-ir` is the user-facing spelling for that artifact set and renders
the identical module through the ordinary output-file machinery. This sink is
the *pre-input publication lease*: it discovers and durably invalidates its
target from raw argv before any input is read, so a compile that dies before a
`Session` exists cannot leave a previous generation's commit marker looking
current. `--emit=trust-ir` prepares its target at finalization instead and
therefore cannot make that guarantee. Prefer `--emit=trust-ir`; reach for this
sink when the invalidation ordering is what you need.

The three files are one publication set, not independent outputs.
`coverage.json` is installed last as the commit marker and binds the exact
binary/text byte lengths and domain-separated SHA-256 digests. A missing
coverage marker, a digest mismatch, or a partial set is not current output.
The marker uses `trust.thir-lower.crate-module.coverage.v2`. Every body carries
typed interpreter and derived-MIR differential verdicts (`agreed`, `mismatch`,
`unsupported`, or `not-run`). Call-bearing bodies deferred at the per-body hook
also carry an explicit resolved crate-seam outcome; non-deferred bodies say
`not-applicable`. The compiler requires an exact one-to-one deferred-result
inventory and renders JSON only after seam resolution. It publishes no artifact
for a missing, duplicate, unexpected, or inconsistent outcome, and it does not
serialize the ambiguous internal `equal` boolean.
Direct publication requires a nonempty, valid explicit `--crate-name`; any
source or injected crate-name attribute must agree with it. Direct publication
cannot use `@response-files`: expanded tokens do not retain sufficiently strong
origin information to authenticate option/value ownership. If outer argv
contains a complete literal publication identity, trustc durably invalidates
that target before opening a response file, so missing, malformed-shell, and
non-UTF-8 files cannot retain a prior generation. A readable response file is
rejected after invalidating every unambiguous, fully known target. Without a
response file, trustc invalidates after typed option validation and before
`--explain`, input-count selection, or a stdin read. Thus no/multiple-input,
input-read, UTF-8 decoding (including stdin), eager tokenization, syntax,
expansion, type, borrow-check, lowering, validation, serialization, and write
failures cannot retain a prior generation as the accepted publication attempt's
output. Typed early exits such as `--explain`, `--print`, lint help, and metadata
listing also invalidate the target and publish no replacement marker. Raw
help/version, `-Wall`, and codegen-pass listing return before typed target
validation. In an invocation without a response file, combining them with
`-Ztrust-dump=ir:<dir>` is rejected and is not a publication attempt.
Publication stages same-directory temporary files, syncs them, renames the data
files, and commits the marker last. Any controlled failure rolls the partial
generation back, so a failed accepted publication attempt cannot leave an old
or mixed generation looking current.

Each target also has a persistent hidden control entry named
`.<crate>.coverage.json.trustc-publish.lock`. It is not part of the artifact
set and must not be deleted. trustc opens it without following links, verifies
its regular-file identity after acquiring an advisory lock, and holds the lock
from pre-input invalidation through Session publication or failure. The OS
releases it after a compiler crash. Within one compiler process, publication
leases sharing a dump directory are excluded before opening a sentinel; this
closes case-folding and Unicode-normalization aliases on process-scoped lock
hosts. Unix operations and stale-temporary
enumeration are relative to a stable directory descriptor. Windows retains
no-delete-share handles for the directory and every ancestor and installs files
with replacement-capable, write-through renames. Windows identity checks retain
the full 128-bit `FILE_ID_INFO` value instead of truncating ReFS identities to
the legacy 64-bit file index. The requested directory path, opened directory
identity, and lock sentinel identity are rechecked at commit boundaries;
unsupported identity queries and hosts fail closed rather than using
pathname-only publication.

If another actor can modify the dump directory, advisory locking and retained
parent handles are not a filesystem sandbox: that actor can race sibling
namespace entries between checks. A detected path or sentinel replacement
aborts publication, and rollback stops if the sentinel identity is lost so it
cannot delete files belonging to a writer on a replacement lock.

Compiler drivers that bypass `rustc_driver_impl` must acquire the same explicit
target lease before they acquire input, retain it across input I/O, and install
that exact lease in the Session before parsing. The parser/finalizer fallback
alone cannot protect a failure that never reaches Session finalization.

These are structural-lowering and differential-parity artifacts, not a proof
result. The direct THIR producer does not yet bind source contracts and proof
obligations to the emitted SSA values. Accordingly, its module has no direct
source obligation authority, an empty obligation table is never interpreted as
"verified with zero obligations", and the MIR-compatibility native-request
planner rejects it. The coverage sidecar exposes this boundary for automation:

```json
"direct_obligation_capability": "structural-parity-only-v1",
"proof_authority": false,
"native_verification_requests": false
```

The directory must be non-empty. The output location invalidates the current
compiler invocation without changing the downstream crate hash because it is
artifact-only. Batteries-on verification enables `-Z trust-ir-lower`
automatically; an explicit no-verification compatibility build must request
lowering itself before it can request a dump. An assembly tripwire or
filesystem publication failure aborts compilation: an explicit evidence
request never succeeds with missing artifacts. The retired `TRUST_IR_DUMP`
environment variable is ignored.
