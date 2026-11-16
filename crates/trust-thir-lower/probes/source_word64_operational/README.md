# Retained two-input callee: canonical SemR execution

`SemRWord64Pair.lean` uses the unchanged canonical `SemR.lean` from the pinned
`first-party/trust-ir/lean/semr` tree. Its complete 224-byte `originalBytes`
is the actual core wrapping-add module retained by the source metadata probe,
also preserved as `core-callee.module` (SHA-256
`da7c4a08645bf039ee1b792015b73c51a922e3fb48863950dab37807613b35de`).
No binary header or emitted instruction is rewritten to fit the proof.

The statements cover canonical decoding, actual entry for both full-range U64
inputs, the complete intermediate state with arbitrary memory, return, and
exclusion of bad finite execution prefixes through SemR's relational theorem.
The negative propositions change trailing bytes, the returned operand, fuel or
the required input-validity premises.

Materialize `Cargo.toml.in` by replacing `@TRUST_ROOT@`, and copy `Cargo.lock`
beside it. Compile the pinned SemR source, `MiniRust.lean` and `SemRMiniRust.lean`, then `SourceWord64Record.lean`,
`SourceWord64RecordOriginal.lean`, `SemRWord64Pair.lean` and
`SourceWord64Evaluation.lean`, `SourceWord64Call.lean` and
`PairCallerOperational.lean` and `SourceWord64MiniRust.lean`, in that order, with pinned Lean 4.30.0-rc2
into an owned directory. Set `TRUST_WORD64_OPERATIONAL_DIR` to
that directory, `TRUST_SOURCE_PAIR_CAPTURES` to the original metadata capture,
and the ordinary source-built compiler and pinned Lean-library inputs used by
the other source probes. Run these exact tests with genuine `targo --unverified
test --offline --locked --all-targets --manifest-path <manifest>`:

1. `tests::operational_reference_kernel_produces_packet -- --exact --nocapture`
2. In a fresh process, with `TRUST_WORD64_OPERATIONAL_FORBID_PRODUCER=1`,
   `tests::operational_fresh_process_replays_unchanged_proofs -- --exact --nocapture`

The additional `tests::deep_proof_transport_roundtrips_without_recursive_json`
control checks a 512-binder term and a truncated-carrier refusal. Proof transport
uses the existing bounded, lossless `CLENEDG2` environment-DAG codec inside a
bounded JSON envelope. It carries only the twenty-six advertised proof declaration records,
with no imported prelude or checked context. It preserves complete expressions rather
than dropping annotations or disabling the JSON recursion guard. A decoded
environment is data only: it never constructs the fresh reference context.

Both processes import untrusted `.olean` data and recheck the complete dependency
closures of all twenty-six proof targets and the four original negative
propositions from empty through `ReferenceKernel`. Safety checks cover every
local declaration in those closures. They bind byte literals to both the
retained callee module, `core-callee.source`, `pair-caller.module` and
`pair-caller.source`, recheck unchanged proofs, and require
genuine kernel type mismatches for all twenty-three false subjects. The original four
controls remain, with nineteen additional attempts to reuse the new proof terms
as proofs of `False`.
Only the usual Ax0 dependencies (`propext`, `Classical.choice`, `Quot.sound`)
are permitted. Native reduction, a structural import or Lean's successful exit
does not replace this replay.

The source-record decoder preserves the original schema-1 claim, including
owner/callee identities and ordinary-versus-registered call kind. The base evaluation
model leaves ordinary Rust calls unresolved. `SourceWord64Call` resolves one
nongeneric ordinary-call claim only against the exact named callee record,
preserving operands and refusing mismatched owners. `PairCallerOperational`
decodes the unchanged caller module and quotes an explicit link that preserves
the caller and callee blocks. It proves four-step execution for all U64 pairs,
retaining zero-depth and absent-body refusals. This is an exact fixture link,
not a general linker or physical relocation proof. `SourceWord64MiniRust`
connects the exact claim and linked execution to the unchanged generated
MiniRust addition operator, for arbitrary reference machine state and every
valid U64 pair. This does not authenticate the source record's builtin label. Its universally quantified theorem
connects the exact retained intrinsic claim with canonical IR execution; the
source claim's authenticity is not a premise established by this model.

This is canonical **IR operational mathematics and record-to-IR agreement**. It gives no Rust source/model
authenticity, physical entry ABI, Rust source NoUB, codegen permission, caller
companion or emitted-machine-code evidence. No certificate or admission grade
is changed. The original metadata producer/consumer modes remain separate.

The `MiniRustWord64Pair*` extension models the complete two-runtime-argument
function boundary, using the generated MiniRust operations. Three allocations
precede both checked argument stores. The actual Assign and Return steps retain
all scheduler choices, reset access logs as the machine specifies, write the
caller result, retire three private slots and resume the caller. The boundary is
explicitly a single-thread caller; this is not a concurrent Rust program theorem.
`MiniRustWord64PairEntryRun.full_tree_exact` preserves the complete guarded
allocation/scheduler tree. `MiniRustWord64PairAvailability.full_function_available`
constructs a normal execution under an explicit high-water room condition rather
than assuming successful entry. `MiniRustWord64PairFullCorrespondence` relates
the final world to the unchanged retained IR bytes. Its false subjects alter
argument slots (observable even though addition commutes), result, arithmetic
and outside memory; `MiniRustWord64PairFalseWorld` alters retirement timing.
`MiniRustWord64PairAllocationControls` independently checks a fresh allocation,
live-overlap refusal and range refusal in the original allocator.

For this extension, compile `MiniRustWord64PairFalseWorld` and
`MiniRustWord64PairAllocationControls`, recursively compiling their local imports
from this directory and the pinned `trust-ir/lean/semr` directory. Retain sources
and `.olean` files together in the owned artifact directory; the extended safety
audit parses every local `.olean` and audits each reachable local declaration.
Keep the original operational modules there too. Run the same three exact test
names under `pair_world_tests::` instead of `tests::`. The producer writes the
separate schema-4 `pair-world-packet.json`; the fresh process forbids the producer.
The extended transport retains the original 26 proofs and 23 refusal controls,
adding seven proof targets and twelve refusal controls (including the five false
world subjects). A successful build or Lean elaboration alone is not a successful
reference replay. Neither packet grants compiler admission or source/ABI authority.
