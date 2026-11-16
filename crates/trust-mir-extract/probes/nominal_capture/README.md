# Live faithful capture custody

`observer.rs` compiles the actual nominal parameter, cached-body and capture
modules against one coherent frozen private compiler dependency closure. It
uses the existing `../nominal_body/fixture.rs`; no duplicate source model is
introduced. The driver prepares the real verification snapshot, observes its
live nominal parameter and immutable body, and invokes the existing faithful
extractor through the owned capture API. The existing MIR compatibility
TrustIR bridge borrows that exact output. Validation and the shared interpreter
execute both declared logical enum inputs, expecting true then false, bounded
by fuel 128/call depth 4 and with zero host calls.

This is a native compiler observer plus IR interpreter control, not generated
machine code or an AST-to-IR semantic preservation theorem. The bridge is the
existing MIR compatibility route, not the direct THIR frontend. Rustc query
provider/cache integrity, faithful extraction and bridge correctness remain
TCB premises. The observed Runtime(PostCleanup) body is not retroactively the
historical TrustVerify-input JSON. No SourceMarker, proof grade, SDK or pin is
changed.

`constructor_refusal.rs` must fail specifically with E0451 for private `source`
and `function` fields: a supplied function, including decoded or changed
extractor output, cannot create the live pair. Output clones remain data.
There is no mutable getter, deserializer or from-parts constructor.

Use the coherent private-component recipe documented by the neighboring
nominal-body probe. A Cargo project needs bins pointing to these two files and
exact metadata/native extern pairs for that recipe, additionally `trust_ir`,
`trust_ir_build`, and `trust_ir_bridge`. Include modules from the checked-out
source; do not substitute frozen extractor modules for the changed capture.
Run the positive observer with the neighboring fixture and stage1 sysroot,
`-Zno-codegen -Zcodegen-backend=dummy -Zthreads=1 -Ztrust-verify=off`.

## Original helper and current Enum wire

`original_helper.rs` observes the actual unchanged `trust-ir-laws/src/lib.rs`
`proof_ref_kind_is_ambiguous`, not the two-variant fixture. Supply the original
source path, crate name `trust_ir_laws`, and compatible runtime-compiler
`trust_ir` metadata/dependency directories to the observer. The seed metadata
used to BUILD the observer cannot compile that source (E0514); use the already
built ffa141 base-lane metadata for that runtime compiler instead. No rebuild,
SDK assembly or pin change is required.

Set `TRUST_CAPTURE_WIRE_OUTPUT` to an explicit owned output path. The observer
writes the actual existing serializer output, checks the 16 actual declaration
names and absence of payloads, validates the module, and executes every declared
logical enum input with expected original returns. Current output is Enum/U8,
not the historical Struct/I64 capture. The checked Lean component is
`trust-source-contract/lean/LiveHelperEnumWire.lean`.

For the source negative, copy the original source to an owned test input and
replace the unique first match alternatives
`ObligationKindShape::Precondition\n            | ObligationKindShape::Postcondition`
with `ObligationKindShape::Postcondition`. Run the same observer with a distinct
wire output path. The published `38ce76fffe` receipt runs the actual producer and fails its old
truth-table assertion at ordinal zero (false versus true), after writing the
actual compiler output. The newer exact-body oracle described below instead
refuses this source edit BEFORE the bridge or wire output. It does not regenerate
that older mutant-wire receipt, nor treat a missing output as serializer failure.
Run `check_original_wire.py SOURCE MUTANT_SOURCE WIRE MUTANT_WIRE`; it checks the
exact source delta and both exact byte literals. Changed byte inputs must fail
this custody check. This script establishes test-data correlation only.


## Exact current body profile

`live_helper_shape.rs` is a read-only bounded oracle in this probe, not a
production frontend or proof token. It checks the actual three-local/four-block
source MIR and faithful output, including Move, retag Yes on Bool Use, every
case/default and edge, all types and the actual nominal declaration. The
original observer now runs 34 cloned-data rejection controls and checks that
they did not mutate the genuine capture. The actual source-arm negative must
fail the `actual original body differs from exact three-local/four-block view`
assertion before creating its fresh wire output file.

`LiveHelperBodyView.lean` records the exact current four-block data, retains
Move/Use-retag metadata, checks all16 finite table paths and composes the
existing Enum byte outcome theorem. Its seven statements and seven axiom guards
do not prove Rust checker/quotation/compiler/extractor correctness. The observed
phase is current Runtime(PostCleanup)/pass1, not historical TrustVerify input.
See the live-MIR structural-view decision for the exact remaining boundaries.
