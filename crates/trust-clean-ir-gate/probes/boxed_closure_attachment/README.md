# Actual boxed closure pipeline DATA

This probe starts with `PinnedLeanSourceWorld`, checks the complete supplied
source batch through its existing closed reference entry, and borrows the
actual `AcceptedLeanSourceContext`. It retains the exact original source,
owned constant payloads, source/world binding data, dependency records and the
maintained persisted-environment DAG. The DAG does not preserve arbitrary
future lazy-provider behavior and is never restored into an accepted owner.

Every owned declaration is submitted to the maintained LCNF lowerer. Additional
runtime references are discovered from actual LCNF `LetValue::Const` nodes,
including function values and nested function/join/case code. Discovery uses
the original structured `Name`, not a reverse interpretation of linker names.
The existing runtime-binding contract checks the actual context at every
consumer. Lowered, valueless/skipped and refused dependencies remain distinct;
`Ok(None)` is never an executable-completeness certificate. A referenced
body-less opaque or axiom is explicitly incomplete and refuses; even an
external symbol registration supplies no implementation owner to this probe.
A value-bearing extern keeps its exact registered symbol and constant type in
the refusal DATA and hits the maintained `ExternWithBody` refusal rather than
compiling its logical body. There is no symbol-name exemption or new physical
ABI claim. Missing payloads refuse, and unused owned siblings are retained.

Only a dependency-only `Ok(None)` is deferred until the maintained pipeline
has produced its actual before-boxing and boxed IR. A complete syntactic
census checks direct calls, partial applications, constructors, reuse and case
alternatives in both views. A missing body still refuses when its name remains
referenced or the pipeline refuses. The raw input row is retained even when no
reference remains. Every explicit owned root must lower normally; missing
payloads, lowering errors and extern refusals are never deferred. The census
is untrusted producer DATA, not a source-erasure theorem.

One full maintained pipeline invocation returns its exact artifact record,
final module and TV report. Its boxed IR is the actual emitter input. The
existing mono/optimized fields remain prefix-replay observations. Ordinary
IR, RC, emission, subset and TV gates are preserved, including hard TV
refusals. Compact JSON is direct Rust serialization of the actual module.
Runtime C/header/extern-source bytes are retained from the producer build.
The actual final artifact record receives the same named-input census before
Module/TV files are written; a newly referenced missing dependency refuses.

The compiler may uncurry a source maker into a function taking its captures
and final argument; its boxed entry can be the physical closure target. A
separate lifted body is not fabricated to match a logical model's roster.
All actual original, generated, runtime and unresolved external rows remain
in the emitted module.

Build and run in an owned workspace/cache with the genuine Trust toolchain:

```sh
build-slot --cpus 2 -- targo --unverified run --locked --offline \
  --manifest-path crates/trust-clean-ir-gate/probes/boxed_closure_attachment/Cargo.toml \
  -- SOURCE.lean NEW_OUTPUT_DIRECTORY
```

The declared source cohort and generated lock must first be coherent; a
successful patched graph is not qualification of a different declared graph.
Output directories must be new so earlier failures survive.

These are DATA and existing source-check outcomes. They grant no source-to-IR
erasure, closure layout, ownership, physical runtime, caller ABI, NoUB, object
or machine-code correspondence, and no new proof/body/artifact token. An
emitted module with unresolved executable dependencies is not working linked
code. Default frontdoor and strict admission refusals stay in force until the
separate Lean-owned relations and downstream obligations are checked.

On incomplete dependency inputs, a separate diagnostic call to the existing
maintained artifact pipeline may retain its actual mono/IR/boxed observations,
including constructor metadata and constructor-node paths. It emits no Module
or TV report, preserves every population refusal, and does not turn a
constructor record or observed node into a completeness or representation
proof. Deferred dependency-only candidates also require an artifact-only
observation before the final full artifact/module/TV invocation.

The fixtures keep the original three-definition arithmetic program, a genuine
custom dictionary whose constructor disappears during the ordinary pipeline,
and an extra unused owned extern. The custom-dictionary case produces Module
DATA, with TV certification still skipped outside the scalar fragment. The
original UInt64 add/mul externs and the extra unused owned extern retain their
ordinary refusals. See the focused command and exact cohort in STATUS.md.
