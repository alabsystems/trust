# Actual word64 source capture component

`../source_word64_capture_component.rs` compiles the identical
`../../src/source_word64.rs` production module in a minimal Rustc-private harness.
It does not supply an alternative constructor or include an IR implementation.
Materialize `Cargo.toml.in` in an owned external directory by replacing
`@TRUST_ROOT@`, then build with genuine `targo --unverified rustc` against one
matching completed compiler SDK namespace. Supply both original rlib/rmeta
files for `rustc_abi`, `rustc_ast`, `rustc_hir`, `rustc_middle`, `rustc_span` and
the target/host dependency search paths. The compiler must match the version
that built those private dependencies; do not select artifacts by modification
time or mix SDKs. Normal original SDK/input leases and machine admission apply.

The source observer `../source_word64_addition.rs` additionally receives this
component's paired rlib/rmeta as `--extern rust_source_word64_capture=...`.
Its original borrowed snapshot is acquired before the observer reads emitted IR
and stays live through query assembly. The actual compiler harness
`../source_word64_self_addition_test.py` keeps the original 19 controls and adds
three fixed-roster source controls: real registered wrapping-add, local same-name
lookalike, and unsupported registered wrapping-sub. It checks original parameter
order and rejects another actual owner in the same compiler session.

This qualifies the reusable source reader only. The last qualified SDK has no production caller,
owner-bound production source payload, source/model proof, rebuilt compiler qualification,
source TV, purity/termination/ABI/NoUB result, caller companion or admission.
An ordinary wrapper call remains an ordinary call; a version fingerprint, display
name or source snapshot cannot replace that callee's required evidence.

`Cargo.tests.toml.in` materializes a separate test-only package. Build its
`source-record` target with `targo --unverified rustc --test source-record`
and the same explicit private dependency pairs, then execute that exact emitted
test artifact. A combined library/integration-test package causes Cargo to build
the library without those target-specific private externs; do not bypass this
with global compiler flags or a different SDK.

The schema-1 source-claim codec preserves the actual captured owner, original
parameter/node identities, source hash, resolved call and exact supported
substitutions. It refuses unknown source substitutions, malformed framing,
out-of-range identities, truncation and trailing bytes. Its decoder creates only
an untrusted owned record; it cannot construct the live borrowed TCX snapshot.
The actual source observer tests encoding and decoding before reading output IR,
checks the actual owner and original expression population, and rejects every
truncation for every captured control. Codec unit tests additionally exercise
malformed fields, parameter aliases, unknown opcodes and literal boundaries.
