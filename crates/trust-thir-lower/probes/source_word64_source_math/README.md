# Retained source-model / IR value mathematics

This standalone source dependency graph includes the identical production
`source_word64/record.rs` codec, which uses only the standard library. It does
not graft Rustc-private or duplicate kernel/IR libraries into ordinary source
packages. Materialize `Cargo.toml.in`, preserving the tracked `Cargo.lock`.

`TRUST_SOURCE_PAIR_CAPTURES` names the immutable actual capture directory with
`core-callee.entry`, `core-callee.source`, `core-callee.module` and
`CORE-CALLEE.json`. `TRUST_SOURCE_PAIR_MATH_OUT` names a fresh output directory.
Build and run with genuine `targo --unverified test --offline --locked`,
original SDK/input leases, machine admission and no global compiler flags.

Run the six `source_record::tests::` codec controls, then the exact test
`tests::actual_source_model_and_original_ir_value_equation_retained` to retain
a proof packet. In a separate process set `TRUST_SOURCE_PAIR_FORBID_PRODUCER=1`
and run the exact
`tests::fresh_source_model_replay_reconstructs_claim_and_rejects_false_models`.
Require the expected artifacts and unchanged packet/input hashes; zero selected
tests cannot count as a pass.

The source-model interpretation reads only decoded source operands/operations,
never output IR. A registered wrapping-add model denotes addition modulo 2^64;
ordinary calls require independent callee semantics and refuse this primitive
interpretation. Separately reflected actual IR supplies the other side of the
universal returned-value equation. The canonical kernel environment checks and
audits the reconstructed claim/proof, disallowing unsafe/partial declarations
and requiring empty axiom, foundational-axiom and trust-marker dependencies.
Changed source operands and constant source values must fail kernel checking.
Fresh replay cannot produce a replacement proof.

This is mathematics about an **unlicensed source claim and actual IR values**.
It proves neither source authenticity nor Rust frontend/source-model correctness,
entry/world preservation, purity/termination, physical ABI, NoUB or machine bytes.
It constructs no live TCX snapshot, Rust-source TV certificate, caller companion,
Clean source identity for Rust or compiler admission. The producer/consumer modes
in the original capture remain distinct; mathematics does not authorize a mode
mismatch. Those complete carrier requirements remain outstanding.
