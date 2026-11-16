# Actual direct-THIR word64 addition connection

This standalone qualification fixture consumes the ORIGINAL serialized Module emitted by
`../source_word64_addition.rs`. It does not build, synthesize, strip debug information,
normalize or edit that module. Supply complete matching SDK/private metadata to the exporter,
and a SEPARATE source-built Clean/IR dependency graph to this fixture. No private extern or
compiled target is transferred across the versioned Module binary codec.

The exporter captures GNU jobserver custody as its FIRST main operation. Its typed closed
profile checks the real safe Rust U64 signature, original parameter binding, entire THIR
expression/block/statement population, checked integer literal, and actual resolved versioned
core wrapper. The original full source text is independently projected by Clean. The private
IR witness validates the decoded complete original Module, with actual constant/add/return
identities and target/Rust logical entry. Canonical reserialization must equal the input bytes.

The first test checks and retains the exact universal source-model/ByteV1 entry/SSA/root-return
connection, including the final retired memory, host, owners and next-owner counter. A fresh
consumer runs only `fresh_actual_thir_` with `TRUST_G4_FORBID_PRODUCER=1`, restores the old proof
and independently expected original inputs, and refuses a different valid ZERO-literal Module
actually emitted by the same producer. It never calls the producer or IR proof assembler.

External inputs:
- `TRUST_ACTUAL_THIR_INPUT`: retained actual exporter directory (source, Module, typed facts).
- `TRUST_ACTUAL_PROOF_OUT`: fresh owned evidence output directory.
- Fresh reader additionally selects `TRUST_ACTUAL_RETAINED_PROOF` and `TRUST_ACTUAL_ZERO_INPUT`.

`Cargo.toml.in` records the actual source dependency/feature recipe used in an OWN external
workspace. Adapt only its source-root locations, use genuine `targo --unverified test`, and
keep all selected source/lock/tool/compiler/component hashes and source bookends. The
qualification is not a verified Targo-lane claim: the Clean kernel checks the explicit theorem.

Scope: logical original-source MODEL to actual captured typed IR. Version fingerprints do not
prove the core wrapper body; that correspondence remains an explicit frontend/model premise.
The TCX exporter remains trusted translation/custody code. Full source/mono population,
physical ABI, SourceNoUB, native bytes, compiler admission and G1–G8 remain OPEN. No new
capability, grade, decoder, axiom or default-policy change is provided here.
