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

The exporter also has a separate diagnostic `word64-self-addition` profile for
`x.wrapping_add(x)`, permitting compiler-parsed inline hints. Select its original
function with `TRUST_ACTUAL_ADDITION_FUNCTION` (default `addition`). Its data
is in `word64_source_profile`; the original `closed_profile` stays literal-only,
so self-addition cannot turn the old experiment's accepted bit green. The new
profile has no conversion to that theorem or to admission. The maintained
`../source_word64_self_addition_test.py` requires an actual source-built observer,
Targo, matching driver sysroot and a fresh evidence directory. Its 19-case roster
includes the unchanged Lean-to-Rust ladder subject and rejects effects, different
parameter binding, nested computation and other attributes.

On a current SDK, real core metadata can keep a wrapping-add call in the raw
per-body query fragment. The exporter preserves those original bytes and every
validator error. It separately exports `canonical-query-assembly.bin` through
the existing ordinary structural assembler and reports its declaration count in
`QUERY-ASSEMBLY.json`. A bodyless declaration does not supply callee meaning or a
closed executable proof subject. Do not substitute this assembled image into
the old literal theorem or discard the unresolved-call failure. Genuine callee
source/IR evidence and complete source association remain required.

The exporter additionally retains the exact actual loaded callee metadata envelope,
checks its producer header/version, original overflow mode and resolved Rust owner,
and exports the decoded module separately. It never installs that body into the
query or supplies a strict upstream-admission token. The original raw fragment
and canonical bodyless query assembly remain unchanged. The separate
`../source_word64_callee_math` fixture checks only that retained implementation's
universal IR value equation and fresh replay; it supplies no Rust-source TV or
conversion into this historical source/ByteV1 theorem.
