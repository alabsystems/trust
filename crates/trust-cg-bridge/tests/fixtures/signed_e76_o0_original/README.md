# Actual e76 signed-input data

These are unmodified input and object bytes from the e76 engineering compiler,
using the same eight-function source as `signed_o0_original`. The native Targo
fixture-generation command explicitly selected `--unverified`; source
verification checked zero obligations. Codegen used its strict output gate,
O0, overflow checks, no debug information and no incremental object reuse.
The compiler reported all eight functions closed in its codegen model. This
fixture is data, not source extraction, verified-lane, SDK or release evidence.

The earlier b8 capture is preserved byte-for-byte. Its module transport predates
`closure_layouts` and is noncanonical under the current codec. The decoder still
rejects it; no default field was inserted into that historical artifact.

Signed-store and leaf tests independently select these new bytes and replay
proofs against their actual subject. Historical v1 packets are also preserved:
an old object subject or trusted environment must refuse. The compatibility
controls generate separate v1-shaped DATA from a normally replayed current v2
seed, with the same current subject and unchanged original equations/proof
advice. The test-only producer cannot accept a historical v1 seed and cannot
mint a checked token. Existing replay still checks the complete current goal,
context, environment and proof; fresh child processes forbid proof production.
This exercises compatible wire transport without relabeling an archived proof
as evidence for new bytes or a new context.
