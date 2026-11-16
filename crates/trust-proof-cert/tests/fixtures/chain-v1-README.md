# Legacy proof-chain binary fixtures

These version-1 envelopes contain one non-authoritative public certificate
record. `chain-v1-with-evidence.bin` uses the pre-KR0 two-field
`ProofEvidence` (reasoning and assurance); `chain-v1-without-evidence.bin`
uses `None`. They pin the binary migration refusal, not proof acceptance.

The old evidence shape is from `eb0e73990a85b8e8f60d888578358834f9ad1404`,
`crates/trust-types/src/result.rs` blob `6e9cc63cadf2854101de3c7019011ea4436c7fc7`.
The certificate, solver, chain and envelope layouts surrounding it are unchanged
at `419ffd4ed4063cbbf616f3c2d5dc8491e4e7deb5`. The generator used those unchanged
carriers and an explicit two-field legacy evidence serializer; these are schema
fixtures, not artifacts of an old compiler run.

On the unchanged version-1 reader, the no-evidence fixture decoded, while the
two-field-evidence fixture failed with an unclassified bincode I/O error. Both
are now refused by their version before positional decoding. The interim KR0
four-field layout also used version 1, so no unambiguous version-1 migration
reader is offered. Regenerate binary records with the current writer. The JSON
envelope and old unstamped JSON reading remain unchanged.
