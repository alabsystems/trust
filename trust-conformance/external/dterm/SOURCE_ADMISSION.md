# dterm Source Admission Fixture

This directory is a production-owned source mirror for the dterm slices admitted
by generated required Kani/trust-mc manifests:

- `trust-conformance/generated/required-full-verify/dterm-core-ffi-contracts.required-kani-trust-mc-proofs.json`
- `trust-conformance/generated/required-full-verify/dterm-alloc.required-kani-trust-mc-proofs.json`

It is intentionally small. It mirrors only the three required Kani
`proof_for_contract` harness entry points and the nine default-visible
`dterm-alloc` harness entry points inventoried from dterm commit
`070b3484655985e03f41820a3a235c5d520de7b4` for #1146, #1117, #1108, #1095,
and #1043. The full external dterm repository is not vendored here.

Release evidence boundary:

- These harnesses remain `bounded_regression` imports.
- Passing Kani compatibility runs produce `RejectedBounded` verifier evidence.
- Accepted release proof evidence still requires native `proof fn` items with
  hash-addressed trust-mc CHC/PDR transcripts, or externally published verifier-run
  evidence bound to the exact dterm source commit and obligation ids.

The Trust Publication V3 required Kani/trust-mc gate can also intake the dterm
`dterm.trust-mc_kani.proof_batch.v1` artifact manifest introduced at dterm commit
`7384877a888ac9c1176f4d0183183c0ce37d0c65`. That intake is fail-closed: the
batch and per-package artifacts must be passing, clean, hash-addressed,
`engine: trust-mc`, and backed by a `trust-trust-mc-chc-pdr-evidence` solver transcript
marker in the captured run logs before Trust emits accepted verifier-run
evidence. Dterm `admission.eligible` alone is not sufficient.

External verifier-run admission:

- Use `scripts/required_kani_trust-mc_proofs.py --manifest <trust-mc-list-v0.2.json>
  --external-verifier-run-manifest <run-manifest.json>` for dterm proof
  batches that publish trust-mc list JSON 0.2 plus `trust.verifier-run-manifest.v1`.
- The Trust-side gate does not run the full dterm proof set in this mode. It
  checks that the external run manifest is dscan-publication-grade evidence and
  that its obligation ids exactly match the supplied trust-mc list batch.
- The emitted report schema is
  `trust.external-verifier-run-admission.required-kani-trust-mc.v1`; the emitted
  verifier fragment still uses
  `trust.verifier-run-manifest.fragment.required-kani-trust-mc-proofs.v1` so
  Publication V3 aggregation and dscan/dpub admission stay on the existing
  run-manifest path.
