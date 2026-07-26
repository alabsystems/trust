# Trust stage0 distribution artifacts

This directory tracks Trust stage0 distribution metadata, not archive payloads.

Generated `*.tar`, `*.tar.gz`, and `*.tar.xz` files under `bootstrap/trust-stage0/dist/`
are local build artifacts. Public upload is forbidden. The tracked channel
manifests, checksum files, and `src/stage0` pin the artifact names and digests
that the default bootstrap expects; archive payloads are generated locally and
are not tracked here.

Run `python3 scripts/fetch_trust_stage0_payloads.py` from the repository root
to check whether the Trust channel manifests declare any fetchable payload
source for missing archives. Use `--fetch` only after that audit reports
fetchable payloads; the helper refuses undeclared URLs and verifies the
`src/stage0` digest before writing.

When a stage0 artifact set changes:

1. Generate the archive payloads locally from Trust-owned dist artifacts.
2. Update the manifests, checksums, and stage0 pins together.
3. Verify no public upload step is present in the workflow.
