# Hardened Lab Corpus

This crate is the hardened lab corpus for `targo trust`. It is a small fixture
crate used to exercise current hardened boundary reporting against intentionally
risky patterns in standalone source-inventory and native compiler-backed runs.

## Reviewer Commands

Run each command from the repository root as a separate CLI invocation. These
are not a shell-script workflow.

Run the curated lab wrapper when you need the corpus source-inventory finding
coverage and per-claim rootless-walkthrough gate:

```sh
targo trust hardened-lab --manifest-path examples/hardened/Cargo.toml --format json --show-vcs
```

Run the raw standalone analyzer when you need hardened source inventory. The
standalone analyzer is hardened by default; add `--no-hardened` only when you
intentionally want non-hardened source inventory:

```sh
targo trust check --standalone --format json --manifest-path examples/hardened/Cargo.toml
```

Run the native compiler-backed check when you need MIR obligations in the proof
path. Native `targo trust check` is hardened by default and requires a
discoverable default-verifying `trustc`:

```sh
targo trust check --format json --manifest-path examples/hardened/Cargo.toml
```

Run the native compiler-backed report when you need saved proof artifacts:

```sh
targo trust report --trust-profile coreutils_hardened --manifest-path examples/hardened/Cargo.toml --report-dir ./out/hardened
```

The lab command runs the standalone analyzer and the rootless walkthrough
binaries in `src/bin`; it exits `0` only when all advertised claims have
matching standalone findings and matching per-claim walkthrough transcript
evidence. The standalone command is expected to
exit non-zero for this intentionally risky corpus because it reports fail-closed
findings. Its JSON is source inventory only. The native `check` and `report`
commands are hardened by default and are the compiler-backed evidence paths;
only native compiler-backed paths can produce `report.json`, `report.html`,
`report.ndjson`, and verification cache metadata. Native hardened success
requires every emitted hardened obligation to have publishable structured
native proof evidence.

## Scope

The corpus currently includes fixtures for raw path re-resolution and path
identity, permission creation/change windows, byte/text conversion boundaries,
discarded errors, panic boundaries, compatibility-observable CLI arguments,
process/SIGPIPE semantics, trust-domain ordering, unsafe-operation inventory,
and FFI-boundary inventory.

In native compiler-backed runs, the trust-domain ordering fixture emits
`hardened_trust_domain_order` obligations for `chroot`, `setuid`, or `setgid`
followed by NSS/account lookups (`getpwnam`, `getgrnam`,
`get_user_by_name`) or `dlopen`. These rows are fail-closed
`HardenedVcCategory::TrustDomainOrder` VCs until the workflow has ordering
evidence. In standalone runs, the analogous `HardenedTrustDomainOrder` row is
source inventory only.

The rootless walkthrough binary performs concrete filesystem re-resolution,
panic catching, account/group lookup, and plugin path probes before it prints
simulated privileged operations. It also emits machine-readable scope keys such
as `privileged_ops_mode=simulated` and
`evidence_scope=rootless_preflight_and_trace_order`. The privileged `chroot`,
`setgid`, and `setuid` effects remain unexercised so the walkthrough can run
without elevated permissions.

These examples are regression inputs for hardened reporting. They should not be
read as proof that a real program is hardened. Read standalone output as source
inventory; read native output as compiler-backed obligations, not as a
certificate unless the report carries evidence for the specific claim.
`--no-hardened` suppresses the hardened inventory/proof obligations and is not
valid evidence for hardened claims.
