# direct_shadow fixtures — M1 differential harness inputs

Real production-driver artifacts, minted 2026-08-31 with the in-tree stage2
driver `trustc 1.99.0-dev (e1591f8f5 2026-08-30)`
(`build/aarch64-unknown-linux-gnu/stage2/bin/trustc`), from each probe
directory's `probe.rs` (crate names `m1probe`, `m1shift`, `m1bounds`).
Nothing here is hand-built: the `.bin` is the direct THIR-lowered module
exactly as the finalizer emitted it (born Pending obligation rows included),
and each `mir/*.trust-mir.json` is the MIR lane's `VerifiableFunction` dump
of the same body.

```sh
# direct module (the .bin/.txt pair; obligations born at the finalizer):
trustc --edition 2021 --crate-type lib --crate-name m1probe \
       -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-dump=ir:<dir> m1probe.rs

# MIR-lane VerifiableFunction dumps (the dump flag rides the verify pass,
# so advisory policy, not -Ztrust-verify=off):
TRUST_DUMP_MONO=1 trustc --edition 2021 --crate-type lib --crate-name m1probe \
       -Ztrust-policy=advisory -Ztrust-dump=mir-only:<dir> m1probe.rs
```

The `mir/` files are renamed from the driver's hashed
`trust-mir-<hash>-<hash>.json` names to `<fn>.trust-mir.json`; the content is
byte-identical to the dump (identity lives in the embedded `def_path`, not the
filename).

The probe is designed for the M1 pin (DIRECT-LANE-PROOF-AUTHORITY.md): every
function carries at least one obligation, and the set deliberately spans both
verdict directions per class —

| probe | function | obligation | expected | measured 2026-08-31 |
|---|---|---|---|---|
| m1probe | `arith` | add/div/mul overflow + div-by-zero | refutable | refutation stated, both lanes |
| m1probe | `remu` | rem-by-zero (`b` unconstrained) | refutable | refutation stated, both lanes |
| m1probe | `remu_safe` | rem-by-zero (`b \| 1` is odd) | provable | PROVED, both lanes |
| m1probe | `divu_safe` | div-by-zero (`b \| 1` is odd) | provable | PROVED, both lanes |
| m1probe | `sh` | shift-in-range (`k` unconstrained) | refutable | refutation stated, both lanes |
| m1shift | `sh_safe` | shift-in-range (`k & 31 < 32`) | provable | PROVED, both lanes |
| m1bounds | `pick` | bounds (`i` unconstrained) | refutable | NOT SOLVED — named blocker |
| m1bounds | `pick_safe` | bounds (`i & 3 < 7`) | provable | NOT SOLVED — named blocker |

The m1bounds probe plans cleanly on both lanes but cannot be SOLVED through
the native proof-grade entry: trust-mc's admission gate refuses
`Inst::ExtractElement` unconditionally. The harness pins that refusal
(`bounds_probe_is_refused_by_the_extract_element_gate_on_both_lanes`) so a
future trust-mc bounds derivation flips it into the solved battery
consciously.

Consumed by `trust-bmc/src/direct_shadow_differential.rs` (feature
`trust-mc-native-trust-ir-bundle`). Re-minting with a newer driver is fine —
the harness binds to obligation identities and classes, not to module bytes —
but re-run the whole battery and update this header.
