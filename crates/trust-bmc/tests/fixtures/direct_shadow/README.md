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
| m1bounds | `pick` | bounds (`i` unconstrained) | refutable | refutation stated, both lanes (2026-11-06) |
| m1bounds | `pick_safe` | bounds (`i & 3 < 7`) | provable | PROVED, both lanes (2026-11-06) |

The m1bounds probe plans cleanly on both lanes. Until trust-mc TMC-1
(`496360df7`) it could not be SOLVED through the native proof-grade entry,
because trust-mc's admission gate refused every `Inst::ExtractElement`. TMC-1
admits a read the translator models as a `select` of SMT-array lanes under its
own bounds obligation. From Trust's pin of it (2026-10-02, `10a825655d`) the
MIR lane refuted `pick` and proved `pick_safe`. The direct lane proved
neither, because the translator did not model its `icmp ult usize` bounds
comparison (`UnsupportedComparison`, failing closed: refutations demote to
unknown), and a retired test
(`bounds_probe_solves_on_the_mir_lane_and_the_direct_lane_fails_closed_at_its_comparison`)
pinned that split. From Trust `8862c94337` (2026-11-02), whose trust-mc pin
brought in trust-mc `c88bca8d7`'s operand-consumption guard, the MIR lane's
read of the root `[i32; 7]` parameter was refused too (NotProved,
`OperandConsumption`): the guard counted a root entry parameter as initialized
only when it was a scalar or a zero-field aggregate. That lasted until trust-mc
`9cb7ffef6` granted a root array parameter its value domain. The probe is in
the solved battery
(`m1_differential_scorecard_agrees_and_pins_both_verdict_directions`) since
Trust pinned trust-mc `5d05b457a` (2026-11-06, BMC-LANE-1), and the entry needs
both fixes: `9cb7ffef6` for the MIR lane, and `00e0292a8` (pointer-width
integer comparisons modeled in both native lanes) for the direct lane.

Consumed by `trust-bmc/src/direct_shadow_differential.rs` (feature
`trust-mc-native-trust-ir-bundle`). Re-minting with a newer driver is fine —
the harness binds to obligation identities and classes, not to module bytes —
but re-run the whole battery and update this header.
