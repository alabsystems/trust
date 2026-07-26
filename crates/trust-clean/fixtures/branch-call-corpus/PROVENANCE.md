# branch-call-corpus — provenance

Trust: the BRANCHY call-arm sub-axis of the call spine
(`SemBranchTree::CallLeaf` / `sem_call_arm_of_mir` in `mirsem.rs`,
`check_branch_call_refinement` in `trustir_anchor.rs`/`trustir_call.rs`),
commit `be516ccb2f`. Scoping: `reports/branchy-multicall-spine-scoping-2026-07-03.md`.

## Honest provenance statement (2026-07-07 audit, §2 item 8)

**These nine JSONs are HAND-BUILT fixture files, not `TRUST_DUMP_MIR` compiler
output.** Specifically:

- There is **no SOURCE.rs and no regenerate path**: no Rust source was ever
  compiled to produce these files, so they cannot be re-dumped with `trustc`.
- The spans are **degenerate placeholders**: every span points at a
  nonexistent `SOURCE.rs` with dummy coordinates (`1:0-1:1` / `1:0-3:1`),
  which is how a genuine dump never looks.
- This is an **authored fixture** (SYNTHETIC, not even SYNTHETIC_EXTRACT):
  the MIR JSON was written by hand to exercise the recognizer/kernel
  machinery. It is NOT published code and NOT compiler-produced MIR — unlike
  the sibling corpora (`assert-guard-corpus`, `real-crossblock-corpus`,
  `leaf-call-corpus`), whose JSONs are genuine `trustc` dumps.
- Per the landing commit's own framing: **infrastructure, ~0 real-crate lift
  today — NOT a measured real-crate coverage lift.** The corpus certifies via
  shape composition over identity/requires-only helpers.

The hand-built shapes are *plausible* MIR (checked-callee calls as sole
writers of the convergence local, `SwitchInt` branches, `Call` terminators),
but nothing guarantees `trustc` would lower equivalent Rust to exactly these
bodies. Claims backed by this corpus are claims about the recognizer and
kernel composition mechanism only.

| fixture | role |
|---|---|
| `helper1.json`, `helper2.json` | certified identity leaf callees |
| `helper_req.json` | leaf callee with a `requires (x) < (1000)` precondition |
| `pick.json` | positive: `if c { helper1(a) } else { helper2(b) }` branch-over-calls |
| `pick_mixed.json` | positive: call arm + scalar arm mix |
| `pick_established.json` | positive: caller requires establish the callee's requires per arm |
| `pick_uncertified.json` | negative control: an arm calls an uncertified callee → declines |
| `pick_bad_arg.json` | negative control: non-scalar / unmodeled arg → declines |
| `pick_partial_establish.json` | negative control: requires established on one arm only → declines |

If this corpus is ever regenerated from real compiled sources, replace this
file's statement with the dump commands and byte-comparison results, per the
`assert-guard-corpus`/`real-crossblock-corpus` pattern.

Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0 OR MIT
