# Call-event conjunctions captured for BRANCH-SPLIT-1

Each `<rung>-<opt>-<triple>.json` is the `conj` that `call_event.rs` hands to the kernel step
(after `abi_fold`, before `try_kernel_recheckable_conjunction`), serialized with `serde_json`.

- Producer IR: `build/host/stage1/bin/trustc` of main `605f57d8cf`,
  `-Ztrust-dump=ir: -Ztrust-ir-lower=on -Ztrust-verify=off -Coverflow-checks=off`, on
  `tests/trust-f1-ladder/{micro/s04_if,micro/s05_if_chain,programs/r02_branch}.rs` (the IR is
  identical at `-Copt-level=0` and `2`). Dumped, not hand-written.
- Objects: the bridge's own trust-cg compile of that IR (assert lines folded, as the compiler lane
  folds an unsited constant-true check) at O0 and O2, per triple; the gate reads the unfolded IR.
- Capture: a temporary, uncommitted `eprintln!` of `serde_json::to_string(&conj)` before
  `kernel_eligible` in `call_event.rs`, driven by a local triage test, on 2026-11-14 at main
  `5d79168624`. Not reproduced by any committed command; regenerate by the same steps.
- At capture: s04 `KernelRecheckable` (bit-blast), s05 `StructuralCitation` (wide multiply, so
  [VALIDATED]), r02 no kernel evidence (two items; [VALIDATED]); the existing
  original-conjunction route declined all twelve. No conjunction holds `Select` or `Store`.
- Distinct inputs: the twelve files hold five distinct conjunctions. The four s04 files are one
  (O0 and O2 give the same conjunction), and each s05 and r02 file equals its other-triple twin,
  so there are three distinct s04/s05 inputs (s04, s05 O0, s05 O2) and two distinct r02 inputs
  (O0, O2). `branch_split::tests::fixture_identities` pins this; the triple dimension adds no
  coverage. Provenance against live IR is the S3 gate test's (rung_fixture), not these files'.

## s07_local_call (BRANCH-SPLIT-1, conjunctions with no atoms)

`s07_local_call-O0-aarch64-apple-darwin.json` is the `conj` of ladder rung s07_local_call at O0
(`h(a) = a * 5 + 1`, `rung(x) = h(x) + h(x + 1)`): five items with no Ite on a variable (two ground
reach indicators `Ite(true, 1, 0)`, the two call arguments, and the result over the call-result
leaves `CER_R@24` / `CER_R@30`), the machine side under the `mov` wrappers `BvOr(0, v)`.

- Producer IR: stage-1 `trustc` of main `80c41bb667`, the flags above, on
  `tests/trust-f1-ladder/micro/s07_local_call.rs` (identical at `-Copt-level=0` and `2`).
- Object: the bridge's own trust-cg compile of that IR at O0; its `rung` words equal the ladder
  certificate's s07 O0 words.
- Capture: the branch split's own `TRUST_GATE_TRACE=1` line `[branch-split] conj <json>`
  (`branch_split.rs` `prove`), driven by a local uncommitted probe on 2026-11-14 at worktree HEAD
  `fdc936d263`, under a tree whose route still declined it ("no side branches on a variable").
  The `aarch64-unknown-linux-gnu` capture is byte-identical, so it is not kept.
- At capture: `AyValidated` ([VALIDATED]); the bit-blast was 2600 refutation steps (over the
  2048 limit) and `closed_branch::retry` declined (every item lowers).
- Not in `DISTINCT`: the legacy fixture pin is the parent's, and the SMT agreement test's `at`
  substitutes only `X0`, not the `CER_R@*` leaves.
