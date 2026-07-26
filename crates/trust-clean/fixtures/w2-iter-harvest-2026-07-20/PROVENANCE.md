# w2-iter-harvest-2026-07-20 — the W2 iterator wall, mapped

21 wrapper-reachable mono instances (for-loop desugar, iter().sum() chain,
count, first_or, while_idx control). Baseline: 19 SHAPE_GAP / 2 SAFETY_GAP / 0 FF.

THE WALL'S STRUCTURE (recon wf_3a36f7c4):
- for-loop desugar: Iter::next is an EXPLICIT Call each iteration (the W6
  call_once pattern); loop CFG = header / Option-switch on next's result
  (= the payload-extract dispatch) / back-edge. Clean skeleton; the in-loop
  Call is the composition gap.
- Iter::next DUMPS (12bb); blocked SOLELY by `Unsupported BinOp::Offset`
  (pointer post-increment). into_iter/Iter::new/fold identically. => INCREMENT-0
  (extraction): model BinOp::Offset (ptr + idx*size) — the same core::ptr
  frontier as e76e5b6590, as a MIR BinOp. Unblocks the whole slice-iter leaf family.
- sum chain depth 5: sum -> Sum::sum -> Iter::fold (SPECIALIZED, no next:
  ptr_offset_from_unsigned len + Offset addressing + unchecked_add idx).
  Iter::count = pure ptr_offset_from_unsigned, NO loop.
- while_idx (index loop, ZERO calls): via_mirsem_loop_shape=TRUE already;
  SAFETY_GAP. => INCREMENT-1 (the vetted design): the slice-index-loop lane.
- Bonus min-repro: intrinsics::cold_path = the literal empty body, still
  SHAPE_GAP (cheapest shape-lane test case).

INCREMENT-1 (adversarially vetted, 3x NEEDS-GATE converging): genuinely
inductive loopInvariantRule + loopRankTerminates (rank toNat(n-i)) over the
CounterInRange invariant; bounds + counter-overflow asserts kernel-discharged
from the invariant; accumulator HAVOCKED (its overflow assert genuinely
undischargeable spec-free). MANDATORY GATES from the skeptics: (1) total-
correctness claims ONLY under function_safety_vcs_all_discharged; (2) partial-
tier claim surface otherwise (a panic exit exists); (3) fail closed unless
declared postconditions are EMPTY (no ensures may ride the havocked acc).
