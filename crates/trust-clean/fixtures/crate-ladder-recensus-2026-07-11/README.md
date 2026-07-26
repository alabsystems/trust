# crate-ladder-recensus-2026-07-11 — W1 re-census evidence (MEASUREMENT ONLY)

Re-census of every committed published-crate corpus against CURRENT main
(`eb90bbfa88`, "keep-abreast: clean pin -> merge … ElabResult::Example arms"),
after a cycle that landed capabilities the corpora were never scored against:

- opaque-chain ADT-return (Tier-1, `reports/m6-tier1-opaque-chain-adt-return-2026-07-10.md`)
- ordering-dispatch opaque-chain + guard-implied assert discharge (P-ORD-CMP,
  `reports/leaf-assert-unhostage-2026-07-11.md`)
- structural-fold lane rungs A–E (self-recursion,
  `docs/design/2026-07-10-structural-fold-lane.md`)
- 128-bit `ShiftWidth::W128` ShiftOob modeling
- `Ty::Datatype` reflect/grounding arm (post-2026-07-09-recensus fix)
- `ElabResult::Example` kernel re-check arms

**ZERO recognizer/pipeline sources were modified in this session** — the diff
is fixtures + report only. The corpora themselves (the committed `*.json`
dumps under `fixtures/census-2026-07-06/`, `fixtures/census-rung2-2026-07-07/`,
and the small named corpora) are BYTE-UNCHANGED; only fresh verdicts over the
same bytes were computed.

## Method

Two production-anchored instruments, both SCRATCH tools already in-tree:

1. **Per-row**: `src/bin/ff-gate-diagnose-2026-07-10.rs` — the exact
   `prove_one_function` FULLY_FAITHFUL gate per function (pinned to the
   production gate by `diagnosis_fully_faithful_matches_production_gate`),
   callees-first composition, sibling dump bodies threaded, no wall-clock
   budget (every verdict definitive, never a timeout artifact).
   Output: `results/<corpus>.ff-gate.tsv` (+ `.stderr` cluster summaries).
2. **Aggregate**: `src/bin/census-2026-07-06.rs --aggregate` — ONE
   `prove_dump_dir_with_budget_and_bodies` call (the function `targo trust
   prove` calls) over each whole corpus, `TRUST_CENSUS_BUDGET_SECS=60`.
   Output: `results/<corpus>.aggregate.txt` (full `ProveScorecard` debug dump).

Binaries: debug builds of this branch's own sources
(census `3f48e2d886805686…`, ff-gate `e0b02a8e8486d3a3…`, sha256 prefixes).
Host: moderately contended (sibling agent builds); budget artifacts, where
they occurred, are called out in the report and re-run at a top-up budget.

## Inventory (`results/`)

- `<corpus>.ff-gate.tsv` + `.stderr` — per-row production-gate verdicts +
  cluster summaries (20 corpora: the 9 published-crate census dirs +
  leaf-call, either-disc, adt-return, from-signed, container, loop-leaf,
  ptr-spine, lift-demo, structural-fold, multi-eq, level-fold).
- `<crate>-flips.targets` + `<crate>-flips.isolated.tsv` — the 9 flipped
  rows re-verified one-by-one through the isolation harness at 120 s.
- `<corpus>.aggregate.txt` + `.stderr` — full `ProveScorecard` dumps from
  the production `prove_dump_dir` driver at 60 s/function.
- `no-recursion-scan.py` + `.out` — the §3.1 proof that no census corpus
  contains a self-recursive row or a call-graph cycle.
- `ffgate-run.log` / `aggregate-run.log` — timings (ff-gate full sweep
  ≈ 9.5 min total; slowest corpus cast at 195 s for 202 rows).

## Scoreboards

See `reports/crate-ladder-recensus-2026-07-11.md` for the BEFORE→AFTER tables,
per-row flip lists with verdict lines, and the gap classification of every
still-short row against the current lane inventory.
