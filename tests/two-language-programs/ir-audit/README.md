# The audit corpus of the producer ratchets

These files are what `scripts/two_language_producer_ratchets.py` holds the
`ir-*` rows' pins against. They are copied, unedited except where stated, from
the archived 2026-09-17 two-language proof program in trust-ir
(`first-party/trust-ir/reports/2026-09-17-two-language-proof-program/`).

One edit applies to all three, made 2026-09-21: the absolute paths the archive
recorded for the run's caches and tools — `/Users/<owner>/Library/Caches/...`
and an agent session scratch directory — are rewritten to `<caches>/...` and
`<agent-session-scratch>`, because this directory ships in the public snapshot
and those paths are forbidden content there. Nothing else changed. The rewrite
is confined to the free-text DETAIL of `FEATURE <id> <verdict> <detail>` lines
and to `report.json`'s `identity` strings; the judge reads only the id, the
verdict and a leading `[class]` bracket (`normalize_verdict`), so no row's
verdict or GAP class can move. Measured either side of the edit: the replay,
audit-check and refusal-class suite in
`scripts/tests/two_language_producer_ratchets_test.py` runs 20 tests with 1
skipped and passes identically.

| File | Source in the archive | What it is |
|---|---|---|
| `parta-5b45b83b8.features.txt` | `parta/out/5b45b83b8/features.txt` | Part A (Rust + Clean island -> trust-ir) judged on the from-source stage1 at `5b45b83b8`. |
| `parta-5b45b83b8.report.json` | `parta/out/5b45b83b8/report.json`, slimmed | The measurements behind that judgment. Only the keys the replay reads are kept: each unit's native, emit and module views, plus the attribution-module view. |
| `parta-lean-5b45b83b8.features.txt` | `rerun-lean-head/out.run3-allsrc/features.txt` | Part A-Lean on the same compiler. `clean` and `trust-cg` were the revisions that compiler pins, built from source. |

How they are used:

- **Replay.** `two_language_producer_ratchets.py replay` re-judges the
  archived Part A measurements with the ported judge and compares the result
  with the archived `features.txt`. The verdict and the GAP class must match
  for every row it can re-judge. `.carried` and `.obligations` rows cannot be
  re-judged, because the archive did not keep the module JSON they read.
  `scripts/tests/two_language_producer_ratchets_test.py` runs this replay.
- **Audit check.** `two_language_producer_ratchets.py audit-check` checks the
  pins against these files:
  - Every pin records its row's verdict here, in the `audit` field.
  - A pin that differs from this verdict names the reason in `moved`.
  - Every row in these files is pinned by exactly one `ir-*` row, or is listed
    in the judge's `NOT_PORTED` table with a reason.

The Part A-Lean file still shows the harness defects recorded as F-120:

- 18 GENERAL `.validate` rows read FAIL. The cause is `repair_fndef.py`, which
  corrupted modules that were correct as emitted.
- STANDALONE needles pin the refusal class alone.

The ported judge does neither. Where its verdict differs from the file, the
pin's `moved` reason says so.
