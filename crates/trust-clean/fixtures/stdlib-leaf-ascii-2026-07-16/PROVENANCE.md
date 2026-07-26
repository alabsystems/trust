# stdlib-leaf-ascii-2026-07-16 — provenance

This corpus began as the **first stdlib leaf-family certification** beyond the
two previously certified `is_ascii_whitespace` functions. It contains the complete
`is_ascii_*` classification-predicate family on `char` and `u8` (24 functions).
The current checked-in verdict table is **24/24 FULLY_FAITHFUL**. Full narrative
and per-function verdicts: `reports/p1-leaf-harvest-ascii-2026-07-16.md` (P1 of
the finishing map, `reports/finishing-map-prove-all-of-rust-2026-07-14.md`).

## Current parity — 24/24

- **24 / 24 FULLY_FAITHFUL (100%)**; both the `char` and `u8` sub-families are
  **12/12**.
- Lane split: **16 via_trustir**, **8 via mirsem**.
- `kernel_rejected = 0`, safety obligations/discharged are `0/0`, and the wall
  tag is `-` on every row.
- The 24 MIR dumps are unchanged. Later production-lane fixes regraded the six
  original SHAPE_GAP rows; they did not replace or edit the harvested bodies.

`regenerate.sh --validate-only` rebuilds the current production gate/census tools,
hash-checks the sources and immutable dumps, and compares every recorded machine
field. This current-checkout validation is distinct from the historical extraction
toolchain record below; it does not retroactively make the originating stage2
environment independently reproducible.

## Historical closure record — 18/24 → 23/24 → 24/24

The originating harvest classified **18/24** rows as FULLY_FAITHFUL (char 11/12,
u8 7/12; 11 via_trustir and 7 via mirsem). Two later, fail-closed recognizer
normalizations completed the unchanged corpus:

1. **WALL-JOINTEMP label: 18/24 → 23/24.** The five u8
   `is_ascii_{digit,octdigit,uppercase,lowercase,graphic}` rows became
   FULLY_FAITHFUL via_trustir. The historical wall name was imprecise: the
   join-temp return move was already admitted by `sem_cf_return_of_mir`. The
   residual blocker was the guard operand's one-time dereference materialization,
   `_3 := Use(Copy(*_1))`. `sem_deref_materialization_temp_operand`, wired into
   `sem_guard_operand_of_mir`, resolves only that identity-shaped temporary to
   the same `Var(param)` as the direct dereference. Non-identity arithmetic,
   copies of other locals, mutable aliases, multiply assigned temps, and
   dereferences of non-parameter bases still decline.
2. **WALL-CAST-LEAF: 23/24 → 24/24.** `char::is_ascii` became
   FULLY_FAITHFUL via mirsem when the compare-side semantic chase learned to
   compose the existing value-identity cast model for its
   `char as u32`-before-`Le(_, 127)` shape. Narrowing, same-width signedness
   reinterpretation, non-integer casts, multiply assigned sources, and forged
   operand provenance remain fail-closed.

A subsequent audit also corrected `char::is_ascii`'s synthetic char-validity
bookkeeping from safety `1/1` to the production census's honest `0/0`; it is an
entry invariant, not a source- or callsite-bound safety obligation. The current
table incorporates that correction and uses the canonical `mirsem` lane spelling.

## What is here

```
dumps/                 24 real TRUST_DUMP_MIR bodies of THIS repo's library/core
                       (the char + u8 `is_ascii_*` predicate family), renamed
                       hash -> sanitized def_path (:: -> __). JSON is preserved
                       except recursive `span.file` paths are canonicalized to
                       stable `library/core/...` paths.
results.tsv            per-fn verdict and lane plus the manually audited wall
                       field (currently `-` on all 24 rows); kernel_rejected and
                       safety obligations/discharged are machine-checked.
TOOLCHAIN.sha256       the dump-capable stage2 trustc launcher version + binary
                       sha256; it does not pin the full driver/sysroot bundle.
SOURCE.sha256          exact hashes of the two core source files containing the
                       24 harvested bodies.
ARTIFACTS.sha256       exact hashes of all 24 MIR dumps + results.tsv.
int_log10-workaround.diff  the ONE surgical extraction workaround (below).
canonicalize_dump_paths.py  replaces ephemeral extraction-root prefixes in
                       recursive span.file fields with `library/core/`.
regenerate.sh          fail-closed extraction + gate/census revalidation recipe
                       when the separately retained stage2 environment exists.
```

## Headline

- **24 / 24 FULLY_FAITHFUL (100%)**, `kernel_rejected = 0` and safety `0/0`
  on every row. The current checked-in script rebuilds and runs both gate/census
  tools and compares every recorded verdict field.
- **char sub-family: 12 / 12**; **u8 sub-family: 12 / 12**.
- FF lane split: **16 via_trustir**, **8 via mirsem** (both production
  kernel-backed lanes; `fully_faithful=1` is the production gate verdict either
  way).
- There are **no current SHAPE_GAP rows or open ASCII-family wall tags**. The six
  original gaps were the two narrow, now-closed normalizations recorded above,
  not any of the 20 deep walls.

## Toolchain

`TOOLCHAIN.sha256` — the dump-capable stage2 trustc:
- `rustc 1.99.0-dev (7df54072f 2026-07-15) (trustc)`, binary sha256
  `c6434343a7f2605bed29cfeec5729485d8d3a1a87505a451d52b0070d184e47c`,
  aarch64-apple-darwin. This is the stage2 with the thir-lower const-generic fix
  (`f151e4cc60`). No rebuild was done — extraction + certification only.

The originating **18/24** gate/census run used
`ff-gate-diagnose-2026-07-10` + `census-2026-07-06`, built release from the
historical `p1/leaf-harvest-2` branch before the two recognizer fixes. The
originating classifier-binary hashes and raw output were not retained. The git
source lineage and result-table history are retained, and `regenerate.sh`
performs a fresh comparison against production tools rebuilt from the current
checkout. The current **24/24** verdict therefore describes the current lanes
over the hash-bound historical dumps; it is not a claim that the original
pre-fix classifier produced 24/24.

This repository does not retain the originating stage2 driver/sysroot bundle or
the contents of its `/opt/homebrew/lib` search path. The launcher hash is useful
but insufficient to reconstruct that full environment, and no matching launcher
is bundled here. Treat this as a hash-bound historical corpus snapshot, not as a
standalone reproducible toolchain artifact. `regenerate.sh` fails closed unless
the caller supplies the recorded launcher/environment and then requires the
path-normalized dumps to match `ARTIFACTS.sha256` exactly.

## Extraction path (and the one honest workaround)

1. **Why compile core itself, not a probe crate.** Core leaf-fn MIR is NOT
   reachable from a downstream crate that merely *calls* the methods: the MIR
   dump records LOCAL bodies only, so `x.is_ascii_digit()` in a fixture dumps the
   *caller*, not `is_ascii_digit` (empirically confirmed this session). So we
   compile library/core ITSELF — exactly as `census-core-m5-2026-07-07` did.

2. **The int_log10 promotion cycle (why a patched copy).** A plain
   `trustc library/core/src/lib.rs` with NO trust flags compiles core cleanly.
   But the CURRENT dump-capable stage2 trustc, under ANY trust verify/dump flag
   (`-Ztrust-policy=advisory`,
   `-Ztrust-ir-lower=no`, `-Zmir-opt-level=0` — all tried), forces a borrowck /
   `const {}` promotion cycle (`E0391`) on the 10 `num::imp::int_log10::{i,u}*`
   functions and aborts before writing any dump. (census-core-m5 used an OLDER
   stage2 that did not force this ordering; the `const {}` in `int_log10.rs`
   itself is unchanged since the initial commit — the regression is in the
   compiler's extraction path, which we are told not to rebuild or modify.)
   We therefore dump a COPY of library/core with ONE surgical
   change in the UNRELATED module `num/imp/int_log10.rs`: the two
   `assert_unchecked(result <= const { .. })` calls are removed
   (`int_log10-workaround.diff`). `assert_unchecked` is a pure optimizer hint;
   removing it does not change any function's result. **No certified body is
   touched** — the 24 ascii predicates live in `num/mod.rs` + `char/methods.rs`
   and are byte-identical to HEAD library/core.

3. **The end-of-run delayed-bug ICE is cosmetic.** The dump run emits all 27,664
   bodies (`warning: 27670 warnings emitted`) and only THEN flushes a delayed bug
   as an ICE (`NonZero<T>::Metadata` normalization ambiguity in
   `rustc_trait_selection`). Every dump file is on disk before the flush; the ICE
   is unrelated to extraction and does not affect the sliced family.

## Honesty notes

- `kernel_rejected = 0`, safety `0/0`, and FULLY_FAITHFUL hold on every current
  row. There are no current declines or SHAPE_GAP rows to hide.
- WALL-JOINTEMP and WALL-CAST-LEAF are retained only as historical names in this
  provenance record. Every `results.tsv` wall field is now `-`; neither wall is
  an open residue or one of the 20 deep walls (W1-W20).
- The 24/24 result is a current production regrade of unchanged, hash-bound MIR
  dumps. The originating extraction environment remains only partially pinned,
  as described under Toolchain; the current result does not erase that limitation.
- Relationship to `census-core-m5-2026-07-07`: that CENSUS snapshot measured this
  same family at **0 FF** with the older lanes. The originating P1 harvest first
  certified **18 FF**, and the two recorded closures brought the same dumps to
  **24 FF**. Relative to the two `is_ascii_whitespace` functions already
  certified in `multi-eq-corpus`, the current family contributes **22 additional
  certified functions** (16 in the initial harvest, then 6 in the closures).
