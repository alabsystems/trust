# optres-accessors-2026-07-16 — Option/Result accessor leaves (the next discriminant-leaf target)

Monomorphized `Option::<i32>` / `Result::<i32,u8>` accessors dumped by the W16
mono hook. ALL SHAPE_GAP at baseline (results-baseline.tsv) — the target of the
next discriminant-compare LEAF recognizer.

Shapes:
- is_some / is_ok  (b=1): `_t = Discriminant(x); _0 = BinaryOp(Eq, _t, K)`  → Bool
- is_none / is_err (b=1): `Discriminant, BinaryOp, UnaryOp` (tag-compare + negate)
- unwrap_or (b=5): SwitchInt(Discriminant) → select payload/fallback
- unwrap_or_default (b=5): SwitchInt(Discriminant) → select payload or call
  `Default::default`; a discriminant-select recognizer alone is therefore
  insufficient for this body

Existing infra to build on: `mirsem::SemOperand::Discriminant(base)` already models
the enum-tag read as `idxElem (g base) MIRSEM_DISCRIMINANT_TAG_KEY` (uninterpreted-
but-total tier), plus the discriminant-switch/guard lanes. So `is_some` =
tag-read + BinaryOp compare is within reach as a straight-line leaf; honesty tier =
uninterpreted-but-total (the tag is the idxElem opaque), faithful to the MIR
(which computes exactly `discriminant(x) == K`). The b=2 forwarders (is_some_i32
etc., a Ref-then-Call of the leaf) cascade via the existing call-return lane once
the leaf certifies.

These dumps and classifications are observational regression inputs only. This
directory does not retain a source manifest, generator identity, or analyzer
receipt. Run `./validate-results.sh` with a freshly built current grader to
require exact six-row reproduction; the validator does not fill the missing
historical generation receipt. Nothing here may discharge a verification
condition or mint a verdict by itself.
