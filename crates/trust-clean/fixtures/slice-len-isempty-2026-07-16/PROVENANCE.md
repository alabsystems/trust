# slice-len-isempty-2026-07-16 — the highest-cascade leaf: slice/str len + is_empty (SHAPE_GAP baseline, teed up)

len/is_empty are the most-forwarded-to leaves in real code. Shapes (from the dumps):
- slice::is_empty (1bb): `_2 := UnaryOp(PtrMetadata, _1); _0 := BinaryOp(Eq, _2, 0)` → Bool
- str::is_empty   (1bb): `_3 := Cast; _2 := UnaryOp(PtrMetadata, _3); _0 := Eq(_2, 0)`
- str::len        (1bb): `_2 := Cast; _0 := UnaryOp(PtrMetadata, _2)` → usize
- slice::len            : `_0 := UnaryOp(PtrMetadata, _1)` (inlined away under -O in this probe)

THE GAP (precise): `PtrMetadata`/`Len` already resolve to the opaque-total
`SemOperand::Len(Var slice)` carrier in `sem_guard_operand_of_mir`
(mirsem.rs:4486) — but ONLY in the index-GUARD context. To certify these leaves,
route that resolution into (a) `resolve_cmp_side` (so `Eq(Len, 0)` composes — the
DIRECT analogue of the just-landed Discriminant-compare arm at mirsem.rs:5653),
and (b) a straight-line leaf RETURN `_0 := PtrMetadata(self)` → `SemOperand::Len`.
Honesty tier: uninterpreted-but-total (Len is the existing opaque length carrier),
faithful to the MIR metadata-compare. Fail-closed gates to inherit: param slice
only, single-assignment length temp, no projection (all present in
sem_guard_operand_of_mir). str::len/is_empty additionally need the fat-pointer
Cast handled.

DEFERRED — the production fully-faithful gate still lacks the bounded
PtrMetadata/Len compare-and-return lane described above. Until that lane lands
with its fail-closed parameter, assignment, projection, and cast checks, these
three bodies remain honest `SHAPE_GAP` rows and mint no certificate.

Regression status: intentionally excluded from the fully-faithful assertions in
`tests/discriminant_predicate_corpora.rs`. `results-baseline.tsv` records the
three observed `SHAPE_GAP` rows; it is a deferred baseline, not a certification
claim. Add a current-results artifact and production-pipeline assertion only
when the PtrMetadata/Len shape lane is implemented.
