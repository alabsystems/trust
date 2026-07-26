# multi-eq-corpus — provenance

Two files, copied byte-for-byte (never hand-transcribed) from
`crates/trust-clean/fixtures/census-core-m5-2026-07-07/{u8-ascii,char-ascii}/`
— themselves real `TRUST_DUMP_MIR` output of THIS repo's own `library/core`
(see that census's own `PROVENANCE.md`/`regenerate.sh`).

This is the mission's MULTI-VALUE SwitchInt gap: `num::<impl u8>::is_ascii_whitespace`
and `char::methods::<impl char>::is_ascii_whitespace` both lower to a SINGLE
`SwitchInt` whose five EXPLICIT targets (`9, 10, 12, 13, 32` — tab, LF, FF, CR,
space; note NOT vertical-tab `11`, which `core`'s own whitespace definition
excludes, unlike `ascii_utils::is_space`'s 6-value set below) all converge on
ONE arm block:

```json
"SwitchInt": {
  "discr": {"Copy": {"local": 1, "projections": ["Deref"]}},
  "targets": [[9,2],[10,2],[12,2],[13,2],[32,2]],
  "otherwise": 1
}
```

`census-core-m5-2026-07-07/VERDICTS.tsv`'s own row for this function ("multi-value
SwitchInt on (*self) + GAP-BOOL") named this exact gap as unclosed as of that
2026-07-06 measurement. The new sibling recognizer
`mirsem::sem_cf_return_of_mir_multi_eq` + `SemMultiEqReturn` + the
kernel-checked witness `trustir_multieq::check_multi_eq_refinement` close it:
the guard denotes as a disjunctive equality
`discr==9 ∨ discr==10 ∨ discr==12 ∨ discr==13 ∨ discr==32` (an N-ary `Bool.or`
fold of `Int.beq` terms over a plain `Int` motive — no ADT registration
needed, since both arms are `bool`-literal `Use` rvalues).

## Scope note: NOT every mission-named target lowers to this shape

The mission also named `core::u8::is_ascii_control`/`ascii_utils::<u8 as
Check>::is_space` as multi-value-guard candidates. A structural scan of every
locally-present fixture corpus (`census-core-m5-2026-07-07`,
`census-rung2-2026-07-07`, `census-2026-07-06`, and every smaller corpus
directory) for the EXACT shape (one `SwitchInt`, 2+ explicit targets, ALL
converging on a single block, `otherwise` reaching a DIFFERENT block) found
ONLY these two real functions. `is_ascii_control` (`(b<=31) || (b==127)`) and
`ascii_utils::is_space` (`(9<=b && b<=13) || b==32`) both lower DIFFERENTLY —
as chained SINGLE-target `SwitchInt`s over `Le`/`Eq` comparison temps (a
range-check + disjunction hybrid, `VERDICTS.tsv`'s own "multi-value +
disjunctive hybrid" tag for `is_ascii_control` independently confirms this),
which is a genuinely DIFFERENT, more complex MIR shape this narrowly-scoped
recognizer does not claim to cover (would need a general disjunction-of-
comparisons guard, not a flat multi-value-equality one) — an honest, named
scope boundary, not a silent miss.

All two measured `fully_faithful=1, via_trustir=1, kernel_rejected=0` through
the real production `prove_dump_dir` gate (see `tests/multi_eq_corpus.rs`).
