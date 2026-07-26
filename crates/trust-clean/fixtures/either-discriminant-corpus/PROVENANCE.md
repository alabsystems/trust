# either-discriminant-corpus — provenance

Two files, copied byte-for-byte (never hand-transcribed) from
`crates/trust-clean/fixtures/census-2026-07-06/either/`:

- `Either__<L, R>__is_left.json`
- `Either__<L, R>__is_right.json`

Both are REAL `TRUST_DUMP_MIR` dumps of `either` 1.15.0's `Either::<L,
R>::is_left`/`is_right` (real, unmodified crates.io source — see the sibling
directory's own `PROVENANCE.md`/`regenerate.sh` for the full compile
provenance). Isolated into their own small directory (rather than reusing the
full 47-function `census-2026-07-06/either/` corpus, most of which is
out-of-scope shape-gaps unrelated to this fixture's purpose, or added to
`fixtures/real-spec-corpus/`, whose own `real_spec_corpus_witness_switchover_
to_trustir_is_live` test pins `fully_faithful_mirsem_fallback == 0` — a
DIFFERENT invariant than what these two functions establish) so the
discriminant-guard regression test (`either_discriminant_guard.rs`) runs a
small, precise, callees-first `prove_dump_dir` pass over EXACTLY the two
functions this gap closes: `is_left` (the enum-discriminant `SwitchInt` guard)
and `is_right` (`!is_left(self)`, the Call-then-UnaryOp desugar), with
`is_right` consuming `is_left`'s certified-callee registry entry exactly as
`prove_dump_dir`'s real callees-first composition does over the whole corpus.

See `reports/flagship-crate-census-2026-07-06.md` for the gap analysis this
fixture closes (THE PICK, M1 rung 1).
