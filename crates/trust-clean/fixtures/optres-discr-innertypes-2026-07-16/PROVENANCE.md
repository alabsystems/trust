# optres-discr-innertypes-2026-07-16 — inner-type breadth of the discr-leaf lane

The W-DISCR-LEAF tag-compare lane (main 5eb24ef961) reads the MIR
`Rvalue::Discriminant`, which is the ABSTRACT enum tag — it abstracts over the
physical layout, INCLUDING niche optimization. So `Option::<T>::is_some` /
`is_none` and `Result::<T,E>::is_ok` certify for essentially ANY inner type,
not just the seed `Option<i32>`.

11 instances, ALL fully_faithful (results.tsv), spanning:
- plain payloads: i32, u8, bool, char, (i32,i32), Result<i64,i64>
- NICHE-optimized payloads: Option<&i32>, Option<Box<i32>>, Option<NonZero<u32>>
  — these use a pointer/range niche at codegen, but the MIR is STILL
  `Discriminant(o) == K`, so the lane certifies them uniformly.

Graded by the release ff-gate-diagnose-2026-07-10 built WITH the discr-leaf lane.
Pure computation, zero new recognizer — confirms the lane's reach is
inner-type-agnostic. Honesty tier unchanged: uninterpreted-but-total, faithful
to the MIR tag-compare.

In-tree regression: `tests/discriminant_predicate_corpora.rs` runs all 11 dumps
through the production `prove_dump_dir` pipeline and pins the MirSem route.
