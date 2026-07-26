# enum-discr-predicates-2026-07-16 — the discr-leaf lane is a GENERAL enum-tag-predicate lane

The W-DISCR-LEAF lane (main 5eb24ef961) is not Option/Result-specific — it
certifies ANY `_0 = Eq(Discriminant(self), K)` [+ Not] enum-tag predicate. 9
stdlib predicates, ALL fully_faithful, zero new lane:
- std::cmp::Ordering::is_lt / is_eq / is_gt / is_le / is_ne
- std::ops::ControlFlow::is_break / is_continue
- std::task::Poll::is_ready / is_pending (is_pending via the is_none/is_err Not-flip)

Graded by the release ff-gate built WITH the discr-leaf lane. These predicates
are ubiquitous in real code (every comparison → Ordering; every ?-in-iterator →
ControlFlow; every async poll → Poll). Honesty tier: uninterpreted-but-total,
faithful to the MIR tag-compare.

In-tree regression: `tests/discriminant_predicate_corpora.rs` runs all 9 dumps
through the production `prove_dump_dir` pipeline and pins the MirSem route.
