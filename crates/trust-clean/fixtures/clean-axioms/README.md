# clean-axioms context fixtures

Inputs for the `clean axioms` instrument (`src/axioms.rs`, `src/bin/clean-axioms.rs`),
exercised by `axioms::tests::supplied_fixture_*` and `tests/clean_axioms_cli.rs`.

`ax_*.json` and `ax2_*.json` are the clean-sorry reviewer's inputs (2026-09-28), copied
verbatim. Before the fix each `ax2_*` context read CLEAN: it counterfeits a foundation
(`propext : False`, `Quot.sound : False`) under a context whose `False` is a Definition, so
the only axiom in the closure carried a foundational NAME. The other files add a trust
marker declared as a Definition (`sorryax_definition`) and as an Axiom (`trustedAy_axiom`),
a foundation declared as a Definition (`choice_definition`), and the two controls: the three
foundations referenced WITHOUT a declaration (the kernel's own axioms: CLEAN) and a trust
marker referenced without one (unresolved: NOT CLEAN).

`def_*.json` (2026-09-29) cover the second route the cb/track-b reviewer measured: context
DEFINITIONS were never type-checked, so an ill-typed `mySorry : False := Sort 0` under a
non-reserved name (`def_ill_typed_mysorry`, the reviewer's `ill_typed_def.json` verbatim) and a
self-referential `x : Prop := x` (`def_self_reference`, the reviewer's `self_ref_def.json`) both
read `CLEAN ✓`. Every definition is now kernel-checked against the entries declared BEFORE it
(`kernel_check::definition_refusal`): those two, a two-definition cycle (`def_cycle`), and a
value at the top universe (`def_universe_overflow`, where `Sort MAX : Sort MAX` used to hold) are
REFUSED. The controls still build: `def_clean_chain` (definitions only, one unfolding through
another) reads CLEAN, and `def_well_typed_chain` (an identity function over a declared `P`) reads
NOT CLEAN, because its two axioms are residual.

`debruijn_*.json` (2026-09-29) cover a kernel bug under the definition check: `infer_type` returned
a bound variable's stored type without lifting it past the binders bound after it
(`kernel_check::infer_type`, the `Var` rule). `debruijn_shift_false`, `debruijn_shift_false_inline`
and `debruijn_poly_id` are the cb/track-b round-2 reviewer's `shift_false.json`,
`shift_false_inline.json` and `poly_id.json` verbatim, and `debruijn_k_true_type` is their
`k_true_type.json`. Before the fix the two `shift_false` contexts, and `debruijn_shift_false_deep`
(the same attack under four binders), read `CLEAN ✓`: `(λP:Sort 2. λx:P. λQ:Prop. x) Type Prop`
typed as `∀Q:Prop, Q`. They are now REFUSED, as is `debruijn_dep_confuse` (`λh:P a. h` declared
`P a → Q b`) and `debruijn_open_axiom` (an axiom whose type has a free variable: the `Const` rule
returns a context type unshifted, so every context type must be closed). The controls the bug
REFUSED now read CLEAN: the polymorphic identity, `K` at its true type, `compose` over six binders
and a dependent hypothesis `λh:P a. h : P a`.
