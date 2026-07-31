// Deciding whether a safety VC the compiler emitted is faithfully modeled
// here. A VC kind with no modeled counterpart must be reported unmodeled: this
// is the gate that stops a whole-function faithfulness claim from covering an
// obligation nothing checked.

use super::*;

/// Build the de-Bruijn grounding map for a list of operand variable names, assigning
/// `names[0] = bvar(n-1)`, …, `names[n-1] = bvar(0)` — the convention `ground_prop`
/// expects (a leading binder is the OUTERMOST, highest index). A non-`Var` operand
/// (a constant, a struct field, …) is NOT mappable here ⇒ `None` (fail closed).
pub(super) fn debruijn_params(names: &[&str]) -> std::collections::HashMap<String, Expr> {
    let n = names.len();
    let mut m = std::collections::HashMap::new();
    for (i, name) in names.iter().enumerate() {
        m.insert((*name).to_string(), Expr::bvar(u32::try_from(n - 1 - i).unwrap_or(0)));
    }
    m
}

/// The variable name of an integer `Formula::Var` leaf (the only operand shape the
/// formula-aware grounder maps to a de-Bruijn binder). A constant / arithmetic /
/// field-projection operand returns `None` ⇒ the VC is outside the formula-aware
/// fragment and the function fails closed.
pub(super) fn formula_var_name(f: &trust_types::Formula) -> Option<&str> {
    match f {
        trust_types::Formula::Var(n, _) => Some(n.as_str()),
        _ => None,
    }
}

/// Search a `Formula` tree for the FIRST leaf matching `pred`, descending through
/// `And`/`Or`/`Not`/`Implies`. Returns the matched sub-formula.
///
/// Trust: OBLIGATION-REGION SELECTION (2026-07-29) — this may ONLY be applied to a VC's
/// [`emitted_obligation_body`], never to `vc.formula`. `vc.formula` is the violation
/// WRAPPED in block-defs, dominating guards, the function's `preconditions` and its
/// parameters' type bounds, all of which are comparisons that share the violation's
/// shapes; a scan of the whole tree therefore reads a HYPOTHESIS. See
/// [`emitted_obligation_body`] for the measurement and the two forgeries it closed.
///
/// Trust: it has NO production caller left — all seven were replaced first by
/// `obligation_violation_leaf` (2026-07-29) and then, when that too proved to be a
/// descent, by [`locate_violation`]'s shape match on the COLLAPSED body (2026-07-31,
/// round-6 F1: `obligation_violation_leaf` is deleted). It is `#[cfg(test)]` so that a
/// new one cannot be added by accident, and survives only as a test-side probe for
/// "does this tree contain
/// a leaf of that shape ANYWHERE", which is how the region tests demonstrate that the
/// hypothesis the fix stops reading is still present in the wrapped formula.
#[cfg(test)]
pub(super) fn find_violation_leaf<'a>(
    f: &'a trust_types::Formula,
    pred: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    if pred(f) {
        return Some(f);
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().find_map(|x| find_violation_leaf(x, pred)),
        F::Not(a) => find_violation_leaf(a, pred),
        F::Implies(a, b) => find_violation_leaf(a, pred).or_else(|| find_violation_leaf(b, pred)),
        _ => None,
    }
}

/// Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the sub-formula of a wrapped VC
/// formula that IS the obligation the emitter built, recovered by INVERTING the conjoin
/// discipline every wrapper uses.
///
/// A safety VC's `formula` is not the violation. `trust_vcgen` wraps the violation, in
/// this order and always the same way:
///
/// ```text
/// combine_relevant_block_defs        -> And([def..,          body])
/// versioned::conjoin (preconditions) -> And([precondition.., body])
/// v2_formula_with_path_guards        -> Or([And([guards_p,   body]) for each path p])
/// semantic / global / slice-iter     -> And([fact..,         body])
/// conjoin_arg_type_ranges & siblings -> And([Le(lo,p),Le(p,hi).., body])
/// ```
///
/// EVERY conjoining wrapper pushes the body LAST (`versioned::conjoin`,
/// `combine_relevant_block_defs`, `conjoin_arg_type_ranges`,
/// `conjoin_local_type_ranges_excluding`, `conjoin_datatype_field_ranges_excluding`,
/// `conjoin_slice_len_bounds`, the semantic/global/slice-iter conjoins), and the ONLY
/// non-conjoining wrapper — the dominating-path guard map — distributes one COPY of the
/// body over a disjunction of paths. So the inverse is: take the LAST conjunct of a
/// top-level `And`; descend into every disjunct of an `Or` that carries the path-guard
/// shape and require the recovered bodies to AGREE. Genuine disagreement FAILS CLOSED,
/// the same discipline [`emitted_shift_violation_pair_probe`] and `resolve_certified_callee`
/// apply.
///
/// THE PATH-GUARD `Or`, EXACTLY (`generate/safety.rs:1078-1121`). One term per
/// dominating path: a GUARDED path pushes `And([guards_p.., body..])` (the body is
/// FLATTENED in when it is itself an `And`, so the body's last conjunct is the term's
/// last conjunct either way); an EMPTY-guard path — every `unguarded_successors` edge:
/// `Goto`, `Call{target}`, `Drop{target}`, `Opaque{targets}`, and every
/// `UnwindEdge::Cleanup` target — pushes the RAW body, `And` or not. So a block reached
/// by one guarded and one unguarded path whose body is NOT an `And` emits a MIXED `Or`,
/// and the all-`And` test this arm used to apply (`v.iter().all(..)`) is the wrong
/// inverse: it declined to decompose exactly that shape and returned the whole `Or`,
/// dominating guards included, as "the obligation body".
///
/// Trust: MIXED-`Or` FORGERY (2026-07-29, lane A finding [1]) — that was a LIVE
/// false-certificate path, reachable from an ordinary MIR CFG through
/// `trust_vcgen::generate_vcs` with no hostile input beyond the CFG shape. MEASURED on
/// the tree before this arm was widened: `bb0: Drop -> [bb1, Cleanup(bb2)]`,
/// `bb1: _4 = i>=8; SwitchInt(_4) -> [(1,bb3)]`, `bb2: Goto(bb3)`,
/// `bb3: Assert{cond:_5, expected:true, msg:BoundsCheck}` emits
/// `And([Eq(_4, Ge(i,8)), Or([And([Ge(i,8), Not(_5)]), Not(_5)])])`; the peel returned
/// the whole `Or` and `safety_vc_is_faithful_formula_aware` minted a kernel-checked
/// `idx_oob 8 i` for an obligation whose own violation is `Not(_5)` and carries no
/// modeled bounds core at all. Pinned by
/// `a_mixed_path_guard_or_can_never_supply_a_bounds_core`.
///
/// The discriminator is therefore "ANY disjunct is an `And`", not "all are": a guarded
/// path term is ALWAYS an `And` (guards are non-empty and the body is appended).
///
/// PRODUCER AUDIT, re-run and CORRECTED (2026-07-29, lane A round-3 finding [4] — the
/// previous text asserted "a modeled violation `Or` has COMPARISON disjuncts and never
/// an `And` one, checked at every producer", listing six sites; that sentence was FALSE
/// at two of the six it cited, and this widening rests on it, so it is spelled out per
/// site instead):
///
/// | site | shape | `And` disjunct? |
/// |---|---|---|
/// | `checked_vcs.rs:259` (bounds, signed index) | `Or([Lt(i,0), Ge(i,len)])` | no |
/// | `checked_vcs.rs:537` (shift, signed amount) | `Or([Lt(n,0), Ge(n,W)])` | no |
/// | `overflow_vc.rs:461` (signed add/sub/mul LIA) | `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])` | no |
/// | `overflow_vc.rs:712` (`differ`, the BV sign test) | `Or([And([x,¬y]), And([¬x,y])])` | **YES** |
/// | `int_conversion.rs:457` (`try_from` out-of-range) | `Or([Lt,Gt,Eq])` — THREE disjuncts | no |
/// | `int_conversion.rs:462` (`try_from` unwrap_or FACT) | `Or([And([Le,Le]), Eq(dst,default)])` | **YES** |
///
/// So there are TWO `Or` shapes in trust-vcgen that carry an `And` disjunct, not one,
/// and the second is not even a violation: `int_try_from_unwrap_or_facts` builds a
/// semantic FACT whose first disjunct is `range::input_range_constraint`, which IS
/// `And([Le(min,x), Le(x,max)])` (`range.rs:92-100`). Citing it as a checked violation
/// producer was wrong on both counts.
///
/// PRODUCER AUDIT, RE-RUN AGAIN and CORRECTED A SECOND TIME (2026-07-30, round-4 defect
/// [3] — the previous text at the `Implies` arm asserted "no safety violation is emitted
/// as an implication (checked at every `Formula::Implies` construction site in
/// trust-vcgen: `trait_verify`, the recursive-datatype induction schemas, and the CHC
/// lowering — none of them reach a safety VC)". **That sentence omitted
/// `generate/ite.rs`, and `generate/ite.rs` is on the safety path.** The
/// `generate/ite.rs` sites, per row:
///
/// | site | shape it builds | safety VC? |
/// |---|---|---|
/// | `ite.rs:43-47` (`guarded`) | `Implies(g, c)`, or bare `c` when `g` is `Bool(true)` | **YES**, via the two below |
/// | `ite.rs:136-143` (`lift_relation_ites`) | `And([guarded(g_ij, R(a_i,b_j))..])` | **YES** |
/// | `ite.rs:180-186` (formula-position `Ite`) | `And([guarded(c,t), guarded(Not(c),e)])` | **YES** |
/// | `ite.rs:20-32` (`ite_free_equality`) | `And([Implies(c,·), Implies(Not(c),·)])` | no |
///
/// That table is NOT an exhaustive re-audit, and is not offered as one. Measured
/// 2026-07-30 by running the greps rather than quoting them: `Formula::Implies(Box::new`
/// occurs at 25 sites across 14 files under `crates/trust-vcgen/src`, and 36 files
/// mention `Formula::Implies` at all. The superseded sentence named three of them, and
/// this pass traced one more to a safety VC. (An earlier draft of this paragraph said
/// "22 files" — a number transcribed from a review rather than re-derived, in the very
/// sentence disclaiming exhaustiveness. State the command or state nothing.) Nothing rests on
/// completing that enumeration, deliberately — the `Implies` arm is now restricted to the
/// ROOT position, so an implication from any producer whatsoever, at any inner position,
/// is pushed as-is and fails closed.
///
/// `generate/entry.rs:603-604` runs `eliminate_term_ites` — the entry point of the middle
/// two rows — over EVERY generated VC whose formula contains an `Ite`, safety VCs
/// included. So a symbolic `Ite` divisor turns the div-by-zero body `Eq(b, 0)` into
/// `And([Implies(c, Eq(n1,0)), Implies(Not(c), Eq(n2,0))])`, and the shift body
/// `Ge(n, W)` into `And([Implies(c, Ge(n1,W)), Implies(Not(c), Ge(n2,W))])`.
///
/// The last row is `no` for a CHECKED reason, not an assumed one: `ite_free_equality`'s
/// only caller in the tree is `generate/contract_vcs.rs:567`, the postcondition
/// `_0 == <modeled saturating/wrapping_neg call>` return pin — grepped, one hit.
///
/// The same previous sentence also called `refine_vc_with_alias` "the only producer in
/// the tree". That remains true of the WRAPPER, and it was re-checked: `:381` is the only
/// `<vc>.formula = Formula::Implies(..)` anywhere in `trust-vcgen` (grepped for
/// `.formula = ` across the crate; every other hit assigns an `And`, a conjoin helper, or
/// a normalization). Note also that nothing in the tree CALLS `refine_vc_with_alias`
/// today — it is a public API with no pipeline caller (only the re-export at
/// `trust-vcgen/src/lib.rs:260` and its own two unit tests) — so its wrapper is
/// unexercised on the emitted path, and "the wrapper is the ROOT" holds for a caller that
/// applies it last, which is the only way it is used.
/// What the sentence is NOT true of is `Implies` in general — the `generate/ite.rs`
/// rows above build implications INSIDE a safety VC's body, and it was that sentence
/// which licensed descending through every one of them.
///
/// Trust: THE ITE CASE-SPLIT PEEL (2026-07-30, round-4 defect [3]) — with the `And`-last
/// rule feeding the (then-unrestricted) `Implies`-consequent rule, that shape peeled to
/// the LAST arm's consequent WITH ITS CASE GUARD STRIPPED, certifying `n2` for an
/// obligation that says `(c → …n1…) ∧ (¬c → …n2…)` and never reading the `c` arm.
/// Selection was POSITIONAL, not semantic: the round-4 verdict measured arms
/// `[Ge(n1,32), Ge(n2,64)]` yielding `ShiftOob(W64)` and the SAME TWO ARMS SWAPPED
/// yielding `ShiftOob(W32)` — the certified WIDTH flipped with conjunct order.
/// (Re-executed here as `shift_core_selection_tests::a_shift_case_split_certifies_no_
/// arms_width_in_either_order`. That two-WIDTH pair is an API-level construction, not an
/// emitted one — a lifted `Ite` AMOUNT gives both arms the same threshold, because
/// `v2_shift_violation_formula` puts a plain `Formula::Int(width)` on the far side of the
/// `Ge`. The EMITTED carrier of the same mechanism is div/rem, which is payload-free;
/// see `obligation_region_tests::an_ite_divisor_case_split_is_certified_by_no_arm`.)
/// Two arms close it, and they are complementary rather than redundant:
///
///   1. an `And` whose conjuncts are ALL `Implies` is refused outright (a case split has
///      no body to peel to), and
///   2. the `Implies` arm is restricted to the OUTERMOST position, the position
///      `refine_vc_with_alias`'s wrapper occupies when it is applied last (see the
///      no-caller note above).
///
/// Rule 1 alone is NOT sufficient, and the reason is worth spelling out because it is
/// the whole argument. `guarded` (`ite.rs:43-47`) drops the implication for a
/// `Bool(true)` guard, so a case split is not always all-`Implies`: `Ite(Bool(true), t, e)`
/// lifts to `And([R(t), Implies(Not(Bool(true)), R(e))])`, whose FIRST conjunct is bare.
/// What holds instead — read off the producer, not assumed — is that the LAST case of a
/// multi-case list is always guarded:
///
///   * `term_ite_cases`' `Ite` arm (`ite.rs:58-74`) appends `else_cases` AFTER
///     `then_cases`, and every else guard is `and_guard(Not(cond_free), g)`;
///   * `and_guard` (`ite.rs:35-40`) reduces to `Bool(true)` only when BOTH operands are
///     `Bool(true)`, and `Not(cond_free)` is an `F::Not`, never `Bool(true)`;
///   * the `Neg` arm (`:75-80`) and `bin_term_ite_cases` (`:101-119`, `a_cases` outer,
///     `b_cases` inner) both keep the last element last, and `term_ite_cases` yields a
///     `Bool(true)` guard only for an `Ite`-free term (the `_` leaf arm at `:97`,
///     propagated through `Neg`/the binop arms) — the one case `lift_relation_ites`
///     short-circuits at `:133-134` before building any `And`, when it holds on BOTH
///     sides;
///   * the formula-position `Ite` arm (`:180-186`) is the same two-element shape, its
///     second conjunct guarded by `Not(cond_free)`.
///
/// So today's `generate/ite.rs` always ends a lifted `And` with an `Implies`, which rule
/// 2 refuses at any inner position. Rule 2 is therefore the one that closes the measured
/// forgery; rule 1 is the semantic statement of the same thing (a case split is not a
/// wrapper) and does not depend on that positional argument surviving a change to the
/// lowering. Both are kept deliberately.
///
/// HONESTY ABOUT RULE 1: it is **not independently falsifiable today**, and this was
/// checked rather than argued. Reverting rule 1 IN PLACE and re-running
/// `obligation_region_tests` + `shift_core_selection_tests` leaves all 24 green, because
/// rule 2 catches the same shapes one step later — an all-`Implies` `And` is only ever
/// reached at a non-outermost position, where its last conjunct is an inner `Implies`.
/// Reverting rule 2 alone fails 1 test; reverting BOTH fails 4, including
/// `a_shift_case_split_certifies_no_arms_width_in_either_order` with the order flip in
/// one line — `(Some(ShiftOob(W64, false)), Some(ShiftOob(W32, false)))` for one
/// proposition written two ways. So rule 1 is redundancy against a future `go` or a
/// future lowering, not a second measured closure, and it is recorded as such.
///
/// COST, MEASURED over `crates/trust-clean/fixtures` (2326 functions, 772 safety VCs):
/// **zero**. 0 VCs peel through an `Implies` at a non-outermost position and 0 VCs peel
/// to an all-`Implies` `And`, so no certificate in the corpus is withdrawn — the
/// per-VC certificate count is 635 and the `function_safety_vcs_faithful` count is 286
/// on both sides of the change. The defect is API-and-`Operand::Symbolic`-reachable, not
/// present in the committed corpus; see the round-4 verdict's scope limit.
///
/// NEITHER is mistaken for a path-guard map, because the arm does not stop at "any
/// `And`" — it decomposes and then REQUIRES THE RECOVERED BODIES TO AGREE. The BV sign
/// test peels to `Not(y)` and `y`; the `unwrap_or` fact peels to `Le(x,max)` and
/// `Eq(dst,default)`. Both disagree ⇒ `None` ⇒ fail closed. That is the same verdict the
/// BV lane already got by other means (no `Gt(Add..)`/`Or([Lt,Gt])` leaf ⇒ decline),
/// unchanged; and the `unwrap_or` facts are conjoined ahead of the obligation
/// (`generate/safety.rs:893-897` pushes `vc.formula` LAST), so today the peel never even
/// reaches one. An all-unguarded `Or([body, body])` has no `And` disjunct at all and is
/// returned whole, which is harmless: the copies are identical, so the leaf search inside
/// it is a singleton.
///
/// WHY this exists. `find_violation_leaf` used to be run over the WHOLE `vc.formula` at
/// seven sites. Measured over the committed ladder + `real-spec-corpus`:
///
/// | site | safety VCs | whole-tree hit | obligation-body hit | **DISAGREE** |
/// |---|---|---|---|---|
/// | bounds | 35 | 34 | 7 | **30** |
/// | div/rem | 20 | 16 | 10 | **6** |
/// | unsigned-add | 36 | 32 | 32 | **9** |
/// | signed add/sub/mul | 26 | 22 | 22 | 0 |
/// | unsigned-mul | 47 | 42 | 42 | 0 |
/// | unsigned-sub | 107 | 107 | 107 | 0 |
///
/// Every disagreement is a certificate about a proposition the VC does not contain:
///
///   * `itoa`'s `<i16 as Sealed>::write` raises a **u8** add-overflow VC whose own
///     violation is `Gt(_63 + 48, 255)`; the whole-tree scan selected the semantic
///     guard `Gt(_43 + 2, 18446744073709551615)` and minted `Overflow(U64)` — a
///     kernel-checked adequacy certificate for a 64-bit addition on an 8-bit one, on
///     unmodified real library code with no hostile input. 8 of the 9 add
///     disagreements are this family.
///   * the bounds disagreements are almost all obligations with NO modeled leaf of their
///     own. `byteorder`'s `read_u*`/`write_u*` emit the container-length shape
///     `Gt(Int 4, buf__slice_len)`; `check_ascii_printable`'s obligation is literally
///     `Bool(true)`, the emitter's fail-closed marker. They were certified off a
///     `Ge(p, 0)` — either `conjoin_slice_len_bounds`' slice-length type invariant
///     (`type_ranges.rs:397`, present with NO contract at all) or the extractor's
///     synthesized parameter-domain precondition — as `idx_oob 0 p`, i.e. "`p` is out of
///     bounds of a length-0 collection", about a collection the VC never mentions.
///     `swap_pop` instead read `Ge(index, len)` in place of its own two-index
///     `Or([Ge(index, _7__slice_len), Ge(_8, _7__slice_len)])`.
///   * `bit_field`'s `BitArray::get_bit`/`set_bit` div/rem obligations are the bare
///     assert-condition local `Var(_4)` — outside the modeled fragment — yet were
///     certified off an unrelated block-def `Eq(__trust_opaque_scalar_u64, 0)`.
///
/// CERTIFICATE DELTA over the same 485 dumps, exact: **28 bounds certificates dropped**
/// (24 `byteorder`, 3 `arrayvec`, 1 `ascii_utils`), **8 `Overflow(W64)` corrected to
/// `Overflow(W8)`**, and **4 div/rem certificates GAINED** — `udiv128::udivmod_1e19` and
/// `unsafe_div`, whose assert-form obligations the loose scan had missed and the new
/// [`assert_condition_binding`] route resolves honestly. No other row moved.
///
/// LADDER IMPACT: **zero**. Re-scored with `ff-gate-diagnose-2026-07-10`, no budget,
/// over all 450 committed ladder dumps: 181 FULLY_FAITHFUL before and after
/// (164 `via_trustir` / 17 `mirsem_fallback`), and the per-row TSVs are byte-identical
/// across all twelve diagnosis columns. Every function that loses a safety certificate
/// here was already `SHAPE_GAP` with `via_ir_shape = via_mirsem_shape = false`, so no
/// ladder row's FULLY_FAITHFUL verdict was resting on a forged leaf. The forged
/// certificates were inflating the scorecard's `safety_vc_faithful` tallies
/// (`prove.rs:13151`), which is a published figure, and were a live false-certificate
/// PATH — not a currently-green forged row on this corpus.
///
/// WHAT THAT LADDER NUMBER IS AND IS NOT EVIDENCE OF — CORRECTED (2026-07-29, lane A
/// round-3 finding [3]). The previous text here said "`fully_faithful` does not read this
/// function at all". **That was false, and it understated this certifier's authority.**
/// The production gate (`prove.rs:13264`) is
///
/// ```text
/// via_mirsem = ( function_fully_faithful_witness_with_callees(..).is_modulo_3()
///                && function_safety_vcs_all_discharged(..)
///                && function_call_requires_established(..) )
///              || synth_loop_.. || break_loop_.. || monotone_nested_..
/// fully_faithful = via_ir || via_mirsem     (and the ptr-offset conjunct)
/// ```
///
/// and `function_fully_faithful_witness_with_callees`'s clause (b) is literally
/// `let certs = function_safety_vcs_faithful(func)?;`
/// (`mirsem/function_witness.rs:592`). So the mirsem straight-line lane's safety pillar
/// is ADEQUACY **and** DISCHARGE conjoined — this certifier is one of its conjuncts, not
/// absent from it. (`function_safety_vcs_all_discharged` is the other one; only the LOOP
/// disjuncts and the trust-ir lane are independent of this function.) The diagnosis path
/// is pinned equal to it by `diagnosis_fully_faithful_matches_production_gate`
/// (`prove.rs:9600`, `:9713`).
///
/// CONSEQUENCE, both directions, and it is why finding [1] and finding [2] are
/// load-bearing rather than tally-only: since `fully_faithful` is a DISJUNCTION, this
/// certifier can only move a row that the trust-ir lane declines — i.e. the
/// `mirsem_fallback` population. Within it, a FORGED certificate here flips a row INTO
/// `fully_faithful`, and a FALSE DECLINE flips one OUT. The other consumer is the
/// scorecard's `safety_vc_faithful` tally (`prove.rs:13151`), a published figure.
///
/// So a byte-identical ladder is a non-regression check over a population where the
/// trust-ir lane was already carrying the verdict — not a measurement of this lane. The
/// load-bearing measurement is the per-VC census over all 486 committed dumps
/// (`census-2026-07-06` + `census-rung2-2026-07-07` + `real-spec-corpus`, recursive
/// walk): 349 safety VCs, 265 certificates, 106 functions certified by
/// [`function_safety_vcs_faithful`] — recorded per row and diffed, not just totalled.
///
/// VALIDATION. This peel is cross-checked against `emitted_shift_violation_pair_probe`,
/// derived independently by matching `v2_shift_violation_formula`'s VERBATIM
/// `And([input_range_constraint, invalid])` pair anywhere in the tree with a singleton
/// requirement: over the ladder's **77 of 77** shift VCs the two agree exactly
/// (`obligation_body_agrees_with_the_shift_emitter_locator`). Two independent
/// derivations of "the emitter's own violation" that coincide on every real row is the
/// evidence that this is the wrapper-inverse and not a heuristic. The probe is
/// `#[cfg(test)]`: shape alone proved forgeable when scanned over the whole formula
/// (round-3 finding [1]), so POSITION — this peel — is what the shift arm now reads.
pub(super) fn emitted_obligation_body(
    formula: &trust_types::Formula,
) -> Option<&trust_types::Formula> {
    emitted_obligation_body_located(formula).map(|(body, _)| body)
}

/// One visit of the wrapper peel: the node it stopped at, together with the conjunct
/// list that node was the LAST element of. `siblings` is `None` when the node sits
/// directly under an `Or` (a path-guard disjunct that is the RAW body) or IS the whole
/// `vc.formula` — in both cases the emitter conjoined nothing beside it HERE, so no
/// side condition can be read off this occurrence.
///
/// Trust: THE OCCURRENCES ARE THE DOMAIN OF A QUANTIFIER (2026-07-31, round-5 defects
/// [5]/[6]/[7]). A lane that reads a SIDE CONDITION off the emitter's sibling conjuncts
/// — the uadd vacuity check is the only one today — must quantify over EVERY occurrence
/// the peel visits, and an occurrence carrying no sibling evidence must FAIL that
/// universal rather than drop out of its domain. That is why the peel now returns the
/// whole visit list instead of only the agreed body: the multi-path guard split repeats
/// the same body once per dominating path, each with ITS OWN conjuncts, and the
/// empty-guard path pushes the body RAW (`generate/safety.rs:1078-1080`) — an occurrence
/// with `siblings: None` and no ranges at all.
#[derive(Clone, Copy)]
pub(super) struct BodyOccurrence<'a> {
    pub(super) node: &'a trust_types::Formula,
    pub(super) siblings: Option<&'a [trust_types::Formula]>,
}

/// [`emitted_obligation_body`] keeping EVERY occurrence of the agreed body, each with
/// the emitter's own sibling conjuncts. The agreement rule is unchanged — genuine
/// disagreement between two peeled bodies still fails closed.
///
/// Note that this lane's `Or` arm descends EVERY disjunct, the bare ones included, so a
/// MIXED path-guard `Or` contributes its raw disjunct as an occurrence with
/// `siblings: None` rather than being invisible here. That is the structural difference
/// from the trust-ir lane's `violation_candidates`, whose `And`-only `Or` descent made
/// the bare disjunct unexaminable and forced that lane to decline on a mixed `Or`
/// outright (round-5 defect [7]). Here the bare disjunct is examined: it fails any
/// sibling-read side condition, and if its body DISAGREES with the guarded twins the
/// peel returns `None` before any site sees it.
pub(super) fn emitted_obligation_body_located(
    formula: &trust_types::Formula,
) -> Option<(&trust_types::Formula, Vec<BodyOccurrence<'_>>)> {
    let found = emitted_obligation_body_occurrences(formula);
    let first = found.first()?.node;
    found.iter().all(|o| o.node == first).then_some((first, found))
}

fn emitted_obligation_body_occurrences(
    formula: &trust_types::Formula,
) -> Vec<BodyOccurrence<'_>> {
    use trust_types::Formula as F;
    /// `sibs` is the conjunct list `f` is the LAST element of, threaded so a site can
    /// read the emitter's own range constraints.
    ///
    /// Trust: THE `outermost` PARAMETER IS GONE (2026-07-31). Its only reader was the
    /// `Implies` peel removed below. Keeping a positional flag that nothing consults
    /// would assert that position governs here when it no longer does — and a locator
    /// claiming a discipline it does not enforce is precisely the defect class this
    /// file has been repairing for four rounds.
    fn go<'a>(f: &'a F, sibs: Option<&'a [F]>, out: &mut Vec<BodyOccurrence<'a>>) {
        macro_rules! push {
            ($node:expr) => {
                out.push(BodyOccurrence { node: $node, siblings: sibs })
            };
        }
        match f {
            // Trust: THE ITE CASE-SPLIT PEEL (2026-07-30, round-4 defect [3]). An `And`
            // whose conjuncts are ALL `Implies` is a CASE SPLIT, not a wrapper — there is
            // no body to peel to, and taking the last arm's consequent would strip that
            // arm's case guard AND discard every other arm. Refuse: push the whole `And`,
            // which no site's core probe matches, so the VC fails closed. See the
            // ITE-elimination row of the producer table in the doc above.
            F::And(v) if !v.is_empty() && v.iter().all(|c| matches!(c, F::Implies(..))) => {
                push!(f);
            }
            F::And(v) if !v.is_empty() => {
                go(v.last().expect("non-empty"), Some(v.as_slice()), out);
            }
            // The dominating-path guard map's `Or([And([guards_p, body..]) | body ..])`:
            // one copy of the SAME body per path, wrapped in that path's guards when it
            // has any. A GUARDED term is always an `And`; an unguarded one is the raw
            // body. Two trust-vcgen `Or`s that are NOT path-guard maps also carry an
            // `And` disjunct — the BV sign test (`overflow_vc.rs:712`) and the
            // `try_from`-unwrap_or FACT (`int_conversion.rs:462`) — so the `any(And)`
            // test alone does not identify this shape; what does is the AGREEMENT
            // requirement below, which both of them fail. See the producer-by-producer
            // table in the doc above, and the mixed-`Or` forgery this arm closes.
            F::Or(v) if !v.is_empty() && v.iter().any(|d| matches!(d, F::And(_))) => {
                // A disjunct is not a conjunct of anything: `sibs` is cleared, so a RAW
                // (unguarded-path) disjunct arrives at the site carrying NO sibling
                // evidence and fails any side condition read off the siblings.
                for d in v {
                    go(d, None, out);
                }
            }
            // HISTORY OF THIS ARM, kept because it is a four-round case study in
            // narrowing a defect instead of removing it.
            //
            // 2026-07-29 (lane A finding [3]) — an `Implies` peel was ADDED here.
            // Before it, the whole implication was returned as "the body" and the leaf
            // search descended into the antecedent: measured
            // `Implies(Ge(i,8), Bool(true))` -> `Some(Bounds)`.
            //
            // 2026-07-30 (round-4 defect [3]) — the peel was NARROWED to the outermost
            // position, because at any inner position an `Implies` is a case-split arm
            // (that is what `generate/ite.rs` builds) and peeling it strips the guard.
            //
            // 2026-07-31 (round-6 recipe R17) — the narrowing was not enough, because
            // the antecedent was still discarded at the root. The peel is now REMOVED.
            //
            // Trust: THE PEEL IS GONE — FAIL CLOSED AT EVERY POSITION (2026-07-31,
            // round-6 recipe R17). This arm used to be
            //     F::Implies(_, consequent) if outermost => go(consequent, ..)   [removed]
            // and the `_` is the whole defect: it DISCARDED THE ANTECEDENT. Because
            // this peel runs strictly ABOVE `locate_violation`, round 6's entire
            // collapsed-body fix ran underneath it and never saw what was thrown away.
            //
            // MEASURED, on the tree that had just closed the disjunctive decoy:
            // `Implies(Not(Gt(__decoy,5)), core)` — the SAME PROPOSITION as the
            // `Or([core, decoy])` round 6 closed — and `Implies(Bool(false), core)` —
            // an identically-true obligation — each minted a kernel-checked
            // certificate at ALL TEN `site_cores()` rows, including the unsigned-add
            // arm that was round 5's own negative control. trust-ir declined all 20.
            //
            // The arm is removed rather than narrowed to the producer's real shape,
            // for three reasons, each checked here rather than recalled:
            //   1. Nothing CALLS the producer. `grep -rn refine_vc_with_alias` over the
            //      whole tree returns its definition (alias_analysis.rs:349), the
            //      re-export (trust-vcgen/src/lib.rs:260), its own two unit tests, and
            //      documentation — no pipeline caller.
            //   2. Root `Implies` occurs 0 times across the 772 safety VCs the real
            //      emitter raises from the 2326 fixture functions (round-6 census), so
            //      removing the inverse withdraws nothing.
            //   3. The wrapper it inverted is not even the shape the tests described:
            //      `refine_vc_with_alias` builds `Not(Eq(Var(alias-loc, Int), Var(..)))`
            //      or an `And` of those, never the `Var(_, Bool)` the old control used.
            //
            // So this was speculative generality in a certificate locator, and it cost
            // a forgery at ten arms. An `Implies` at ANY position now falls to the
            // default and is pushed as-is, which fails closed. If an aliasing wrapper
            // ever acquires a real caller, re-introduce the inverse GATED ON THE
            // ANTECEDENT — match the producer's shape and verify the antecedent is not
            // contentless — never on position alone.
            _ => push!(f),
        }
    }
    let mut found: Vec<BodyOccurrence<'_>> = Vec::new();
    go(formula, None, &mut found);
    found
}

/// THE ONE LOCATOR every arm of this lane goes through: the single proposition this
/// VC's BODY states, together with every body-position occurrence of it — returned ONLY
/// when the COLLAPSED body itself satisfies the arm's own shape predicate.
///
/// Trust: `is_core` APPLIES TO THE COLLAPSED BODY, NEVER TO A LEAF FOUND BY DESCENDING
/// IT (2026-07-31, round-6). This function REPLACES `obligation_violation_leaf`, which
/// peeled the wrapper to the body and then searched INSIDE it for the first sub-formula
/// matching the arm's predicate. That search was the round-6 root cause and it is
/// deleted rather than narrowed: a leaf found under a body is not the body, so
/// certifying it states something the obligation does not.
///
/// THE FORGERY IT CLOSES, in one shape. For any arm whose core is `C`, the body
/// `Or([C, Gt(decoy, 5)])` — an obligation asserting `C ∨ decoy > 5`, strictly weaker
/// than `C` —
/// has no `And` disjunct, so [`emitted_obligation_body_occurrences`] returns the whole
/// `Or` as the body; the deleted leaf search then descended it, found `C`, and minted a
/// kernel-checked certificate for `C`. MEASURED on the tree before this change, driven
/// through `safety_vc_is_faithful_formula_aware` with each arm's own emitted core in the
/// first position (`obligation_region_tests::a_disjoined_decoy_is_certified_by_no_arm`):
///
/// ```text
/// bounds / IndexOutOfBounds -> Bounds
/// bounds / SliceBoundsCheck -> Bounds
/// div-by-zero               -> DivByZero
/// rem-by-zero               -> RemByZero
/// unsigned-sub underflow    -> UnsignedSubUnderflow(W32)
/// unsigned-mul overflow     -> UnsignedMulOverflow(W32)
/// signed add overflow       -> SignedOverflow(Add, W32)
/// negation overflow         -> NegationOverflow(W32)
/// ```
///
/// — eight of that test's ten rows. The two that already declined are the arms this
/// change was copied FROM, and they are unchanged: the unsigned-ADD arm was already a
/// SHAPE MATCH on the collapsed body (round-5 defects [5]/[6]), and the SHIFT arm has read
/// `shift_violation_shape` off the collapsed body since round 3.
///
/// NOT CLAIMED HERE: what the trust-ir lane does with the same recipes. The round-6
/// defect list states that `trustir_safety.rs`'s own `locate_violation` declines them,
/// and that asymmetry is the reason this change exists — but nothing in this file drives
/// that lane, so it is recorded as the brief's finding rather than as a measurement taken
/// here. Its owner is repairing it concurrently and a parity checker runs afterwards.
///
/// AGREEMENT AND OCCURRENCES are unchanged — they come from
/// [`emitted_obligation_body_located`], which already collapses every body-position
/// occurrence the wrapper peel visits and fails closed on genuine disagreement. What is
/// new is only that the arm's predicate is asked about THAT node.
///
/// COST over `crates/trust-clean/fixtures`: **zero**, re-measured in this tree rather
/// than quoted — `obligation_region_tests::mirsem_corpus_census` reports
/// `funcs=2326 safety=772 certs=635 fn_certified=286` and the identical 28-entry
/// per-kind table before and after. Every certified row's peeled body IS its arm's core
/// (or is the assert-condition indirection, which the second route resolves); the only
/// leaf-under-body population was unsigned-mul's 51 `Or([Lt(a*b,0), Gt(a*b,MAX)])`
/// bodies, and that arm is converted to the unsigned-add shape match with the same
/// vacuity side condition rather than left descending.
pub(super) fn locate_violation<'a>(
    formula: &'a trust_types::Formula,
    is_core: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<(&'a trust_types::Formula, Vec<BodyOccurrence<'a>>)> {
    let (body, occurrences) = emitted_obligation_body_located(formula)?;
    is_core(body).then_some((body, occurrences))
}

/// Which of the two emitter constructions [`assert_bound_or_body_core`] recovered a
/// core from. The negation arm layers an ADDITIONAL subject gate on the assert route
/// (see the `assert_negation_subject` call there), so the route has to be reported
/// rather than erased.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum CoreRoute {
    /// The peeled body IS the violation core (`v2_divisor_is_zero_formula`'s `Eq(b,0)`,
    /// `v2_build_negation_raw_vc`'s `Eq(v, MIN)`).
    Body,
    /// The peeled body is the bare `Var(_c)` assert-condition local and the core is the
    /// RHS of its MIR-confirmed block definition.
    AssertCondition,
}

/// Trust: SHIFT-CORE SELECTION (2026-07-29) — the SHAPE of a shift VC's emitted
/// violation, destructured: `(amount, threshold W, is_signed_form)`.
///
///   * unsigned amount — `Ge(n, Int W)`
///   * signed amount   — `Or([Lt(n, Int 0), Ge(n, Int W)])`
///
/// Exactly the two forms `trust_vcgen::generate::checked_vcs::v2_shift_violation_formula`
/// builds. `None` for anything else (fail-closed).
pub(super) fn shift_violation_shape(
    invalid: &trust_types::Formula,
) -> Option<(&trust_types::Formula, i128, bool)> {
    use trust_types::Formula as F;
    match invalid {
        F::Ge(n, w) => {
            let F::Int(t) = &**w else { return None };
            Some((&**n, *t, false))
        }
        F::Or(disjuncts) => {
            let [F::Lt(n_lt, zero), F::Ge(n_ge, w)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0)) || n_lt != n_ge {
                return None;
            }
            let F::Int(t) = &**w else { return None };
            Some((&**n_ge, *t, true))
        }
        _ => None,
    }
}

/// Trust: BOUNDS-CORE SELECTION (2026-07-31, round-5 defect [4]) — the SHAPE of a
/// bounds VC's emitted violation, destructured: `(index, len, is_signed_index)`.
///
///   * unsigned index — `Ge(i, len)`
///   * signed index   — `Or([Lt(i, Int 0), Ge(i, len)])`
///
/// Exactly the two forms `v2_build_bounds_assert_vc` builds
/// (`generate/checked_vcs.rs:257-265`: the `Or` is emitted whenever
/// `operand_ty_cow(lhs).is_signed()`). `None` for anything else (fail-closed).
///
/// This is the analogue of [`shift_violation_shape`], which has carried the same
/// signed/unsigned discrimination since round 3 — and the asymmetry is the defect:
/// the shift arm refuses a signed-form body under an unsigned `shift_ty`, while the
/// bounds arm read the `Ge` disjunct straight out of the signed `Or` and minted
/// `SafetyVcKind::Bounds`, whose spec `idx_oob len i` says nothing about the `i < 0`
/// half the VC also states.
pub(super) fn bounds_violation_shape(
    violation: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula, bool)> {
    use trust_types::Formula as F;
    match violation {
        F::Ge(i, len) => Some((&**i, &**len, false)),
        F::Or(disjuncts) => {
            let [F::Lt(i_lt, zero), F::Ge(i_ge, len)] = disjuncts.as_slice() else { return None };
            if !matches!(&**zero, F::Int(0) | F::UInt(0)) || i_lt != i_ge {
                return None;
            }
            Some((&**i_ge, &**len, true))
        }
        _ => None,
    }
}

/// Whether `f` carries, anywhere, the SIGNED-index bounds violation
/// `Or([Lt(i,0), Ge(i,len)])`.
///
/// Trust: THE DROPPED SIGNED DISJUNCT (2026-07-31, round-5 defect [4]). The bounds arm
/// used to locate a `Ge(i, len)` leaf INSIDE the obligation body, and the locator of the
/// day (`obligation_violation_leaf`, deleted in round 6) descended `Or`s — so for a
/// signed index the located leaf
/// was the SECOND DISJUNCT of the emitted violation and the certificate asserted that the
/// modeled condition IS the emitted one when the emitted one is strictly larger. The
/// direction is over-refutation (the VC states MORE than `idx_oob`), so this is a false
/// ADEQUACY statement and a kind gap rather than a live safety hole — but a certificate
/// whose proposition is not the VC's own is exactly what this tier must never mint.
///
/// CLOSED BY DECLINING, and that is a deliberate choice of the two available directions:
///
///   * Modeling it needs a signed `idx_oob_signed` spec constant AND a
///     `SafetyVcKind::Bounds` signedness variant. `SafetyVcKind` lives in
///     `mirsem/mod.rs` and the spec constants in the MirSem spec module — neither is
///     this file, and minting a signedness-LABELLED certificate whose kernel def-eq is
///     still against the unsigned `idx_oob` would be the forgery itself, not a fix. So
///     the capability gap is recorded as one, exactly as `trustir_safety.rs` records it
///     (`idxOobSigned`, `:815-821`), and this lane declines the same shape the sibling
///     lane declines.
///   * The scan is over the whole located BODY rather than the located leaf alone, so a
///     signed violation nested inside a body this arm would otherwise read fails closed
///     too.
///
/// COST: **zero** — 0 of the 68 bounds VCs over `crates/trust-clean/fixtures` peel to a
/// body carrying a signed-index `Or`, so none of the 33 bounds certificates is
/// withdrawn (`obligation_region_tests::mirsem_corpus_census`, whose command
/// [`discarded_negative_disjunct_is_vacuous`]'s doc block states). That zero is a CORPUS
/// fact, not an emitter fact:
/// `generate/checked_vcs.rs:257-265` builds this `Or` for any signed index operand — the
/// regression test drives it end-to-end through `trust_vcgen::generate_vcs`.
fn carries_signed_index_violation(f: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    if bounds_violation_shape(f).is_some_and(|(_, _, signed)| signed) {
        return true;
    }
    match f {
        F::And(v) | F::Or(v) => v.iter().any(carries_signed_index_violation),
        F::Not(a) => carries_signed_index_violation(a),
        F::Implies(a, b) => carries_signed_index_violation(a) || carries_signed_index_violation(b),
        _ => false,
    }
}

/// Trust: SHIFT-CORE SELECTION (2026-07-29) — locate a shift VC's OWN emitted
/// violation by the EMITTER'S CONSTRUCTION, not by a loose scan for a leaf that
/// merely looks like one.
///
/// `v2_shift_violation_formula` returns, VERBATIM,
///
/// ```text
/// And([ input_range_constraint(n, shift_ty),   //  And([Le(Int lo, n), Le(n, Int hi)])
///       invalid ])                             //  Ge(n, Int W)  |  Or([Lt(n,0), Ge(n,W)])
/// ```
///
/// and `v2_build_shift_overflow_vc` then WRAPS that in block definitions, dominating
/// guards, the function's own `preconditions`, and its parameters' type bounds. The
/// wrapper is full of comparisons that share the violation's shape, so a first-match
/// pre-order scan of `vc.formula` for `Ge(var|int, Int)` — what this lane used to do —
/// picks a HYPOTHESIS most of the time. Measured on the 450 committed ladder fixtures:
/// of the 77 emitted `ShiftOverflow` VCs, **68** had more than one candidate leaf and in
/// all 68 the first one was a hypothesis, never the violation. Both directions of that
/// mis-selection were real:
///
///   * FAIL-CLOSED — the extractor's synthesized parameter-domain precondition
///     `And([Ge(bit,0), Le(bit,u64::MAX)])` puts `Ge(bit,0)` ahead of the real core
///     `Ge(bit,8)`; `ShiftWidth::from_bits(0)` then declines and the FUNCTION loses its
///     certificate. That is the whole `bit_field::get_bit` −12 in
///     `reports/2026-07-29-ladder-fixture-refreeze.md` §5. Note the asymmetry that
///     report measured: the mirror spelling `Le(0,bit)` — the SAME proposition, and the
///     one `augment_with_type_bounds` emits — never matched the `F::Ge` probe, so it
///     never declined. The gap was a spelling collision, not a missing arm.
///   * FALSE CERTIFICATE — a precondition `Ge(other, 32)` on a `u8` body (real core
///     `Ge(bit, 8)`) was selected instead and minted a kernel-checked `ShiftOob(W32)`
///     adequacy certificate: a claim about a width the VC does not contain, over a
///     variable the body never shifts by. Pinned by
///     `shift_core_selection_tests::a_precondition_can_never_supply_the_certified_shift_width`.
///
/// The first repair took the violation from the emitter's PAIR — the range constraint's
/// bounds must be integer LITERALS, its constrained term `n` must be the SAME formula as
/// the violation's amount, and the set of DISTINCT violations so located must be a
/// SINGLETON — but ran that match over the WHOLE `vc.formula`, descending through `Not`
/// and `Implies` as well. SHAPE without POSITION is not enough, and this function is
/// therefore no longer the production locator.
///
/// Trust: WHOLE-FORMULA SHIFT FORGERY (2026-07-29, lane A round-3 finding [1]) — the
/// shape match alone was FORGEABLE, MEASURED against `probe_func()` on the tree that
/// preceded this change, with `vc.kind = ShiftOverflow{Shl, u32, u32}` and `pair` the
/// emitter's verbatim `And([And([Le(0,n), Le(n,u32::MAX)]), Ge(n,32)])`:
///
/// ```text
/// Not(pair)                    -> Some(ShiftOob(W32, false))
/// Implies(pair, Bool(true))    -> Some(ShiftOob(W32, false))
/// And([pair, Bool(true)])      -> Some(ShiftOob(W32, false))
/// And([Not(pair), Bool(true)]) -> Some(ShiftOob(W32, false))
/// ```
///
/// The third needs no polarity trick at all: the obligation's own body is the emitter's
/// fail-closed marker `Bool(true)` and the certified core is read out of a HYPOTHESIS
/// conjunct — verbatim the statement of
/// `obligation_region_tests::no_site_certifies_an_obligation_whose_own_body_has_no_modeled_core`,
/// at the one site whose `site_hypotheses()` table has no row. Pinned now by
/// `shift_core_selection_tests::a_shift_hypothesis_conjunct_can_never_supply_the_certified_core`.
///
/// So POSITION governs: the production arm reads [`emitted_obligation_body`], the same
/// region the other seven sites read, and this pair matcher survives ONLY as the
/// INDEPENDENT derivation the region tests cross-check that peel against
/// (`obligation_body_agrees_with_the_shift_emitter_locator`, 77/77 on the ladder). It is
/// `#[cfg(test)]` so a new production caller cannot be added by accident — the same
/// treatment [`find_violation_leaf`] got.
#[cfg(test)]
pub(super) fn emitted_shift_violation_pair_probe(
    formula: &trust_types::Formula,
) -> Option<&trust_types::Formula> {
    use trust_types::Formula as F;

    fn is_int_literal(f: &F) -> bool {
        matches!(f, F::Int(_) | F::UInt(_))
    }

    fn walk<'a>(f: &'a F, out: &mut Vec<&'a F>) {
        if let F::And(conjuncts) = f
            && let [F::And(range), invalid] = conjuncts.as_slice()
            && let [F::Le(lo, n_lo), F::Le(n_hi, hi)] = range.as_slice()
            && is_int_literal(lo)
            && is_int_literal(hi)
            && n_lo == n_hi
            && shift_violation_shape(invalid).is_some_and(|(n, _, _)| n == &**n_lo)
        {
            out.push(invalid);
        }
        match f {
            F::And(v) | F::Or(v) => v.iter().for_each(|x| walk(x, out)),
            F::Not(a) => walk(a, out),
            F::Implies(a, b) => {
                walk(a, out);
                walk(b, out);
            }
            _ => {}
        }
    }

    let mut found: Vec<&F> = Vec::new();
    walk(formula, &mut found);
    let first = *found.first()?;
    // The wrapper duplicates conjuncts (32 of the ladder's 77 shift VCs carry the pair
    // more than once); duplicates of the SAME proposition are fine, two DIFFERENT ones
    // are not.
    found.iter().all(|f| *f == first).then_some(first)
}

/// The base place name of a versioned VC variable — `_6#s3_0` names the same place as
/// `_6`. The staleness machinery stamps `#token` suffixes on both defs and body reads
/// (`version_rename_at` / `version_block_def_at_establish`), so a name comparison that
/// is to recognize "the def OF this local" must be on the base.
fn base_var_name(f: &trust_types::Formula) -> Option<&str> {
    let n = formula_var_name(f)?;
    Some(n.split('#').next().unwrap_or(n))
}

/// Trust: ASSERT-BOUND CORE SELECTION (2026-07-29) — the genuine violation core of an
/// ASSERT-driven safety VC, resolved through the block definition that BINDS the assert's
/// own condition local.
///
/// `v2_build_assert_negation_vc` and the `AssertMessage::DivisionByZero`/
/// `RemainderByZero` arms of `generate_v2_safety_vcs_impl` do NOT emit `Eq(x, MIN)` /
/// `Eq(b, 0)` as their obligation. They emit `v2_assert_failure_formula`, which for the
/// `expected == false` asserts rustc lowers these to is the BARE condition local
/// `Var(c)`; the core reaches the formula only as the RHS of the SSA guard-binding block
/// definition `Eq(Var c, Eq(x, MIN))` / `Eq(Var c, Eq(b, 0))` that
/// `extract_block_definitions_until` emits for `c := (x == MIN)` / `c := (b == 0)`.
/// (`abs_nonneg`'s negation VC is exactly this shape: obligation body `Var("_6", Bool)`;
/// so are `checked_div`/`guarded_div`/`BitArray::get_bit`'s div and rem twins.)
///
/// **ONLY the bare `Var(c)` body is admitted** — see [`assert_bound_or_body_core`]. For
/// `expected == false` the emitted violation IS `c`, so `c`'s binding RHS is literally
/// the obligation and certifying it is exact. A `Not(Var c)` body (`expected == true`,
/// the shape the BOUNDS assert takes) means the violation is `¬RHS`, which is NOT the
/// modeled core — certifying the RHS there would claim the complement of the obligation.
///
/// The previous `find_violation_leaf_through_eq` reached the negation core by descending
/// into the operands of EVERY `Eq` anywhere in `vc.formula` — which is every block
/// definition in the function, plus any `Eq`-shaped precondition. That was the widest
/// hypothesis surface of the seven sites: the located `Eq(Var, Int)` could be any
/// `let m = i32::MIN;` block-def or a `#[requires] y == -128`, and
/// `swidth_of_signed_min` then read the certified width off it.
///
/// This resolves the def by NAME: the base name of `cond` must be the base name of the
/// def's subject, and the def set so located must be a SINGLETON (two definitions of the
/// assert's condition local give no principled choice ⇒ fail closed). The returned RHS
/// still has to satisfy the caller's own shape test, so a def whose RHS is not a modeled
/// core declines.
///
/// Trust: THE DOC IS NOW THE CODE (2026-07-29, lane A finding [4]). A name-matching scan
/// of `vc.formula` does NOT restrict the match to a block definition, and cannot: once
/// `v2_formula_with_path_guards` FLATTENS the wrapped `And` (`generate/safety.rs:1115`),
/// a block definition `Eq(_3, Eq(b,0))` and an `Eq`-shaped PRECONDITION `Eq(_3, Eq(b,0))`
/// are the same tree in the same position. The singleton rule is not a defense when the
/// genuine def is ABSENT: MEASURED on the tree before this change, an `OverflowNeg`
/// assert whose cond local has no defining statement, plus
/// `#[requires] _3 == (y == -128)`, minted `NegationOverflow(W8)` for an **i32**
/// negation over a variable the body never negates.
///
/// So the located binding is now CONFIRMED against the MIR the emitter itself read
/// ([`mir_assert_condition_core`]): the function must contain an `Assert` on this local
/// in a block that DEFINES it, that definition must be the `c := (x == k)` comparison the
/// `expected == false` lowering produces, and the binding found in the formula must be
/// that definition — operand for operand, through the emitter's own
/// `trust_vcgen::operand_to_formula`, modulo the `#token` version stamps
/// `version_block_def_at_establish` adds. A `#[requires]`/`#[ensures]` cannot manufacture
/// a body statement, so the contract surface is closed rather than merely outnumbered.
///
/// COST: zero on the corpus. All 11 assert-route certificates over the 485 committed
/// dumps (7 `DivByZero` + 3 `RemByZero` + 1 `NegationOverflow`, the VCs whose peeled body
/// is a bare `Var`) survive the MIR confirmation unchanged — real rustc-lowered MIR binds
/// the assert's condition local in the assert's own block, which is precisely what this
/// requires and what a crafted `VerifiableFunction` had been able to skip.
fn assert_condition_binding<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
    cond: &trust_types::Formula,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    let want = base_var_name(cond)?;
    // The MIR's own binding of this assert's condition local. No statement binds it ⇒
    // the route the doc describes does not exist for this VC ⇒ fail closed.
    let mir_core = mir_assert_condition_core(func, want)?;
    fn collect<'a>(f: &'a F, want: &str, out: &mut Vec<&'a F>) {
        if let F::Eq(lhs, rhs) = f
            && base_var_name(lhs).is_some_and(|n| n == want)
        {
            out.push(rhs);
            return;
        }
        match f {
            // `And`/`Or` only: a binding under a `Not` is a negated fact and one in an
            // `Implies` antecedent is a hypothesis — neither is a block definition.
            F::And(v) | F::Or(v) => v.iter().for_each(|x| collect(x, want, out)),
            _ => {}
        }
    }
    let mut found: Vec<&F> = Vec::new();
    collect(formula, want, &mut found);
    let first = *found.first()?;
    if !found.iter().all(|f| *f == first) {
        return None; // two DIFFERENT bindings of the condition local ⇒ fail closed
    }
    // … and the one binding the formula carries must BE the MIR's definition.
    formula_agrees_modulo_versions(first, &mir_core).then_some(first)
}

/// Trust: ASSERT-BOUND CORE SELECTION (2026-07-29) — the MIR side of
/// [`assert_condition_binding`]: the comparison the assert's condition local is DEFINED
/// by, lowered exactly as the VC emitter lowers it.
///
/// Requires, all of them, or `None`:
///
///   * a block whose terminator is an `expected == false` `Assert` on the local named
///     `want` — the only lowering that makes a bare `Var(c)` the obligation body
///     (`v2_assert_failure_formula` emits `Not(Var c)` for `expected == true`, which this
///     route does not admit at all),
///   * exactly ONE statement in THAT block assigning it (the region
///     `extract_block_definitions_until` reads; SSA, so a second assignment means the
///     name does not identify a unique definition), and
///   * that statement being the `c := (x == k)` comparison the `expected == false`
///     `DivisionByZero` / `RemainderByZero` / `OverflowNeg` lowering emits.
///
/// Two asserts on the same local in different blocks are admitted only if they resolve
/// to the SAME comparison; otherwise the VC's own assert is ambiguous ⇒ fail closed.
fn mir_assert_condition_core(
    func: &trust_types::VerifiableFunction,
    want: &str,
) -> Option<trust_types::Formula> {
    use trust_types::{BinOp, Formula as F, Operand, Rvalue, Statement, Terminator};
    let names = |p: &trust_types::Place| trust_vcgen::place_to_var_name(func, p) == want;
    let mut found: Vec<F> = Vec::new();
    for block in &func.body.blocks {
        let Terminator::Assert { cond, expected: false, .. } = &block.terminator else {
            continue;
        };
        let (Operand::Copy(p) | Operand::Move(p)) = cond else { continue };
        if !names(p) {
            continue;
        }
        let mut defs = block.stmts.iter().filter_map(|s| match s {
            Statement::Assign { place, rvalue, .. } if names(place) => Some(rvalue),
            _ => None,
        });
        let Some(rvalue) = defs.next() else { return None }; // asserted, never defined
        if defs.next().is_some() {
            return None; // two definitions in the assert's own block ⇒ fail closed
        }
        let Rvalue::BinaryOp(BinOp::Eq, a, b) = rvalue else { return None };
        found.push(F::Eq(
            Box::new(trust_vcgen::operand_to_formula(func, a)),
            Box::new(trust_vcgen::operand_to_formula(func, b)),
        ));
    }
    let first = found.first()?.clone();
    found.iter().all(|f| *f == first).then_some(first)
}

/// Trust: NEGATION SUBJECT (2026-07-31, round-5 defects [1]/[8]) — the
/// `(variable name, MIR type)` of EVERY operand this function's MIR actually negates:
/// the subject each `VcKind::NegationOverflow` producer in `trust-vcgen` takes, and the
/// operand whose `crate::operand_ty` becomes that kind's `ty`.
///
/// The three producers, read off the emitter rather than assumed — a claim about a
/// producer is false if any sibling branch admits the case, so all three are listed and
/// all three are covered by ONE scan. THE DENOMINATOR, with the command (2026-07-31, run
/// in this tree, from `crates/`):
///
/// ```text
/// grep -rn "kind: VcKind::NegationOverflow {" --include='*.rs' trust-vcgen/src   # 9 hits
/// grep -rn "Some(VcKind::NegationOverflow"     --include='*.rs' trust-vcgen/src   # 1 hit
/// ```
///
/// Of those 10: 5 are `#[cfg(test)]` fixtures in `abstract_interp/tests.rs`; 4 are
/// `checked_vcs.rs:109/121` (the assert producer's BV and Int paths) and `:817/836` (the
/// raw producer's two); 1 is `unwrap_panic.rs:1385`, the `abs` `kind_override`. So THREE
/// producers, five construction sites, two subject rules. `cross_check/reference_vcgen.rs:112`
/// pushes a bare KIND into a cross-check list and emits no `VerificationCondition` — the
/// round-4 claim audit left a note at that line saying so, and it is excluded here for
/// that reason, not overlooked.
///
/// | producer | subject |
/// |---|---|
/// | `checked_vcs.rs:775` `v2_build_negation_raw_vc` | the `Rvalue::UnaryOp(Neg, operand)` the statement negates |
/// | `checked_vcs.rs:57` `v2_build_assert_negation_vc` | `v2_find_target_neg_operand(func, target)` — the FIRST `Rvalue::UnaryOp(Neg, ..)` statement of the assert's TARGET block (`block_defs.rs:881-895`) |
/// | `unwrap_panic.rs:1382-1387` (`signed_abs_panic_body`, `:138`) | the FIRST argument of a signed `iN::abs` call |
///
/// The first two are both `Rvalue::UnaryOp(UnOp::Neg, ..)` statements, and the second's
/// operand is a member of the first's set by construction (it is one such statement, in
/// one particular block), so a scan over every `Neg` rvalue in the body covers both
/// WITHOUT keying on the route. That is deliberate: round 4 closed this defect on the
/// trust-ir lane by keying its gate on the assert-condition ROUTE, which left the
/// body-route half re-openable from the API (round-5 defect [8]). The gate here is keyed
/// on the SUBJECT — every negation certificate, by whatever route, must name a variable
/// this MIR negates.
///
/// THE `abs` RECOGNIZER IS A DELIBERATELY NARROWER TWIN. `is_signed_abs_call`
/// (`unwrap_panic.rs:123`) is `pub(super)` inside `trust-vcgen`, so it is re-derived
/// here as `<last `::` segment> == "abs"` plus the same `core::num::` / `std::num::`
/// anchor. The emitter's third condition — a SIGNED-int receiver
/// (`signed_abs_panic_body`, `:141-143`) — is not re-tested here but at the USE site:
/// `SWidth::from_mir` returns `None` for an unsigned width (`mirsem/mod.rs:2408-2410`),
/// so an unsigned subject declines there. `trust-vcgen`'s own `method_tail`
/// additionally strips TRAILING turbofish groups (`alloc_bounds.rs:162-196`), which this
/// twin does not: a path ending in a turbofish therefore matches THERE and not HERE, so
/// the twin's recognized set is a SUBSET of the emitter's and the disagreement direction
/// is over-rejection (a lost certificate), never over-acceptance (a subject the emitter
/// never used).
fn negation_subjects(
    func: &trust_types::VerifiableFunction,
) -> Vec<(String, trust_types::Ty)> {
    use trust_types::{Operand, Rvalue, Statement, Terminator, UnOp};
    fn is_signed_abs_call(callee: &str) -> bool {
        callee.trim().rsplit("::").next() == Some("abs")
            && (callee.contains("core::num::") || callee.contains("std::num::"))
    }
    let mut out: Vec<(String, trust_types::Ty)> = Vec::new();
    let mut push = |operand: &Operand| {
        let (Operand::Copy(p) | Operand::Move(p)) = operand else { return };
        let Some(ty) = trust_vcgen::operand_ty(func, operand) else { return };
        out.push((trust_vcgen::place_to_var_name(func, p), ty));
    };
    for block in &func.body.blocks {
        for stmt in &block.stmts {
            if let Statement::Assign { rvalue: Rvalue::UnaryOp(UnOp::Neg, operand), .. } = stmt {
                push(operand);
            }
        }
        if let Terminator::Call { func: callee, args, target: Some(_), .. } = &block.terminator
            && is_signed_abs_call(callee)
            && let Some(arg) = args.first()
        {
            push(arg);
        }
    }
    out
}

/// Trust: THE ASSERT-NEGATION SUBJECT (2026-07-31, round-6 item F2) — the
/// `(variable name, MIR type)` of the operand the ASSERT-NEGATION emitter takes as ITS
/// subject in this function. The consumer-side twin of `v2_find_target_neg_operand`
/// (`block_defs.rs:881-895`), which `v2_build_assert_negation_vc` reads at
/// `checked_vcs.rs:65` and whose `crate::operand_ty` at `checked_vcs.rs:69` becomes
/// `VcKind::NegationOverflow { ty }`.
///
/// For every block whose terminator is an `expected == false`
/// `Assert { msg: AssertMessage::OverflowNeg, target, .. }` — the sole call site of that
/// producer (`safety.rs:177-178`) and the only assert polarity whose body is the bare
/// `Var(_c)` the assert route resolves — take the FIRST `Rvalue::UnaryOp(UnOp::Neg,
/// operand)` statement of `target`, exactly as `v2_find_target_neg_operand`'s `find_map`
/// does. Collapse to the single `(name, ty)` they all agree on; disagreement, a missing
/// negation, or a non-place operand ⇒ `None`, fail closed.
///
/// PORTED FROM `trustir_safety.rs`, AND IT LAYERS ON THE UNION RATHER THAN REPLACING IT.
/// [`negation_subjects`] is the whole-body union over all THREE producers and is keyed on
/// the SUBJECT, so it runs on every route; this one is strictly narrower — it pins the
/// subject to THIS assert's own target block — and is therefore applied ONLY on the
/// assert route, as an ADDITIONAL conjunct. Replacing the union with it would withdraw
/// real rows: 7 of this lane's 12 corpus negation certificates take the assert route
/// (`mirsem_corpus_census`, `neg=12/12 (assert route 7)`), and the other 5 take the body
/// route, where this function has nothing to say. Both survive the pair — `certs=635`
/// and `neg=12/12` unchanged, re-measured in this tree.
fn assert_negation_subject(
    func: &trust_types::VerifiableFunction,
) -> Option<(String, trust_types::Ty)> {
    use trust_types::{AssertMessage, Operand, Rvalue, Statement, Terminator, UnOp};
    let mut found: Option<(String, trust_types::Ty)> = None;
    for block in &func.body.blocks {
        let Terminator::Assert { expected: false, msg: AssertMessage::OverflowNeg, target, .. } =
            &block.terminator
        else {
            continue;
        };
        let target_block = func.body.blocks.get(target.0)?;
        let operand = target_block.stmts.iter().find_map(|stmt| {
            let Statement::Assign { rvalue, .. } = stmt else { return None };
            match rvalue {
                Rvalue::UnaryOp(UnOp::Neg, operand) => Some(operand),
                _ => None,
            }
        })?;
        let (Operand::Copy(p) | Operand::Move(p)) = operand else { return None };
        let entry =
            (trust_vcgen::place_to_var_name(func, p), trust_vcgen::operand_ty(func, operand)?);
        match &found {
            Some(prev) if *prev != entry => return None, // ambiguous ⇒ fail closed
            _ => found = Some(entry),
        }
    }
    found
}

/// The MIR type of the negation subject named `want` ([`negation_subjects`]).
///
/// `None` — fail closed — when this MIR negates nothing named `want` (the certified
/// variable is not the one the obligation is about) or when two negations of that name
/// disagree on the type (ambiguous ⇒ no principled width).
///
/// Trust: THE `#` STRIP IS ONE-SIDED (2026-07-31, round-6 item F3). `want` is the caller's
/// [`base_var_name`] of a FORMULA variable, so the `#token` version stamp is already off
/// that side. This function used to strip `#` off the MIR side too, and that is the
/// base/segment-boundary hazard `place_to_var_name` closed for `.`/`[`/`*`/`@` reopened
/// for `#`: a MIR local whose name is literally `y#s3_0` would have matched a formula
/// variable spelled `y`, letting a negation of one place authenticate a certificate about
/// another. The MIR side is now compared WHOLE.
///
/// WHY THIS SIDE AND NOT THE EMITTER. The alternative F3 named is to demote `#` at the
/// emitter beside `.`/`[`/`*`/`@` — i.e. add it to `trust_vcgen`'s
/// `PROJECTION_SEGMENT_LEAD` (`trust-vcgen/src/lib.rs:4281`) so a source name containing
/// one demotes to the unique `_<local>` spelling. That is the wider fix and it is NOT
/// available from here: `trust-vcgen` is not this lane's file, and the demotion would
/// change the emitted variable VOCABULARY of every consumer at once (the guard-implied
/// assert augmentation in `prove.rs` spells the same names) rather than one certifier's
/// name comparison. Its cost would also not be zero by construction — it renames a local
/// wherever it fires, where this change only ever REFUSES a match.
///
/// WHAT THE OTHER WOULD HAVE COST, MEASURED rather than argued (2026-07-31, in this tree):
/// `obligation_region_tests::mirsem_corpus_census` tallies every `LocalDecl` source name
/// over the whole fixture corpus and asserts `locals=16827 named=4923 named_with_hash=0`,
/// so the emitter-side demotion would fire on 0 locals of this corpus and cost 0 rows —
/// the same zero this side costs. The choice between them is therefore about BLAST RADIUS
/// and ownership, not about corpus cost, and the direction here is over-rejection either
/// way: a genuine `#` in a MIR place name is minted by nothing in the tree
/// (`generate/path_defs.rs:859`'s `format!("{name}#{tok}")` is the only producer of the
/// character and it stamps FORMULA variables, never `place_to_var_name`'s output), so the
/// whole-name comparison loses no real subject.
pub(super) fn negation_subject_ty(
    func: &trust_types::VerifiableFunction,
    want: &str,
) -> Option<trust_types::Ty> {
    let mut found: Option<trust_types::Ty> = None;
    for (name, ty) in negation_subjects(func) {
        if name != want {
            continue;
        }
        match &found {
            Some(prev) if *prev != ty => return None, // ambiguous ⇒ fail closed
            _ => found = Some(ty),
        }
    }
    found
}

/// Structural equality of two `Formula`s that ignores the `#token` version stamps the
/// staleness machinery puts on place variables (`_6#s3_0` and `_6` name the same place).
/// Used to compare a conjunct of the WRAPPED, version-renamed VC formula against a term
/// freshly lowered from the MIR, which carries bare names.
fn formula_agrees_modulo_versions(a: &trust_types::Formula, b: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    match (a, b) {
        (F::Var(x, sx), F::Var(y, sy)) => {
            sx == sy
                && x.as_str().split('#').next() == y.as_str().split('#').next()
        }
        (F::And(u), F::And(v)) | (F::Or(u), F::Or(v)) => {
            u.len() == v.len()
                && u.iter().zip(v).all(|(x, y)| formula_agrees_modulo_versions(x, y))
        }
        (F::Not(x), F::Not(y)) | (F::Neg(x), F::Neg(y)) => formula_agrees_modulo_versions(x, y),
        (F::Implies(x1, x2), F::Implies(y1, y2))
        | (F::Eq(x1, x2), F::Eq(y1, y2))
        | (F::Lt(x1, x2), F::Lt(y1, y2))
        | (F::Le(x1, x2), F::Le(y1, y2))
        | (F::Gt(x1, x2), F::Gt(y1, y2))
        | (F::Ge(x1, x2), F::Ge(y1, y2))
        | (F::Add(x1, x2), F::Add(y1, y2))
        | (F::Sub(x1, x2), F::Sub(y1, y2))
        | (F::Mul(x1, x2), F::Mul(y1, y2))
        | (F::Div(x1, x2), F::Div(y1, y2))
        | (F::Rem(x1, x2), F::Rem(y1, y2)) => {
            formula_agrees_modulo_versions(x1, y1) && formula_agrees_modulo_versions(x2, y2)
        }
        // Every other shape (literals, bitvector terms, selects, calls, …) carries no
        // version stamp of its own; exact equality is the right test and anything this
        // arm does not recognize compares unequal unless it is literally identical.
        _ => a == b,
    }
}

/// This VC's own violation core: the emitted body itself when the body IS the core
/// ([`locate_violation`]), else — for the `expected == false` ASSERT shape, whose body
/// is the BARE condition local — the core that local is BOUND to
/// ([`assert_condition_binding`]). Both routes are the emitter's own construction; a
/// body outside both declines. The `CoreRoute` says which one fired.
///
/// A `Not(Var c)` body is deliberately NOT admitted: there the violation is the
/// COMPLEMENT of the binding, so the binding is not this obligation.
///
/// Trust: THE BODY ROUTE IS A SHAPE MATCH (2026-07-31, round-6). The first route used
/// to be `obligation_violation_leaf`, which DESCENDED the peeled body looking for the
/// arm's core. That is the round-6 root cause and it is gone: see [`locate_violation`]
/// for the four recipes (`div`, `rem`, `negation` and the bounds arm that shares this
/// helper's discipline) it minted.
fn assert_bound_or_body_core<'a>(
    func: &trust_types::VerifiableFunction,
    formula: &'a trust_types::Formula,
    is_core: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<(&'a trust_types::Formula, CoreRoute)> {
    if let Some((core, _)) = locate_violation(formula, is_core) {
        return Some((core, CoreRoute::Body));
    }
    let cond = emitted_obligation_body(formula)?;
    if formula_var_name(cond).is_none() {
        return None;
    }
    let bound = assert_condition_binding(func, formula, cond)?;
    is_core(bound).then_some((bound, CoreRoute::AssertCondition))
}

/// Kernel-check that the LIVE grounding of `cg.core` (via `clean_ground::ground_prop`)
/// is def-eq, modulo the 3 foundational axioms, to the spec term `spec` (already built
/// over the SAME de-Bruijn refs). This is the bridge check: it certifies the term the
/// reflection pipeline ACTUALLY grounds equals the pinned machine-semantics condition,
/// not a hand-built shape. Returns `true` ONLY on a real modulo-3 kernel def-eq.
pub(super) fn live_ground_def_eq_spec(cg: &CoreGround<'_>, spec: &Expr, binder_count: usize) -> bool {
    let Ok(mut env) = mirsem_safety_env() else {
        return false;
    };
    let Some(grounded) = crate::clean_ground::ground_prop(cg.core, &cg.params) else {
        return false; // the live grounder declined this core ⇒ no cert (fail closed)
    };
    // Kernel-register `theorem … : @Eq Prop grounded spec := Eq.refl Prop grounded`,
    // under `binder_count` Int binders (the operands). It type-checks IFF `grounded`
    // and `spec` are def-eq; then audit the axiom closure ⊆ the 3 axioms.
    let bd = || BinderData::from(BinderInfo::Default);
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let mut statement = Expr::apps(eq, [Expr::prop(), grounded.clone(), spec.clone()]);
    let eq_refl = Expr::const_(Name::from_string("Eq.refl"), vec![Level::succ(Level::zero())]);
    let mut proof = Expr::apps(eq_refl, [Expr::prop(), grounded]);
    for _ in 0..binder_count {
        statement = Expr::pi(bd(), int_ty(), statement);
        proof = Expr::lam(bd(), int_ty(), proof);
    }
    {
        let tc = TypeChecker::new(&env);
        if tc.check_type(&proof, &statement).is_err() {
            return false; // NOT def-eq ⇒ the emitted core is not the spec ⇒ fail closed
        }
    }
    let name = Name::from_string("Trust.MirSem.FormulaAware.bridge");
    if env
        .add_decl(Declaration::Theorem {
            name: name.clone(),
            level_params: vec![],
            type_: statement,
            value: proof,
        })
        .is_err()
    {
        return false;
    }
    matches!(env.axiom_deps(&name), Some(residue) if residue.is_empty())
}

/// Whether an integer operand `Formula` is in the formula-aware fragment — a bare
/// `Var` (mapped to a de-Bruijn binder) OR an integer CONSTANT `Int(k)` (grounded
/// directly to a closed literal by the live `ground_int`, no binder). These are the
/// operand shapes `x + y`, `x + 1`, `1 + x` produce; a nested arithmetic / field /
/// pointer operand is OUTSIDE the fragment ⇒ the caller fails closed.
pub(super) fn operand_in_fragment(t: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    matches!(t, F::Var(_, _) | F::Int(_) | F::UInt(_))
}

/// The two operand `Formula`s of a computed binary sub-term `Add(a,b)` / `Sub(a,b)`,
/// in order — the OVERFLOW-family violation cores carry the operands inside this
/// computed result, not as bare comparison leaves. Each operand may be a `Var` OR an
/// integer constant (`x + 1`); a nested-arithmetic / field operand is OUT of the
/// fragment ⇒ `None` (fail closed).
pub(super) fn binop_operands(
    t: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    match t {
        // `Mul` is included so the formula-aware signed-overflow bridge can extract the
        // operands of a CONSTANT-multiplier mul's LIA `Or([Lt(Mul…),Gt(Mul…)])` core
        // (`ground_int` grounds `F::Mul` to `Int.mul`). A `var*var` mul is NOT emitted as
        // an `F::Mul`-cored disjunction (it is a BV formula), so this never spuriously
        // matches the deferred BV shape.
        F::Add(a, b) | F::Sub(a, b) | F::Mul(a, b)
            if operand_in_fragment(a) && operand_in_fragment(b) =>
        {
            Some((a, b))
        }
        _ => None,
    }
}

/// The term an `input_range_constraint` constrains, with its LOWER bound.
/// `trust_vcgen::range::input_range_constraint` builds VERBATIM
/// `And([Le(Int lo, t), Le(t, Int hi)])` (`range.rs:92-100`) — anything else is not one
/// and returns `None`.
fn range_constraint_parts(
    f: &trust_types::Formula,
) -> Option<(&trust_types::Formula, &trust_types::Formula)> {
    use trust_types::Formula as F;
    let F::And(v) = f else { return None };
    let [F::Le(lo, t_lo), F::Le(t_hi, hi)] = v.as_slice() else { return None };
    let is_lit = |x: &F| matches!(x, F::Int(_) | F::UInt(_));
    (is_lit(lo) && is_lit(hi) && t_lo == t_hi).then(|| (&**t_lo, &**lo))
}

/// Whether some conjunct of `sibs` is an `input_range_constraint` on `term` whose LOWER
/// end is exactly `0` — i.e. the emitter proved `term ≥ 0` alongside the violation, the
/// UNSIGNED operand range.
///
/// The ARITY of `sibs` is deliberately not fixed: a dominating path guard is FLATTENED
/// into the same `And` as the emitter's range/violation group
/// (`v2_formula_with_path_guards`, `generate/safety.rs:1110-1115`), so the group's own
/// conjuncts are siblings of the guards rather than a nested triple.
fn has_nonneg_range_sibling(sibs: &[trust_types::Formula], term: &trust_types::Formula) -> bool {
    use trust_types::Formula as F;
    sibs.iter().any(|s| {
        range_constraint_parts(s)
            .is_some_and(|(t, lo)| t == term && matches!(lo, F::Int(0) | F::UInt(0)))
    })
}

/// Trust: UNSIGNED-OVERFLOW VACUITY (2026-07-31, round-5 defects [5]/[6]; extended to
/// unsigned-MUL in round-6) — whether the disjunct the unsigned-add / unsigned-mul
/// certificate DISCARDS is provably unsatisfiable at every occurrence of the violation.
///
/// The emitter's unsigned-add violation is the two-disjunct
/// `Or([Lt(a+b, 0), Gt(a+b, MAX)])` — `generate/overflow_vc.rs:459-465`, the `else` of
/// the unsigned-`Sub` special case, so it is the shape BOTH the signed and the unsigned
/// non-`Sub` arms build (unsigned MUL included, with `Mul` in place of `Add`); the
/// emitter then wraps it as
/// `And([range(lhs), range(rhs), out_of_range])` at `:467`, which is where the two
/// sibling ranges this check reads come from. The pinned specs
/// `uadd_overflows_uW` / `umul_overflows_uW` model the `Gt` half ONLY. Grounding that
/// half alone certifies LESS than the VC states — a certificate about a strictly weaker
/// proposition, which is the same defect class as certifying a hypothesis. It is sound
/// EXACTLY WHEN the discarded `Lt(a∘b, 0)` half is unsatisfiable under the conjuncts the
/// emitter puts beside the violation: `0 ≤ a` and `0 ≤ b`, its two unsigned operand
/// ranges.
///
/// THIS LANE HAD NO SUCH SIDE CONDITION AT ALL. Before round 5 the unsigned-add arm took
/// the `Gt` leaf out of the `Or` with the since-deleted `obligation_violation_leaf` and
/// certified it, at EVERY uadd row — the honest ones included. The check is therefore not
/// a narrowing of an existing defence; it is the defence, and it is the same one
/// `trustir_safety.rs`'s uadd arm carries.
///
/// Trust: AND THE UNSIGNED-MUL ARM NOW SHARES IT (2026-07-31, round-6). Round 5 left the
/// mul twin descending into the same `Or` with `obligation_violation_leaf` and recorded
/// the gap; round 6 routes both arms through [`unsigned_overflow_over_disjunct`], which
/// shape-matches the `Or` on the COLLAPSED body and calls this universal. That is why
/// the name no longer says `uadd`.
///
/// A REJECTED OCCURRENCE FAILS, IT DOES NOT DROP. The universal ranges over every
/// occurrence [`emitted_obligation_body_located`] visited, and an occurrence with NO
/// sibling list — a RAW disjunct of a mixed path-guard `Or`, or a body that IS the whole
/// formula — FAILS it. That is round-5 defects [5]/[6] stated as code: a path with no
/// vacuity evidence must not be excluded from the quantifier it cannot satisfy. The
/// empty occurrence list fails too (`!occurrences.is_empty()`), so the universal can
/// never pass vacuously.
///
/// COST: zero, at BOTH arms. All 114 unsigned-add and all 51 unsigned-mul certificates
/// over `crates/trust-clean/fixtures` carry the `Or([Lt(a∘b,0), Gt(a∘b,MAX)])` shape and
/// satisfy this condition at every occurrence — the census's `uadd={Or2-Lt0: 114}` and
/// `umul={Or2-Lt0: 51}` lines, re-run in this tree after the round-6 change with
/// `certs=635` unchanged.
///
/// MEASUREMENT COMMAND, stated rather than transcribed (2026-07-31). Every cost number
/// in this file comes from `obligation_region_tests::mirsem_corpus_census`, an
/// `#[ignore]`d harness that walks every committed dump under
/// `crates/trust-clean/fixtures` (2330 files, 2326 of which deserialize into a
/// `VerifiableFunction`), drives `trust_vcgen::generate_vcs` on each, and tallies
/// `safety_vc_is_faithful_formula_aware` per VC and `function_safety_vcs_faithful` per
/// function. It ASSERTS the numbers below, so they cannot rot silently:
///
/// ```text
/// cd crates && RUSTC_BOOTSTRAP=1 cargo test --offline \
///   -p trust-clean --lib -- --ignored --nocapture mirsem_corpus_census
/// ```
///
/// PRE (this tree, before the round-5 fixes), POST-round-5 and POST-round-6 are all
/// IDENTICAL: `funcs=2326 safety=772 certs=635 fn_certified=286`, the same 28-entry
/// per-kind table, `neg=12/12 (assert route 7)`, `bounds=68/33 signed_body=0`,
/// `uadd={Or2-Lt0: 114}`, `umul={Or2-Lt0: 51}`. The round-6 run was taken in this tree
/// with the command above.
///
/// Trust: A FALSE "IN BOTH LANES" CORRECTED (2026-07-31, round-6 item F5). The text that
/// stood here said the unguarded unsigned-mul shape was open "IN BOTH LANES". That was
/// FALSE and it was a transcription, not a measurement: `trustir_safety.rs` has no
/// unsigned-mul arm AT ALL, so the shape cannot be open there. RE-RUN in this tree on
/// 2026-07-31, from `crates/`:
///
/// ```text
/// grep -c 'umul\|UMul\|UnsignedMul' trust-clean/src/trustir_safety.rs   # 0
/// ```
///
/// What is true is narrower and is the reason the gap survived round 5: the mul twin was
/// deferred because the round-5 defect list named uadd only, and a single-lane fix looked
/// like the asymmetry that had already made this defect recur. Round 6's F1 closes it on
/// the lane that HAS the arm; there is no counterpart to match on the other lane, and
/// that is a fact about the arm's existence rather than a matched deferral.
fn discarded_negative_disjunct_is_vacuous(
    occurrences: &[BodyOccurrence<'_>],
    a_op: &trust_types::Formula,
    b_op: &trust_types::Formula,
) -> bool {
    !occurrences.is_empty()
        && occurrences.iter().all(|o| match o.siblings {
            Some(sibs) => {
                has_nonneg_range_sibling(sibs, a_op) && has_nonneg_range_sibling(sibs, b_op)
            }
            // No sibling conjuncts at this occurrence ⇒ no vacuity evidence for THIS
            // path ⇒ FAIL the universal (never drop out of it).
            None => false,
        })
}

/// Trust: THE UNSIGNED-OVERFLOW BODY, SHAPE-MATCHED (2026-07-31, round-6) — the
/// load-bearing `Gt(a∘b, MAX)` disjunct of an unsigned add/mul obligation, taken from
/// the COLLAPSED body rather than searched for inside it.
///
/// Two admitted body shapes, both the emitter's own:
///
///   * `Gt(a∘b, Int MAX)` — the whole obligation IS the overflow comparison, so nothing
///     is discarded and there is nothing to prove vacuous;
///   * `Or([Lt(a∘b, 0), Gt(a∘b, Int MAX)])` — `generate/overflow_vc.rs:459-465`. Both
///     disjuncts must carry the SAME computed term, the discarded half must be against
///     `0`, and that half must be UNSATISFIABLE at every occurrence
///     ([`discarded_negative_disjunct_is_vacuous`]).
///
/// `head` is the arm's own computed-term test (`F::Add` for unsigned add, `F::Mul` for
/// unsigned mul). It is required in ADDITION to [`binop_operands`], which admits
/// `Add`/`Sub`/`Mul` alike: without it an `ArithmeticOverflow{Add, ..}` kind with a
/// `Gt(a-b, MAX)` body passes the shape test and reaches the def-eq bridge, leaving the
/// kernel as the only thing standing between it and a certificate. Whether the bridge
/// alone rejects it was NOT measured here — the point of the head test is that this arm
/// no longer needs that question answered. The direction is over-rejection, and it costs
/// nothing on the corpus: `certs=635` and the whole per-kind table are unchanged with it
/// in place.
///
/// ANY OTHER BODY DECLINES. In particular `Or([Gt(a∘b, MAX), Gt(z, 5)])` — the round-6
/// decoy — is not this shape, so the umul arm now returns `None` on it where it used to
/// descend and certify.
fn unsigned_overflow_over_disjunct<'a>(
    body: &'a trust_types::Formula,
    occurrences: &[BodyOccurrence<'a>],
    head: &dyn Fn(&trust_types::Formula) -> bool,
) -> Option<&'a trust_types::Formula> {
    use trust_types::Formula as F;
    match body {
        F::Gt(lhs, rhs)
            if head(lhs) && binop_operands(lhs).is_some() && matches!(&**rhs, F::Int(_)) =>
        {
            Some(body)
        }
        F::Or(v) => {
            let [F::Lt(under_t, zero_f), gt @ F::Gt(over_t, max_f)] = v.as_slice() else {
                return None;
            };
            if under_t != over_t || !matches!(&**zero_f, F::Int(0) | F::UInt(0)) {
                return None;
            }
            if !head(over_t) || binop_operands(over_t).is_none() || !matches!(&**max_f, F::Int(_)) {
                return None;
            }
            let (a_op, b_op) = binop_operands(over_t)?;
            discarded_negative_disjunct_is_vacuous(occurrences, a_op, b_op).then_some(gt)
        }
        _ => None,
    }
}

/// Trust: MIXED-WIDTH NARROWING (2026-07-30, round-4 defect [2]) — whether an
/// `ArithmeticOverflow` VC whose two `operand_tys` have DIFFERENT widths is entitled to
/// the narrower one, given the operands the located violation core actually carries.
///
/// [`signed_overflow_vc_modeled`] certifies at `min(wa, wb)`. That rule exists for one
/// reason and it is a real one: `generate::type_ranges::int_op_type` (`type_ranges.rs:540-562`) takes
/// the operation's `(width, signed)` from a NON-CONSTANT operand, because
/// `operand_ty` fabricates `Ty::Int { width: 64, signed: true }` for a widthless
/// `ConstValue::Int` (`trust-vcgen/src/lib.rs:1237-1241`) — so `100i8 + x` emits an
/// i8-thresholded body under a kind that reads `(i64, i8)`, and demanding `wa == wb`
/// there would drop a genuine certificate. See the round-3 caveat recorded at
/// [`signed_overflow_vc_modeled`].
///
/// But `min()` makes the `vc.kind`-vs-formula width cross-check VACUOUS in exactly that
/// case: the round-4 verdict's recipe 4 is a kind of `(i64, i8)` with an i8-thresholded
/// body and TWO BARE `Var` operands, which mints `SignedOverflow(Add, W8)` for an
/// obligation nothing narrows. The committed regression tests all use same-width kinds,
/// where `min()` is the identity and the hole is invisible.
///
/// So when the widths differ, require the WIDER POSITION to be an integer LITERAL in the
/// located core — the constant that justifies the narrowing in the first place. The
/// position mapping is the emitter's own. Both producers that build the LIA
/// `Or([Lt(a∘b, MIN), Gt(a∘b, MAX)])` core this arm matches take `operand_tys` and the
/// computed `Add/Sub/Mul` from the SAME `(lhs, rhs)` pair in the SAME order:
/// `generate/overflow_vc.rs:428-434` + `:498` (the direct/checked BinaryOp Int path) and
/// `generate/panic_calls.rs:929-951` + `generate/safety.rs:292` (the
/// `unchecked_{add,sub,mul}` call path). `operand_to_formula` renders `ConstValue::Int(n)`
/// as `F::Int(n)` (`trust-vcgen/src/lib.rs:3253`).
///
/// If some FUTURE producer paired them the other way round, this check would look at the
/// wrong position and REFUSE — over-rejection, never over-acceptance: it can only turn a
/// grant into a decline, because equal widths short-circuit to `true` and the differing-
/// width branch is the only one that can return `false`.
///
/// EQUAL widths return `true` unconditionally — there is nothing to justify, and this
/// must not become a second, silent same-width restriction.
///
/// COST, MEASURED over `crates/trust-clean/fixtures` (2326 functions, 772 safety VCs):
/// **zero**. 49 signed `ArithmeticOverflow` VCs carry differing kind widths; 41 locate a
/// core and in ALL 41 the wider position is an `F::Int` literal, and the remaining 8
/// locate no core at all (they already decline upstream of this check). 0 rows are
/// `wider-position-is-not-a-literal`. Per-VC certificates 635 and functions certified 286,
/// unchanged.
fn mixed_width_narrowing_is_justified(
    kind: &trust_types::VcKind,
    a_op: &trust_types::Formula,
    b_op: &trust_types::Formula,
) -> bool {
    use trust_types::{Formula as F, Ty, VcKind as K};
    let K::ArithmeticOverflow { operand_tys: (a_ty, b_ty), .. } = kind else {
        return false; // not this kind ⇒ the caller has no business here (fail closed)
    };
    let (Ty::Int { width: wa, .. }, Ty::Int { width: wb, .. }) = (a_ty, b_ty) else {
        return false;
    };
    if wa == wb {
        return true; // `min` is the identity; the cross-check already has real content
    }
    let wider = if wa > wb { a_op } else { b_op };
    matches!(wider, F::Int(_) | F::UInt(_))
}

/// The distinct `Var` operand names of a list of operand `Formula`s, in first-
/// appearance order (a constant operand contributes no name — it grounds to a closed
/// literal, not a binder).
pub(super) fn distinct_var_names<'a>(operands: &[&'a trust_types::Formula]) -> Vec<&'a str> {
    let mut names: Vec<&str> = Vec::new();
    for op in operands {
        if let Some(n) = formula_var_name(op) {
            if !names.contains(&n) {
                names.push(n);
            }
        }
    }
    names
}

/// FORMULA-AWARE bridge for an OVERFLOW-family core whose operands appear inside a
/// COMPUTED `Add`/`Sub`/`Eq` sub-term (Lemma 2/5/6/8). Ground the EMITTED `core`
/// through the LIVE `clean_ground::ground_prop` and kernel-check it `is_def_eq`
/// (modulo 3) to `spec(g a, g b)` — where `g a`/`g b` are the operands grounded
/// through the SAME LIVE `ground_int` (a `Var` → its de-Bruijn binder; an integer
/// CONSTANT → its closed literal, NO binder), so the spec is built over the exact
/// operand terms the grounder produces (handling repeated operands `x + x` AND mixed
/// const operands `x + 1` uniformly). `spec_of(&[g_op])` builds the registered
/// per-kind predicate applied to those grounded operands. Returns `true` ONLY on a
/// genuine modulo-3 kernel def-eq; the live grounder declining the core/operand, or a
/// spec/grounder shape mismatch, fails closed.
pub(super) fn overflow_family_live_def_eq(
    core: &trust_types::Formula,
    operands: &[&trust_types::Formula],
    spec_of: &dyn Fn(&[Expr]) -> Expr,
) -> bool {
    // Distinct `Var` operand names → de-Bruijn binders (constants carry no binder).
    let distinct = distinct_var_names(operands);
    let params = debruijn_params(&distinct);
    // Ground each operand POSITION through the SAME live `ground_int`, so the spec is
    // applied to the exact de-Bruijn / literal terms the grounder emits.
    let mut grounded_ops: Vec<Expr> = Vec::with_capacity(operands.len());
    for op in operands {
        match crate::clean_ground::ground_int(op, &params) {
            Some(e) => grounded_ops.push(e),
            None => return false, // the live grounder declined this operand ⇒ fail closed
        }
    }
    let spec = spec_of(&grounded_ops);
    let cg = CoreGround { core, params };
    live_ground_def_eq_spec(&cg, &spec, distinct.len())
}

/// FORMULA-AWARE faithfulness for ONE safety VC: ground the ACTUAL emitted violation
/// core through the LIVE grounder and kernel-check it def-eq to the spec for THAT VC,
/// recovering the width/threshold FROM THE EMITTED FORMULA. Returns the modeled
/// `(kind, AdequacyVerdict)` ONLY when the bridge def-eq holds modulo 3; `None` (fail
/// closed) when the core is outside the formula-aware fragment OR the emitted threshold
/// does not match any modeled spec (e.g. the `1i32<<n` desync — emitted `32 ≤ n`, no
/// def-eq to a 64-width spec).
pub(super) fn safety_vc_is_faithful_formula_aware(
    func: &trust_types::VerifiableFunction,
    vc: &trust_types::VerificationCondition,
) -> Option<(SafetyVcKind, AdequacyVerdict)> {
    use trust_types::{Formula as F, VcKind as K};
    match &vc.kind {
        // BOUNDS (Lemma 3): the emitted core is `Ge(i, len)`. The INDEX is always a
        // variable; the LENGTH is a variable (a SLICE — `Var len`) OR a constant (a
        // FIXED ARRAY — `Int N`). Live-ground the WHOLE core → `Int.le (g len) (g i)`
        // and build the spec `idx_oob (g len) (g i)` over the SAME grounded operands, so
        // the array (`idx_oob (Int.ofNat N) i`) and slice (`idx_oob len i`) cases BOTH
        // certify by the same def-eq. The index binds at bvar 0; a length VARIABLE binds
        // at bvar 1 (so the proof carries 2 binders), a length CONSTANT carries no binder
        // (1 binder — just the index).
        K::IndexOutOfBounds | K::SliceBoundsCheck => {
            // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — read THIS VC's own
            // emitted violation (`v2_build_bounds_assert_vc`'s `Ge(i, len)` /
            // `Or([Lt(i,0), Ge(i,len)])`), not the first `Ge(var, var|int)` anywhere
            // in the wrapped formula. 30 of the corpus's 35 bounds VCs selected a
            // HYPOTHESIS under the old scan — 26 of them the extractor's synthesized
            // `Ge(p, 0)` parameter-domain precondition, which certified `idx_oob 0 p`
            // for functions whose obligation carries no modeled core at all.
            //
            // Trust: THE DROPPED SIGNED DISJUNCT (2026-07-31, round-5 defect [4]). For a
            // SIGNED index the emitted violation is `Or([Lt(i,0), Ge(i,len)])`
            // (`generate/checked_vcs.rs:259`) and the leaf search below descends `Or`s,
            // so it returned the `Ge` disjunct and minted `SafetyVcKind::Bounds` for an
            // obligation strictly larger than `idx_oob len i`. Modeling the signed form
            // needs a spec constant and a kind variant this file does not own, so the
            // shape is DECLINED — the same disposition `trustir_safety.rs` records for
            // it. See [`carries_signed_index_violation`].
            //
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // This arm used to hand its `Ge(i, len)` predicate to the since-deleted
            // `obligation_violation_leaf`, which DESCENDED the peeled body. MEASURED on
            // the tree before this change: a body of `Or([Ge(i, len), Gt(z, 5)])` —
            // strictly weaker than `idx_oob len i` — minted `Some(Bounds)`, and so did
            // every blacklisted decoy wrapped in the same disjunction. The predicate is
            // now asked about the COLLAPSED body ([`locate_violation`]) and that recipe
            // returns `None`, which is what the trust-ir lane has always returned.
            let body = emitted_obligation_body(&vc.formula)?;
            if carries_signed_index_violation(body) {
                return None;
            }
            let (leaf, _) = locate_violation(&vc.formula, &|f| {
                matches!(f, F::Ge(a, b)
                    if formula_var_name(a).is_some()
                        && (formula_var_name(b).is_some() || matches!(&**b, F::Int(_))))
            })?;
            let F::Ge(i_f, len_f) = leaf else { return None };
            let i_name = formula_var_name(i_f)?;
            // Bind the index at bvar 0; the length VARIABLE (if any) at bvar 1.
            let (params, binder_count, len_expr) = match formula_var_name(len_f) {
                Some(len_name) => {
                    let mut m = std::collections::HashMap::new();
                    m.insert(len_name.to_string(), Expr::bvar(1));
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 2usize, Expr::bvar(1))
                }
                None => {
                    let F::Int(n) = &**len_f else { return None };
                    let mut m = std::collections::HashMap::new();
                    m.insert(i_name.to_string(), Expr::bvar(0));
                    (m, 1usize, int_lit(*n))
                }
            };
            let cg = CoreGround { core: leaf, params };
            // spec `idx_oob (g len) i` over the SAME grounded length term + index bvar.
            let spec = Expr::apps(cst(MIRSEM_IDX_OOB), [len_expr, Expr::bvar(0)]);
            live_ground_def_eq_spec(&cg, &spec, binder_count)
                .then_some((SafetyVcKind::Bounds, AdequacyVerdict::ProvenModulo3))
        }
        // DIV / REM by zero (Lemma 4/9): the emitted core is `Eq(b, 0)` (divisor zero).
        // Live-ground → `@Eq Int b (Int.ofNat 0)`; spec `div_by_zero b` / `rem_by_zero b`.
        K::DivisionByZero | K::RemainderByZero => {
            // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the statement-driven
            // `v2_divisor_is_zero_formula` emits `Eq(b, 0)` as the body; the
            // ASSERT-driven twin emits the bare condition local `Var(c)` and binds the
            // core in `Eq(Var c, Eq(b, 0))`, resolved by name. Scanning the WHOLE
            // formula instead certified the assert twin off an unrelated block-def
            // (`Eq(__trust_opaque_scalar_u64, 0)` in `bit_field::BitArray::get_bit`,
            // whose own obligation is `Var("_4", Bool)`).
            //
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // [`assert_bound_or_body_core`]'s first route used to descend the peeled
            // body. MEASURED before this change: a body of `Or([Eq(b, 0), Gt(z, 5)])`
            // minted `Some(DivByZero)` / `Some(RemByZero)` for an obligation that says
            // only `b = 0 ∨ z > 5`. The assert route is untouched — it resolves the bare
            // `Var(_c)` body against the MIR's own binding, which is a position, not a
            // search.
            let is_core = |f: &F| {
                matches!(f, F::Eq(a, b) if formula_var_name(a).is_some() && matches!(&**b, F::Int(0)))
            };
            let (leaf, _) = assert_bound_or_body_core(func, &vc.formula, &is_core)?;
            let F::Eq(b_f, _) = leaf else { return None };
            let b_name = formula_var_name(b_f)?;
            let params = debruijn_params(&[b_name]);
            let cg = CoreGround { core: leaf, params };
            let (spec_name, kind) = if matches!(vc.kind, K::DivisionByZero) {
                (MIRSEM_DIV_BY_ZERO, SafetyVcKind::DivByZero)
            } else {
                (MIRSEM_REM_BY_ZERO, SafetyVcKind::RemByZero)
            };
            let spec = Expr::app(cst(spec_name), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((kind, AdequacyVerdict::ProvenModulo3))
        }
        // SHIFT-amount OOB (Lemma 7): the emitted core is `Ge(n, Int(W))` (unsigned
        // amount) — W is the EMITTED threshold, read from the formula (NOT operand_ty,
        // which fabricates i64 for a const shifted value). Live-ground → `Int.le W n`;
        // spec `shift_amount_oob_W n`. The width is whatever the formula actually says,
        // so the `1i32<<n` emitted `32 ≤ n` certifies at W32 and NEVER mints a 64-cert.
        // A signed shift amount adds the `Lt(n,0)` disjunct (the `Or` core).
        K::ShiftOverflow { shift_ty, .. } => {
            let amount_signed = matches!(shift_ty, trust_types::Ty::Int { signed: true, .. });
            // Trust: SHIFT-CORE SELECTION (2026-07-29) — take THIS VC's OWN emitted
            // violation, rather than the first `Ge(var|int, Int)` leaf anywhere in the
            // WRAPPED formula. That old scan read the hypothesis side — the function's
            // `preconditions`, its parameters' type bounds, the dominating guards — and
            // so both lost real certificates (`bit_field::get_bit`'s `Ge(bit,0)`
            // precondition, −12) and minted false ones (a `Ge(_,32)` precondition
            // certifying `ShiftOob(W32)` on a `u8` body).
            //
            // Trust: lane A round-3 finding [1]/[2] (2026-07-29) — the region is
            // `emitted_obligation_body`, exactly as at the other seven sites. The
            // interim repair matched the emitter's `And([range, invalid])` PAIR but
            // still scanned the whole `vc.formula` for it (descending `Not` and
            // `Implies` too), and shape without position is forgeable: MEASURED,
            // `And([pair, Bool(true)])` — an obligation whose own body is the emitter's
            // fail-closed `Bool(true)` marker — minted `ShiftOob(W32, false)` off the
            // hypothesis conjunct, as did `Not(pair)` and `Implies(pair, Bool(true))`.
            // The peel is also strictly WIDER: `v2_formula_with_path_guards` FLATTENS
            // an `And`-shaped body into the guarded term (`generate/safety.rs:1115`),
            // destroying the 2-element pair, so a shift under a dominating guard emits
            // `And([guard, And([Le,Le]), Ge(n,W)])` — pair `None`, body `Ge(n,W)`. The
            // pair matcher survives as the `#[cfg(test)]` cross-check
            // `emitted_shift_violation_pair_probe`; the two agree on 77/77 ladder rows.
            //
            // The amount `n` is a VARIABLE (the original Lemma-7 shape) or — Trust: M6
            // rung 6 — a CLOSED LITERAL (`x >> 44`'s emitted `Ge(Int(44), Int(64))`,
            // the `ExprMeta::loose_bvar_range`-class constant shift: the core is a
            // CLOSED Prop, its reflection is `Int.le (ofNat W) (ofNat k)`, and the spec
            // is `shift_amount_oob_W k` applied at the literal — the SAME def-eq
            // bridge, zero binders). UNSIGNED amounts only for the literal arm (a
            // signed literal amount would need the `Or` core located at a literal too —
            // not observed in real MIR, fail-closed).
            let core = emitted_obligation_body(&vc.formula)?;
            let (n_f, threshold, signed_form) = shift_violation_shape(core)?;
            // The emitted violation's FORM must agree with the VC's own `shift_ty`: a
            // signed amount emits the `Or([Lt(n,0), Ge(n,W)])` disjunction, an unsigned
            // one the bare `Ge(n,W)`. A disagreement means the located violation is not
            // the one this VcKind describes ⇒ fail closed.
            if signed_form != amount_signed {
                return None;
            }
            // The EMITTED threshold W must be a modeled shift-width literal
            // (`8/16/32/64/128` — the 128-bit value widths ARE in this lane's set).
            //
            // Trust: NO WIDTH CROSS-CHECK HERE — a DELIBERATE, MEASURED omission, and
            // the four OTHER width-from-formula arms do make one (lane A round-3
            // finding [5]). `shift_vc_modeled` reads the width off `operand_ty`, and for
            // a CONSTANT shifted value (`1i32 << bit`) the extractor fabricates i64
            // there, so the kind's width and the emitted threshold disagree on real
            // rows.
            //
            // SCOPE OF THE OMISSION, RE-MEASURED (2026-07-30, round-4 defect [3]) over
            // the LADDER (`fixtures/census-2026-07-06` + `fixtures/census-rung2-2026-07-07`):
            // 77 shift VCs, every one of which locates a `shift_violation_shape`.
            // `(operand_ty width, emitted threshold)`, exhaustively —
            //
            //     agree:    (8,8) 3   (16,16) 3   (32,32) 27   (64,64) 20   (128,128) 12
            //     disagree: (64,8) 3  (64,16) 3   (64,32) 3    (64,128) 3
            //
            // i.e. 12 of 77 disagree. (The previous text's attribution of all twelve to
            // the `bit_field` `<i8|i16|i32|i128 as BitField>::get_bit`/`::set_bit` rows
            // is CARRIED OVER, not re-measured — this pass re-measured the pair census
            // above, not the row identities.) The previous text stopped at the bare
            // "12 of 77"; the DIRECTION matters and is NOT one-sided:
            // 9 rows are KIND-WIDER (64 against 8/16/32) and 3 are KIND-NARROWER
            // (64 against 128, the i128 `BitField` rows). So neither a one-sided
            // `kind_w >= threshold` nor a one-sided `kind_w <= threshold` is available:
            // the first drops the 3 i128 rows, the second drops the other 9, and
            // equality drops all 12 — contradicting `shift_core_selection_tests::
            // bit_field_get_bit_certifies_its_own_shift_width_under_a_ge_spelled_
            // precondition`, which pins the EMITTED threshold as the honest one.
            // (Over the whole `crates/trust-clean/fixtures` tree: 133 shift VCs, of
            // which 12 disagree with the same `(operand_ty width, emitted threshold)`
            // pair distribution. Whether they are literally the same twelve rows was
            // NOT measured — see the CARRIED OVER note above.)
            //
            // Trust: MATCHED DEFERRAL (2026-07-31, round-5 defect [3]). This omission is
            // OPEN IN BOTH CERTIFICATE LANES and is deliberately left open in both, in
            // the same shape, this round: the honest matched deferral the round-5 defect
            // list names as the acceptable outcome for [3], as against an undocumented
            // asymmetry. It was previously documented HERE and not in `trustir_safety.rs`
            // — that asymmetry is what this paragraph closes. Nothing about the omission
            // changed; what changed is that both lanes now say so.
            //
            // WHAT IS AND IS NOT CLAIMED. This is not "the kind and the formula agree";
            // they measurably do not. It is that `operand_ty` is not evidence about the
            // certified width in EITHER direction here, so no sound comparison against
            // it exists — closing the gap needs the EMITTER to record the true shifted
            // width in the `VcKind`, which is a trust-vcgen change and is deliberately
            // NOT attempted from this side. Until then the certified width comes from
            // the emitted threshold and from the region-selected body alone, and the
            // kind cross-check this arm CAN make is signedness, which it makes above.
            let w = ShiftWidth::from_bits(u32::try_from(threshold).ok()?)?;
            // Trust: M6 rung 6 — the CLOSED-LITERAL amount arm (unsigned only).
            if let F::Int(k) = n_f {
                if amount_signed {
                    return None; // literal-amount signed shift — outside the arm.
                }
                let cg = CoreGround { core, params: std::collections::HashMap::new() };
                let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), int_lit(*k));
                return live_ground_def_eq_spec(&cg, &spec, 0).then_some((
                    SafetyVcKind::ShiftOob(w, amount_signed),
                    AdequacyVerdict::ProvenModulo3,
                ));
            }
            let n_name = formula_var_name(n_f)?;
            let params = debruijn_params(&[n_name]);
            let cg = CoreGround { core, params };
            let spec = Expr::app(cst(&shift_amount_oob_name(w, amount_signed)), Expr::bvar(0));
            live_ground_def_eq_spec(&cg, &spec, 1).then_some((
                SafetyVcKind::ShiftOob(w, amount_signed),
                AdequacyVerdict::ProvenModulo3,
            ))
        }
        // ARITHMETIC OVERFLOW / UNDERFLOW (Lemma 2/5/8). The violation core carries a
        // COMPUTED `Add(a,b)`/`Sub(a,b)` sub-term (not bare comparison Vars). We
        // discriminate the three modeled shapes by the EMITTED formula itself —
        // operand signedness from the VC's `operand_tys` only selects WHICH shape to
        // look for; the threshold (hence the certified width) is read FROM THE FORMULA.
        K::ArithmeticOverflow { op, operand_tys: (a_ty, b_ty) } => {
            use trust_types::{BinOp, Ty};
            let (Ty::Int { signed: sa, .. }, Ty::Int { signed: sb, .. }) = (a_ty, b_ty) else {
                return None;
            };
            match op {
                // UNSIGNED-ADD OVERFLOW (Lemma 2): the load-bearing disjunct is
                // `Gt(Add(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or`. Read MAX from the formula → the modeled UWidth; ground the
                // overflow disjunct live and check def-eq to `uadd_overflows_uW (g a) (g b)`.
                BinOp::Add if !sa && !sb => {
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — 9 of the
                    // corpus's 36 unsigned-add VCs read a HYPOTHESIS here. `itoa`'s
                    // `<i16 as Sealed>::write` raises a u8 add whose own violation is
                    // `Gt(_63 + 48, 255)`, and the whole-tree scan took the semantic
                    // guard `Gt(_43 + 2, u64::MAX)` — minting `Overflow(U64)` for an
                    // 8-bit addition, on unmodified real library code.
                    //
                    // Trust: PARTIAL ADEQUACY, MADE A CHECK (2026-07-31, round-5
                    // defects [5]/[6]). The emitted violation is the two-disjunct
                    // `Or([Lt(a+b, 0), Gt(a+b, MAX)])` and `uadd_overflows_uW` models
                    // the `Gt` half only, so the body is now matched as a SHAPE — the
                    // discarded half must be `Lt` over the SAME computed sum against
                    // `0` — and the vacuity of that half is a REQUIRED side condition
                    // over EVERY occurrence of the body
                    // ([`discarded_negative_disjunct_is_vacuous`]). This lane previously
                    // read the `Gt` out of the `Or` with the since-deleted
                    // `obligation_violation_leaf` and certified half the proposition at
                    // every uadd row.
                    //
                    // Trust: THIS ARM IS THE ROUND-6 MODEL (2026-07-31). It was already a
                    // SHAPE MATCH on the collapsed body, so it declined the
                    // `Or([<core>, Gt(z,5)])` decoy that the other six arms minted; F1
                    // copies the discipline outward and the match itself is now the
                    // shared [`unsigned_overflow_over_disjunct`], which the unsigned-MUL
                    // arm calls with `F::Mul` in place of `F::Add`.
                    let (body, occurrences) = emitted_obligation_body_located(&vc.formula)?;
                    let leaf = unsigned_overflow_over_disjunct(body, &occurrences, &|t| {
                        matches!(t, F::Add(_, _))
                    })?;
                    let F::Gt(add_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(add_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // The certified width is read from the FORMULA's threshold; the VC's
                    // own `operand_tys` carries it INDEPENDENTLY. They must agree, exactly
                    // as the shift arm requires the located form's signedness to agree
                    // with `shift_ty`. Without it, MEASURED against `probe_func()`:
                    // `kind = ArithmeticOverflow{Add, (u8,u8)}` with body
                    // `Gt(a+b, 18446744073709551615)` minted `Some(Overflow(W64))` — a
                    // kernel-checked claim that an 8-bit addition is a 64-bit one.
                    // COST: zero. Over the 486 committed dumps the kind width and the
                    // formula width disagree on 0 of the 265 certificates at all four
                    // width-from-formula arms.
                    if overflow_vc_modeled_width(&vc.kind) != Some(w) {
                        return None;
                    }
                    let name = uadd_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((SafetyVcKind::Overflow(w), AdequacyVerdict::ProvenModulo3))
                }
                // SIGNED ADD/SUB/MUL OVERFLOW (Lemma 5): the full out-of-range `Or([Lt(a∘b,
                // MIN), Gt(a∘b, MAX)])`. Read MIN+MAX from the formula → the modeled
                // SWidth (and confirm they agree); ground the whole `Or` live and check
                // def-eq to `s<op>_overflows_iW (g a) (g b)`.
                //
                // MUL is included ADDITIVELY: a CONSTANT-multiplier signed mul (`x * 4`)
                // is emitted by trust-vcgen on the LIA Int-path as the SAME
                // `Or([Lt(Mul(a,b),MIN), Gt(Mul(a,b),MAX)])` disjunction, so it certifies
                // by the identical reflexivity (the spec body just heads `Int.mul`). A
                // `var*var` signed mul is emitted as a BITVECTOR formula instead, which has
                // NO such `Or([Lt(Mul…),Gt(Mul…)])` leaf — `find_violation_leaf` returns
                // `None` below ⇒ this arm declines ⇒ the deferred BV mul fails closed (no
                // false cert; the `mul_*`/`sq_nonneg` corpus stays HONESTLY not-faithful).
                BinOp::Add | BinOp::Sub | BinOp::Mul if *sa && *sb => {
                    let sop = match op {
                        BinOp::Add => SignedOp::Add,
                        BinOp::Sub => SignedOp::Sub,
                        _ => SignedOp::Mul,
                    };
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the corpus shows
                    // 0 disagreements at this site today, but the shape is reachable
                    // from a hypothesis: `#[requires] a + b < -128 || a + b > 127` on an
                    // i32 body mints `SignedOverflow(Add, W8)` (pinned by
                    // `a_precondition_can_never_supply_the_certified_signed_width`).
                    //
                    // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31,
                    // round-6 F1). The predicate below used to be handed to the
                    // since-deleted `obligation_violation_leaf`, which descended the
                    // peeled body — so a NESTED `Or`, `Or([Or([Lt(a+b,MIN),
                    // Gt(a+b,MAX)]), Gt(z,5)])`, had its inner disjunction located and
                    // certified. MEASURED before this change: `Some(SignedOverflow(Add,
                    // W8))` for an obligation stating the disjunction OR `z > 5`. Asking
                    // the SAME predicate about the COLLAPSED body declines it: the outer
                    // `Or` has two disjuncts but its first is not an `Lt`.
                    let (or, _) = locate_violation(&vc.formula, &|f| match f {
                        F::Or(v) if v.len() == 2 => {
                            let lt_min = matches!(&v[0], F::Lt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            let gt_max = matches!(&v[1], F::Gt(l, r)
                                if binop_operands(l).is_some() && matches!(&**r, F::Int(_)));
                            lt_min && gt_max
                        }
                        _ => false,
                    })?;
                    let F::Or(v) = or else { return None };
                    let (F::Lt(under_t, min_f), F::Gt(over_t, max_f)) = (&v[0], &v[1]) else {
                        return None;
                    };
                    // Both disjuncts must reference the SAME computed `a∘b` operands.
                    let (a_op, b_op) = binop_operands(under_t)?;
                    if binop_operands(over_t)? != (a_op, b_op) {
                        return None;
                    }
                    let (F::Int(min), F::Int(max)) = (&**min_f, &**max_f) else { return None };
                    let w = swidth_of_signed_bounds(*min, *max)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // Without it, MEASURED: `kind = ArithmeticOverflow{Add, (i32,i32)}`
                    // with body `Or([Lt(a+b,-128), Gt(a+b,127)])` minted
                    // `Some(SignedOverflow(Add, W8))`. The comparison is against the WHOLE
                    // `(op, width)` pair, so the located disjunction's op is pinned too.
                    //
                    // MEASURED BEFORE APPLIED, because `signed_overflow_vc_modeled` takes
                    // `min(wa, wb)` on purpose (an untyped integer constant operand
                    // defaults to i64, so the real check type is the narrower one):
                    // over the 486 committed dumps this equality holds for all 22 signed
                    // certificates — 0 disagreements — so the `min` rule and the emitted
                    // threshold are already byte-aligned and the check costs no row.
                    if signed_overflow_vc_modeled(&vc.kind) != Some((sop, w)) {
                        return None;
                    }
                    // Trust: MIXED-WIDTH NARROWING (2026-07-30, round-4 defect [2]).
                    // The cross-check above is satisfied BY CONSTRUCTION when the two
                    // kind widths differ, because `signed_overflow_vc_modeled` narrows
                    // to `min(wa, wb)`: a kind of `(i64, i8)` accepts an i8-thresholded
                    // body whatever the body's operands are. The narrowing is only
                    // legitimate for the reason `int_op_type` narrows — one operand is
                    // an untyped integer CONSTANT whose `operand_ty` fabricates i64 —
                    // so require the WIDER position to actually BE that constant.
                    if !mixed_width_narrowing_is_justified(&vc.kind, a_op, b_op) {
                        return None;
                    }
                    let name = signed_overflows_name(sop, w);
                    let ok = overflow_family_live_def_eq(or, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::SignedOverflow(sop, w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-SUB UNDERFLOW (Lemma 8): the single core `Lt(Sub(a,b),
                // Int(0))`. The underflow bound is `0` at EVERY width (the threshold
                // carries no width), and the spec body is width-invariant — so we ground
                // the live core and check def-eq to `usub_underflows_uW (g a) (g b)` for
                // the operand width the VC carries (sound: the def-eq holds at every
                // modeled width; the width only names the per-kind tally bucket).
                BinOp::Sub if !sa && !sb => {
                    let w = usub_underflow_vc_modeled(&vc.kind)?;
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — the width comes
                    // from the VC KIND here, so a hypothesis leaf would not forge the
                    // width; it would forge the OPERANDS, building the spec over a
                    // subtraction the obligation is not about.
                    //
                    // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31,
                    // round-6 F1). MEASURED before this change: a body of
                    // `Or([Lt(a-b, 0), Gt(z, 5)])` minted
                    // `Some(UnsignedSubUnderflow(W8))`. The emitter's own body for this
                    // kind is the bare `Lt(a-b, 0)` — `overflow_vc.rs`'s unsigned-`Sub`
                    // special case, which is the ONE arm that does not build the
                    // two-disjunct `Or` — so requiring the collapsed body to BE it costs
                    // nothing: all 188 corpus certificates keep theirs.
                    let (leaf, _) = locate_violation(&vc.formula, &|f| match f {
                        F::Lt(lhs, rhs) => {
                            matches!(&**lhs, F::Sub(_, _))
                                && binop_operands(lhs).is_some()
                                && matches!(&**rhs, F::Int(0))
                        }
                        _ => false,
                    })?;
                    let F::Lt(sub_t, _) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(sub_t)?;
                    let name = usub_underflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedSubUnderflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                // UNSIGNED-MUL OVERFLOW: the load-bearing disjunct is
                // `Gt(Mul(a,b), Int(MAX))` (MAX = 2^w−1) inside the emitted 2-element
                // `Or([Lt(Mul(a,b),0), Gt(Mul(a,b),MAX)])`. This is EXACTLY the
                // unsigned-ADD shape with `Mul` in place of `Add` — read MAX from the
                // formula → the modeled UWidth; ground the overflow disjunct live and
                // check def-eq to `umul_overflows_uW (g a) (g b)`.
                //
                // MUL is here for the CONSTANT-multiplier LIA emission only: trust-vcgen
                // routes `flag * 32` / `x * 4` (a constant operand, no widening cast) to
                // the Int path where `ground_int` grounds `F::Mul` to `Int.mul`. A
                // `var*var` unsigned mul is emitted as a BITVECTOR formula
                // (`And([a≠0, bvudiv(bvmul(a,b),a)≠b])`) — its body is not this shape at
                // all, so the shape match below returns `None` ⇒ this arm declines ⇒ the
                // deferred BV mul fails closed (no false cert; `wrapping_mul` and every
                // full-range product stay HONESTLY not-faithful). The MODELING here is
                // orthogonal to the DISCHARGE: even a certified-adequate `x*4` VC is
                // discharged only if `x*4 > MAX` refutes under the caller's facts (a
                // full-range `x` leaves it SAT ⇒ undischarged ⇒ SAFETY_GAP, never FF).
                BinOp::Mul if !sa && !sb => {
                    // Trust: OBLIGATION-REGION SELECTION (2026-07-29) — this is also the
                    // gate that keeps the `var*var` BV mul fail-closed: with the whole
                    // tree in scope, a hypothesis `Gt(Mul(a,b), Int MAX)` supplied the
                    // `Gt(Mul..)` leaf the BV obligation does not contain.
                    //
                    // Trust: THE UADD TWIN, FINALLY (2026-07-31, round-6 F1). This arm
                    // was the ONE leaf-under-body population left on this lane: the
                    // emitter's body is the two-disjunct
                    // `Or([Lt(a*b, 0), Gt(a*b, MAX)])` and this arm handed a `Gt(Mul..)`
                    // predicate to the since-deleted `obligation_violation_leaf`, which
                    // descended the `Or` and certified the `Gt` half — the SAME partial
                    // adequacy round 5 closed at unsigned-add and deferred here, plus the
                    // `Or([Gt(a*b, MAX), Gt(z, 5)])` decoy the descent also accepted
                    // (MEASURED: `Some(UnsignedMulOverflow(W8))`). Both close together by
                    // routing through [`unsigned_overflow_over_disjunct`], the unsigned-add
                    // arm's own matcher, with `F::Mul` for `F::Add`. COST: zero — all 51
                    // corpus certificates carry the `Or2-Lt0` shape and satisfy the
                    // vacuity condition, so `certs=635` is unchanged.
                    let (body, occurrences) = emitted_obligation_body_located(&vc.formula)?;
                    let leaf = unsigned_overflow_over_disjunct(body, &occurrences, &|t| {
                        matches!(t, F::Mul(_, _))
                    })?;
                    let F::Gt(mul_t, max_f) = leaf else { return None };
                    let (a_op, b_op) = binop_operands(mul_t)?;
                    let F::Int(max) = &**max_f else { return None };
                    let w = UWidth::from_mir(width_of_unsigned_max(*max)?, false)?;
                    // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]).
                    // Without it, MEASURED: `kind = ArithmeticOverflow{Mul, (u32,u32)}`
                    // with body `Gt(a*b, 255)` minted `Some(UnsignedMulOverflow(W8))`.
                    if umul_overflow_vc_modeled(&vc.kind) != Some(w) {
                        return None;
                    }
                    let name = umul_overflows_name(w);
                    let ok = overflow_family_live_def_eq(leaf, &[a_op, b_op], &|ops| {
                        Expr::apps(cst(&name), [ops[0].clone(), ops[1].clone()])
                    });
                    ok.then_some((
                        SafetyVcKind::UnsignedMulOverflow(w),
                        AdequacyVerdict::ProvenModulo3,
                    ))
                }
                _ => None,
            }
        }
        // NEGATION OVERFLOW (Lemma 6): the core `Eq(Var x, Int(MIN))`. Read MIN from the
        // formula → the modeled SWidth; ground the live core and check def-eq to
        // `neg_overflows_iW (g x)`.
        //
        // Trust: NEGATION-CORE SELECTION (2026-07-29) — two emitter shapes, both taken
        // from the emitter's own construction:
        //
        //   * `v2_build_negation_raw_vc` emits `And([input_range(v), Eq(v, MIN)])`, so
        //     the obligation BODY is the core.
        //   * `v2_build_assert_negation_vc` emits the assert failure — the BARE
        //     condition local `Var(c)` for the `expected == false` `OverflowNeg` assert
        //     rustc lowers `-x` to — and leaves the core as the RHS of the SSA
        //     guard-binding block definition `Eq(Var c, Eq(x, MIN))`, resolved by NAME
        //     through `assert_condition_binding`, singleton-or-nothing.
        //
        // The old `find_violation_leaf_through_eq` reached the second case by descending
        // into the operands of EVERY `Eq` in `vc.formula` — i.e. into every block
        // definition in the function and any `Eq`-shaped precondition. That is deleted,
        // not kept as a fallback: a fallback keeps the forgery lane open.
        K::NegationOverflow { .. } => {
            let is_core = |f: &F| match f {
                F::Eq(lhs, rhs) => formula_var_name(lhs).is_some() && matches!(&**rhs, F::Int(_)),
                _ => false,
            };
            // Trust: THE BODY IS SHAPE-MATCHED, NOT SEARCHED (2026-07-31, round-6 F1).
            // [`assert_bound_or_body_core`]'s body route used to descend the peeled body,
            // so the DECOY `Or([Eq(x, -128), Gt(z, 5)])` — an obligation stating strictly
            // less than `neg_overflows_i8 x` — located the `Eq` and minted
            // `Some(NegationOverflow(W8))`. MEASURED before this change; `None` after.
            let (leaf, route) = assert_bound_or_body_core(func, &vc.formula, &is_core)?;
            let F::Eq(x_f, min_f) = leaf else { return None };
            if formula_var_name(x_f).is_none() {
                return None;
            }
            let F::Int(min) = &**min_f else { return None };
            let w = swidth_of_signed_min(*min)?;
            // Trust: WIDTH CROSS-CHECK (2026-07-29, lane A round-3 finding [5]). The
            // certified width comes from the formula's `MIN` literal; `NegationOverflow`
            // carries the negated type INDEPENDENTLY. Without this check the MIR
            // confirmation is not enough on its own — `mir_assert_condition_core` checks
            // that the assert's condition local is defined by the located COMPARISON, and
            // nothing in that chain looks at the WIDTH. MEASURED, both routes: the body
            // route, `kind = NegationOverflow{i32}` with body `Eq(y,-128)` ->
            // `Some(NegationOverflow(W8))`; and the assert route, a crafted
            // `VerifiableFunction` with an `expected == false` `OverflowNeg` `Assert` on
            // `_3` plus the single defining statement `_3 := (y == -128)`, which satisfies
            // the whole MIR-confirmation chain and still minted `W8` for an i32 negation.
            // Pinned by
            // `obligation_region_tests::the_certified_width_must_agree_with_the_vc_kinds_own_width`.
            if negation_vc_modeled(&vc.kind) != Some(w) {
                return None;
            }
            // Trust: THE CERTIFIED SUBJECT (2026-07-31, round-5 defects [1]/[8]). Every
            // check above authenticates the SHAPE of the located core and the WIDTH the
            // VC's own kind carries — and `vc.kind`'s `ty` describes whatever local the
            // emitter took as its subject, which the two checks above never compare with
            // the variable being certified. MEASURED on the tree before this arm existed,
            // driven end-to-end through `trust_vcgen::generate_vcs`: a dominating
            // `assert!(!(x == i32::MIN))` over a negation of an UNRELATED `y` minted
            // `NegationOverflow(W32)` about `x`, and `y` — the operand actually negated —
            // appeared nowhere in the formula or in the certified proposition. Narrowing
            // `x` to `i8` still minted a 32-BIT certificate about an i8: a type that can
            // never hold −2³¹.
            //
            // Two witnesses exist and were never brought into contact. The fix brings
            // them into contact on BOTH routes, keyed on the SUBJECT rather than on the
            // route (the trust-ir lane's round-4 half was route-keyed, which left it
            // API-reopenable — round-5 defect [8]):
            //
            //   * the certified variable must BE an operand this MIR negates
            //     ([`negation_subjects`], the consumer-side twin of the emitter's three
            //     producers), and
            //   * the certified width must come from `operand_ty` OF THAT VARIABLE, not
            //     from `vc.kind`'s `ty`.
            //
            // COST: zero — all 12 negation certificates over
            // `crates/trust-clean/fixtures` survive. Their bodies, tallied by
            // `obligation_region_tests::mirsem_corpus_census`:
            // 5 are `Eq(v, MIN)` (the raw-`Neg` and `abs` producers) and 7 are the bare
            // condition local `Var(_c, Bool)` — i.e. 7 of the 12 take the ASSERT route,
            // the very route this check authenticates, and all 7 keep their certificate.
            // That 7 is why this gate is keyed on the SUBJECT and not on the route: on
            // this lane the assert route is where the certificates ARE, so a route-keyed
            // gate would have run on 7 honest rows and on the forgery alike, and left the
            // body route — the other 5 — with no subject check at all.
            let subject = base_var_name(x_f)?;
            let subject_ty = negation_subject_ty(func, subject)?;
            let trust_types::Ty::Int { width: sub_w, signed: sub_signed } = &subject_ty else {
                return None;
            };
            if SWidth::from_mir(*sub_w, *sub_signed) != Some(w) {
                return None;
            }
            // Trust: THE ASSERT ROUTE GETS A SECOND, NARROWER SUBJECT CHECK (2026-07-31,
            // round-6 item F2). The union above is keyed on the SUBJECT and therefore
            // runs on every route, which is what makes it API-closed; what it deliberately
            // does NOT do is pin the subject to the assert this VC came from. Any `Neg` in
            // the whole body satisfies it, so on the assert route a function that negates
            // `y` somewhere and asserts `-x`'s overflow elsewhere still agrees with itself.
            // [`assert_negation_subject`] is the trust-ir lane's narrower twin: the FIRST
            // `Neg` of THIS assert's own TARGET block, exactly the operand
            // `v2_find_target_neg_operand` hands the emitter.
            //
            // IT LAYERS, IT DOES NOT REPLACE. Applying it on every route would withdraw
            // the 5 body-route certificates (the raw-`Neg` and `abs` producers, which have
            // no `OverflowNeg` assert at all and would get `None` from it); applying it
            // INSTEAD of the union on the assert route would drop the union's coverage of
            // the 5. The pair is the union AND, on the assert route only, this. COST:
            // zero — `neg=12/12 (assert route 7)` is unchanged, so all 7 assert-route
            // certificates satisfy both.
            if route == CoreRoute::AssertCondition {
                let (asserted_name, asserted_ty) = assert_negation_subject(func)?;
                if asserted_name != subject || asserted_ty != subject_ty {
                    return None;
                }
            }
            let name = neg_overflows_name(w);
            let ok = overflow_family_live_def_eq(leaf, &[x_f], &|ops| {
                Expr::app(cst(&name), ops[0].clone())
            });
            ok.then_some((SafetyVcKind::NegationOverflow(w), AdequacyVerdict::ProvenModulo3))
        }
        _ => None,
    }
}

/// Map an unsigned-overflow MAX threshold literal `2^w − 1` (read from the emitted
/// `Gt(a+b, Int(MAX))` disjunct) to its bit width — the INVERSE of `UWidth::max_value`,
/// so the certified width is recovered FROM THE FORMULA, not from `operand_ty`. `None`
/// (fail closed) for a threshold that is not exactly some modeled `2^w − 1`.
pub(super) fn width_of_unsigned_max(max: i128) -> Option<u32> {
    [8u32, 16, 32, 64].into_iter().find(|&w| (1i128 << w) - 1 == max)
}

/// Map a signed out-of-range `(MIN, MAX)` threshold pair (read from the emitted
/// `Or([Lt(a∘b,MIN), Gt(a∘b,MAX)])`) to its modeled `SWidth` — requiring BOTH that
/// `MIN = −2^(w−1)` AND `MAX = 2^(w−1) − 1` for the SAME `w` (a mismatched pair is a
/// real shape inconsistency ⇒ fail closed, never a spuriously-certified width).
pub(super) fn swidth_of_signed_bounds(min: i128, max: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min && w.max_value() == max {
            return Some(w);
        }
    }
    None
}

/// Map a negation-overflow MIN threshold literal `−2^(w−1)` (read from the emitted
/// `Eq(x, Int(MIN))` core) to its modeled `SWidth`. `None` (fail closed) for a literal
/// that is not exactly some modeled `−2^(w−1)`.
pub(super) fn swidth_of_signed_min(min: i128) -> Option<SWidth> {
    for w in [SWidth::W8, SWidth::W16, SWidth::W32, SWidth::W64] {
        if w.min_value() == min {
            return Some(w);
        }
    }
    None
}

/// Whether a `VcKind` is a SAFETY obligation (a runtime-UB / panic check the §6
/// pipeline must discharge) — as opposed to a postcondition/precondition/contract or
/// a non-safety property (temporal, taint, …). The generalized metric requires EVERY
/// safety VC the emitter raises to classify into a MODELED kind; a safety VC of an
/// unmodeled kind (shift/cast/negation overflow, float div, unreachable, …) makes the
/// function fail closed.
pub(super) fn is_safety_vc_kind(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    matches!(
        kind,
        K::ArithmeticOverflow { .. }
            | K::ShiftOverflow { .. }
            | K::DivisionByZero
            | K::RemainderByZero
            | K::IndexOutOfBounds
            | K::SliceBoundsCheck
            | K::CastOverflow { .. }
            | K::NegationOverflow { .. }
            | K::FloatDivisionByZero
    )
}

/// Public accessor for [`is_safety_vc_kind`] — the scorecard's straight-line
/// fully-faithful SOUNDNESS GATE (`prove::function_safety_vcs_all_discharged`) uses it
/// to select the safety VCs whose precondition-aware discharge it requires.
#[must_use]
pub fn is_safety_vc_kind_pub(kind: &trust_types::VcKind) -> bool {
    is_safety_vc_kind(kind)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-ADD case of a MODELED width Lemma 2
/// certifies (`op == Add`, both operands unsigned with a `u8`/`u16`/`u32`/`u64`
/// width), return that width. `None` for a signed add, a non-Add op (the signed
/// `Div` `MIN/-1` overflow is an `ArithmeticOverflow{op:Div}`), an unmodeled width
/// (`u128`), or mismatched operand widths — those are UNMODELED ⇒ fail-closed.
pub(super) fn overflow_vc_modeled_width(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Add, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be unsigned at the same modeled width.
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-MUL case of a MODELED width
/// (`op == Mul`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width), return
/// that width. `None` for a signed mul (that is the Lemma-5 case), a non-Mul op, an
/// unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. MIRRORS [`overflow_vc_modeled_width`] exactly (Add→Mul), and shares its
/// modeled unsigned width set `{u8,u16,u32,u64}`.
///
/// KIND-level accept is NECESSARY-not-sufficient: the load-bearing gate is the
/// formula-aware def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies
/// ONLY the CONSTANT-multiplier LIA emission (`Gt(Mul(a,b), MAX)`) and DECLINES the
/// `var*var` BV mul shape. So a full-range `u8 * u8` VC is kind-modeled here but fails
/// closed at the bridge (and, separately, at the discharge) — `wrapping_mul` and every
/// unbounded product stay honestly not-faithful.
pub(super) fn umul_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Mul, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed mul is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the UNSIGNED-SUB case of a MODELED width Lemma 8
/// certifies (`op == Sub`, both operands unsigned with a `u8`/`u16`/`u32`/`u64` width),
/// return that width. `None` for a signed sub (that is the Lemma-5 case), a non-Sub op,
/// an unmodeled width (`u128`), or mismatched operand widths — those are UNMODELED ⇒
/// fail-closed. The emitter's unsigned-Sub VC is `ArithmeticOverflow{op:Sub, (u_W,u_W)}`
/// whose violation core is the single underflow disjunct `Lt(Sub(a,b), 0)`.
pub(super) fn usub_underflow_vc_modeled(kind: &trust_types::VcKind) -> Option<UWidth> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op: BinOp::Sub, operand_tys: (a, b) } = kind else {
        return None;
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    if wa != wb {
        return None;
    }
    // BOTH operands must be UNSIGNED at the same modeled width (a signed sub is Lemma 5).
    let wa = UWidth::from_mir(*wa, *sa)?;
    let wb = UWidth::from_mir(*wb, *sb)?;
    (wa == wb).then_some(wa)
}

/// If an `ArithmeticOverflow` VC is the SIGNED-ADD/SUB/MUL case of a MODELED width Lemma
/// 5 certifies (`op ∈ {Add, Sub, Mul}`, both operands signed), return that `(op, width)`.
/// `None` for an unsigned operand, a non-Add/Sub/Mul op (the signed `Div` `MIN/-1`
/// overflow is an `ArithmeticOverflow{op:Div}`), or an unmodeled check width (`i128`) —
/// those are UNMODELED ⇒ fail-closed. NOTE: signed MUL is kind-modeled here, but the
/// load-bearing gate is the formula-aware def-eq bridge, which certifies only the LIA
/// constant-multiplier shape and declines a `var*var` BV mul (fail-closed).
///
/// The MODELED width is the NARROWER (`min`) of the two operand widths — exactly the
/// type the emitter's overflow check is against (`generate.rs::int_op_type` recovers
/// the true type from the NON-constant operand; an untyped integer constant defaults to
/// the widest `i64`, so when the operand widths differ the real check type is the
/// narrower one, and the emitted `±2^(W−1)` threshold is at that width). For genuine
/// same-width arithmetic (`x:i32 + y:i32`) `min` is just that shared width. This keeps
/// the certified width byte-aligned with the emitted threshold (guarded end-to-end by
/// `signed_overflow_vc_shape_matches_trust_vcgen_emission`).
pub(super) fn signed_overflow_vc_modeled(kind: &trust_types::VcKind) -> Option<(SignedOp, SWidth)> {
    use trust_types::{BinOp, Ty, VcKind as K};
    let K::ArithmeticOverflow { op, operand_tys: (a, b) } = kind else {
        return None;
    };
    let sop = match op {
        BinOp::Add => SignedOp::Add,
        BinOp::Sub => SignedOp::Sub,
        // Signed MUL is now a MODELED kind (Lemma 5 spec heads `Int.mul`). This kind-level
        // accept is NECESSARY-not-sufficient: the load-bearing gate is the formula-aware
        // def-eq bridge (`safety_vc_is_faithful_formula_aware`), which certifies ONLY the
        // LIA constant-multiplier emission and DECLINES the `var*var` BV mul shape. So the
        // BV mul VC is kind-modeled here but fails closed at the bridge — the `mul_*`/
        // `sq_nonneg` corpus stays not-faithful (its product is genuinely unbounded).
        BinOp::Mul => SignedOp::Mul,
        // Every other op (Div/Rem/shift/…) is not a Lemma-5 shape.
        _ => return None,
    };
    let (Ty::Int { width: wa, signed: sa }, Ty::Int { width: wb, signed: sb }) = (a, b) else {
        return None;
    };
    // BOTH operands must be signed. The check width is the narrower of the two (the
    // emitter's `int_op_type` recovers it from the non-constant — real-typed — operand).
    if !sa || !sb {
        return None;
    }
    let check_width = (*wa).min(*wb);
    let w = SWidth::from_mir(check_width, true)?;
    Some((sop, w))
}

/// If a `NegationOverflow` VC is on a MODELED signed width Lemma 6 certifies
/// (`i8`/`i16`/`i32`/`i64`), return that width. `None` for an unsigned type (negation
/// of an unsigned value carries no overflow obligation; `is_signed` is false) or an
/// unmodeled width (`i128` — the deferred bitvector case) — those are UNMODELED ⇒
/// fail-closed.
pub(super) fn negation_vc_modeled(kind: &trust_types::VcKind) -> Option<SWidth> {
    use trust_types::{Ty, VcKind as K};
    let K::NegationOverflow { ty } = kind else {
        return None;
    };
    let Ty::Int { width, signed } = ty else {
        return None;
    };
    SWidth::from_mir(*width, *signed)
}

/// If a `ShiftOverflow` VC is on a MODELED value width Lemma 7 certifies, return that
/// `(value width, amount signedness)`. The MODELED width is the SHIFTED VALUE's width
/// (the `n ≥ W` UB threshold is `W` = the value width); the bool is the shift AMOUNT's
/// signedness (a signed amount adds the `n < 0` disjunct). The modeled set is
/// `8/16/32/64/128` — INCLUDING the `i128`/`u128` value widths (the former "128-bit
/// shift VC width" residue: the threshold is the width literal itself, which stays a
/// closed `Int.ofNat` at 128). `None` for a non-integer value type or any other
/// width — those are UNMODELED ⇒ fail-closed.
pub(super) fn shift_vc_modeled(kind: &trust_types::VcKind) -> Option<(ShiftWidth, bool)> {
    use trust_types::{Ty, VcKind as K};
    let K::ShiftOverflow { operand_ty, shift_ty, .. } = kind else {
        return None;
    };
    let Ty::Int { width, .. } = operand_ty else {
        return None;
    };
    // The shifted-VALUE width drives the `n ≥ W` threshold. Map any integer value
    // width (signed OR unsigned) to the modeled W ∈ {8,16,32,64,128} (the ShiftWidth
    // names the THRESHOLD W, not the value's signedness).
    let w = ShiftWidth::from_bits(*width)?;
    let Ty::Int { signed: amount_signed, .. } = shift_ty else {
        return None;
    };
    Some((w, *amount_signed))
}

/// Whether a SAFETY `VcKind` is one MirSem models an adequacy lemma for (unsigned-add
/// overflow ∨ UNSIGNED-SUB underflow ∨ SIGNED add/sub overflow ∨ bounds ∨ div ∨ rem ∨
/// NEGATION overflow ∨ SHIFT-amount OOB). A safety VC outside this set is UNMODELED ⇒
/// the function fails closed in the generalized metric. For `ArithmeticOverflow` the
/// modeled set is the unsigned-add-of-modeled-width case (`overflow_vc_modeled_width`,
/// Lemma 2), the unsigned-SUB-of-modeled-width case (`usub_underflow_vc_modeled`,
/// Lemma 8), the signed add/sub/mul-of-modeled-width case (`signed_overflow_vc_modeled`,
/// Lemma 5), OR the UNSIGNED-MUL-of-modeled-width case (`umul_overflow_vc_modeled`). Both
/// signed AND unsigned MUL are kind-modeled, but the formula-aware bridge certifies only
/// the LIA constant-multiplier shape (`Gt(Mul(a,b), MAX)`) — a `var*var` BV mul declines
/// there (fail-closed), so the `var*var` corpus stays effectively deferred. `DivisionByZero`
/// (Lemma 4) and `RemainderByZero` (Lemma 9) are modeled; `NegationOverflow` of a
/// modeled width (Lemma 6) and `ShiftOverflow` of a modeled value width — INCLUDING
/// 128 (Lemma 7) — are modeled; a `CastOverflow` / `FloatDivisionByZero` / `i128`
/// negation remains UNMODELED.
pub(super) fn safety_vc_kind_is_modeled(kind: &trust_types::VcKind) -> bool {
    use trust_types::VcKind as K;
    match kind {
        K::ArithmeticOverflow { .. } => {
            overflow_vc_modeled_width(kind).is_some()
                || usub_underflow_vc_modeled(kind).is_some()
                || signed_overflow_vc_modeled(kind).is_some()
                || umul_overflow_vc_modeled(kind).is_some()
        }
        K::DivisionByZero | K::RemainderByZero | K::IndexOutOfBounds | K::SliceBoundsCheck => true,
        K::NegationOverflow { .. } => negation_vc_modeled(kind).is_some(),
        K::ShiftOverflow { .. } => shift_vc_modeled(kind).is_some(),
        _ => false,
    }
}

/// THE GENERALIZED SAFETY-VC-FAITHFULNESS HOOK (Goal #4, generalized
/// `safety_vc_faithful` tier). For a reflected function, mint per-kind safety-VC
/// adequacy certificates iff:
///
///   1. the function raises AT LEAST ONE modeled safety VC (overflow ∨ bounds ∨ div),
///      AND
///   2. EVERY safety VC the emitter (`trust_vcgen::generate_vcs`) raises classifies
///      into a MODELED kind (no unmodeled shift/cast/negation/float safety VC), AND
///   3. each modeled kind's reflected VC is PROVEN (modulo 3) def-eq to its pinned
///      machine-semantics condition (`uadd_overflows_uW` / `idx_oob` / `div_by_zero`).
///
/// Fail-closed (`None`): a function with NO modeled safety VC, a function whose
/// emitter raises an UNMODELED safety VC kind, or any modeled kind whose adequacy
/// proof does not kernel-check modulo 3 — never a false witness.
///
/// A `Some` result means: when the §6 pipeline discharges this function's safety VCs,
/// it is refuting EXACTLY the machine condition for EACH — overflow `(2^w−1)<a+b`,
/// bounds `len≤i`, or div-zero `b=0` — the safety discharge is kernel-certified
/// FAITHFUL across all the function's modeled safety obligations, not merely trusted.
#[must_use]
pub fn function_safety_vcs_faithful(
    func: &trust_types::VerifiableFunction,
) -> Option<FunctionSafetyVcCertificates> {
    // Drive the REAL emitter so the classification is over the VCs that ACTUALLY get
    // raised (the same empirical grounding Lemma 2's value rested on).
    let vcs = trust_vcgen::generate_vcs(func);

    // ALL modeled safety-VC kinds are now FORMULA-AWARE: each cert is minted by
    // grounding the ACTUAL emitted `vc.formula` violation core through the LIVE
    // `clean_ground::ground_prop` and kernel-checking it def-eq to the per-kind spec
    // (recovering the width/threshold from the FORMULA, not from `operand_ty`). The
    // OVERFLOW-family cores (unsigned-add OVERFLOW, signed ADD/SUB OVERFLOW, unsigned-SUB
    // UNDERFLOW, NEGATION) carry a COMPUTED `Add`/`Sub`/`Eq` sub-term whose operands the
    // live grounder DOES ground — closing the model→grounder bridge for them too. Dedup
    // by the `SafetyVcKind` the formula-aware certifier returns.
    let mut certs = FunctionSafetyVcCertificates::default();
    let mut bounds_cert: Option<SafetyVcCertificate> = None;
    let mut div_cert: Option<SafetyVcCertificate> = None;
    let mut rem_cert: Option<SafetyVcCertificate> = None;
    let mut shift_certs: Vec<SafetyVcCertificate> = Vec::new();
    for vc in &vcs {
        if !is_safety_vc_kind(&vc.kind) {
            continue; // a postcondition / contract / non-safety property — not our concern
        }
        if !safety_vc_kind_is_modeled(&vc.kind) {
            return None; // an UNMODELED safety VC kind ⇒ fail closed (cannot certify ALL)
        }
        // FORMULA-AWARE certification for EVERY modeled safety VC: ground the REAL
        // emitted core live and kernel-check def-eq to its spec. Fail-closed if this
        // VC's core is outside the formula-aware fragment OR not def-eq to the spec —
        // even though `safety_vc_kind_is_modeled` accepted the VcKind, the live-grounded
        // def-eq is the stricter (and load-bearing) bridge check.
        let (kind, verdict) = safety_vc_is_faithful_formula_aware(func, vc)?;
        match &kind {
            SafetyVcKind::Overflow(_) => {
                if !certs.overflow.iter().any(|c| c.kind == kind) {
                    certs.overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedSubUnderflow(_) => {
                if !certs.usub.iter().any(|c| c.kind == kind) {
                    certs.usub.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::SignedOverflow(_, _) => {
                if !certs.signed_overflow.iter().any(|c| c.kind == kind) {
                    certs.signed_overflow.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::UnsignedMulOverflow(_) => {
                if !certs.umul.iter().any(|c| c.kind == kind) {
                    certs.umul.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::NegationOverflow(_) => {
                if !certs.negation.iter().any(|c| c.kind == kind) {
                    certs.negation.push(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::Bounds => {
                if bounds_cert.is_none() {
                    bounds_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::DivByZero => {
                if div_cert.is_none() {
                    div_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::RemByZero => {
                if rem_cert.is_none() {
                    rem_cert = Some(SafetyVcCertificate { kind, verdict });
                }
            }
            SafetyVcKind::ShiftOob(_, _) => {
                if !shift_certs.iter().any(|c| c.kind == kind) {
                    shift_certs.push(SafetyVcCertificate { kind, verdict });
                }
            }
        }
    }

    certs.bounds = bounds_cert;
    certs.div = div_cert;
    certs.rem = rem_cert;
    certs.shift = shift_certs;

    // Require at least one modeled safety VC (an unmodeled body is not certified).
    if certs.any() { Some(certs) } else { None }
}
