// Kernel certification of the EXHAUSTIVE-ENUM `otherwise -> unreachable` trap:
// the discriminant validity fact `d ∈ {cases}` resolved against the
// `SwitchIntOtherwise` guard `d ∉ {cases}`.
//
// THE ROW THIS CLOSES. a3d's gate (`./scripts/verify.sh` over
// `crates/a3d-kernel`) reports, once per function across at least eight
// functions (`cell_index_1d`, `det3_i128`, `dist_sq_i64`, `insphere_explicit`,
// `insphere_i128`, `lift_sq3`, `octree_node_count`, `orient2d_i128`, ...):
//
// ```text
// [unreach] unreachable code reached @ crates/a3d-kernel/src/lib.rs:NNN
//          (structural-propositional-unsat, 0ms)
// runtime-checked: solver reported Proved without exact kernel/native proof authority
// ```
//
// Every one of those is the `?`/`Try` desugar on `Option`: a two-variant
// `SwitchInt` on `Discriminant(_)` whose `otherwise` arm is a bare
// `Terminator::Unreachable`. `promote_structurally_dead_unreachable`
// (rustc_mir_transform/src/trust_verify.rs) already DECIDES it — the violation is
// propositionally UNSAT — and labels it `Proved` with the solver name
// `structural-propositional-unsat`. But that promotion attaches
// `proof_certificate: None`, so `certify_all` finds no `ProofEvidence::CleanCic`,
// no exact row authority is minted, and the report demotes the row to
// `runtime-checked`. The verdict was right; the CERTIFICATE was missing.
//
// THE FORMULA. Pinned from `trust_vcgen::generate_vcs` on the
// `enum_discriminant_match` shape (`crates/trust-vcgen/src/tests.rs`), whose
// doc-comment states it is "exactly what `trust-mir-extract`'s
// `enum_discriminant_range_preconditions` emits for a match on an enum value":
//
// ```text
// And([And([Not(Eq(Var("_2", Int), Int(0))), Not(Eq(Var("_2", Int), Int(1)))]),
//      Or([Eq(Var("_2", Int), Int(0)), Eq(Var("_2", Int), Int(1))]),
//      Bool(true)])
// ```
//
// `trust_router::constant_folder::formula_is_propositionally_unsat` returns
// `true` on it (that is precisely why the promotion fires) and
// `trust_certify::certify_vc` returned `None` before this lane existed.
//
// WHY EVERY EARLIER LANE DECLINED — a FRAGMENT gap in each, not a search-budget
// one. The conjunct that CARRIES the contradiction is dropped before any rung
// runs:
//  * `certify_disjunctive_contradiction` sends each disjunct to `parse_disjunct`,
//    whose final arm requires `normalize_atom` to yield EXACTLY ONE order atom.
//    `Eq(d, c)` yields TWO (`d ≤ c`, `c ≤ d`), so `let [atom] = …` returns None.
//    That refusal is deliberate and documented at the head of that function
//    ("parse_disjunct rejects discriminant `Eq`-disjuncts").
//  * `certify_linear_int_fragment` drops the `Or` conjunct outright —
//    `normalize_atom` has no `Or` arm — leaving the two disequalities plus the
//    interval `0 ≤ d ≤ 1` that `membership_interval_bounds` derives. MEASURED:
//    that interval-only spelling does not certify either (see
//    `interval_only_spelling_is_not_what_closes_this`), so the derived bounds are
//    not a back door into the arithmetic lanes.
//  * `certify_propositional_closure_contradiction` needs a `Not(And(leaves))`
//    conjunct. Here the negation is DISTRIBUTED (`¬E₀ ∧ ¬E₁`) and no negated
//    conjunction is ever present.
//
// THE FIX is the dual of the propositional-closure lane, using the same
// opaque-`Int`-indicator abstraction that lane already documents and audits:
// `Or.rec` over `(P₀ = 1) ∨ … ∨ (Pₙ = 1)`, each branch closed by applying its own
// `¬(Pᵢ = 1)` hypothesis. One resolution step per disjunct, no theory reasoning,
// and the clean CIC kernel re-checks the term — so the authority comes from a
// machine-checked proof, NOT from the structural solver's say-so.
//
// NOTE ON CODE MOTION: `elide_kernel_certified_checks` is gated to
// `VcKind::ArithmeticOverflow { op: Add|Sub|Mul }`, so a certified
// `VcKind::Unreachable` row elides NOTHING. These certificates change verdicts
// and reports only, never generated code.

use trust_types::{Formula, Sort};

fn d() -> Formula {
    Formula::Var("_2".to_string(), Sort::Int)
}
fn eq(tag: i128) -> Formula {
    Formula::Eq(Box::new(d()), Box::new(Formula::Int(tag)))
}
fn neq(tag: i128) -> Formula {
    Formula::Not(Box::new(eq(tag)))
}
fn member(tags: &[i128]) -> Formula {
    Formula::Or(tags.iter().copied().map(eq).collect())
}

/// The pinned violation: the exhaustive `Option`-discriminant trap. Byte-for-byte
/// the `Formula` `trust_vcgen::generate_vcs` builds for the `otherwise` arm of a
/// fully-covered two-variant `SwitchInt`, `Bool(true)` goal included.
fn exhaustive_option_trap() -> Formula {
    Formula::And(vec![Formula::And(vec![neq(0), neq(1)]), member(&[0, 1]), Formula::Bool(true)])
}

/// The same trap over a three-variant enum (`Ordering`), fully covered.
fn exhaustive_three_variant_trap() -> Formula {
    Formula::And(vec![
        Formula::And(vec![neq(0), neq(1), neq(2)]),
        member(&[0, 1, 2]),
        Formula::Bool(true),
    ])
}

fn certified(violation: &Formula) -> bool {
    matches!(
        trust_certify::certify_violation(violation),
        Some(trust_ir::ProofEvidence::CleanCic { .. })
    )
}

// ---------------------------------------------------------------------------
// POSITIVE — the rows the a3d gate is stuck on.
// ---------------------------------------------------------------------------

/// FALSIFICATION CONTROL. This is the load-bearing assertion: at the parent
/// commit `certify_violation` returns `None` here (measured), and it returns
/// `None` again the moment the `certify_membership_disjunction_resolution` call
/// site is removed from `certify_with_identity_uncached`. Nothing else in the
/// crate reaches this shape.
#[test]
fn exhaustive_option_trap_certifies() {
    assert!(
        certified(&exhaustive_option_trap()),
        "the `?`-desugar exhaustive-enum unreachable trap did not certify"
    );
}

#[test]
fn exhaustive_three_variant_trap_certifies() {
    assert!(
        certified(&exhaustive_three_variant_trap()),
        "the three-variant exhaustive unreachable trap did not certify"
    );
}

/// The COMPILER'S entry point, not the formula-only one. `certify_all` calls
/// `certify_vc` on the `Proved` row `promote_structurally_dead_unreachable`
/// produced, and the exact row authority is minted only from the resulting
/// `CleanCic`. This pins the full identity binding and its replay.
#[test]
fn trap_certifies_through_the_vc_entry_point_and_replays() {
    let vc = trust_types::VerificationCondition {
        kind: trust_types::VcKind::Unreachable,
        function: "a3d_kernel::dist_sq_i64".into(),
        location: trust_types::SourceSpan::default(),
        formula: exhaustive_option_trap(),
        contract_metadata: None,
        obligation: None,
    };
    let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
        trust_certify::certify_vc(&vc)
    else {
        panic!("certify_vc declined the exhaustive-enum unreachable trap");
    };
    assert!(
        trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &vc),
        "the VC-bound certificate did not replay"
    );
}

/// The consumer side must accept what the producer minted: `recheck_cleancic`
/// independently REGENERATES the certificate from the violation and compares
/// bytes, so this also pins the lane's determinism (indicator numbering, the
/// negation-hypothesis order, and the branch order of the `Or.rec` tree).
#[test]
fn certificates_replay_through_recheck() {
    for (name, violation) in [
        ("option_trap", exhaustive_option_trap()),
        ("three_variant_trap", exhaustive_three_variant_trap()),
    ] {
        let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
            trust_certify::certify_violation(&violation)
        else {
            panic!("{name}: producer declined");
        };
        assert!(
            trust_certify::recheck_cleancic(&term, &context, &lineage, &violation),
            "{name}: consumer re-check rejected the producer's own certificate"
        );
    }
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROLS — every one is SATISFIABLE and must NOT certify.
//
// The first is the one that matters: a genuinely REACHABLE `unreachable` is real
// UB, and certifying it dead would be a false proof blessed by the verifier.
// ---------------------------------------------------------------------------

/// A three-variant enum with only two arms covered: tag 2 REACHES the trap. This
/// is a genuinely reachable `unreachable_unchecked` — the exact false proof this
/// lane must never mint. `_2 = 2` is a model.
#[test]
fn partial_match_leaves_the_trap_reachable_and_declines() {
    let violation = Formula::And(vec![
        Formula::And(vec![neq(0), neq(1)]),
        member(&[0, 1, 2]),
        Formula::Bool(true),
    ]);
    assert!(
        !certified(&violation),
        "REACHABLE unreachable (uncovered tag 2) was certified dead — a false proof of UB"
    );
}

/// No membership fact at all (a bare `Unreachable` with only the otherwise
/// guard): every `_2` outside {0,1} is a model.
#[test]
fn missing_membership_fact_declines() {
    let violation = Formula::And(vec![neq(0), neq(1), Formula::Bool(true)]);
    assert!(!certified(&violation), "a trap with no validity fact must not certify");
}

/// The membership fact ranges over a DIFFERENT variable than the guard negates.
/// Nothing connects them; `_2 ∈ {0,1}` with `_9 ∉ {0,1}` is satisfiable.
#[test]
fn membership_over_a_different_variable_declines() {
    let other = |tag: i128| {
        Formula::Not(Box::new(Formula::Eq(
            Box::new(Formula::Var("_9".to_string(), Sort::Int)),
            Box::new(Formula::Int(tag)),
        )))
    };
    let violation = Formula::And(vec![
        Formula::And(vec![other(0), other(1)]),
        member(&[0, 1]),
        Formula::Bool(true),
    ]);
    assert!(
        !certified(&violation),
        "a membership fact about a different variable must not close the guard"
    );
}

/// A NEAR-MISS constant: the guard excludes {0, 2} while the enum's tags are
/// {0, 1}. `_2 = 1` is a model. Pins that the presence test is exact structural
/// equality and cannot pair a disjunct with a different unit.
#[test]
fn near_miss_tag_declines() {
    let violation = Formula::And(vec![
        Formula::And(vec![neq(0), neq(2)]),
        member(&[0, 1]),
        Formula::Bool(true),
    ]);
    assert!(!certified(&violation), "a near-miss excluded tag must not close the disjunction");
}

/// One tag ASSERTED rather than negated. `Or([E₀,E₁]) ∧ ¬E₀ ∧ E₁` is satisfied by
/// `_2 = 1`; the lane must not read a positive unit as a negative one.
#[test]
fn asserted_tag_instead_of_negated_declines() {
    let violation = Formula::And(vec![member(&[0, 1]), neq(0), eq(1), Formula::Bool(true)]);
    assert!(!certified(&violation), "a positively asserted tag must not close the disjunction");
}

/// The negations present but the disjunction WEAKENED to one extra unrelated
/// tag on a second variable: still satisfiable, still declines. Guards against a
/// "some disjunct matched" (rather than "every disjunct matched") gate.
#[test]
fn one_unmatched_disjunct_declines() {
    let foreign =
        Formula::Eq(Box::new(Formula::Var("_9".to_string(), Sort::Int)), Box::new(Formula::Int(7)));
    let violation = Formula::And(vec![
        Formula::Or(vec![eq(0), eq(1), foreign]),
        neq(0),
        neq(1),
        Formula::Bool(true),
    ]);
    assert!(
        !certified(&violation),
        "a disjunction with an unmatched disjunct must not certify (partial cover)"
    );
}

/// EXHAUSTIVE-MODEL ORACLE over the whole family: every membership set `M` and
/// every excluded set `X` drawn from the tags `{0,1,2}`, in both the flat and the
/// vcgen-nested conjunct spelling. The violation is SAT exactly when `M \ X` is
/// non-empty (that witness value satisfies the membership and every exclusion),
/// and the oracle enumerates the whole integer domain to say so rather than
/// asserting it. EVERY satisfiable instance must decline; every unsatisfiable one
/// is expected to certify, which also pins that the lane is not fixture-keyed to
/// the two tag sets above.
#[test]
fn exhaustive_model_oracle_over_the_membership_family() {
    // Domain covers every tag plus values outside the tag set, so a formula with
    // no membership constraint is correctly seen as SAT.
    let domain: Vec<i128> = (-2..=5).collect();
    let subsets: Vec<Vec<i128>> = (0u8..8)
        .map(|mask| (0i128..3).filter(|t| mask & (1 << t) != 0).collect::<Vec<_>>())
        .collect();

    let mut sat_declined = 0usize;
    let mut unsat_certified = 0usize;
    for membership in &subsets {
        if membership.is_empty() {
            continue; // an empty `Or` is not a shape vcgen emits.
        }
        for excluded in &subsets {
            for nested in [false, true] {
                let negs: Vec<Formula> = excluded.iter().copied().map(neq).collect();
                let mut parts = vec![member(membership)];
                if nested {
                    if !negs.is_empty() {
                        parts.insert(0, Formula::And(negs));
                    }
                } else {
                    parts.extend(negs);
                }
                parts.push(Formula::Bool(true));
                let violation = Formula::And(parts);

                // The oracle: is there an integer making every conjunct true?
                let sat = domain
                    .iter()
                    .any(|v| membership.contains(v) && !excluded.iter().any(|x| x == v));
                let cert = certified(&violation);
                if sat {
                    assert!(
                        !cert,
                        "SATISFIABLE instance certified (M={membership:?} X={excluded:?} \
                         nested={nested}) — a false proof: {violation:?}"
                    );
                    sat_declined += 1;
                } else {
                    assert!(
                        cert,
                        "UNSAT instance declined (M={membership:?} X={excluded:?} \
                         nested={nested}) — the lane is fixture-keyed: {violation:?}"
                    );
                    unsat_certified += 1;
                }
            }
        }
    }
    // Non-vacuity: the oracle must actually have exercised both directions.
    assert!(sat_declined >= 20, "oracle covered too few satisfiable instances: {sat_declined}");
    assert!(unsat_certified >= 20, "oracle covered too few UNSAT instances: {unsat_certified}");
}

// ---------------------------------------------------------------------------
// The FRAGMENT-GAP claim, measured rather than asserted.
// ---------------------------------------------------------------------------

/// The interval `0 ≤ _2 ≤ 1` that `membership_interval_bounds` derives from the
/// `Or`, WITHOUT the `Or` itself, against the same two disequalities. It is UNSAT
/// over ℤ, and it does not certify — which is why the contradiction had to be
/// closed on the disjunction itself and not left to the linear-Int lanes. (It is
/// also why `formula_is_propositionally_unsat` returns `false` for this
/// spelling: there is no `Or` conjunct to resolve.)
#[test]
fn interval_only_spelling_is_not_what_closes_this() {
    let violation = Formula::And(vec![
        Formula::Le(Box::new(Formula::Int(0)), Box::new(d())),
        Formula::Le(Box::new(d()), Box::new(Formula::Int(1))),
        neq(0),
        neq(1),
    ]);
    assert!(
        !certified(&violation),
        "the derived-interval spelling certified; the fragment-gap analysis in this file's \
         banner would then be wrong and must be rewritten"
    );
}

// The lock-step against the compiler's own `structural-propositional-unsat`
// recognizer, and the end-to-end run through `trust_vcgen::generate_vcs`, live in
// `crates/trust-vcgen/tests/exhaustive_unreachable_certifies.rs` — that crate
// already dev-depends on both `trust-router` and `trust-certify`, so the two
// deciders can be compared in one process without widening this crate's
// dependency surface.
