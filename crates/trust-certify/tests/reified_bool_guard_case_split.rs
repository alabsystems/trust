// Kernel certification of the CLAMP-THEN-GUARD panic-freedom violations whose
// branch condition is REIFIED into a `Bool`-sorted temporary.
//
// The formulas below are the EXACT formulas stage2 `trustc` at 6819d5840 hands
// `trust_certify::certify_vc` for
// `tests/trust-falsification/proved/contract_panic_annotated.rs`, captured with
//
// ```text
// TRUST_ASSERT_DEBUG=1 AY_CERT_DUMP=1 trustc --edition 2021 --crate-type lib \
//   --emit=metadata -Cpanic=abort -Ztrust-policy=certify \
//   tests/trust-falsification/proved/contract_panic_annotated.rs -o /dev/null
// ```
//
// which prints, in order,
//
// ```text
// [ASSERT_REFUTE] block=BlockId(5) grounded=true pinned=3 free=["_5#s3_0", "i"]
// [ASSERT_PROVE] PROVED Assertion { .. }          x2   (one per split disjunct)
// [ASSERT_PROVE] discharging whole-function panic-freedom @ .. slot_index
// [CERTDUMP] <implication_pair_residual()>
// [CERTDUMP] <disjunct_split_residual()>
// ```
//
// `disjunct_split_residual` is the WHOLE-FUNCTION PANIC-FREEDOM residual: with
// `split_path_feasibility_disjuncts` (32bb80cb22) the refutation lane proves one
// candidate per path, so `refute_full_assert_obligations`' grounding rewrite
// installs `Or([f_arm0, f_arm1])` as the catch-all's formula. It is the row the
// report calls `[assert] runtime-checked … reported Proved without exact
// kernel/native proof authority` — the diagnostic's span is the whole function
// (`43:1`–`49:1`), which is the panic-freedom aggregate's span and the only span
// the grounding rewrite ever writes to. So — exactly as for
// `wrapping_chain_commute` — the ONLY thing standing between the fixture and
// `rc=0` is whether it certifies (see `convert_result`: a `Proved` without a
// row-bound kernel authority token maps to `Unknown`).
//
// BOTH formulas are UNSAT, ay proves both, and before the reified-`Bool` guard
// lane NEITHER certified: the `Ite` guard `Not(Var("_3", Bool))` has no
// `ite_split_order_nonneg` arm, so `parse_ite_definition` dropped the definition
// and `IteCaseSplitPlan::build` declined with `ite_definitions == 0`, while the
// implication pair is outside every fragment in the crate. That is the same
// FRAGMENT gap as the `collect_term_vars` `Ite` hole, one indirection deeper.

use trust_types::{Formula, Sort};

fn v(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}
fn b(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Bool)
}
fn i(n: i128) -> Formula {
    Formula::Int(n)
}
fn eq(a: Formula, c: Formula) -> Formula {
    Formula::Eq(Box::new(a), Box::new(c))
}
fn lt(a: Formula, c: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(c))
}
fn le(a: Formula, c: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(c))
}
fn ge(a: Formula, c: Formula) -> Formula {
    Formula::Ge(Box::new(a), Box::new(c))
}
fn not(a: Formula) -> Formula {
    Formula::Not(Box::new(a))
}
fn implies(a: Formula, c: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(c))
}
fn ite(c: Formula, t: Formula, e: Formula) -> Formula {
    Formula::Ite(Box::new(c), Box::new(t), Box::new(e))
}
fn and(xs: Vec<Formula>) -> Formula {
    Formula::And(xs)
}
fn or(xs: Vec<Formula>) -> Formula {
    Formula::Or(xs)
}

/// `usize`'s type range on the fixture's target.
const U64MAX: i128 = 18446744073709551615;
/// The clamp temporary, spelled exactly as vcgen names its switch merge.
const K: &str = "k#s1_0_s2_0";

fn i_range() -> Formula {
    and(vec![ge(v("i"), i(0)), le(v("i"), i(U64MAX))])
}

/// The two switch-arm path conditions of `if i < 8`, in emission order.
fn arm_paths() -> [Formula; 2] {
    [not(lt(v("i"), i(8))), lt(v("i"), i(8))]
}

// ---------------------------------------------------------------------------
// THE GROUNDED PANIC-FREEDOM RESIDUAL — `Or` of the two per-path candidates.
//
// `guard_atom` is the reified definition of `_3` and `else_value` the value the
// clamp writes when `_3` is FALSE, so the mutants below can perturb exactly one
// of the two facts the refutation rests on; `with_definition` drops the
// reification entirely.
// ---------------------------------------------------------------------------

fn disjunct_split_residual(
    guard_atom: Formula,
    else_value: Formula,
    with_definition: bool,
) -> Formula {
    let disjunct = |path: Formula| {
        let mut body =
            vec![eq(v("_5"), v(K)), eq(v(K), ite(not(b("_3")), else_value.clone(), v("i")))];
        if with_definition {
            body.push(eq(b("_3"), guard_atom.clone()));
        }
        body.push(and(vec![path, ge(v("_5"), i(8)), Formula::Bool(true)]));
        and(vec![i_range(), and(body)])
    };
    let [arm0, arm1] = arm_paths();
    or(vec![disjunct(arm0), disjunct(arm1)])
}

/// The whole-function panic-freedom residual of `slot_index`, byte-for-byte.
fn grounded_residual() -> Formula {
    disjunct_split_residual(lt(v("i"), i(8)), i(7), true)
}

// ---------------------------------------------------------------------------
// THE SECOND `certify_vc` CALL of the same run — the per-arm block context in
// its IMPLICATION-PAIR spelling. Unchanged byte-for-byte between the 88b99d6812
// snapshot and 6819d5840, so it pins the other derivation of the lane.
// ---------------------------------------------------------------------------

fn implication_pair_context(
    guard_atom: Formula,
    else_value: Formula,
    with_definition: bool,
) -> Formula {
    let mut parts = Vec::new();
    if with_definition {
        parts.push(eq(b("_3"), guard_atom));
    }
    parts.extend(vec![
        and(vec![
            implies(not(b("_3")), eq(v(K), else_value)),
            implies(not(not(b("_3"))), eq(v(K), v("i"))),
        ]),
        eq(v("_5"), v(K)),
        eq(b("_4"), ge(v("_5"), i(8))),
        Formula::Bool(true),
    ]);
    and(parts)
}

fn implication_pair_residual(
    guard_atom: Formula,
    else_value: Formula,
    with_definition: bool,
) -> Formula {
    let arm = |path: Formula| {
        and(vec![
            path,
            ge(v("_5"), i(8)),
            i_range(),
            implication_pair_context(guard_atom.clone(), else_value.clone(), with_definition),
        ])
    };
    let [arm0, arm1] = arm_paths();
    and(vec![i_range(), and(vec![Formula::Bool(true), or(vec![arm(arm0), arm(arm1)])])])
}

fn implication_pair_form() -> Formula {
    implication_pair_residual(lt(v("i"), i(8)), i(7), true)
}

/// The PRE-SPLIT spelling of the residual — one candidate carrying
/// `Or([arm0, arm1])` rather than two candidates — which is what stage2 emitted
/// at the 88b99d6812 snapshot, before `split_path_feasibility_disjuncts`. Kept
/// so the lane is pinned against both shapes of the same body and a future
/// un-split does not silently reopen the fixture.
fn combined_ite_restatement() -> Formula {
    let [arm0, arm1] = arm_paths();
    and(vec![
        i_range(),
        and(vec![
            eq(v("_5"), v(K)),
            eq(v(K), ite(not(b("_3")), i(7), v("i"))),
            eq(b("_3"), lt(v("i"), i(8))),
            or(vec![
                and(vec![arm0, ge(v("_5"), i(8)), Formula::Bool(true)]),
                and(vec![arm1, ge(v("_5"), i(8)), Formula::Bool(true)]),
            ]),
        ]),
    ])
}

fn certified(f: &Formula) -> bool {
    matches!(trust_certify::certify_violation(f), Some(trust_ir::ProofEvidence::CleanCic { .. }))
}

// ---------------------------------------------------------------------------
// The formulas are BYTE-IDENTICAL to what stage2 `trustc` hands the certifier.
// If vcgen's block model or the disjunct split ever changes shape this test
// fails FIRST, so the certification tests below cannot silently start proving
// something the compiler no longer asks.
// ---------------------------------------------------------------------------

#[test]
fn formulas_match_the_compiler_dump() {
    // Both captured from stage2 `trustc` at 6819d5840.
    let expected: [&str; 2] = [
        r#"And([And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Bool(true), Or([And([Not(Lt(Var("i", Int), Int(8))), Ge(Var("_5", Int), Int(8)), And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Eq(Var("_3", Bool), Lt(Var("i", Int), Int(8))), And([Implies(Not(Var("_3", Bool)), Eq(Var("k#s1_0_s2_0", Int), Int(7))), Implies(Not(Not(Var("_3", Bool))), Eq(Var("k#s1_0_s2_0", Int), Var("i", Int)))]), Eq(Var("_5", Int), Var("k#s1_0_s2_0", Int)), Eq(Var("_4", Bool), Ge(Var("_5", Int), Int(8))), Bool(true)])]), And([Lt(Var("i", Int), Int(8)), Ge(Var("_5", Int), Int(8)), And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Eq(Var("_3", Bool), Lt(Var("i", Int), Int(8))), And([Implies(Not(Var("_3", Bool)), Eq(Var("k#s1_0_s2_0", Int), Int(7))), Implies(Not(Not(Var("_3", Bool))), Eq(Var("k#s1_0_s2_0", Int), Var("i", Int)))]), Eq(Var("_5", Int), Var("k#s1_0_s2_0", Int)), Eq(Var("_4", Bool), Ge(Var("_5", Int), Int(8))), Bool(true)])])])])])"#,
        r#"Or([And([And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Eq(Var("_5", Int), Var("k#s1_0_s2_0", Int)), Eq(Var("k#s1_0_s2_0", Int), Ite(Not(Var("_3", Bool)), Int(7), Var("i", Int))), Eq(Var("_3", Bool), Lt(Var("i", Int), Int(8))), And([Not(Lt(Var("i", Int), Int(8))), Ge(Var("_5", Int), Int(8)), Bool(true)])])]), And([And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Eq(Var("_5", Int), Var("k#s1_0_s2_0", Int)), Eq(Var("k#s1_0_s2_0", Int), Ite(Not(Var("_3", Bool)), Int(7), Var("i", Int))), Eq(Var("_3", Bool), Lt(Var("i", Int), Int(8))), And([Lt(Var("i", Int), Int(8)), Ge(Var("_5", Int), Int(8)), Bool(true)])])])])"#,
    ];
    let actual = [format!("{:?}", implication_pair_form()), format!("{:?}", grounded_residual())];
    for (index, (got, want)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(got, want, "formula {index} differs from the 6819d5840 dump");
    }

    // Captured from the standalone stage2 snapshot at 88b99d6812, before
    // `split_path_feasibility_disjuncts` split the candidate per path.
    assert_eq!(
        format!("{:?}", combined_ite_restatement()),
        r#"And([And([Ge(Var("i", Int), Int(0)), Le(Var("i", Int), Int(18446744073709551615))]), And([Eq(Var("_5", Int), Var("k#s1_0_s2_0", Int)), Eq(Var("k#s1_0_s2_0", Int), Ite(Not(Var("_3", Bool)), Int(7), Var("i", Int))), Eq(Var("_3", Bool), Lt(Var("i", Int), Int(8))), Or([And([Not(Lt(Var("i", Int), Int(8))), Ge(Var("_5", Int), Int(8)), Bool(true)]), And([Lt(Var("i", Int), Int(8)), Ge(Var("_5", Int), Int(8)), Bool(true)])])])])"#,
        "the pre-split spelling differs from the 88b99d6812 dump",
    );
}

// ---------------------------------------------------------------------------
// FALSIFICATION CONTROLS. Every one of these fails without the reified-`Bool`
// guard lane: measured `certified = false` for all three formulas at HEAD
// 6819d58406 before it.
// ---------------------------------------------------------------------------

#[test]
fn grounded_residual_certifies() {
    assert!(
        certified(&grounded_residual()),
        "the grounded panic-freedom residual of slot_index did not certify"
    );
}

#[test]
fn implication_pair_form_certifies() {
    assert!(
        certified(&implication_pair_form()),
        "the implication-pair spelling of slot_index did not certify"
    );
}

#[test]
fn combined_ite_restatement_certifies() {
    assert!(
        certified(&combined_ite_restatement()),
        "the pre-split Ite restatement of slot_index did not certify"
    );
}

/// The COMPILER'S entry point, not the formula-only one. `certify_all` calls
/// `certify_vc` on the results row whose formula `refute_full_assert_obligations`
/// rewrote to the grounded residual, and `convert_result` mints the row-bound
/// authority token only from the resulting `CleanCic`. This pins the full
/// identity binding (function, kind, location, formula) and its replay.
#[test]
fn grounded_residual_certifies_through_the_vc_entry_point() {
    let vc = trust_types::VerificationCondition {
        kind: trust_types::VcKind::Assertion {
            message: "panic freedom: no assertion, `unreachable!`, or panic is reachable"
                .to_string(),
        },
        function: "contract_panic_annotated::slot_index".into(),
        location: trust_types::SourceSpan::default(),
        formula: grounded_residual(),
        contract_metadata: None,
        obligation: None,
    };
    let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
        trust_certify::certify_vc(&vc)
    else {
        panic!("certify_vc declined the grounded panic-freedom residual");
    };
    assert!(
        trust_certify::recheck_vc_cleancic(&term, &context, &lineage, &vc),
        "the VC-bound certificate did not replay"
    );
}

/// The consumer side must accept what the producer minted: `recheck_cleancic`
/// independently REGENERATES the certificate from the violation and compares
/// bytes, so this also pins the lane's determinism (the implication-pair
/// orientation and the reading order of a var/var equality both feed it).
///
/// The regeneration may be a memo hit; a hit is byte-identical to a fresh run
/// by construction (trust-certify's `memo_hit_is_byte_identical_to_fresh`), so
/// the test is meaningful either way.
#[test]
fn certificates_replay_through_recheck() {
    for (name, violation) in [
        ("grounded_residual", grounded_residual()),
        ("implication_pair", implication_pair_form()),
        ("combined_ite", combined_ite_restatement()),
    ] {
        let Some(trust_ir::ProofEvidence::CleanCic { term, context, lineage, .. }) =
            trust_certify::certify_violation(&violation)
        else {
            panic!("{name}: no certificate");
        };
        assert!(
            trust_certify::recheck_cleancic(&term, &context, &lineage, &violation),
            "{name}: certificate did not replay"
        );
    }
}

// ---------------------------------------------------------------------------
// NEGATIVE CONTROLS — SATISFIABLE violations of the SAME shape. Each is a real
// counterexample, so certifying any of them would be a false proof.
// ---------------------------------------------------------------------------

/// The reification of `_3` is GONE, so nothing ties the branch selector to
/// `i < 8`. Satisfiable: take `_3` TRUE and `i = 8` — the `Ite` takes its else
/// branch, `k = i = 8`, so `_5 = 8 ≥ 8` and the `i ≥ 8` disjunct is open.
///
/// This is the sharpest control on the lane: it fails if the derivation ever
/// ASSUMES the guard rather than reading it out of a present definition.
#[test]
fn residual_without_the_reification_stays_uncertified() {
    assert!(
        !certified(&disjunct_split_residual(lt(v("i"), i(8)), i(7), false)),
        "SATISFIABLE mutant (no reified definition) was certified"
    );
    assert!(
        !certified(&implication_pair_residual(lt(v("i"), i(8)), i(7), false)),
        "SATISFIABLE implication-pair mutant (no reified definition) was certified"
    );
}

/// The clamp writes `9`, not `7`. Satisfiable: `i = 8` gives `k = 9 ≥ 8`, so the
/// panic really is reachable.
#[test]
fn residual_with_out_of_range_clamp_stays_uncertified() {
    assert!(
        !certified(&disjunct_split_residual(lt(v("i"), i(8)), i(9), true)),
        "SATISFIABLE mutant (clamp to 9) was certified"
    );
    assert!(
        !certified(&implication_pair_residual(lt(v("i"), i(8)), i(9), true)),
        "SATISFIABLE implication-pair mutant (clamp to 9) was certified"
    );
}

/// The reified selector tests `i < 16` while the switch still splits on
/// `i < 8`. Satisfiable: `i = 10` makes `_3` true, so `k = i = 10 ≥ 8` on the
/// `i ≥ 8` disjunct.
#[test]
fn residual_with_mismatched_guard_stays_uncertified() {
    assert!(
        !certified(&disjunct_split_residual(lt(v("i"), i(16)), i(7), true)),
        "SATISFIABLE mutant (guard reified at 16) was certified"
    );
    assert!(
        !certified(&implication_pair_residual(lt(v("i"), i(16)), i(7), true)),
        "SATISFIABLE implication-pair mutant (guard reified at 16) was certified"
    );
}

/// FAIL-CLOSED ON AMBIGUITY. `_3` is reified TWICE, at different thresholds.
/// The violation is still UNSAT (the `i < 8` definition alone refutes it), but
/// the definition map declines a doubly-bound name outright rather than picking
/// one, so no certificate is minted. Unproved is not proved — this test pins
/// that the lane declines rather than guessing.
#[test]
fn doubly_reified_guard_declines() {
    let disjunct = |path: Formula| {
        and(vec![
            i_range(),
            and(vec![
                eq(v("_5"), v(K)),
                eq(v(K), ite(not(b("_3")), i(7), v("i"))),
                eq(b("_3"), lt(v("i"), i(8))),
                eq(b("_3"), lt(v("i"), i(16))),
                and(vec![path, ge(v("_5"), i(8)), Formula::Bool(true)]),
            ]),
        ])
    };
    let [arm0, arm1] = arm_paths();
    assert!(
        !certified(&or(vec![disjunct(arm0), disjunct(arm1)])),
        "a doubly-reified guard must decline, not guess"
    );
}
