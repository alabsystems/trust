// trust_vcgen/generate/summary_dest_retiming_tests.rs
//
// Trust (postcondition composition — THE TIME AXIS of the terminator-fact
// channel, and the guard that now closes it).
//
// `build_semantic_guard_map_with_summaries` injects a callee's postcondition by
// (a) rebinding formals -> actual operands and `_0` -> the caller's destination
// (`rebind_callee_postconditions`) and then (b) handing the whole clause to
// `version_terminator_dest_fact`, which
//
//     read_versioned = version_rename_at(fact, sv, func, block, stmts.len())   // PRE-call
//     then rewrites EVERY Var whose BASE name is the destination's name to the
//     POST-call token `s{b}_t`.
//
// Step (b)'s rewrite is a blanket base-name match, not a match on the occurrence
// the `_0` substitution produced. So if any ARGUMENT of the same call renders to
// the destination's own variable name — i.e. the call's destination local is
// also read, unprojected, as one of its arguments — then the argument's PRE-call
// read is retimed to the POST-call token, and the clause stops saying what the
// callee proved.
//
// The consequences were not "one imprecise fact". For a strict relation between
// the result and that formal (`ensures result > n`, the ordinary shape) the
// injected hypothesis became `n#s0_t > n#s0_t` — UNSATISFIABLE. Trust's VC
// convention is "SAT iff violation" and the assumption is CONJOINED into the
// guard set of the dominated successors, so a false hypothesis made every
// obligation in that scope unsatisfiable-to-refute: PROVED, including
// obligations about locals the callee's contract cannot bear on at all
// (`no_false_hypothesis_reaches_an_unrelated_downstream_obligation` still owns
// that observation, now in the negative). The SIBLING producers on the same
// channel fail the other way and just as badly: `wrapping_neg`, `saturating_*`,
// the modeled intrinsics and `from_bits` all pin `dest == f(arg)`, which under
// the alias becomes the fixpoint equation `d == f(d)` — a STRENGTHENING of the
// hypothesis, not a loss.
//
// THE ASYMMETRY THIS FILE WAS WRITTEN FOR. `rebind_callee_postconditions` already
// knew about this exact time shift and refused it — for the ANTECEDENT only:
//
//     // In the ANTECEDENT it would be a silent time shift: an entry condition
//     // re-read against the post-state ... Refuse instead.
//     if antecedent.free_variables().iter().any(|v| *v == dest_name) { return Vec::new(); }
//
// (callsite.rs, the guarded branch). The CONSEQUENT had no such check, and the
// consequent is the half that rides the L0 lane
// (`definitional_precondition_free_subset` admits precondition-free definitional
// summaries, so the Clean-origin / `with_definitional_postcondition` minter is
// injected below `L1Functional` where the guarded branch never runs).
//
// WHAT USED TO STOP THIS — measured, and it was not a gate in this crate. Every
// named gate on the injection path ADMITTED the shape
// (`six_gates_admit_the_retimed_shape_and_the_seventh_refuses_it` still
// enumerates all six admissions): the definitional-evidence bit, the
// projection-free destination, the arity match, the destination's whole-write
// gate (then `is_single_static_assignment`, which counted a call-terminator dest
// on a PARAMETER as 1 because it never charged the entry definition; now
// `local_defs::dest_fact_is_version_pinnable`, which admits the shape for a
// STATED reason instead of an accidental one — see gate 4 below), the guard-ride
// predicate and `postcondition_rebindable`. What stopped it was an UNSTATED property of the
// MIR that reaches `TrustVerify`: rustc evaluates call arguments into fresh
// temporaries, and neither `CopyProp` nor `DestinationPropagation` (both of
// which run immediately BEFORE `TrustVerify` in `rustc_mir_transform::lib`'s
// optimized pipeline) will merge a local that is read by a call terminator with
// that terminator's destination.
//
// MEASURED 2026-08-31, with the production predicates themselves
// (`place_to_var_name` + `operand_to_formula` + `Formula::free_variables` +
// `is_single_static_assignment`) run over every `Call` terminator in the
// dependency-closed corpus `~/trust-corpora/mir-closed-mono`:
//
//     bodies=37612  calls=105703  arg_name_equals_dest_name=0  and_dest_is_SSA=0
//
// The FIRST conjunct is 0 on its own, so that measurement does not depend on
// which destination predicate the second conjunct used, and it survives the
// 2026-08-31 gate split unchanged.
//
// and separately, `_N = f(.. copy/move _N ..)` appears 0 times in the MIR this
// tree's own `rustc` emits for eight self-assigning shapes (`n = step(n)`
// straight-line, in a loop, behind a branch, through a field, nested,
// two-argument) at `-Zmir-opt-level` 1/2/3/4.
//
// THE REPAIR, landed 2026-08-31 and pinned below. It is the one the antecedent
// already had, applied at the CHANNEL rather than in one lane:
// `version_terminator_dest_fact` answers `None` — no fact at all, for the whole
// batch — when `terminator_args_read_name` says an argument of this call renders
// to the subject's base name; `callee_postcondition_is_injectable` carries the
// same conjunct so ADMIT and EMIT agree and `assumptions_injected` cannot
// over-count; and `rebind_callee_postconditions` refuses on exactly the same
// condition. COST, measured: zero facts on the corpus above, and every positive
// twin in this file and in `guarded_postcondition_tests` /
// `clean_origin_wrapping_summary_tests` / `modular::tests` still injects.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    VerifiableFunction,
};

use crate::generate::{
    build_semantic_guard_map, build_semantic_guard_map_with_summaries,
    callee_postcondition_is_injectable, rebind_callee_postconditions, terminator_args_read_name,
};
use crate::modular::{FunctionSummary, SummaryDatabase};

const CALLEE: &str = "retime::step";

/// The destination local of the aliasing shape: `_1`, which is ALSO argument 0.
const ALIASING_DEST: usize = 1;
/// The destination local of the control: `_3`, a fresh local.
const FRESH_DEST: usize = 3;

/// `fn caller(n: usize, k: usize) { <dest> = step(n); let _ = k + 1; }`
///
/// One call, one argument (`n` = `_1`, a PARAMETER), one successor that owns a
/// real checked-add overflow obligation about `k` — a local the call never
/// touches. `dest_local` is the only difference between the attack and the
/// control:
///   * `ALIASING_DEST` (`_1`)  — the destination IS argument 0's local, the
///     shape `n = step(n)` would produce if the argument temp were ever merged
///     away;
///   * `FRESH_DEST` (`_3`)     — the destination is a fresh local, the shape
///     rustc actually emits.
/// In both cases the call terminator is the destination's ONLY whole write, so
/// `local_defs::dest_fact_is_version_pinnable` admits it. Note the two are NOT
/// interchangeable on `ALIASING_DEST`: `_1` is a PARAMETER, so the bare-name
/// question (`is_single_static_assignment`) refuses it and the version-pinned
/// question admits it — see gate 4 for why each answer is right for its own lane.
fn caller(dest_local: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: "caller".to_string(),
        def_path: "retime::caller".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::usize(), name: Some("n".into()) },
                LocalDecl { index: 2, ty: Ty::usize(), name: Some("k".into()) },
                LocalDecl { index: 3, ty: Ty::usize(), name: Some("r".into()) },
                LocalDecl { index: 4, ty: Ty::Tuple(vec![Ty::usize(), Ty::Bool]), name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                        func: CALLEE.to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(dest_local),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    // `k + 1` on a `usize`: overflows exactly when `k == usize::MAX`,
                    // so with no hypothesis in scope the violation is satisfiable.
                    stmts: vec![Statement::Assign {
                        place: Place::local(4),
                        rvalue: Rvalue::CheckedBinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Assert {
                        unwind: UnwindEdge::Unreachable,
                        cond: Operand::Copy(Place::field(4, 1)),
                        expected: false,
                        msg: AssertMessage::Overflow(BinOp::Add),
                        target: BlockId(2),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The shape rustc DOES emit for `n = step(n)`: the argument is a temporary
/// copied from `n` in the same block, and the destination is a different local
/// again. Included as the production control — it differs from the attack
/// fixture by one statement and one operand, which is the whole distance
/// between "sound" and "unsatisfiable hypothesis", and it must keep injecting.
fn caller_via_argument_temp() -> VerifiableFunction {
    let mut f = caller(FRESH_DEST);
    f.body.blocks[0].stmts = vec![Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: SourceSpan::default(),
    }];
    let Terminator::Call { args, dest, .. } = &mut f.body.blocks[0].terminator else {
        unreachable!("fixture terminator is a Call")
    };
    // `_3 = copy _1; _1 = step(move _3)` — dest is the PARAMETER, the argument is
    // the temp. Still one write to `_1` in the body, so SSA admits it.
    *args = vec![Operand::Move(Place::local(3))];
    *dest = Place::local(1);
    f
}

/// `ensures result > n` — the ordinary strict-relation postcondition, and the
/// one production minter that can carry it below `L1Functional`: definitional
/// authority, no preconditions, one formal.
fn definitional_result_gt_formal() -> FunctionSummary {
    FunctionSummary::new(CALLEE)
        .with_param_names(vec!["n".to_string()])
        .with_definitional_postcondition(Formula::Gt(
            Box::new(Formula::var("_0", Sort::Int)),
            Box::new(Formula::var("n", Sort::Int)),
        ))
}

/// The same clause under the callee's own `requires n <= 100`, minted by the
/// authored-`ensures` lane. Reaches the GUARDED branch of
/// `rebind_callee_postconditions`.
fn guarded_result_gt_formal() -> FunctionSummary {
    FunctionSummary::new(CALLEE)
        .with_param_names(vec!["n".to_string()])
        .with_precondition(Formula::Le(
            Box::new(Formula::var("n", Sort::Int)),
            Box::new(Formula::Int(100)),
        ))
        .with_verified_callee_postcondition(Formula::Gt(
            Box::new(Formula::var("_0", Sort::Int)),
            Box::new(Formula::var("n", Sort::Int)),
        ))
}

fn definitional_db() -> SummaryDatabase {
    let mut db = SummaryDatabase::new();
    db.insert(definitional_result_gt_formal());
    db
}

fn guards_at(func: &VerifiableFunction, db: &SummaryDatabase, block: usize) -> Vec<Formula> {
    build_semantic_guard_map_with_summaries(func, db)
        .get(&BlockId(block))
        .cloned()
        .unwrap_or_default()
}

fn smt(fs: &[Formula]) -> Vec<String> {
    fs.iter().map(Formula::to_smtlib).collect()
}

/// True iff `f` contains a comparison whose two operands are the SAME variable
/// name — a hypothesis no execution can satisfy when the comparison is strict.
fn has_self_strict_comparison(f: &Formula) -> bool {
    fn same_var(a: &Formula, b: &Formula) -> bool {
        matches!((a, b), (Formula::Var(x, _), Formula::Var(y, _)) if x == y)
    }
    let hit = match f {
        Formula::Gt(a, b) | Formula::Lt(a, b) => same_var(a, b),
        _ => false,
    };
    hit || f.children().iter().any(|c| has_self_strict_comparison(c))
}

/// THE MECHANISM, and the falsify-once pair. One call, one summary, one
/// difference: whether the destination local is also the argument's local.
///
/// The attack half is the REFUSAL pin. The other two halves are the positive
/// twins that keep the refusal from being "the lane stopped working": a fresh
/// destination, and the argument-temp shape rustc actually emits, both still
/// carry the callee's `ensures` to the post-call block.
#[test]
fn dest_aliasing_an_argument_is_refused_and_the_unaliased_shapes_still_inject() {
    let db = definitional_db();

    // POSITIVE TWIN 1 — a fresh destination. The result reads at the POST-call
    // token and the argument reads at its own (entry) name: two DIFFERENT
    // symbols, which is the fact the callee actually proved.
    let control = guards_at(&caller(FRESH_DEST), &db, 1);
    assert!(
        smt(&control).iter().any(|s| s == "(> |r#s0_t| n)"),
        "control: the injected fact relates the post-call dest to the entry \
         argument: {:?}",
        smt(&control)
    );
    assert!(
        !control.iter().any(|f| has_self_strict_comparison(f)),
        "control: no self-comparison: {:?}",
        smt(&control)
    );

    // THE REFUSAL — the destination IS the argument's local, so
    // `version_terminator_dest_fact`'s base-name rewrite would retime the
    // argument's pre-call read onto the post-call token. The whole batch is
    // withheld instead: no clause at all, and in particular no clause naming one
    // symbol on both sides of a strict comparison.
    let attack = guards_at(&caller(ALIASING_DEST), &db, 1);
    assert!(
        !attack.iter().any(|f| has_self_strict_comparison(f)),
        "the retimed self-comparison must not be built: {:?}",
        smt(&attack)
    );
    assert!(
        !smt(&attack).iter().any(|s| s.contains("#s0_t")),
        "and nothing at all is pinned to the post-call token on this call: {:?}",
        smt(&attack)
    );

    // POSITIVE TWIN 2 — the production MIR shape (argument via a temp) is one
    // `CopyProp`/`DestinationPropagation` decision away from the attack, and is
    // exactly what the refusal must NOT catch. The dest is still the parameter
    // `_1`; only the argument moved to a temp.
    let via_temp = guards_at(&caller_via_argument_temp(), &db, 1);
    assert!(
        smt(&via_temp).iter().any(|s| s == "(> |n#s0_t| |r#s0_0|)"),
        "the shape rustc actually emits keeps the two reads distinct and STILL \
         injects: {:?}",
        smt(&via_temp)
    );
    assert!(
        !via_temp.iter().any(|f| has_self_strict_comparison(f)),
        "and it carries no self-comparison: {:?}",
        smt(&via_temp)
    );
}

/// SIX GATES, SIX ADMISSIONS — AND THE SEVENTH.
///
/// The six are enumerated one by one so a reader looking for the defence does
/// not have to guess which conjunct is meant to be it: none of them is. The
/// seventh (`terminator_args_read_name`) is the one that was missing, and it is
/// asserted here against its own precision control so it cannot quietly become a
/// blanket "the dest local appears somewhere" over-refusal.
#[test]
fn six_gates_admit_the_retimed_shape_and_the_seventh_refuses_it() {
    let func = caller(ALIASING_DEST);
    let summary = definitional_result_gt_formal();
    let dest = Place::local(ALIASING_DEST);
    let args = [Operand::Copy(Place::local(1))];

    // (1) the definitional-evidence bit — the canonical reuse bar.
    assert!(summary.has_reusable_postcondition_evidence(), "gate 1 admits");
    // (2) projection-free destination.
    assert!(dest.projections.is_empty(), "gate 2 admits");
    // (3) arity.
    assert_eq!(summary.param_names.len(), args.len(), "gate 3 admits");
    // (4) the destination's post-call TOKEN names one value.
    //
    //     CHANGED 2026-08-31, and the old assertion here was asserting a defect as
    //     correct. It read `is_single_static_assignment(&func, ALIASING_DEST)`, with
    //     the reason "a parameter written only by this call terminator counts as SSA"
    //     — and that reading is FALSE. A parameter is defined at ENTRY, so its bare
    //     name denotes TWO values, and `is_single_static_assignment` licenses BARE-NAME
    //     GLOBAL facts (`build_min_max_facts`, `build_fp_abs_facts`, the rest of
    //     `build_global_invariant_facts`) that are conjoined onto every VC of the
    //     function. Under the old answer this was PROVED and kernel-certified:
    //
    //         pub fn wc(mut i: u8, j: u8, c: bool) -> u8 {
    //             if c { i = j.min(3); }
    //             i + 200
    //         }
    //
    //     — `optimized_mir` at `-Copt-level=1` puts the `min` call's destination
    //     directly on the `mut` parameter, the scan counted 1, `i <= 3` was emitted as
    //     a global fact on the bare name, and the skip path (`c == false`) went UNSAT.
    //     Stock rustc 1.96.0 with `-C debug-assertions=on -C opt-level=1`, actually
    //     executed over the swept input space, panics on 51,200 of 131,072 inputs;
    //     first `wc(56, 0, false)`. The attribution probe is the byte-identical program
    //     plus one more write to `i`, which main REFUTED.
    //
    //     THIS LANE IS NOT THAT LANE, which is why the gate SPLIT rather than
    //     tightened. Nothing here is keyed on the bare name: the clause is threaded
    //     through `version_terminator_dest_fact`, which pins every occurrence of the
    //     dest's base name to `{dest}#s{block}_t` — a spelling the entry value is never
    //     read under, structurally, because `normalize_ssa_version_tokens` collapses a
    //     versioned token to bare only under `local_versions_collapse_to_bare`, whose
    //     parameter arm requires `!local_has_call_dest_write`. So gate 4 is now
    //     `local_defs::dest_fact_is_version_pinnable`, which asks the question this
    //     lane actually needs and STILL admits the shape, keeping the seventh gate the
    //     one that refuses.
    assert!(
        crate::local_defs::dest_fact_is_version_pinnable(&func, ALIASING_DEST),
        "gate 4 admits: this call terminator is the destination's only whole write, so \
         its post-call token names one value"
    );
    // ...and the bare-name question, correctly, does NOT admit it. The two answers
    // differ here and that difference is the point of the split; asserting only the
    // first would let the two silently re-merge.
    assert!(
        !super::callee_summaries::is_single_static_assignment(&func, ALIASING_DEST),
        "the BARE-NAME question refuses a parameter: its entry definition is a second \
         value the bare name denotes (witness `wc`, above)"
    );
    // (5) the guard-ride predicate is not even consulted (no preconditions).
    assert!(summary.preconditions.is_empty(), "gate 5 is vacuous here");
    // (6) rebindability — both free vars are `_0` and the one formal.
    assert!(
        crate::generate::postcondition_rebindable(&summary.postconditions[0], &summary.param_names),
        "gate 6 admits"
    );

    // (7) THE TIME AXIS — the one that refuses.
    let dest_name = crate::place_to_var_name(&func, &dest);
    assert!(
        terminator_args_read_name(&func, &args, &dest_name),
        "gate 7 fires: argument 0 renders to the destination's own name `{dest_name}`"
    );
    // ...and its PRECISION control: the predicate keys on the rendered BASE
    // name, because that is exactly what the retiming keys on. A PROJECTED read
    // of the same local renders to a different base name, is not retimed, and
    // must not be refused.
    let tuple_name = crate::place_to_var_name(&func, &Place::local(4));
    assert!(
        terminator_args_read_name(&func, &[Operand::Copy(Place::local(4))], &tuple_name),
        "precision control: the whole local IS a read of the subject"
    );
    assert!(
        !terminator_args_read_name(&func, &[Operand::Copy(Place::field(4, 0))], &tuple_name),
        "precision control: a projected read renders to a different base name \
         (`{}` vs `{tuple_name}`), is never retimed, and is admitted",
        crate::place_to_var_name(&func, &Place::field(4, 0))
    );

    // ADMIT ≡ EMIT, and the telemetry agrees with both.
    assert!(
        !callee_postcondition_is_injectable(&func, &dest, &summary, &args),
        "six admit, the seventh refuses, so nothing is injected"
    );
    assert!(
        rebind_callee_postconditions(&func, &args, &dest, &summary).is_empty(),
        "and the EMIT side refuses on the same condition"
    );
    let attacked = crate::modular::modular_vcgen(&func, &definitional_db());
    assert_eq!(attacked.assumptions_injected, 0, "no injection is counted");
    assert_eq!(attacked.havoced_calls, 1, "the call is havoced instead");

    // POSITIVE TWIN — the identical summary at a fresh destination passes all
    // seven and is both injected and counted.
    let fresh = caller(FRESH_DEST);
    let fresh_dest = Place::local(FRESH_DEST);
    assert!(
        callee_postcondition_is_injectable(&fresh, &fresh_dest, &summary, &args),
        "all seven admit at a fresh destination"
    );
    assert_eq!(
        rebind_callee_postconditions(&fresh, &args, &fresh_dest, &summary).len(),
        1,
        "and the clause is emitted"
    );
    assert_eq!(
        crate::modular::modular_vcgen(&fresh, &definitional_db()).assumptions_injected,
        1,
        "and counted"
    );
}

/// THE CONSEQUENCE, at the obligation level — now in the negative.
///
/// `k + 1` on a `usize` overflows exactly when `k == usize::MAX`. The callee's
/// contract says nothing whatever about `k`, so no correct reading of it can
/// discharge that row. Before the repair the aliased injection put an
/// unsatisfiable hypothesis into that row's violation formula, which makes the
/// formula unsatisfiable and the row PROVED. This test observes the FORMULA (the
/// layer this crate owns); "unsatisfiable hypothesis conjoined into a
/// SAT-iff-violation VC" is what that means to the solver.
#[test]
fn no_false_hypothesis_reaches_an_unrelated_downstream_obligation() {
    let db = definitional_db();

    let overflow_vc = |func: &VerifiableFunction| -> String {
        crate::modular::modular_vcgen(func, &db)
            .body_vcs
            .iter()
            .find(|vc| format!("{:?}", vc.kind).contains("Overflow"))
            .map(|vc| vc.formula.to_smtlib())
            .unwrap_or_else(|| panic!("fixture must own an overflow obligation"))
    };

    let attack = overflow_vc(&caller(ALIASING_DEST));
    assert!(
        !attack.contains("(> |n#s0_t| |n#s0_t|)"),
        "the unsatisfiable hypothesis must not reach the violation formula of an \
         obligation about `k`: {attack}"
    );

    // POSITIVE TWIN, on the same obligation: the fresh-destination control does
    // carry the callee's `ensures` into that very formula, so the refusal above
    // is a refusal of the ALIAS and not of the channel.
    let control = overflow_vc(&caller(FRESH_DEST));
    // The guard arrives bare-renamed (`bare_ssa_guard_variant`: the dest is
    // single-static-assignment, so `r#s0_t` and `r` are the same value) — the
    // point is that it arrives, and that its two sides are DIFFERENT symbols.
    assert!(
        control.contains("(> r n)"),
        "control: the sound rebinding still reaches the same obligation: {control}"
    );
    assert!(
        !control.contains("(> r r)") && !control.contains("(> n n)"),
        "control: and it is not a self-comparison: {control}"
    );
}

/// THE ASYMMETRY, CLOSED. The identical time shift, on the identical body and
/// call, is now refused wherever it lands.
///
/// `rebind_callee_postconditions`'s guarded branch refused an antecedent whose
/// free variables include the destination's name, with a comment naming the time
/// shift precisely. The consequent reached `version_terminator_dest_fact` with no
/// equivalent check — and the consequent is the half that rides L0, because
/// `definitional_precondition_free_subset` admits precondition-FREE definitional
/// summaries and those never take the guarded branch at all. Both halves refuse
/// now, on ONE condition checked in ONE place, and `assumptions_injected` agrees
/// with both (it used to count the guarded refusal as an injection the body VCs
/// never received).
#[test]
fn both_halves_of_the_clause_refuse_the_shape_only_the_antecedent_knew() {
    let func = caller(ALIASING_DEST);
    let dest = Place::local(ALIASING_DEST);
    let args = [Operand::Copy(Place::local(1))];

    for (what, summary) in
        [("guarded", guarded_result_gt_formal()), ("definitional", definitional_result_gt_formal())]
    {
        assert!(
            !callee_postcondition_is_injectable(&func, &dest, &summary, &args),
            "{what}: ADMIT refuses"
        );
        assert!(
            rebind_callee_postconditions(&func, &args, &dest, &summary).is_empty(),
            "{what}: EMIT refuses"
        );
        let mut db = SummaryDatabase::new();
        db.insert(summary);
        assert_eq!(
            crate::modular::modular_vcgen(&func, &db).assumptions_injected,
            0,
            "{what}: and the count matches what the body VCs received"
        );
        assert!(
            !guards_at(&func, &db, 1).iter().any(|f| has_self_strict_comparison(f)),
            "{what}: nothing false is threaded"
        );
    }
}

/// `fn f(x: i64) { <dest> = x.wrapping_neg(); }` — a SIBLING producer on the
/// same channel, with no summary database in sight.
fn wrapping_neg_caller(dest_local: usize) -> VerifiableFunction {
    VerifiableFunction {
        name: "f".into(),
        def_path: "retime::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i64(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i64(), name: Some("n".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: "core::num::<impl i64>::wrapping_neg".into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(dest_local),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// THE GUARD IS AT THE CHANNEL, NOT IN THE SUMMARY LANE — and the sibling
/// producers fail the OTHER way, which is why it has to be.
///
/// `wrapping_neg` pins `dest == ite(x == MIN, MIN, -x)`. Under the alias the
/// blanket retiming turns that into `d == ite(d == MIN, MIN, -d)`, whose only
/// solutions are `0` and `i64::MIN` — a hypothesis STRICTLY STRONGER than
/// anything the model licenses, conjoined into every dominated obligation. No
/// summary database is involved, so a repair that lived only in
/// `rebind_callee_postconditions` would have left this open.
#[test]
fn the_refusal_covers_the_sibling_value_producers_on_the_same_channel() {
    let guards = |f: &VerifiableFunction| {
        build_semantic_guard_map(f).get(&BlockId(1)).cloned().unwrap_or_default()
    };

    // POSITIVE TWIN — a fresh destination still gets the exact `Ite` definition.
    let control = guards(&wrapping_neg_caller(2));
    assert!(
        smt(&control).iter().any(|s| s.contains("|n#s0_t|") && s.contains("ite")),
        "control: the wrapping_neg value definition is still pinned: {:?}",
        smt(&control)
    );

    // THE REFUSAL — the destination IS the operand.
    let attack = guards(&wrapping_neg_caller(1));
    assert!(
        !smt(&attack).iter().any(|s| s.contains("#s0_t")),
        "no terminator fact may be threaded when the operand IS the destination \
         — the retimed form `d == ite(d == MIN, MIN, -d)` admits only 0 and \
         i64::MIN: {:?}",
        smt(&attack)
    );
}
