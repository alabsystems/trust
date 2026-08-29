// trust_vcgen/generate/guarded_postcondition_tests.rs
//
// Trust (postcondition composition, slice 2): THE GUARD PIN.
//
// A callee's `ensures` is guaranteed only WHERE ITS `requires` HELD, so a
// summary minted by `FunctionSummary::with_verified_callee_postcondition` must
// reach a call site as the implication the callee proved —
// `pre[formals:=actuals] -> post[formals:=actuals, _0:=dest]` — and never as the
// bare consequent. Assuming the consequent alone is a false PROVE for every
// caller that is out of the callee's contract, and the compiler-level fixtures
// (`tests/ui/trust/postcondition_composition_preconditioned_*.rs`) can only
// observe it through a verdict. These tests observe the FORMULA.
//
// The two halves pinned here are the two ways this lane can go wrong:
//   * the ADMIT and EMIT sides disagreeing, so a summary rides the L0 database
//     that the injector then hands over unguarded; and
//   * an antecedent that is built but is not the callee's actual entry
//     condition (`_0` bound to the caller's destination — an entry guard
//     silently re-read against the value the call just produced).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Sort, SourceSpan, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

use crate::generate::{
    callee_postcondition_is_injectable, rebind_callee_postconditions,
    summary_postconditions_ride_with_their_guard,
};
use crate::modular::FunctionSummary;

const CALLEE: &str = "guarded::positive_part";

/// `fn triple(x: i32) -> i32 { let y = positive_part(x); .. }` — one call, one
/// successor, dest is a fresh single-static-assignment local.
fn caller() -> VerifiableFunction {
    VerifiableFunction {
        name: "triple".into(),
        def_path: "guarded::triple".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::i32(), name: Some("_0".into()) },
                LocalDecl { index: 1, ty: Ty::i32(), name: Some("x".into()) },
                LocalDecl { index: 2, ty: Ty::i32(), name: Some("y".into()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Unreachable,
                        func: CALLEE.into(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(2),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        is_foreign: false,
                        callee_identity: None,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
            return_ty: Ty::i32(),
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn call_site(func: &VerifiableFunction) -> (&[Operand], &Place) {
    let Terminator::Call { args, dest, .. } = &func.body.blocks[0].terminator else {
        unreachable!("built with a Call terminator");
    };
    (args, dest)
}

/// The call site's own spelling of an actual / of the destination place. Derived
/// from the SAME helpers the injector uses, so these tests pin the STRUCTURE of
/// the injected clause rather than re-guessing a variable name or a sort.
fn actual_formula(func: &VerifiableFunction, actual: &Operand) -> Formula {
    crate::operand_to_formula(func, actual)
}

fn dest_formula(func: &VerifiableFunction, dest: &Place) -> Formula {
    Formula::var(
        &crate::place_to_var_name(func, dest),
        crate::place_sort(func, dest).unwrap_or(Sort::Int),
    )
}

/// `requires a0 > 0` over the single formal.
fn formal_positive() -> Formula {
    Formula::Gt(Box::new(Formula::var("a0", Sort::Int)), Box::new(Formula::Int(0)))
}

/// `ensures result > 0`.
fn result_positive() -> Formula {
    Formula::Gt(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::Int(0)))
}

/// The shape the compiler's slice-2 mint produces: a `requires` + a verified
/// `ensures`, over one formal.
fn guarded_summary() -> FunctionSummary {
    FunctionSummary::new(CALLEE)
        .with_param_names(vec!["a0".to_string()])
        .with_precondition(formal_positive())
        .with_verified_callee_postcondition(result_positive())
}

#[test]
fn a_preconditioned_verified_summary_is_injected_as_an_implication() {
    let func = caller();
    let (args, dest) = call_site(&func);
    let summary = guarded_summary();

    assert!(
        summary_postconditions_ride_with_their_guard(&summary),
        "a rebindable, machine-arithmetic-free `requires` must be expressible as \
         a call-site antecedent"
    );
    assert!(
        callee_postcondition_is_injectable(&func, dest, &summary, args.len()),
        "slice 2: a preconditioned callee is injectable once its clause rides \
         under its own guard"
    );

    let rebound = rebind_callee_postconditions(&func, args, dest, &summary);
    assert_eq!(rebound.len(), 1, "one authored `ensures`, one injected clause");

    // The load-bearing assertion: what arrives is `x > 0 -> y > 0`, NOT `y > 0`.
    let Formula::Implies(antecedent, consequent) = &rebound[0] else {
        panic!(
            "a preconditioned callee's clause must arrive as the implication it \
             proved, not as the bare consequent; got {:?}",
            rebound[0]
        );
    };
    assert_eq!(
        **antecedent,
        Formula::Gt(Box::new(actual_formula(&func, &args[0])), Box::new(Formula::Int(0))),
        "the antecedent is the callee's `requires` with formals rebound to THIS \
         call's actuals"
    );
    assert_eq!(
        **consequent,
        Formula::Gt(Box::new(dest_formula(&func, dest)), Box::new(Formula::Int(0))),
        "the consequent is the `ensures` with `_0` rebound to the call dest"
    );
}

#[test]
fn a_precondition_free_verified_summary_is_untouched_by_the_guard_lane() {
    // Slice 1's shape. `with_verified_callee_postcondition` sets the guard bit
    // unconditionally, so this is the pin that an EMPTY precondition set still
    // produces the bare clause — i.e. slice 2 did not silently wrap slice 1's
    // facts in a vacuous implication.
    let func = caller();
    let (args, dest) = call_site(&func);
    let summary = FunctionSummary::new(CALLEE)
        .with_param_names(vec!["a0".to_string()])
        .with_verified_callee_postcondition(result_positive());

    assert!(
        !summary_postconditions_ride_with_their_guard(&summary),
        "with no preconditions there is no guard to ride under"
    );
    let rebound = rebind_callee_postconditions(&func, args, dest, &summary);
    assert_eq!(
        rebound,
        vec![Formula::Gt(Box::new(dest_formula(&func, dest)), Box::new(Formula::Int(0)))],
        "a precondition-free verified clause is injected exactly as before"
    );
}

#[test]
fn a_precondition_naming_the_result_symbol_injects_nothing() {
    // `_0` is the callee's RESULT. An antecedent allowed to mention it would be
    // rebound to the caller's destination — an entry condition re-read against
    // the value the call has just produced, dischargeable by the call's own
    // effect. Refuse the whole injection rather than build that guard.
    let func = caller();
    let (args, dest) = call_site(&func);
    let summary = FunctionSummary::new(CALLEE)
        .with_param_names(vec!["a0".to_string()])
        .with_precondition(result_positive())
        .with_verified_callee_postcondition(result_positive());

    assert!(
        !summary_postconditions_ride_with_their_guard(&summary),
        "`_0` is not a formal, so this guard is not call-site expressible"
    );
    assert!(!callee_postcondition_is_injectable(&func, dest, &summary, args.len()));
    assert!(
        rebind_callee_postconditions(&func, args, dest, &summary).is_empty(),
        "EMIT must refuse on exactly the condition ADMIT refuses on — an \
         unguarded preconditioned clause is the false PROVE this lane exists to \
         prevent"
    );
}

#[test]
fn an_unexpressible_guard_conjunct_kills_the_whole_injection() {
    // ALL OR NOTHING. The callee proved `p AND q -> post`; injecting `p -> post`
    // is a STRONGER claim than the contract supports, so a partially-built
    // antecedent is unsound in the OPPOSITE direction from the usual "dropping a
    // hypothesis is safe". One unexpressible conjunct must therefore drop the
    // clause, not the conjunct.
    let func = caller();
    let (args, dest) = call_site(&func);
    let unexpressible = Formula::Gt(
        Box::new(Formula::var("callee_internal", Sort::Int)),
        Box::new(Formula::Int(0)),
    );
    let summary = FunctionSummary::new(CALLEE)
        .with_param_names(vec!["a0".to_string()])
        .with_precondition(formal_positive())
        .with_precondition(unexpressible)
        .with_verified_callee_postcondition(result_positive());

    assert!(!summary_postconditions_ride_with_their_guard(&summary));
    assert!(!callee_postcondition_is_injectable(&func, dest, &summary, args.len()));
    assert!(rebind_callee_postconditions(&func, args, dest, &summary).is_empty());
}

#[test]
fn the_l0_database_admits_exactly_what_the_injector_will_guard() {
    // The ADMIT/EMIT biconditional, stated as a test rather than as a comment.
    // A summary that rides the L0 database must be one the injector guards; a
    // summary the injector refuses must be withheld with its fail-closed row.
    use crate::modular::SummaryDatabase;

    let func = caller();
    let (args, dest) = call_site(&func);

    let mut admitted = SummaryDatabase::new();
    admitted.insert(guarded_summary());
    let subset = admitted.definitional_precondition_free_subset();
    assert!(
        subset.get(CALLEE).is_some(),
        "a guarded preconditioned summary rides L0 — its value fact and its \
         guard are one formula and cannot be separated by a level filter"
    );
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), None);
    let guarded = rebind_callee_postconditions(&func, args, dest, subset.get(CALLEE).unwrap());
    assert!(
        matches!(guarded.as_slice(), [Formula::Implies(..)]),
        "what the L0 lane admitted must arrive guarded"
    );

    // The converse: no guard bit (a DEFINITIONAL preconditioned summary) is
    // still withheld, exactly as before slice 2.
    let mut withheld = SummaryDatabase::new();
    withheld.insert(
        FunctionSummary::new(CALLEE)
            .with_param_names(vec!["a0".to_string()])
            .with_precondition(formal_positive())
            .with_definitional_postcondition(result_positive()),
    );
    let subset = withheld.definitional_precondition_free_subset();
    assert!(subset.get(CALLEE).is_none(), "no guard bit, no L0 ride");
    assert_eq!(subset.l0_withheld_precondition_count(CALLEE), Some(1));
}
