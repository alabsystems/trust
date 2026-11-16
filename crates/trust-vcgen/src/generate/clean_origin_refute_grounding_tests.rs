// trust_vcgen/generate/clean_origin_refute_grounding_tests.rs
//
// Trust (Clean-origin definitional grounding in the ASSERT-REFUTATION lane):
// the pins for `assert_refutation::clean_origin_definitional_call_models`.
//
// THE GAP THESE TESTS CLOSE (measured 2026-09-13, stage1 `trustc` at HEAD,
// `-Ztrust-verify=on`, opt-level 0):
//
//     mod m { clean { def pick (a : UInt64) (b : UInt64) : UInt64 := a } }
//     fn main() { let v = m::pick(41, 7); assert!(v == 41); }
//
// The VC lane closes `vc:main__main:assertion:0` KernelCertified from the
// Clean-origin definitional summary (`_0 == arg0`, minted from the kernel-gated
// plan of record). The refutation lane — which is what discharges the
// whole-function panic-freedom aggregate and licenses the `core::panicking::
// panic` exemption in the interprocedural call gate — modeled call results only
// for `wrapping_*` and the `?`/slice extractors and never read the summary, so
// `v` stayed free: `[ASSERT_REFUTE] block=BlockId(3) grounded=false
// free=["_2#s1_0"]`, `[ASSERT_P2] … pf_idxs=[] proved=0`, and the aggregate
// stayed UNKNOWN.
//
// Each test below holds one gate of the lane:
//   * the summary GROUNDS `v` and the assert block is refuted-unreachable (the
//     path-feasibility formula has no model);
//   * the same definition REFUTES a wrong claim (the formula has a model) — a
//     definition states what the callee returns, it does not bless the assert;
//   * an ORDINARY contract postcondition (`with_postcondition`, and the proved
//     `with_verified_callee_postcondition`) never becomes a model at all;
//   * a model for a DIFFERENT callee identity — same rendered name or not —
//     never grounds; an absent identity admits nothing; a name mismatch under
//     the same identity refuses;
//   * a definitional clause that does not DETERMINE the result is refused at
//     the consumer (the SAT-direction guard);
//   * a chain of Clean-origin calls grounds through its intermediate result.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashMap;
use trust_types::{
    BasicBlock, BinOp, BlockId, CalleeIdentity, ConstValue, Formula, LocalDecl, Operand, Place,
    Rvalue, Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody,
    VerifiableFunction,
};

use crate::modular::{CleanOriginDefinitionalCallModel, FunctionSummary};
use crate::{CalleeSummaryContext, VcgenContext, generate_full_assert_refutation_vcs_with_context};

/// The rendered callee name the extracted `Terminator::Call` carries
/// (`func_operand_name`), which is also the summary's key in the VC lane.
const PICK: &str = "m::pick";
const CALLER: &str = "test::main";

/// The sealed identity the extractor stamps on a direct call to `m::pick`.
const ID_PICK: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 0xC1EA, def_index: 3, substs_digest: [0, 0] };
/// A different def in the same crate.
const ID_OTHER: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 0xC1EA, def_index: 4, substs_digest: [0, 0] };

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn u64_const(v: u64) -> Operand {
    Operand::Constant(ConstValue::Uint(u128::from(v), 64))
}

fn call(
    callee: &str,
    identity: Option<CalleeIdentity>,
    args: Vec<Operand>,
    dest: usize,
    target: BlockId,
) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(target),
        span: span(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        // The Clean-origin emitter's own edge (a `WrappingBinOp` body is total
        // by construction); `unwind` is deliberately not a gate of the lane.
        unwind: UnwindEdge::Unreachable,
        callee_identity: identity,
        callee_key: crate::sep_engine::tests::fixture_key(&callee.to_string()),
    }
}

/// `bbN: core::panicking::panic(..)` — the assert's failure block, exactly
/// the shape `is_assert_refutation_target_block` recognizes.
fn panic_block(id: usize, dest: usize) -> BasicBlock {
    BasicBlock {
        id: BlockId(id),
        stmts: vec![],
        terminator: Terminator::Call {
            func: "core::panicking::panic".into(),
            args: vec![],
            dest: Place::local(dest),
            target: None,
            span: span(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Continue,
            callee_identity: None,
            callee_key: crate::sep_engine::tests::fixture_key("core::panicking::panic"),
        },
    }
}

/// `fn main() { let v = pick(41, 7); assert!(v == claim); }`, reduced MIR:
///
/// ```text
/// bb0: v = pick(41, 7) -> bb1
/// bb1: _2 = Eq(v, claim); switchInt(_2) [0 -> bb2] otherwise -> bb3
/// bb2: core::panicking::panic(..)          // the assert's failure block
/// bb3: return
/// ```
fn caller(callee: &str, identity: Option<CalleeIdentity>, claim: u64) -> VerifiableFunction {
    VerifiableFunction {
        name: "main".into(),
        def_path: CALLER.into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: Ty::Bool, name: None },
                LocalDecl { index: 3, ty: Ty::Never, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(
                        callee,
                        identity,
                        vec![u64_const(41), u64_const(7)],
                        1,
                        BlockId(1),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(1)),
                            u64_const(claim),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                },
                panic_block(2, 3),
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `fn main() { let v = pick(41, 7); let w = pick(v, 7); assert!(w == 41); }`
/// — the outer call's actual is the inner call's result.
fn chained_caller() -> VerifiableFunction {
    VerifiableFunction {
        name: "main".into(),
        def_path: CALLER.into(),
        span: span(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("v".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("w".into()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: None },
                LocalDecl { index: 4, ty: Ty::Never, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: call(
                        PICK,
                        Some(ID_PICK),
                        vec![u64_const(41), u64_const(7)],
                        1,
                        BlockId(1),
                    ),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: call(
                        PICK,
                        Some(ID_PICK),
                        vec![Operand::Copy(Place::local(1)), u64_const(7)],
                        2,
                        BlockId(2),
                    ),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Eq,
                            Operand::Copy(Place::local(2)),
                            u64_const(41),
                        ),
                        span: span(),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Move(Place::local(3)),
                        targets: vec![(0, BlockId(3))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: span(),
                    },
                },
                panic_block(3, 4),
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 0,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn formals() -> Vec<String> {
    vec!["__trust_clean_origin_arg0".to_string(), "__trust_clean_origin_arg1".to_string()]
}

/// The compiler's Clean-origin summary for `def pick (a b : UInt64) := a`
/// (`clean_origin_callee_summary` — `CleanOriginCallModel::Projection {
/// projected: 0, arity: 2 }` -> `_0 == arg0`).
fn projection_post() -> Formula {
    Formula::Eq(
        Box::new(Formula::var("_0", Sort::Int)),
        Box::new(Formula::var("__trust_clean_origin_arg0", Sort::Int)),
    )
}

fn definitional_pick_summary(name: &str) -> FunctionSummary {
    FunctionSummary::new(name)
        .with_param_names(formals())
        .with_definitional_postcondition(projection_post())
}

fn context_with(models: Vec<(CalleeIdentity, CleanOriginDefinitionalCallModel)>) -> VcgenContext {
    let map: FxHashMap<CalleeIdentity, CleanOriginDefinitionalCallModel> =
        models.into_iter().collect();
    VcgenContext::for_function(CALLER).with_callee_summaries(
        CalleeSummaryContext::default().with_clean_origin_definitional_models(map),
    )
}

fn pick_model_named(name: &str) -> CleanOriginDefinitionalCallModel {
    CleanOriginDefinitionalCallModel::from_clean_origin_summary(&definitional_pick_summary(name))
        .expect("a pure definitional summary is the admitted shape")
}

fn pick_model() -> CleanOriginDefinitionalCallModel {
    pick_model_named(PICK)
}

// ---------------------------------------------------------------------------
// A tiny total evaluator over the fragment the emitted formula uses, so the
// verdict-direction facts are checked WITHOUT a solver: the assert's
// path-feasibility formula is UNSAT iff no environment satisfies it, and here
// the definition pins `v` to one value, so enumerating the Boolean temp is the
// whole model space.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq)]
enum Val {
    I(i128),
    B(bool),
}

fn base(name: &str) -> &str {
    name.split('#').next().unwrap_or(name)
}

fn eval(f: &Formula, env: &dyn Fn(&str) -> Option<Val>) -> Option<Val> {
    let int = |f: &Formula| match eval(f, env)? {
        Val::I(v) => Some(v),
        Val::B(_) => None,
    };
    let boolean = |f: &Formula| match eval(f, env)? {
        Val::B(v) => Some(v),
        Val::I(_) => None,
    };
    Some(match f {
        Formula::Bool(b) => Val::B(*b),
        Formula::Int(v) => Val::I(*v),
        Formula::UInt(v) => Val::I(i128::try_from(*v).ok()?),
        Formula::Var(name, _) => env(base(name))?,
        Formula::Eq(a, b) => match (eval(a, env)?, eval(b, env)?) {
            (Val::I(x), Val::I(y)) => Val::B(x == y),
            (Val::B(x), Val::B(y)) => Val::B(x == y),
            _ => return None,
        },
        Formula::Lt(a, b) => Val::B(int(a)? < int(b)?),
        Formula::Le(a, b) => Val::B(int(a)? <= int(b)?),
        Formula::Gt(a, b) => Val::B(int(a)? > int(b)?),
        Formula::Ge(a, b) => Val::B(int(a)? >= int(b)?),
        Formula::Not(a) => Val::B(!boolean(a)?),
        Formula::And(cs) => {
            let mut acc = true;
            for c in cs {
                acc &= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Or(cs) => {
            let mut acc = false;
            for c in cs {
                acc |= boolean(c)?;
            }
            Val::B(acc)
        }
        Formula::Implies(a, b) => Val::B(!boolean(a)? || boolean(b)?),
        Formula::Ite(c, t, e) => {
            if boolean(c)? {
                eval(t, env)?
            } else {
                eval(e, env)?
            }
        }
        _ => return None,
    })
}

/// Whether `f` contains the conjunct `v == <literal>` for the given literal —
/// the definition the model contributes, in either literal spelling.
fn pins_var_to(f: &Formula, var: &str, literal: i128) -> bool {
    let is_lit = |x: &Formula| match x {
        Formula::Int(v) => *v == literal,
        Formula::UInt(v) => i128::try_from(*v).ok() == Some(literal),
        _ => false,
    };
    match f {
        Formula::Eq(a, b) => {
            (a.var_name().is_some_and(|n| base(n) == var) && is_lit(b))
                || (b.var_name().is_some_and(|n| base(n) == var) && is_lit(a))
                || pins_var_to(a, var, literal)
                || pins_var_to(b, var, literal)
        }
        Formula::And(cs) | Formula::Or(cs) => cs.iter().any(|c| pins_var_to(c, var, literal)),
        Formula::Not(a) => pins_var_to(a, var, literal),
        Formula::Implies(a, b) => pins_var_to(a, var, literal) || pins_var_to(b, var, literal),
        Formula::Ite(c, t, e) => {
            pins_var_to(c, var, literal)
                || pins_var_to(t, var, literal)
                || pins_var_to(e, var, literal)
        }
        _ => false,
    }
}

/// Every free variable of the emitted formula, by base name.
fn free_base_names(f: &Formula) -> Vec<String> {
    let mut names: Vec<String> = f.free_variables().iter().map(|v| base(v).to_string()).collect();
    names.sort();
    names.dedup();
    names
}

/// The lane's verdict on `func`, as the compiler would read it: the emitted
/// candidate for the assert's failure block, or none (declined as ungrounded).
fn refutation_candidate(func: &VerifiableFunction, context: &VcgenContext) -> Option<Formula> {
    let vcs = generate_full_assert_refutation_vcs_with_context(func, context);
    let mut asserts = vcs.into_iter().filter(|vc| matches!(vc.kind, VcKind::Assertion { .. }));
    let first = asserts.next()?;
    assert!(asserts.next().is_none(), "exactly one candidate per failure block");
    Some(first.formula)
}

// ---------------------------------------------------------------------------

#[test]
fn definitional_summary_grounds_the_call_result_and_the_assert_block_is_unreachable() {
    let func = caller(PICK, Some(ID_PICK), 41);
    let context = context_with(vec![(ID_PICK, pick_model())]);

    let formula = refutation_candidate(&func, &context)
        .expect("with the Clean-origin model the panic block must produce a grounded candidate");

    // GROUNDED: nothing but the call result and the assert's Boolean temp is
    // free, and the call result carries its definition `v == 41`.
    let free = free_base_names(&formula);
    assert!(
        free.iter().all(|n| n == "v" || n == "_2"),
        "every free variable must be the pinned call result or the assert temp; got {free:?}"
    );
    assert!(pins_var_to(&formula, "v", 41), "the model must pin `v` to 41; got {formula:?}");

    // UNSAT: `v` is pinned to 41, so the model space is the two values of the
    // Boolean temp, and neither satisfies the panic path — the assert holds for
    // every input, which is what lets the compiler prove the panic block
    // unreachable and exempt its `core::panicking::panic` edge.
    for temp in [true, false] {
        let env = |name: &str| match name {
            "v" => Some(Val::I(41)),
            "_2" => Some(Val::B(temp)),
            _ => None,
        };
        assert_eq!(
            eval(&formula, &env),
            Some(Val::B(false)),
            "the panic path must be infeasible under v = 41, _2 = {temp}; formula {formula:?}"
        );
    }
}

#[test]
fn the_same_definition_refutes_a_wrong_claim() {
    // `assert!(v == 42)` after `v = pick(41, 7)` REALLY panics. The definition
    // states what the callee returns; SAT here is a genuine counterexample, so
    // the lane surfaces the wrong claim as a violation rather than blessing it.
    let func = caller(PICK, Some(ID_PICK), 42);
    let context = context_with(vec![(ID_PICK, pick_model())]);

    let formula = refutation_candidate(&func, &context)
        .expect("the wrong claim is grounded by the same model");
    assert!(pins_var_to(&formula, "v", 41));
    let env = |name: &str| match name {
        "v" => Some(Val::I(41)),
        "_2" => Some(Val::B(false)),
        _ => None,
    };
    assert_eq!(
        eval(&formula, &env),
        Some(Val::B(true)),
        "v = 41 drives execution into the panic of `assert!(v == 42)`; formula {formula:?}"
    );
}

#[test]
fn without_a_model_the_call_result_stays_free_and_the_assert_is_declined() {
    // The pre-lane behaviour, byte-identical: an empty context grounds nothing.
    let func = caller(PICK, Some(ID_PICK), 41);
    let context = VcgenContext::for_function(CALLER);
    assert!(
        refutation_candidate(&func, &context).is_none(),
        "an opaque call destination must leave the assert ungrounded (declined)"
    );
}

#[test]
fn an_ordinary_contract_postcondition_never_becomes_a_model() {
    // A PARSED contract (`with_postcondition`) is a caller-assumed claim, not a
    // definition: the carrier refuses it outright, so it can never reach the
    // refutation lane's candidate set.
    let contract = FunctionSummary::new(PICK)
        .with_param_names(formals())
        .with_postcondition(projection_post());
    assert!(
        CleanOriginDefinitionalCallModel::from_clean_origin_summary(&contract).is_none(),
        "`with_postcondition` clears definitional authority and must be refused"
    );

    // A PROVED `ensures` (`with_verified_callee_postcondition`) is true of the
    // result but need not determine it — sound to assume in the UNSAT-only VC
    // lane, a false refutation in this one. Refused.
    let proved = FunctionSummary::new(PICK)
        .with_param_names(formals())
        .with_verified_callee_postcondition(projection_post());
    assert!(
        CleanOriginDefinitionalCallModel::from_clean_origin_summary(&proved).is_none(),
        "a proved-but-not-definitional postcondition must be refused"
    );

    // Mixed provenance fails closed in both orders, exactly as the VC lane's bit does.
    let mixed = definitional_pick_summary(PICK).with_postcondition(projection_post());
    assert!(CleanOriginDefinitionalCallModel::from_clean_origin_summary(&mixed).is_none());

    // A preconditioned definitional summary is withheld here as it is at L0.
    let guarded = definitional_pick_summary(PICK).with_precondition(Formula::Gt(
        Box::new(Formula::var("__trust_clean_origin_arg1", Sort::Int)),
        Box::new(Formula::Int(0)),
    ));
    assert!(CleanOriginDefinitionalCallModel::from_clean_origin_summary(&guarded).is_none());
}

#[test]
fn a_model_for_a_different_callee_identity_never_grounds() {
    // Same rendered name, DIFFERENT sealed identity: the map is keyed by
    // identity, so the call's own identity misses and `v` stays free.
    let func = caller(PICK, Some(ID_PICK), 41);
    let context = context_with(vec![(ID_OTHER, pick_model())]);
    assert!(
        refutation_candidate(&func, &context).is_none(),
        "a model registered under another identity must not ground this call"
    );

    // Absent identity (an indirect call, a `dyn` dispatch, a generic the
    // extractor refused to fingerprint) admits nothing — never a name fallback,
    // even though the model IS registered and the names DO match.
    let func = caller(PICK, None, 41);
    let context = context_with(vec![(ID_PICK, pick_model())]);
    assert!(
        refutation_candidate(&func, &context).is_none(),
        "an absent identity must not fall back to the rendered name"
    );

    // Same identity, DIFFERENT rendered name (the belt): refused.
    let func = caller(PICK, Some(ID_PICK), 41);
    let context = context_with(vec![(ID_PICK, pick_model_named("other::pick"))]);
    assert!(
        refutation_candidate(&func, &context).is_none(),
        "a model whose name disagrees with the terminator's `func` must be refused"
    );
}

#[test]
fn a_definitional_clause_that_does_not_determine_the_result_is_refused() {
    // `_0 <= 100` is TRUE of `pick` but does not pin the result; in a lane that
    // reads SAT as a counterexample it would let `v` float below 41 and refute
    // the honest `assert!(v == 41)`. The carrier cannot see this (the clause
    // is "definitional" by the producer's word); the consumer's structural
    // determination check must.
    let partial =
        FunctionSummary::new(PICK).with_param_names(formals()).with_definitional_postcondition(
            Formula::Le(Box::new(Formula::var("_0", Sort::Int)), Box::new(Formula::Int(100))),
        );
    let model = CleanOriginDefinitionalCallModel::from_clean_origin_summary(&partial)
        .expect("the carrier admits by authority bit; determination is the consumer's gate");
    let func = caller(PICK, Some(ID_PICK), 41);
    let context = context_with(vec![(ID_PICK, model)]);
    assert!(
        refutation_candidate(&func, &context).is_none(),
        "a non-determining clause must not ground the call result"
    );

    // Two competing definitions of the result are refused the same way.
    let doubled = definitional_pick_summary(PICK).with_definitional_postcondition(Formula::Eq(
        Box::new(Formula::var("_0", Sort::Int)),
        Box::new(Formula::var("__trust_clean_origin_arg1", Sort::Int)),
    ));
    let model = CleanOriginDefinitionalCallModel::from_clean_origin_summary(&doubled).unwrap();
    let context = context_with(vec![(ID_PICK, model)]);
    assert!(refutation_candidate(&func, &context).is_none());
}

#[test]
fn a_chain_of_clean_origin_calls_grounds_through_its_intermediate_result() {
    // `w = pick(v, 7)` reads the earlier Clean-origin result `v` as its actual;
    // the fixpoint grounds `v` first (constants), then `w` through `v`.
    let func = chained_caller();
    let context = context_with(vec![(ID_PICK, pick_model())]);
    let formula = refutation_candidate(&func, &context)
        .expect("the outer call's result must ground through the inner call's");
    let free = free_base_names(&formula);
    assert!(
        free.iter().all(|n| n == "v" || n == "w" || n == "_3"),
        "only the two pinned results and the assert temp may be free; got {free:?}"
    );
    for temp in [true, false] {
        let env = |name: &str| match name {
            "v" | "w" => Some(Val::I(41)),
            "_3" => Some(Val::B(temp)),
            _ => None,
        };
        assert_eq!(
            eval(&formula, &env),
            Some(Val::B(false)),
            "the chained assert's panic path must be infeasible; formula {formula:?}"
        );
    }
}
