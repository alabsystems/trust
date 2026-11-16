// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! The Beyond-TLA model prelude, kernel-checked (lane B1a, B1A-01b).
//!
//! Every module trust-model-prelude serves elaborates, in order, with no failed
//! declaration; nothing the prelude adds reaches a domain axiom; the expected
//! declarations are there; `Trust.Model.epVersion` agrees with `EP_VERSION` through
//! a Bool door accepted by `check_model_theorem` (the temporal surface's
//! `checked_theorem`, audit included); and an ill-typed extra module is refused.
//!
//! Tests that elaborate the prelude are release-only (B1A-D42): this crate has no
//! opt-level overrides for Clean, and a debug build of the finite-model prelude
//! costs tens of seconds per worker. The `smoke_` tests run in debug, on the push
//! lane, and elaborate nothing.

use clean_kernel::ConstantKind;
use clean_kernel::name::Name;
use trust_model_prelude::{EP_VERSION, MODULE_ORDER, MODULES, UNMODELED_CODES};
#[cfg(feature = "test-support")]
use trust_spec_temporal::model_prelude::{
    DEFINITE_MISMATCH, HEARTBEAT_EXCEEDED, HEARTBEAT_EXCEEDED_VARIANT, STUCK,
};
use trust_spec_temporal::model_prelude::{
    DoorStatement, MODEL_DECL_BUDGET, ModelPrelude, ModelPreludeError, Rejection,
    check_model_theorem, classify_rejection, elaborate_model_suffix, prelude_added_constants,
    with_model_prelude,
};
use trust_spec_temporal::{
    CLEAN_TEMPORAL_PRELUDE, CleanTemporalCertificateError, FINITE_MODEL_PRELUDE,
};

/// Declarations the model prelude must add to Clean's kernel prelude. Each lane row
/// that adds a module adds its names here.
const EXPECTED_DECLS: &[&str] = &[
    // Trust.Temporal
    "Trust.Temporal.Behavior",
    "Trust.Temporal.Formula",
    "Trust.Temporal.drop",
    "Trust.Temporal.Always",
    "Trust.Temporal.Eventually",
    "Trust.Temporal.LeadsTo",
    "Trust.Temporal.StateMachine",
    "Trust.Temporal.StateMachine.mk",
    "Trust.Temporal.StateMachine.rec",
    "Trust.Temporal.Runs",
    "Trust.Temporal.Enabled",
    "Trust.Temporal.WeakFair",
    "Trust.Temporal.StrongFair",
    "Trust.Temporal.FairnessConstraint",
    "Trust.Temporal.Satisfies",
    // Trust.FiniteModel (namespace Trust.Temporal.FiniteModel)
    "Trust.Temporal.FiniteModel.ScalarExpr",
    "Trust.Temporal.FiniteModel.Model",
    "Trust.Temporal.FiniteModel.ScalarModel.asModel",
    "Trust.Temporal.FiniteModel.Member",
    "Trust.Temporal.FiniteModel.Every",
    "Trust.Temporal.FiniteModel.State",
    "Trust.Temporal.FiniteModel.Value",
    "Trust.Temporal.FiniteModel.StateMachine",
    "Trust.Temporal.FiniteModel.SafetyClaim",
    // Trust.List (namespace Trust.Temporal; B1A-09)
    "Trust.Temporal.Member",
    "Trust.Temporal.Distinct",
    "Trust.Temporal.memBy",
    "Trust.Temporal.lookupBy",
    "Trust.Temporal.nthD",
    "Trust.Temporal.allB",
    "Trust.Temporal.anyB",
    "Trust.Temporal.insertBy",
    "Trust.Temporal.lengthEqB",
    // Trust.Graph (namespace Trust.Temporal; B1A-09, B1A-D05)
    "Trust.Temporal.Terminal",
    "Trust.Temporal.Reach",
    "Trust.Temporal.Reach.init",
    "Trust.Temporal.Reach.step",
    "Trust.Temporal.Reach.rec",
    "Trust.Temporal.Star",
    "Trust.Temporal.Star.refl",
    "Trust.Temporal.Star.tail",
    "Trust.Temporal.Star.rec",
    "Trust.Temporal.MaxPath",
    "Trust.Temporal.Chain",
    "Trust.Temporal.lastOf",
    "Trust.Temporal.FirstAtEnd",
    "Trust.Temporal.WitnessPath",
    // Trust.Model.Value (B1A-10)
    "Trust.Model.InfKind",
    "Trust.Model.Value",
    "Trust.Model.Value.bool",
    "Trust.Model.Value.infSet",
    "Trust.Model.Value.rec",
    "Trust.Model.IntMode",
    "Trust.Model.IntMode.tlc32",
    "Trust.Model.IntMode.unbounded",
    "Trust.Model.Fail",
    "Trust.Model.Fail.overflow",
    "Trust.Model.Fail.assertFailed",
    "Trust.Model.Fail.unmodeled",
    "Trust.Model.Res",
    "Trust.Model.Res.ok",
    "Trust.Model.Res.error",
    "Trust.Model.Res.rec",
    "Trust.Model.State",
    "Trust.Model.Res.bind",
    "Trust.Model.Res.map",
    "Trust.Model.Res.concat",
    "Trust.Model.intBeq",
    "Trust.Model.natAbs",
    "Trust.Model.isNeg",
    "Trust.Model.inRange32",
    "Trust.Model.IntMode.check",
    "Trust.Model.intAdd",
    "Trust.Model.intSub",
    "Trust.Model.intMul",
    "Trust.Model.intNeg",
    "Trust.Model.floorDiv",
    "Trust.Model.floorMod",
    "Trust.Model.isIntMinByNegOne",
    "Trust.Model.intDiv",
    "Trust.Model.intMod",
    "Trust.Model.powNat",
    "Trust.Model.intPow",
    // Trust.Model.Value's order (B1A-11a, B1A-D86)
    "Trust.Model.Code.cmpUnpinned",
    "Trust.Model.natCmp",
    "Trust.Model.intCmp",
    "Trust.Model.boolCmp",
    "Trust.Model.boolBeq",
    "Trust.Model.InfKind.tag",
    "Trust.Model.Value.size",
    "Trust.Model.Value.elim",
    "Trust.Model.Value.asBool",
    "Trust.Model.Value.asInt",
    "Trust.Model.Value.asStr",
    "Trust.Model.Value.asMv",
    "Trust.Model.Value.asTmv",
    "Trust.Model.Value.asSet",
    "Trust.Model.Value.asFn",
    "Trust.Model.Value.asInfSet",
    "Trust.Model.Value.isTmv",
    "Trust.Model.Value.isStr",
    "Trust.Model.strKeys",
    "Trust.Model.fnIsRecord",
    "Trust.Model.unpinnedCmp",
    "Trust.Model.crossCmp",
    "Trust.Model.cmpThen",
    "Trust.Model.cmpListWith",
    "Trust.Model.cmpPairsWith",
    "Trust.Model.tlcCmpF",
    "Trust.Model.tlcCmp",
    "Trust.Model.tlcLt",
    "Trust.Model.beqListWith",
    "Trust.Model.beqPairsWith",
    "Trust.Model.Value.beqF",
    "Trust.Model.Value.beq",
    // Trust.Model.Value's equality and canonical forms (B1A-11b, B1A-D14, B1A-D87)
    "Trust.Model.unpinnedEq",
    "Trust.Model.Value.tag",
    "Trust.Model.mvArgEq",
    "Trust.Model.intArgIncomparable",
    "Trust.Model.eqThen",
    "Trust.Model.eqListWith",
    "Trust.Model.eqPairsWith",
    "Trust.Model.keyEqWith",
    "Trust.Model.valueEqF",
    "Trust.Model.valueEq",
    "Trust.Model.ltOk",
    "Trust.Model.strictInc",
    "Trust.Model.keysOf",
    "Trust.Model.Value.Canon",
    "Trust.Model.listGetD",
    "Trust.Model.listInsertAt",
    "Trust.Model.midOf",
    "Trust.Model.normSearchF",
    "Trust.Model.normInsert",
    "Trust.Model.normSet",
    "Trust.Model.tupleFrom",
    "Trust.Model.mkTuple",
    "Trust.Model.mkSeq",
    "Trust.Model.zipPairs",
    "Trust.Model.mkFn",
    "Trust.Model.rcdInsert",
    "Trust.Model.rcdPairs",
    "Trust.Model.mkRecord",
    "Trust.Model.epVersion",
    // Trust.Model.Syntax (B1A-12, B1A-D10, B1A-D11, B1A-D15, B1A-D89)
    "Trust.Model.QKind",
    "Trust.Model.QKind.qEx",
    "Trust.Model.QKind.qFn",
    "Trust.Model.PrimOp",
    "Trust.Model.PrimOp.intAdd",
    "Trust.Model.PrimOp.recGet",
    "Trust.Model.PrimOp.recNew",
    "Trust.Model.PrimOp.tupleGet",
    "Trust.Model.PrimOp.valueEq",
    "Trust.Model.PrimOp.valueAsBool",
    "Trust.Model.PrimOp.natSuccU",
    "Trust.Model.PrimOp.natSatU",
    "Trust.Model.PrimOp.assert",
    "Trust.Model.Expr",
    "Trust.Model.Expr.lit",
    "Trust.Model.Expr.enabled",
    "Trust.Model.Expr.rec",
    "Trust.Model.Act",
    "Trust.Model.Act.conj",
    "Trust.Model.Act.pchoice",
    "Trust.Model.Act.rec",
    "Trust.Model.Expr.and_",
    "Trust.Model.Expr.or_",
    "Trust.Model.Expr.not_",
    "Trust.Model.Expr.implies_",
    "Trust.Model.Expr.equiv_",
    "Trust.Model.Expr.size",
    "Trust.Model.Act.size",
    "Trust.Model.Expr.mapVar",
    "Trust.Model.Expr.enabledArg",
    "Trust.Model.Act.mapVar",
    "Trust.Model.shiftVar",
    "Trust.Model.Expr.shift",
    "Trust.Model.revOnto",
    "Trust.Model.pickArg",
    "Trust.Model.substVar",
    "Trust.Model.Expr.subst",
    "Trust.Model.Act.subst",
    "Trust.Model.Act.inst",
    // Trust.Model.Spec (B1A-13, B1A-D15, B1A-D16, B1A-D17, B1A-D18, B1A-D43)
    "Trust.Model.FairEntry",
    "Trust.Model.FairEntry.mk",
    "Trust.Model.FairEntry.binders",
    "Trust.Model.FairEntry.sub",
    "Trust.Model.ChoiceMode",
    "Trust.Model.ChoiceMode.none",
    "Trust.Model.ChoiceMode.uniformStates",
    "Trust.Model.Spec",
    "Trust.Model.Spec.mk",
    "Trust.Model.Spec.vars",
    "Trust.Model.Spec.tokens",
    "Trust.Model.Spec.next",
    "Trust.Model.Spec.choice",
    "Trust.Model.Spec.StateWf",
    "Trust.Model.Spec.stateWfB",
    "Trust.Model.QKind.oneBinder",
    "Trust.Model.Expr.foldSites",
    "Trust.Model.Act.foldSites",
    "Trust.Model.Expr.allSites",
    "Trust.Model.Act.allSites",
    "Trust.Model.tagIn",
    "Trust.Model.noTag",
    "Trust.Model.curTags",
    "Trust.Model.stateTags",
    "Trust.Model.Value.ints32",
    "Trust.Model.litOk",
    "Trust.Model.arityAt",
    "Trust.Model.arityIs",
    "Trust.Model.Spec.siteOk",
    "Trust.Model.Spec.exprWf",
    "Trust.Model.Spec.actWf",
    "Trust.Model.FairEntry.wfIn",
    "Trust.Model.Spec.termsWf",
    "Trust.Model.Spec.refSite",
    "Trust.Model.Spec.exprRefs",
    "Trust.Model.Spec.actRefs",
    "Trust.Model.Spec.nodeCount",
    "Trust.Model.Spec.nodeMap",
    "Trust.Model.Spec.adj",
    "Trust.Model.natMax",
    "Trust.Model.depthIn",
    "Trust.Model.dfsChildren",
    "Trust.Model.dfsF",
    "Trust.Model.dfsFrom",
    "Trust.Model.natRange",
    "Trust.Model.Spec.dfs",
    "Trust.Model.Spec.acyclic",
    "Trust.Model.Spec.callDepth",
    "Trust.Model.allFlagged",
    "Trust.Model.Spec.reachFree",
    "Trust.Model.Spec.initPrimed",
    "Trust.Model.Spec.poolConstant",
    "Trust.Model.strBeq",
    "Trust.Model.distinctBy",
    "Trust.Model.Spec.wf",
    "Trust.Model.sumNat",
    "Trust.Model.Spec.size",
    "Trust.Model.Spec.fuel",
    "Trust.Model.Action",
    "Trust.Model.Action.mk",
    "Trust.Model.Action.binders",
    "Trust.Model.Action.body",
    "Trust.Model.Action.toAct",
    "Trust.Model.Action.flat",
    "Trust.Model.Expr.primeFree",
    "Trust.Model.Act.isGuard",
    "Trust.Model.nonGuardSplits",
    "Trust.Model.conjWith",
    "Trust.Model.splitConj",
    "Trust.Model.splitLet",
    "Trust.Model.Act.split",
    "Trust.Model.Spec.actions",
    // Trust.Model.Value additions (B1A-14a, the M0 review's findings 4, 5, 14)
    "Trust.Model.infSetCmp",
    "Trust.Model.keyCmpWith",
    // Trust.Model.Tlc (B1A-14a, B1A-D07, B1A-D21, B1A-D36, B1A-D92)
    "Trust.Model.Ctx",
    "Trust.Model.Ctx.mk",
    "Trust.Model.SetGen",
    "Trust.Model.SetGen.ofVal",
    "Trust.Model.SetGen.subset",
    "Trust.Model.SetGen.fnSet",
    "Trust.Model.SetGen.prod",
    "Trust.Model.SetGen.rcdSet",
    "Trust.Model.SetGen.filter",
    "Trust.Model.XVal",
    "Trust.Model.XVal.val",
    "Trust.Model.XVal.lazyFn",
    "Trust.Model.XVal.fnX",
    "Trust.Model.XVal.lazySet",
    "Trust.Model.Frame",
    "Trust.Model.Ctx.elim",
    "Trust.Model.SetGen.elim",
    "Trust.Model.XVal.elim",
    "Trust.Model.Ctx.env",
    "Trust.Model.Ctx.post",
    "Trust.Model.XVal.isReducible",
    "Trust.Model.keysOfX",
    "Trust.Model.XVal.wfB",
    "Trust.Model.SetGen.wfB",
    "Trust.Model.Ctx.wfB",
    "Trust.Model.XVal.Wf",
    "Trust.Model.SetGen.Wf",
    "Trust.Model.Ctx.Wf",
    "Trust.Model.Tlc.rule.materializeQFn",
    "Trust.Model.Tlc.rule.forceCtorDomains",
    "Trust.Model.Tlc.rule.keepLazyReset",
    "Trust.Model.Tlc.rule.forceAtAssign",
    "Trust.Model.Tlc.rule.eagerFilter",
    "Trust.Model.Tlc.rule.memByForcing",
    "Trust.Model.Job",
    "Trust.Model.Job.evalX",
    "Trust.Model.Job.tlcHoldsF",
    "Trust.Model.Out",
    "Trust.Model.Out.xval",
    "Trust.Model.Out.states",
    "Trust.Model.Tlc.mismatch",
    "Trust.Model.Tlc.todo",
    "Trust.Model.Out.asXVal",
    "Trust.Model.Out.asValue",
    "Trust.Model.Out.asBool",
    "Trust.Model.Out.asNext",
    "Trust.Model.Out.asValues",
    "Trust.Model.Out.asStates",
    "Trust.Model.Tlc.goEvalX",
    "Trust.Model.Tlc.goForce",
    "Trust.Model.Tlc.goApplyX",
    "Trust.Model.Tlc.goMemX",
    "Trust.Model.Tlc.goEnumNext",
    "Trust.Model.Tlc.goEnumAll",
    "Trust.Model.Tlc.goEnumF",
    "Trust.Model.Tlc.goEnabledF",
    "Trust.Model.Tlc.goHoldsF",
    "Trust.Model.Tlc.stepEvalX",
    "Trust.Model.Tlc.stepForce",
    "Trust.Model.Tlc.stepApplyX",
    "Trust.Model.Tlc.stepMemX",
    "Trust.Model.Tlc.stepEnumNext",
    "Trust.Model.Tlc.stepEnumAll",
    "Trust.Model.Tlc.stepEnumF",
    "Trust.Model.Tlc.stepEnabledF",
    "Trust.Model.Tlc.stepHoldsF",
    // B1A-14b: the core evaluation's helpers (Tlc.stepEvalX's cases, B1A-D95).
    "Trust.Model.Tlc.illFormed",
    "Trust.Model.Tlc.nth",
    "Trust.Model.Tlc.at",
    "Trust.Model.XVal.asBool",
    "Trust.Model.Tlc.truth",
    "Trust.Model.Tlc.ifB",
    "Trust.Model.Tlc.domainOf",
    "Trust.Model.Tlc.consEach",
    "Trust.Model.Tlc.contexts",
    "Trust.Model.Tlc.pushAll",
    "Trust.Model.Tlc.evalDomains",
    "Trust.Model.Tlc.oneBinder",
    "Trust.Model.Tlc.bodyAt",
    "Trust.Model.Tlc.exLoop",
    "Trust.Model.Tlc.allLoop",
    "Trust.Model.Tlc.chooseLoop",
    "Trust.Model.Tlc.filterLoop",
    "Trust.Model.Tlc.forcedElem",
    "Trust.Model.Tlc.mapLoop",
    "Trust.Model.Tlc.boolX",
    "Trust.Model.Tlc.quantX",
    "Trust.Model.Tlc.caseX",
    "Trust.Model.Tlc.appX",
    "Trust.Model.Tlc.step",
    "Trust.Model.Tlc.run",
    "Trust.Model.evalX",
    "Trust.Model.force",
    "Trust.Model.applyX",
    "Trust.Model.memX",
    "Trust.Model.enumNext",
    "Trust.Model.enumAll",
    "Trust.Model.tlcEnumF",
    "Trust.Model.tlcEnabledF",
    "Trust.Model.tlcHoldsF",
    // B1A-14b: evaluate, then force (10:299-302).
    "Trust.Model.Frame.ofState",
    "Trust.Model.evalE",
    // B1A-15: the PrimOp evaluator (and Spec.wf's operand-count site, the set-normalization
    // refusal of B1A-D96, the binder-count check).
    "Trust.Model.PrimOp.arityOk",
    "Trust.Model.boolNat",
    "Trust.Model.Fail.deferCmp",
    "Trust.Model.Tlc.normDefer",
    "Trust.Model.Tlc.someBinders",
    "Trust.Model.Prim.typeErr",
    "Trust.Model.Prim.args1",
    "Trust.Model.Prim.args2",
    "Trust.Model.Prim.args3",
    "Trust.Model.Prim.int",
    "Trust.Model.Prim.arith",
    "Trust.Model.Prim.cmp",
    "Trust.Model.Prim.lookup",
    "Trust.Model.Prim.apply",
    "Trust.Model.Prim.replace",
    "Trust.Model.Prim.except",
    "Trust.Model.Prim.seqFrom",
    "Trust.Model.Prim.seq",
    "Trust.Model.Prim.drop",
    "Trust.Model.Prim.take",
    "Trust.Model.Prim.inRange",
    "Trust.Model.Prim.subSeq",
    "Trust.Model.Prim.subSeqV",
    "Trust.Model.Prim.concat",
    "Trust.Model.Prim.removeAt",
    "Trust.Model.Prim.setOf",
    "Trust.Model.Prim.defer",
    "Trust.Model.Prim.memSet",
    "Trust.Model.Prim.allB",
    "Trust.Model.Prim.mvOr",
    "Trust.Model.Prim.memF",
    "Trust.Model.Prim.mem",
    "Trust.Model.Prim.filterM",
    "Trust.Model.Prim.setV",
    // B1A-15 repair round 1: UNION's eagerness test, SetOfFcnsValue.size().
    "Trust.Model.Prim.allSets",
    "Trust.Model.Prim.unions",
    "Trust.Model.Prim.rangeFrom",
    "Trust.Model.Prim.range",
    "Trust.Model.Prim.isInf",
    // B1A-15 repair round 2: set.subseteq's Enumerable test; `Prim.fnOpK` replaces
    // `Prim.isEmptyK` and `Prim.sizeK` (one lookup, no unreachable branch in cardFnSet).
    "Trust.Model.Prim.isFnSet",
    "Trust.Model.Prim.fnOpK",
    "Trust.Model.Prim.cardFnSet",
    "Trust.Model.Prim.card",
    "Trust.Model.Prim.isFinite",
    "Trust.Model.Prim.fields",
    "Trust.Model.Prim.assertMsg",
    "Trust.Model.PrimOp.evalV",
    "Trust.Model.Tlc.evalOps",
    "Trust.Model.Tlc.allVals",
    "Trust.Model.Tlc.opX",
    // B1A-16: laziness I (function constructors, keepLazy, applyX, DOMAIN, EXCEPT, force).
    "Trust.Model.Tlc.rhsX",
    "Trust.Model.Tlc.xOfGen",
    "Trust.Model.Tlc.genOf",
    "Trust.Model.Tlc.gensOf",
    "Trust.Model.Tlc.entryVals",
    "Trust.Model.Tlc.mkFnX",
    "Trust.Model.Tlc.indexX",
    "Trust.Model.Tlc.ctxKey",
    "Trust.Model.Tlc.bodiesAt",
    "Trust.Model.Tlc.insertKey",
    "Trust.Model.Tlc.keyed",
    "Trust.Model.Tlc.setElems",
    "Trust.Model.Tlc.materialize",
    "Trust.Model.Tlc.qFnX",
    "Trust.Model.Tlc.lookupX",
    "Trust.Model.Tlc.replaceX",
    "Trust.Model.Tlc.seqFromX",
    "Trust.Model.Tlc.oneToN",
    "Trust.Model.Tlc.memAll",
    "Trust.Model.Tlc.inDomains",
    "Trust.Model.Tlc.forceDomain",
    "Trust.Model.Tlc.forceDomains",
    "Trust.Model.Tlc.forceVals",
    "Trust.Model.Tlc.lazyTuple",
    "Trust.Model.Tlc.headTail",
    "Trust.Model.Tlc.isFnX",
    "Trust.Model.Tlc.argVal",
    "Trust.Model.Tlc.argE1",
    "Trust.Model.Tlc.argE2",
    "Trust.Model.Tlc.argE3",
    "Trust.Model.Tlc.applyOpX",
    "Trust.Model.Tlc.okEntry",
    "Trust.Model.Tlc.recGetX",
    "Trust.Model.Tlc.domainX",
    "Trust.Model.Tlc.exceptAt",
    "Trust.Model.Tlc.exceptX",
    "Trust.Model.Tlc.headTailX",
    "Trust.Model.Tlc.atPositions",
    "Trust.Model.Tlc.recordX",
    "Trust.Model.Tlc.opLazyX",
];

fn module_names() -> Vec<&'static str> {
    MODULES.iter().map(|(module, _, _)| *module).collect()
}

/// The modules served are this crate's own files, byte for byte: what ty consumes is
/// what this crate certifies (one copy).
#[test]
fn smoke_served_modules_are_this_crates_files() {
    let source = |name: &str| {
        MODULES
            .iter()
            .find(|(module, _, _)| *module == name)
            .map(|(_, _, source)| *source)
            .unwrap_or_else(|| panic!("{name} is not served"))
    };
    assert_eq!(source("Trust.Temporal"), CLEAN_TEMPORAL_PRELUDE);
    assert_eq!(source("Trust.FiniteModel"), FINITE_MODEL_PRELUDE);
    assert_eq!(source("Trust.List"), include_str!("../clean/Trust/List.lean"));
    assert_eq!(source("Trust.Graph"), include_str!("../clean/Trust/Graph.lean"));
    assert_eq!(source("Trust.Model.Value"), include_str!("../clean/Trust/Model/Value.lean"));
    assert_eq!(source("Trust.Model.Syntax"), include_str!("../clean/Trust/Model/Syntax.lean"));
    assert_eq!(source("Trust.Model.Spec"), include_str!("../clean/Trust/Model/Spec.lean"));
    assert_eq!(source("Trust.Model.Tlc"), include_str!("../clean/Trust/Model/Tlc.lean"));
}

/// MODULES is a subsequence of the D50 order, each module's dependencies come before
/// it, and the budget the API arms is finite and enabled.
#[test]
fn smoke_modules_are_in_dependency_order() {
    let names = module_names();
    let mut order = MODULE_ORDER.iter();
    for name in &names {
        assert!(order.any(|ordered| ordered == name), "{name} is out of the B1A-D50 order");
    }
    for (index, (module, deps, _)) in MODULES.iter().enumerate() {
        for dep in *deps {
            assert!(names[..index].contains(dep), "{module} depends on {dep}, served after it");
        }
    }
    assert_eq!(names.first(), Some(&"Trust.Temporal"));
    const { assert!(MODEL_DECL_BUDGET > 0, "a zero budget disables the budget") };
}

/// Every served module elaborates, in order, with no failed declaration, and every
/// one was elaborated under the armed declaration budget (a disabled budget reports
/// zero ticks spent).
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn every_module_elaborates() {
    let (modules, budget) = with_model_prelude(|prelude| {
        (prelude.module_names(), prelude.module_budget_used().to_vec())
    })
    .expect("the model prelude elaborates");
    assert_eq!(modules, module_names());
    for (module, used) in budget {
        println!("module {module}: {used} declaration-budget ticks (budget {MODEL_DECL_BUDGET})");
        assert!(used > 0 && used < MODEL_DECL_BUDGET, "{module} spent {used} budget ticks");
    }
}

/// Nothing the prelude adds is an axiom, or reaches one beyond Clean's canonical
/// foundations.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn no_prelude_constant_has_axiom_deps() {
    let violations = with_model_prelude(|prelude| {
        let environment = prelude.environment();
        let added = prelude_added_constants(environment);
        let mut violations = Vec::new();
        for name in &added {
            if environment.get_const(name).is_some_and(|c| c.kind == ConstantKind::Axiom) {
                violations.push(format!("{name}: is an axiom"));
            }
            match environment.axiom_deps(name) {
                Some(axioms) if axioms.is_empty() => {}
                Some(axioms) => {
                    let mut axioms: Vec<String> = axioms.iter().map(ToString::to_string).collect();
                    axioms.sort();
                    violations.push(format!("{name}: reaches {axioms:?}"));
                }
                None => violations.push(format!("{name}: no axiom closure")),
            }
        }
        (added.len(), violations)
    })
    .expect("the model prelude elaborates");
    assert!(violations.0 >= EXPECTED_DECLS.len(), "only {} constants added", violations.0);
    assert!(violations.1.is_empty(), "{:#?}", violations.1);
}

#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn expected_decls_present() {
    let missing = with_model_prelude(|prelude| {
        let added = prelude_added_constants(prelude.environment());
        EXPECTED_DECLS
            .iter()
            .filter(|name| !added.contains(&Name::from_string(name)))
            .map(|name| (*name).to_owned())
            .collect::<Vec<_>>()
    })
    .expect("the model prelude elaborates");
    assert!(missing.is_empty(), "the model prelude does not add {missing:?}");
}

/// The recursors of the design's mutual Expr/Act (Trust/Model/Syntax.lean, 10:130-161) take
/// twelve motives: one per type of the block plus one per distinct nested instantiation of
/// a block type (List Expr, List (Expr × Expr), Option Expr, List Act, List (Expr × Act),
/// Option Act, List (Nat × Act), Expr × Expr, Expr × Act, Nat × Act), the rule B1A-02b
/// measured on the capability files (B1A-D70; MOTIVES). Their discovery order is the one
/// Syntax.lean's every-motive recursions use: `Expr.mapVar` gives each motive a different
/// type, so another order does not elaborate.
/// B1A-14a adds the executable values Ctx/SetGen/XVal (Trust/Model/Tlc.lean, 10:230-249): ten
/// motives (the three types, then List (Option XVal), List SetGen, List (Nat × SetGen),
/// List (Value × XVal), Option XVal, Nat × SetGen, Value × XVal, the order sanity
/// tlc_skeleton.lean's `motive_order` pins), and the block's plain Job and Out (one each).
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn syntax_recursor_motives() {
    let measured = with_model_prelude(|prelude| {
        [
            "Trust.Model.Expr.rec",
            "Trust.Model.Act.rec",
            "Trust.Model.Value.rec",
            "Trust.Model.Ctx.rec",
            "Trust.Model.SetGen.rec",
            "Trust.Model.XVal.rec",
            "Trust.Model.Job.rec",
            "Trust.Model.Out.rec",
        ]
        .iter()
        .map(|recursor| {
            let motives = prelude
                .environment()
                .get_recursor(&Name::from_string(recursor))
                .map(|recursor| recursor.num_motives);
            ((*recursor).to_owned(), motives)
        })
        .collect::<Vec<_>>()
    })
    .expect("the model prelude elaborates");
    for (recursor, motives) in &measured {
        println!("motives {recursor}: {motives:?}");
    }
    assert_eq!(
        measured,
        vec![
            ("Trust.Model.Expr.rec".to_owned(), Some(12)),
            ("Trust.Model.Act.rec".to_owned(), Some(12)),
            ("Trust.Model.Value.rec".to_owned(), Some(4)),
            ("Trust.Model.Ctx.rec".to_owned(), Some(10)),
            ("Trust.Model.SetGen.rec".to_owned(), Some(10)),
            ("Trust.Model.XVal.rec".to_owned(), Some(10)),
            ("Trust.Model.Job.rec".to_owned(), Some(1)),
            ("Trust.Model.Out.rec".to_owned(), Some(1)),
        ]
    );
}

/// `Trust.Model.epVersion` is `EP_VERSION`, through a Bool door the acceptance path
/// takes; the wrong literal is refused, and the acceptance path refuses what is not
/// a theorem.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn ep_version_door() {
    let (door, wrong, not_theorem, missing) = with_model_prelude(|mut prelude| {
        let door = elaborate_model_suffix(
            &mut prelude,
            &format!("theorem epVersion_door : Nat.beq Trust.Model.epVersion {EP_VERSION} = true := rfl\n"),
            "epVersion door",
        )
        .and_then(|()| check_model_theorem(prelude.environment(), "epVersion_door"));
        let wrong = elaborate_model_suffix(
            &mut prelude,
            &format!(
                "theorem epVersion_door_wrong : Nat.beq Trust.Model.epVersion {} = true := rfl\n",
                EP_VERSION + 1
            ),
            "wrong epVersion door",
        )
        .and_then(|()| check_model_theorem(prelude.environment(), "epVersion_door_wrong"));
        let not_theorem = check_model_theorem(prelude.environment(), "Trust.Model.epVersion");
        let missing = check_model_theorem(prelude.environment(), "noSuchTheorem");
        (door, wrong, not_theorem, missing)
    })
    .expect("the model prelude elaborates");
    assert_eq!(door, Ok(()));
    assert!(matches!(wrong, Err(ModelPreludeError::Clean(_))), "{wrong:?}");
    assert_eq!(
        not_theorem,
        Err(ModelPreludeError::Clean(CleanTemporalCertificateError::NotTheorem(
            "Trust.Model.epVersion".to_owned()
        )))
    );
    assert_eq!(
        missing,
        Err(ModelPreludeError::Clean(CleanTemporalCertificateError::MissingTheorem(
            "noSuchTheorem".to_owned()
        )))
    );
}

/// trust-model-prelude's `UNMODELED_CODES` mirror agrees with the kernel (B1A-D13):
/// every mirrored `Trust.Model.Code.*` constant holds its mirrored number (a Bool door
/// accepted by `check_model_theorem`, its `number + 1` mutant refuted as Definite), and
/// the prelude adds no `Trust.Model.Code.*` constant the mirror does not list. The unit
/// test `tests::unmodeled_codes_mirror_the_lean_table` checks the same table on the source
/// text.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn unmodeled_codes_are_kernel_values() {
    assert!(!UNMODELED_CODES.is_empty());
    let failures = with_model_prelude(|prelude| {
        let mut failures: Vec<String> = Vec::new();
        let mut in_kernel: Vec<String> = prelude_added_constants(prelude.environment())
            .iter()
            .map(ToString::to_string)
            .filter(|name| name.starts_with("Trust.Model.Code."))
            .collect();
        in_kernel.sort();
        let mut mirrored: Vec<String> =
            UNMODELED_CODES.iter().map(|entry| entry.lean.to_owned()).collect();
        mirrored.sort();
        if in_kernel != mirrored {
            failures.push(format!("kernel codes {in_kernel:?}, mirror {mirrored:?}"));
        }
        for (index, entry) in UNMODELED_CODES.iter().enumerate() {
            let door = format!("Nat.beq {} {}", entry.lean, entry.number);
            let statement = DoorStatement { namespace: "Trust.Model", binders: "", door: &door };
            let (result, _) = try_door(&prelude, &statement, &format!("code_door_{index}"));
            if let Err(error) = result {
                failures.push(format!("{}: door `{door}` refused: {error}", entry.code));
            }
            let mutant = format!("Nat.beq {} {}", entry.lean, entry.number + 1);
            let statement = DoorStatement { namespace: "Trust.Model", binders: "", door: &mutant };
            let (result, class) = try_door(&prelude, &statement, &format!("code_mutant_{index}"));
            if class != Some(Rejection::Definite) {
                failures.push(format!(
                    "{}: mutant `{mutant}` class {class:?}, expected Definite: {result:?}",
                    entry.code
                ));
            }
        }
        failures
    })
    .expect("the model prelude elaborates");
    assert!(failures.is_empty(), "unmodeled codes:\n{}", failures.join("\n"));
}

/// An ill-typed extra module is refused, and so is an authored parser extension.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn ill_typed_extra_module_is_refused() {
    let (ill_typed, extension) = with_model_prelude(|mut prelude| {
        let ill_typed = elaborate_model_suffix(
            &mut prelude,
            "namespace Trust\nnamespace Model\ndef illTypedExtra : Nat := true\nend Model\nend Trust\n",
            "ill-typed extra module",
        );
        let extension = elaborate_model_suffix(
            &mut prelude,
            "notation:65 a \" +++ \" b => Nat.add a b\n",
            "parser extension",
        );
        (ill_typed, extension)
    })
    .expect("the model prelude elaborates");
    assert!(
        matches!(
            ill_typed,
            Err(ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate {
                unit: "ill-typed extra module",
                ..
            }))
        ),
        "{ill_typed:?}"
    );
    assert_eq!(
        extension,
        Err(ModelPreludeError::Clean(CleanTemporalCertificateError::ForbiddenParserExtension {
            declaration: "notation"
        }))
    );
}

/// Restores the thread's declaration budget to disabled, unwinding included, so a
/// pooled worker never carries this test's budget into another job.
struct OuterBudget;

impl OuterBudget {
    fn arm(limit: u64) -> Self {
        clean_kernel::tc::set_declaration_budget(limit);
        Self
    }
}

impl Drop for OuterBudget {
    fn drop(&mut self) {
        clean_kernel::tc::clear_declaration_budget();
    }
}

/// A budget that runs out is `BudgetExhausted`, never a pass and never a refutation:
/// under a one-tick budget armed by the caller (which the API leaves in charge), a
/// door that passes unbudgeted is neither accepted nor refuted, for elaboration and
/// for the theorem check alike.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn an_exhausted_budget_is_neither_pass_nor_refutation() {
    let (unbudgeted, starved_check, starved_suffix, after) = with_model_prelude(|mut prelude| {
        let door = "theorem starvedDoor : Nat.beq Trust.Model.epVersion 1 = true := rfl\n";
        let unbudgeted = elaborate_model_suffix(&mut prelude, door, "door")
            .and_then(|()| check_model_theorem(prelude.environment(), "starvedDoor"));
        let starved_check = {
            let _outer = OuterBudget::arm(1);
            check_model_theorem(prelude.environment(), "starvedDoor")
        };
        let starved_suffix = {
            let _outer = OuterBudget::arm(1);
            elaborate_model_suffix(
                &mut prelude,
                "theorem starvedSuffix : Nat.beq 2 2 = true := rfl\n",
                "starved suffix",
            )
        };
        let after = clean_kernel::tc::declaration_budget_limit();
        (unbudgeted, starved_check, starved_suffix, after)
    })
    .expect("the model prelude elaborates");
    assert_eq!(unbudgeted, Ok(()));
    assert_eq!(
        starved_check,
        Err(ModelPreludeError::BudgetExhausted { unit: "starvedDoor".to_owned(), limit: 1 })
    );
    assert_eq!(
        starved_suffix,
        Err(ModelPreludeError::BudgetExhausted { unit: "starved suffix".to_owned(), limit: 1 })
    );
    assert_eq!(after, 0, "the budget leaked out of the API call");
}

/// The sanity files, `tests/model_prelude/sanity/<topic>.lean` (TASK-STATE section 10: each
/// encoding row adds one), with the theorems each must declare, sorted. The directory
/// holds exactly these files.
const SANITY: &[(&str, &str, &[&str])] = &[
    (
        "list_graph",
        include_str!("model_prelude/sanity/list_graph.lean"),
        &[
            "Trust.Temporal.Sanity.allB_false",
            "Trust.Temporal.Sanity.allB_nil",
            "Trust.Temporal.Sanity.allB_true",
            "Trust.Temporal.Sanity.anyB_false",
            "Trust.Temporal.Sanity.anyB_nil",
            "Trust.Temporal.Sanity.anyB_true",
            "Trust.Temporal.Sanity.chain_cons",
            "Trust.Temporal.Sanity.chain_counter",
            "Trust.Temporal.Sanity.chain_nil",
            "Trust.Temporal.Sanity.counter_not_terminal",
            "Trust.Temporal.Sanity.distinct_cons",
            "Trust.Temporal.Sanity.distinct_nil",
            "Trust.Temporal.Sanity.distinct_one_two",
            "Trust.Temporal.Sanity.false_ne_true",
            "Trust.Temporal.Sanity.firstAtEnd_cons",
            "Trust.Temporal.Sanity.firstAtEnd_counter",
            "Trust.Temporal.Sanity.firstAtEnd_nil",
            "Trust.Temporal.Sanity.halted_terminal",
            "Trust.Temporal.Sanity.insertBy_new",
            "Trust.Temporal.Sanity.insertBy_new_door",
            "Trust.Temporal.Sanity.insertBy_present",
            "Trust.Temporal.Sanity.insertBy_present_door",
            "Trust.Temporal.Sanity.lastOf_cons",
            "Trust.Temporal.Sanity.lastOf_door",
            "Trust.Temporal.Sanity.lastOf_nil",
            "Trust.Temporal.Sanity.lastOf_nil_door",
            "Trust.Temporal.Sanity.lengthEqB_equal",
            "Trust.Temporal.Sanity.lengthEqB_longer",
            "Trust.Temporal.Sanity.lengthEqB_nil",
            "Trust.Temporal.Sanity.lengthEqB_shorter",
            "Trust.Temporal.Sanity.lookupBy_first",
            "Trust.Temporal.Sanity.lookupBy_miss",
            "Trust.Temporal.Sanity.lookupBy_nil",
            "Trust.Temporal.Sanity.maxPath_counter",
            "Trust.Temporal.Sanity.maxPath_halted",
            "Trust.Temporal.Sanity.memBy_hit",
            "Trust.Temporal.Sanity.memBy_miss",
            "Trust.Temporal.Sanity.memBy_nil",
            "Trust.Temporal.Sanity.member_alias",
            "Trust.Temporal.Sanity.member_every",
            "Trust.Temporal.Sanity.member_from_finite_model",
            "Trust.Temporal.Sanity.member_head",
            "Trust.Temporal.Sanity.member_tail",
            "Trust.Temporal.Sanity.member_to_finite_model",
            "Trust.Temporal.Sanity.not_distinct_one_one",
            "Trust.Temporal.Sanity.not_member_nil",
            "Trust.Temporal.Sanity.not_member_one",
            "Trust.Temporal.Sanity.nthD_last",
            "Trust.Temporal.Sanity.nthD_nil",
            "Trust.Temporal.Sanity.nthD_one",
            "Trust.Temporal.Sanity.nthD_past",
            "Trust.Temporal.Sanity.nthD_zero",
            "Trust.Temporal.Sanity.reach_two",
            "Trust.Temporal.Sanity.star_zero_two",
            "Trust.Temporal.Sanity.terminal_def",
            "Trust.Temporal.Sanity.true_ne_false",
            "Trust.Temporal.Sanity.witnessPath_def",
            "Trust.Temporal.Sanity.witness_counter",
        ],
    ),
    (
        "value_core",
        include_str!("model_prelude/sanity/value_core.lean"),
        &[
            "Trust.Model.Sanity.bind_error",
            "Trust.Model.Sanity.codes_distinct",
            "Trust.Model.Sanity.concat_first_error",
            "Trust.Model.Sanity.concat_length",
            "Trust.Model.Sanity.concat_nil",
            "Trust.Model.Sanity.concat_order",
            "Trust.Model.Sanity.div_exact_neg",
            "Trust.Model.Sanity.div_min_neg_one_unbounded_is_not_the_refusal",
            "Trust.Model.Sanity.div_pos_neg_exact",
            "Trust.Model.Sanity.div_pos_pos",
            "Trust.Model.Sanity.div_zero_dividend_neg_divisor",
            "Trust.Model.Sanity.epVersion_one",
            "Trust.Model.Sanity.map_error",
            "Trust.Model.Sanity.map_ok",
            "Trust.Model.Sanity.mod_exact_neg",
            "Trust.Model.Sanity.mod_pos",
            "Trust.Model.Sanity.pow_large_exponent",
            "Trust.Model.Sanity.pow_neg_one_even",
            "Trust.Model.Sanity.pow_neg_one_odd",
            "Trust.Model.Sanity.pow_neg_two_31",
            "Trust.Model.Sanity.pow_one_large",
            "Trust.Model.Sanity.pow_two_30",
            "Trust.Model.Sanity.pow_zero_exponent",
            "Trust.Model.Sanity.pow_zero_pos",
            "Trust.Model.Sanity.pow_zero_zero",
            "Trust.Model.Sanity.probe_IntAddMax",
            "Trust.Model.Sanity.probe_IntAddMaxExact",
            "Trust.Model.Sanity.probe_IntAddMin",
            "Trust.Model.Sanity.probe_IntDivMinNegOne",
            "Trust.Model.Sanity.probe_IntDivMinNegTwo",
            "Trust.Model.Sanity.probe_IntDivMinThree",
            "Trust.Model.Sanity.probe_IntDivMinTwo",
            "Trust.Model.Sanity.probe_IntDivNegNeg",
            "Trust.Model.Sanity.probe_IntDivNegPos",
            "Trust.Model.Sanity.probe_IntDivPosNeg",
            "Trust.Model.Sanity.probe_IntDivZero",
            "Trust.Model.Sanity.probe_IntLitNegMin",
            "Trust.Model.Sanity.probe_IntLitOutOfRange",
            "Trust.Model.Sanity.probe_IntModMinNegOne",
            "Trust.Model.Sanity.probe_IntModMinNegTwo",
            "Trust.Model.Sanity.probe_IntModMinThree",
            "Trust.Model.Sanity.probe_IntModMinTwo",
            "Trust.Model.Sanity.probe_IntModNeg",
            "Trust.Model.Sanity.probe_IntModNegDivisor",
            "Trust.Model.Sanity.probe_IntModZeroDivisor",
            "Trust.Model.Sanity.probe_IntMulMinExact",
            "Trust.Model.Sanity.probe_IntMulMinNegOne",
            "Trust.Model.Sanity.probe_IntMulNegOverflow",
            "Trust.Model.Sanity.probe_IntMulPosOverflow",
            "Trust.Model.Sanity.probe_IntNegMin",
            "Trust.Model.Sanity.probe_IntPowNegExp",
            "Trust.Model.Sanity.probe_IntPowOverflow",
            "Trust.Model.Sanity.probe_IntSubMaxNegOne",
            "Trust.Model.Sanity.probe_IntSubMin",
            "Trust.Model.Sanity.probe_IntSubMinExact",
            "Trust.Model.Sanity.range_below_min",
            "Trust.Model.Sanity.range_max",
            "Trust.Model.Sanity.range_min",
            "Trust.Model.Sanity.unbounded_add",
            "Trust.Model.Sanity.unbounded_div_min",
            "Trust.Model.Sanity.unbounded_div_zero",
            "Trust.Model.Sanity.unbounded_mod_neg",
            "Trust.Model.Sanity.unbounded_pow",
        ],
    ),
    (
        "value_eq",
        include_str!("model_prelude/sanity/value_eq.lean"),
        &[
            "Trust.Model.Sanity.builders_fn",
            "Trust.Model.Sanity.builders_record",
            "Trust.Model.Sanity.builders_tuple_seq",
            "Trust.Model.Sanity.canon_fn_keys",
            "Trust.Model.Sanity.canon_no_range_bound",
            "Trust.Model.Sanity.canon_of_normSet",
            "Trust.Model.Sanity.canon_recursive",
            "Trust.Model.Sanity.canon_sets",
            "Trust.Model.Sanity.cross_kind_unpinned",
            "Trust.Model.Sanity.eq_fuel_runs_out_only_below_size",
            "Trust.Model.Sanity.fn_deep_equal",
            "Trust.Model.Sanity.fn_key_kinds_unpinned",
            "Trust.Model.Sanity.fn_keys_before_values",
            "Trust.Model.Sanity.fn_kinds_still_compared",
            "Trust.Model.Sanity.fn_record_guard",
            "Trust.Model.Sanity.fn_size_first",
            "Trust.Model.Sanity.fn_values",
            "Trust.Model.Sanity.infSet_unpinned",
            "Trust.Model.Sanity.infSet_vs_mv",
            "Trust.Model.Sanity.mv_against_other_kinds",
            "Trust.Model.Sanity.normSet_errors",
            "Trust.Model.Sanity.normSet_singleton",
            "Trust.Model.Sanity.normSet_sorts_and_dedupes",
            "Trust.Model.Sanity.probe_CStrEqInt",
            "Trust.Model.Sanity.probe_CTmvInt",
            "Trust.Model.Sanity.probe_ChooseOrderInt",
            "Trust.Model.Sanity.probe_ChooseOrderStr",
            "Trust.Model.Sanity.probe_EnMemberBoundErr",
            "Trust.Model.Sanity.probe_ModelValueIntVsMv",
            "Trust.Model.Sanity.probe_ModelValueIntVsTmv",
            "Trust.Model.Sanity.probe_ModelValueMvSetOrder",
            "Trust.Model.Sanity.probe_ModelValueMvVsInt",
            "Trust.Model.Sanity.probe_ModelValueMvVsStr",
            "Trust.Model.Sanity.probe_ModelValueMvVsTmv",
            "Trust.Model.Sanity.probe_ModelValueStrVsMv",
            "Trust.Model.Sanity.probe_ModelValueStrVsTmv",
            "Trust.Model.Sanity.probe_ModelValueTmvDiffType",
            "Trust.Model.Sanity.probe_ModelValueTmvSameType",
            "Trust.Model.Sanity.probe_ModelValueTmvVsInt",
            "Trust.Model.Sanity.probe_ModelValueTmvVsMv",
            "Trust.Model.Sanity.probe_ModelValueTmvVsStr",
            "Trust.Model.Sanity.scalars_equal",
            "Trust.Model.Sanity.set_element_errors",
            "Trust.Model.Sanity.set_elementwise",
            "Trust.Model.Sanity.set_first_false_wins",
            "Trust.Model.Sanity.set_size_first",
            "Trust.Model.Sanity.str_never_mv",
            "Trust.Model.Sanity.tmv_against_non_model",
        ],
    ),
    (
        "syntax",
        include_str!("model_prelude/sanity/syntax.lean"),
        &[
            "Trust.Model.Sanity.act_subst_letA",
            "Trust.Model.Sanity.and_truth_table",
            "Trust.Model.Sanity.capture_bound_actual",
            "Trust.Model.Sanity.capture_not_bvar0",
            "Trust.Model.Sanity.capture_state_var",
            "Trust.Model.Sanity.equiv_truth_table",
            "Trust.Model.Sanity.implies_truth_table",
            "Trust.Model.Sanity.inst_one",
            "Trust.Model.Sanity.inst_two",
            "Trust.Model.Sanity.inst_under_ex",
            "Trust.Model.Sanity.mapVar_every_constructor",
            "Trust.Model.Sanity.mapVar_locals_stay",
            "Trust.Model.Sanity.naive_equiv_differs",
            "Trust.Model.Sanity.not_truth_table",
            "Trust.Model.Sanity.or_truth_table",
            "Trust.Model.Sanity.shift_cutoff",
            "Trust.Model.Sanity.shift_free_only",
            "Trust.Model.Sanity.size_facts",
            "Trust.Model.Sanity.size_literal",
            "Trust.Model.Sanity.subst_bound_actual_under_let",
            "Trust.Model.Sanity.subst_lowers_outer",
            "Trust.Model.Sanity.subst_parameter_order",
            "Trust.Model.Sanity.subst_under_two_binders",
        ],
    ),
    (
        "spec",
        include_str!("model_prelude/sanity/spec.lean"),
        &[
            "Trust.Model.Sanity.conj_empty_disj_stays",
            "Trust.Model.Sanity.conj_guard_descends",
            "Trust.Model.Sanity.conj_keeps_inner_ex",
            "Trust.Model.Sanity.conj_no_descent",
            "Trust.Model.Sanity.disj_flattens_in_order",
            "Trust.Model.Sanity.ex_over_disj_one_action",
            "Trust.Model.Sanity.fuel_chain",
            "Trust.Model.Sanity.fuel_diamond_depth",
            "Trust.Model.Sanity.fuel_petri",
            "Trust.Model.Sanity.letA_descends",
            "Trust.Model.Sanity.no_descent_through_app_or_call",
            "Trust.Model.Sanity.other_forms_one_action",
            "Trust.Model.Sanity.petri_toAct",
            "Trust.Model.Sanity.petri_two_actions_in_order",
            "Trust.Model.Sanity.stateWf_decider",
            "Trust.Model.Sanity.wf_controls",
            "Trust.Model.Sanity.wf_fairness_scopes",
            "Trust.Model.Sanity.wf_rejects_bad_indices",
            "Trust.Model.Sanity.wf_rejects_cur_in_init",
            "Trust.Model.Sanity.wf_rejects_cycles_across_kinds",
            "Trust.Model.Sanity.wf_rejects_cyclic_defs",
            "Trust.Model.Sanity.wf_rejects_duplicate_tokens",
            "Trust.Model.Sanity.wf_rejects_noncanonical_literal",
            "Trust.Model.Sanity.wf_rejects_out_of_range_literal",
            "Trust.Model.Sanity.wf_rejects_state_in_pool",
        ],
    ),
    (
        "tlc_core",
        include_str!("model_prelude/sanity/tlc_core.lean"),
        &[
            "Trust.Model.Sanity.core_app",
            "Trust.Model.Sanity.core_body_not_boolean",
            "Trust.Model.Sanity.core_bound_not_a_set",
            "Trust.Model.Sanity.core_case",
            "Trust.Model.Sanity.core_case_errors",
            "Trust.Model.Sanity.core_choose",
            "Trust.Model.Sanity.core_context_order",
            "Trust.Model.Sanity.core_domains_first",
            "Trust.Model.Sanity.core_evalE",
            "Trust.Model.Sanity.core_ex_all",
            "Trust.Model.Sanity.core_filter",
            "Trust.Model.Sanity.core_fuel",
            "Trust.Model.Sanity.core_ill_formed",
            "Trust.Model.Sanity.core_ite",
            "Trust.Model.Sanity.core_leaves",
            "Trust.Model.Sanity.core_let",
            "Trust.Model.Sanity.core_let_capture",
            "Trust.Model.Sanity.core_map",
            "Trust.Model.Sanity.core_map_lazy_element",
            "Trust.Model.Sanity.core_nxt",
            "Trust.Model.Sanity.core_pending",
            "Trust.Model.Sanity.core_pool",
            "Trust.Model.Sanity.core_wf_one_binder",
        ],
    ),
    (
        "primops",
        include_str!("model_prelude/sanity/primops.lean"),
        &[
            "Trust.Model.Sanity.and_truth_table",
            "Trust.Model.Sanity.equiv_truth_table",
            "Trust.Model.Sanity.implies_truth_table",
            "Trust.Model.Sanity.mem_fn_set",
            "Trust.Model.Sanity.mem_nat_int_string",
            "Trust.Model.Sanity.mem_seq",
            "Trust.Model.Sanity.naive_equiv_differs",
            "Trust.Model.Sanity.not_truth_table",
            "Trust.Model.Sanity.op_assert",
            "Trust.Model.Sanity.op_funcApply",
            "Trust.Model.Sanity.op_funcDomain",
            "Trust.Model.Sanity.op_funcExcept",
            "Trust.Model.Sanity.op_funcSet",
            "Trust.Model.Sanity.op_intAdd",
            "Trust.Model.Sanity.op_intDiv",
            "Trust.Model.Sanity.op_intGe",
            "Trust.Model.Sanity.op_intGt",
            "Trust.Model.Sanity.op_intLe",
            "Trust.Model.Sanity.op_intLt",
            "Trust.Model.Sanity.op_intMod",
            "Trust.Model.Sanity.op_intMul",
            "Trust.Model.Sanity.op_intNeg",
            "Trust.Model.Sanity.op_intPow",
            "Trust.Model.Sanity.op_intSub",
            "Trust.Model.Sanity.op_natSatU",
            "Trust.Model.Sanity.op_natSuccU",
            "Trust.Model.Sanity.op_recGet",
            "Trust.Model.Sanity.op_recNew",
            "Trust.Model.Sanity.op_recSetOf",
            "Trust.Model.Sanity.op_recWith",
            "Trust.Model.Sanity.op_seqAppend",
            "Trust.Model.Sanity.op_seqConcat",
            "Trust.Model.Sanity.op_seqHead",
            "Trust.Model.Sanity.op_seqIndex",
            "Trust.Model.Sanity.op_seqLen",
            "Trust.Model.Sanity.op_seqRemoveAt",
            "Trust.Model.Sanity.op_seqSet",
            "Trust.Model.Sanity.op_seqSubseq",
            "Trust.Model.Sanity.op_seqTail",
            "Trust.Model.Sanity.op_setBigUnion",
            "Trust.Model.Sanity.op_setCard",
            "Trust.Model.Sanity.op_setDiff",
            "Trust.Model.Sanity.op_setEnum",
            "Trust.Model.Sanity.op_setIn",
            "Trust.Model.Sanity.op_setInsert",
            "Trust.Model.Sanity.op_setIntersect",
            "Trust.Model.Sanity.op_setIsFinite",
            "Trust.Model.Sanity.op_setPowerset",
            "Trust.Model.Sanity.op_setProduct",
            "Trust.Model.Sanity.op_setRange",
            "Trust.Model.Sanity.op_setSubseteq",
            "Trust.Model.Sanity.op_setUnion",
            "Trust.Model.Sanity.op_tupleGet",
            "Trust.Model.Sanity.op_tupleNew",
            "Trust.Model.Sanity.op_valueAsBool",
            "Trust.Model.Sanity.op_valueEq",
            "Trust.Model.Sanity.op_valueNe",
            "Trust.Model.Sanity.or_truth_table",
            "Trust.Model.Sanity.prim_ill_formed",
            "Trust.Model.Sanity.prim_lazy_operand_pending",
            "Trust.Model.Sanity.probe_IntAddMax",
            "Trust.Model.Sanity.probe_IntAddMaxExact",
            "Trust.Model.Sanity.probe_IntAddMin",
            "Trust.Model.Sanity.probe_IntDivMinNegOne",
            "Trust.Model.Sanity.probe_IntDivMinNegTwo",
            "Trust.Model.Sanity.probe_IntDivMinThree",
            "Trust.Model.Sanity.probe_IntDivMinTwo",
            "Trust.Model.Sanity.probe_IntDivNegNeg",
            "Trust.Model.Sanity.probe_IntDivNegPos",
            "Trust.Model.Sanity.probe_IntDivPosNeg",
            "Trust.Model.Sanity.probe_IntDivZero",
            "Trust.Model.Sanity.probe_IntLitNegMin",
            "Trust.Model.Sanity.probe_IntLitOutOfRange",
            "Trust.Model.Sanity.probe_IntModMinNegOne",
            "Trust.Model.Sanity.probe_IntModMinNegTwo",
            "Trust.Model.Sanity.probe_IntModMinThree",
            "Trust.Model.Sanity.probe_IntModMinTwo",
            "Trust.Model.Sanity.probe_IntModNeg",
            "Trust.Model.Sanity.probe_IntModNegDivisor",
            "Trust.Model.Sanity.probe_IntModZeroDivisor",
            "Trust.Model.Sanity.probe_IntMulMinExact",
            "Trust.Model.Sanity.probe_IntMulMinNegOne",
            "Trust.Model.Sanity.probe_IntMulNegOverflow",
            "Trust.Model.Sanity.probe_IntMulPosOverflow",
            "Trust.Model.Sanity.probe_IntNegMin",
            "Trust.Model.Sanity.probe_IntPowNegExp",
            "Trust.Model.Sanity.probe_IntPowOverflow",
            "Trust.Model.Sanity.probe_IntSubMaxNegOne",
            "Trust.Model.Sanity.probe_IntSubMin",
            "Trust.Model.Sanity.probe_IntSubMinExact",
            "Trust.Model.Sanity.probe_PIntCmp",
            "Trust.Model.Sanity.quant_fn_set_pending",
            "Trust.Model.Sanity.set_of_all_defers",
        ],
    ),
    (
        "tlc_skeleton",
        include_str!("model_prelude/sanity/tlc_skeleton.lean"),
        &[
            "Trust.Model.Sanity.block_applyX",
            "Trust.Model.Sanity.block_enumAll",
            "Trust.Model.Sanity.block_enumNext",
            "Trust.Model.Sanity.block_evalX",
            "Trust.Model.Sanity.block_force",
            "Trust.Model.Sanity.block_memX",
            "Trust.Model.Sanity.block_mismatch_is_fuel",
            "Trust.Model.Sanity.block_projection_passes",
            "Trust.Model.Sanity.block_tlcEnabledF",
            "Trust.Model.Sanity.block_tlcEnumF",
            "Trust.Model.Sanity.block_tlcHoldsF",
            "Trust.Model.Sanity.ctx_projections",
            "Trust.Model.Sanity.motive_order",
            "Trust.Model.Sanity.rule_eagerFilter",
            "Trust.Model.Sanity.rule_forceAtAssign",
            "Trust.Model.Sanity.rule_forceCtorDomains",
            "Trust.Model.Sanity.rule_keepLazyReset",
            "Trust.Model.Sanity.rule_materializeQFn",
            "Trust.Model.Sanity.rule_memByForcing",
            "Trust.Model.Sanity.wf_ctx",
            "Trust.Model.Sanity.wf_fnX",
            "Trust.Model.Sanity.wf_lazyFn",
            "Trust.Model.Sanity.wf_setGen",
            "Trust.Model.Sanity.wf_val",
        ],
    ),
    (
        "value_order",
        include_str!("model_prelude/sanity/value_order.lean"),
        &[
            "Trust.Model.Sanity.beq_ModelValueMvVsInt",
            "Trust.Model.Sanity.beq_ModelValueMvVsTmv",
            "Trust.Model.Sanity.beq_ModelValueStrVsMv",
            "Trust.Model.Sanity.beq_ModelValueTmvSameType",
            "Trust.Model.Sanity.beq_deep_leaf_differs",
            "Trust.Model.Sanity.beq_deep_reflexive",
            "Trust.Model.Sanity.beq_fuel_zero",
            "Trust.Model.Sanity.beq_shapes",
            "Trust.Model.Sanity.bool_order",
            "Trust.Model.Sanity.cross_kind_unpinned",
            "Trust.Model.Sanity.fn_deep_equal",
            "Trust.Model.Sanity.fn_keys_before_values",
            "Trust.Model.Sanity.fn_keys_of_two_kinds",
            "Trust.Model.Sanity.fn_kinds_still_ordered",
            "Trust.Model.Sanity.fn_size_first",
            "Trust.Model.Sanity.fn_values",
            "Trust.Model.Sanity.fuel_runs_out_only_below_size",
            "Trust.Model.Sanity.infSet_unpinned",
            "Trust.Model.Sanity.int_order",
            "Trust.Model.Sanity.probe_ChooseOrderInt",
            "Trust.Model.Sanity.probe_ChooseOrderStr",
            "Trust.Model.Sanity.probe_ModelValueIntVsMv",
            "Trust.Model.Sanity.probe_ModelValueIntVsTmv",
            "Trust.Model.Sanity.probe_ModelValueMvSetOrder",
            "Trust.Model.Sanity.probe_ModelValueMvVsInt",
            "Trust.Model.Sanity.probe_ModelValueMvVsStr",
            "Trust.Model.Sanity.probe_ModelValueMvVsTmv",
            "Trust.Model.Sanity.probe_ModelValueStrVsMv",
            "Trust.Model.Sanity.probe_ModelValueStrVsTmv",
            "Trust.Model.Sanity.probe_ModelValueTmvDiffType",
            "Trust.Model.Sanity.probe_ModelValueTmvSameType",
            "Trust.Model.Sanity.probe_ModelValueTmvVsInt",
            "Trust.Model.Sanity.probe_ModelValueTmvVsMv",
            "Trust.Model.Sanity.probe_ModelValueTmvVsStr",
            "Trust.Model.Sanity.probe_MvCompound",
            "Trust.Model.Sanity.probe_MvInfSets",
            "Trust.Model.Sanity.probe_MvScalars",
            "Trust.Model.Sanity.probe_RecEmpty",
            "Trust.Model.Sanity.probe_RecFcn",
            "Trust.Model.Sanity.probe_RecTup",
            "Trust.Model.Sanity.probe_RecTupSame",
            "Trust.Model.Sanity.probe_TmvInt",
            "Trust.Model.Sanity.probe_TmvMv",
            "Trust.Model.Sanity.probe_TmvNat",
            "Trust.Model.Sanity.record_names_by_rank",
            "Trust.Model.Sanity.set_cardinality_first",
            "Trust.Model.Sanity.set_element_error",
            "Trust.Model.Sanity.set_elementwise",
            "Trust.Model.Sanity.set_empty",
            "Trust.Model.Sanity.set_first_difference_wins",
            "Trust.Model.Sanity.set_nested",
            "Trust.Model.Sanity.size_counts_parts",
            "Trust.Model.Sanity.str_mv_rank_order",
            "Trust.Model.Sanity.tlcLt_error",
            "Trust.Model.Sanity.tlcLt_values",
            "Trust.Model.Sanity.tmv_against_other_kinds",
        ],
    ),
    (
        "lazy_fn",
        include_str!("model_prelude/sanity/lazy_fn.lean"),
        &[
            "Trust.Model.Sanity.lazy_apply",
            "Trust.Model.Sanity.lazy_apply_control",
            "Trust.Model.Sanity.lazy_ctor",
            "Trust.Model.Sanity.lazy_dead_branch_tuple",
            "Trust.Model.Sanity.lazy_domain",
            "Trust.Model.Sanity.lazy_except",
            "Trust.Model.Sanity.lazy_except_refused",
            "Trust.Model.Sanity.lazy_force",
            "Trust.Model.Sanity.lazy_head_tail",
            "Trust.Model.Sanity.lazy_nat_domain",
            "Trust.Model.Sanity.lazy_pending",
            "Trust.Model.Sanity.lazy_pool",
            "Trust.Model.Sanity.lazy_rec_get",
            "Trust.Model.Sanity.lazy_tuple",
            "Trust.Model.Sanity.lazy_tuple_clear",
            "Trust.Model.Sanity.lazy_tuple_keep",
        ],
    ),
];

/// Mutated-literal doors over a sanity file's definitions: `(file, namespace, door)`, each
/// a closed Bool door that is false, so it must be refused with class Definite (its
/// complement kernel-checked, B1A-D54). They show the sanity doors compute the stated
/// values rather than passing vacuously.
const SANITY_MUTANTS: &[(&str, &str, &str)] = &[
    ("list_graph", "Trust.Temporal.Sanity", "memBy Nat.beq 4 [1, 2, 3]"),
    (
        "list_graph",
        "Trust.Temporal.Sanity",
        "optIs (lookupBy Nat.beq 2 [(1, 10), (2, 20), (2, 30)]) 30",
    ),
    ("list_graph", "Trust.Temporal.Sanity", "Nat.beq (nthD [5, 6, 7] 1 9) 7"),
    ("list_graph", "Trust.Temporal.Sanity", "Nat.beq (nthD [5, 6, 7] 3 9) 7"),
    ("list_graph", "Trust.Temporal.Sanity", "allB (fun x => Nat.blt 0 x) [1, 0]"),
    ("list_graph", "Trust.Temporal.Sanity", "anyB (Nat.beq 3) [1, 2]"),
    ("list_graph", "Trust.Temporal.Sanity", "Nat.beq (List.length (insertBy Nat.beq 2 [1, 2])) 3"),
    ("list_graph", "Trust.Temporal.Sanity", "Nat.beq (nthD (insertBy Nat.beq 3 [1, 2]) 0 0) 3"),
    ("list_graph", "Trust.Temporal.Sanity", "lengthEqB [1] [true, false]"),
    ("list_graph", "Trust.Temporal.Sanity", "Nat.beq (lastOf 0 [1, 2, 3]) 2"),
    // value_core (B1A-10): each a batch-B fact with its literal or class mutated.
    ("value_core", "Trust.Model.Sanity", "isOk (div (neg (lit 7)) (lit 2)) (-3)"),
    ("value_core", "Trust.Model.Sanity", "isOk (div (lit 7) (neg (lit 2))) (-3)"),
    ("value_core", "Trust.Model.Sanity", "isOk (div intMin (lit 3)) (-715827882)"),
    ("value_core", "Trust.Model.Sanity", "isOk (mod (neg (lit 7)) (lit 2)) (-1)"),
    ("value_core", "Trust.Model.Sanity", "isOk (mod intMin (lit 3)) 2"),
    ("value_core", "Trust.Model.Sanity", "isErr (div intMin (neg (lit 1))) Fail.overflow"),
    ("value_core", "Trust.Model.Sanity", "isUnmodeled (div intMin (neg (lit 2))) Code.intDivWrap"),
    ("value_core", "Trust.Model.Sanity", "isErr (mod intMin (neg (lit 1))) Fail.overflow"),
    ("value_core", "Trust.Model.Sanity", "isErr (add (lit 2147483646) (lit 1)) Fail.overflow"),
    (
        "value_core",
        "Trust.Model.Sanity",
        "isErr (sub (neg (lit 2147483647)) (lit 1)) Fail.overflow",
    ),
    ("value_core", "Trust.Model.Sanity", "isErr (mul (neg (lit 65536)) (lit 32768)) Fail.overflow"),
    ("value_core", "Trust.Model.Sanity", "isErr (neg intMin) Fail.divZero"),
    ("value_core", "Trust.Model.Sanity", "isErr (pow (lit 2) (neg (lit 1))) Fail.overflow"),
    ("value_core", "Trust.Model.Sanity", "isOk (pow (lit 2) (lit 30)) 1073741823"),
    ("value_core", "Trust.Model.Sanity", "inRange32 2147483648"),
    (
        "value_core",
        "Trust.Model.Sanity",
        "isErr (intAdd IntMode.unbounded 2147483647 1) Fail.overflow",
    ),
    ("value_core", "Trust.Model.Sanity", "isOk (pow (neg (lit 1)) (lit 2147483647)) 1"),
    (
        "value_core",
        "Trust.Model.Sanity",
        "Nat.beq (rErrTag (Res.concat [Res.ok [1], Res.error Fail.divZero, Res.error Fail.overflow])) (failTag Fail.overflow)",
    ),
    // value_order (B1A-11a): each an order fact with its literal, class or code mutated.
    ("value_order", "Trust.Model.Sanity", "isTrue (tlcLt (Value.mv 2) (Value.mv 1))"),
    ("value_order", "Trust.Model.Sanity", "isTrue (tlcLt (Value.mv 3) (Value.mv 1))"),
    ("value_order", "Trust.Model.Sanity", "isTrue (tlcLt (Value.str 548) (Value.str 547))"),
    ("value_order", "Trust.Model.Sanity", "isTrue (tlcLt (int 3) (int 2))"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.tmv 65 1) (Value.tmv 65 2)) 1"),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isErrN (tlcCmp (Value.tmv 65 1) (Value.tmv 66 2)) Fail.typeErr",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isUnmodeledN (tlcCmp (Value.tmv 65 1) (int 1)) Code.cmpUnpinned",
    ),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.mv 1) (int 1)) 2"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.mv 1) (Value.tmv 65 2)) 2"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.bool true) (Value.bool false)) 0"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (int (-3)) (int 2)) 2"),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (Value.set [int 5]) (Value.set [int 1, int 2])) 2",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (fn2 (int 1) (int 9) (int 2) (int 0)) (fn2 (int 1) (int 0) (int 3) (int 0))) 2",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (fn1 (Value.str 10) (int 0)) (fn1 (Value.str 9) (int 5))) 0",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (Value.set [int 0, Value.tmv 65 1]) (Value.set [int 1, int 2])) 2",
    ),
    ("value_order", "Trust.Model.Sanity", "Value.beq (Value.str 1) (Value.mv 1)"),
    ("value_order", "Trust.Model.Sanity", "Value.beq (Value.tmv 65 1) (Value.tmv 65 2)"),
    ("value_order", "Trust.Model.Sanity", "Nat.beq (Value.size deep) 11"),
    // value_order (B1A-11a repair round 1): the size order a record against a function
    // with no record form would get without the guard (TLC raises in one order), in both
    // orders, and one ordered control.
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (rcdA 372) tup12) 0"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp tup12 (rcdA 375)) 2"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (rcdA 372) fn23) 0"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp fn23 (rcdA 378)) 2"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.fn []) (rcdA 375)) 0"),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp tup12 fn23) 2"),
    // value_order (B1A-14a, the M0 review's findings 4, 5, 14): the untyped model value's
    // order flipped, a refused pair given TLC's answer, a rank order inverted.
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.str 1) (Value.mv 1)) 0"),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (Value.infSet InfKind.nat []) (Value.mv 1)) 0",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (Value.infSet InfKind.nat []) (Value.tmv 65 2)) 2",
    ),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (fn1 (int 1) (int 0)) (fn1 (Value.mv 1) (int 0))) 2",
    ),
    ("value_order", "Trust.Model.Sanity", "isOrd (tlcCmp (Value.tmv 65 1) (Value.mv 2)) 2"),
    (
        "value_order",
        "Trust.Model.Sanity",
        "isOrd (tlcCmp (Value.mv 1) (Value.infSet InfKind.fnSet [])) 2",
    ),
    // value_eq (B1A-11b): each an equality, normalization, canonicity or builder fact with
    // its literal, class, code or order mutated.
    ("value_eq", "Trust.Model.Sanity", "isTrue (valueEq (Value.str 1) (Value.mv 1))"),
    ("value_eq", "Trust.Model.Sanity", "isFalse (valueEq (Value.tmv 65 1) (int 1))"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isUnmodeledB (valueEq (Value.mv 1) (Value.tmv 65 2)) Code.cmpUnpinned",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isErrB (valueEq (Value.tmv 65 2) (Value.mv 1)) Fail.incomparable",
    ),
    ("value_eq", "Trust.Model.Sanity", "isTrue (valueEq (Value.tmv 65 1) (Value.tmv 65 2))"),
    ("value_eq", "Trust.Model.Sanity", "isFalse (valueEq (Value.tmv 65 1) (Value.tmv 66 2))"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isOkList (normSet [Value.mv 3, Value.mv 2, Value.mv 1]) [Value.mv 3, Value.mv 2, Value.mv 1]",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isOkList (normSet [Value.str 549, Value.str 548, Value.str 547]) [Value.str 548, Value.str 549, Value.str 547]",
    ),
    ("value_eq", "Trust.Model.Sanity", "isErrB (valueEq (Value.str 378) (int 1)) Fail.typeErr"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isUnmodeledB (valueEq (mkTuple [int 1]) (int 1)) Code.cmpUnpinned",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isErrB (valueEq (fn2 (int 1) (Value.str 5) (int 3) (int 1)) (fn2 (int 1) (int 1) (int 2) (int 1))) Fail.incomparable",
    ),
    ("value_eq", "Trust.Model.Sanity", "isFalse (valueEq (rcdA 372) tup12)"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isErrB (valueEq (fn1 (Value.tmv 65 1) (int 1)) tup1) Fail.incomparable",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isOkList (normSet [int 2, int 1, int 2, int 1]) [int 1, int 2, int 2]",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isErrL (normSet [int 1, Value.str 5, Value.tmv 65 1]) Fail.incomparable",
    ),
    ("value_eq", "Trust.Model.Sanity", "Value.Canon (Value.set [int 2, int 1])"),
    ("value_eq", "Trust.Model.Sanity", "notB (Value.Canon (int 1099511627776))"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isOkVal (mkRecord [(5, int 1), (3, int 2)]) (fn2 (Value.str 5) (int 1) (Value.str 3) (int 2))",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isOkVal (mkRecord [(5, int 1), (3, int 2), (5, int 3)]) (fn2 (Value.str 3) (int 2) (Value.str 5) (int 3))",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isTrue (valueEq (Value.set [int 1]) (Value.set [Value.str 1]))",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isUnmodeledB (valueEq (Value.infSet InfKind.nat []) (Value.mv 1)) Code.cmpUnpinned",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isFalse (valueEq (Value.infSet InfKind.fnSet []) (Value.mv 1))",
    ),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "isFalse (valueEq (Value.infSet InfKind.nat []) (Value.tmv 65 1))",
    ),
    ("value_eq", "Trust.Model.Sanity", "isFalse (valueEq (Value.bool true) (int 1))"),
    (
        "value_eq",
        "Trust.Model.Sanity",
        "Value.beq (mkTuple [Value.str 1, Value.bool true]) (fn2 (int 0) (Value.str 1) (int 1) (Value.bool true))",
    ),
    // syntax (B1A-12): a captured or misordered substitution, a variable not shifted, a
    // wrong size, and TLC truth-table rows with the result or the error class mutated.
    (
        "syntax",
        "Trust.Model.Sanity",
        "exprEq (Expr.subst [Expr.cur 3] opBody) (Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])] (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.lit (int 0)]))",
    ),
    (
        "syntax",
        "Trust.Model.Sanity",
        "exprEq (Expr.subst [Expr.bvar 0] opBody) (Expr.quant QKind.qAll [Expr.lit (Value.set [int 1])] (Expr.op PrimOp.valueEq [Expr.bvar 0, Expr.lit (int 0)]))",
    ),
    (
        "syntax",
        "Trust.Model.Sanity",
        "exprEq (Expr.subst [Expr.lit (int 7), Expr.lit (int 2)] (Expr.op PrimOp.intSub [Expr.bvar 1, Expr.bvar 0])) (Expr.op PrimOp.intSub [Expr.lit (int 2), Expr.lit (int 7)])",
    ),
    (
        "syntax",
        "Trust.Model.Sanity",
        "exprEq (Expr.subst [Expr.lit (int 5)] (Expr.op PrimOp.intAdd [Expr.bvar 0, Expr.bvar 1])) (Expr.op PrimOp.intAdd [Expr.lit (int 5), Expr.bvar 1])",
    ),
    (
        "syntax",
        "Trust.Model.Sanity",
        "exprEq (Expr.shift 0 1 (everyCtor 0 1 2 3 4 3 9)) (everyCtor 1 2 3 4 5 4 9)",
    ),
    (
        "syntax",
        "Trust.Model.Sanity",
        "actEq (Act.inst [int 1, int 2] (Act.pred (Expr.op PrimOp.intSub [Expr.bvar 1, Expr.bvar 0]))) (Act.pred (Expr.op PrimOp.intSub [Expr.lit (int 2), Expr.lit (int 1)]))",
    ),
    ("syntax", "Trust.Model.Sanity", "Nat.beq (Expr.size opBody) 4"),
    ("syntax", "Trust.Model.Sanity", "row Expr.and_ inF inE oDZ"),
    ("syntax", "Trust.Model.Sanity", "row Expr.or_ inT inN oTE"),
    ("syntax", "Trust.Model.Sanity", "row Expr.implies_ inF inE oDZ"),
    ("syntax", "Trust.Model.Sanity", "row Expr.equiv_ inN inE oTE"),
    ("syntax", "Trust.Model.Sanity", "row Expr.equiv_ inT inF oT"),
    ("syntax", "Trust.Model.Sanity", "row (fun a _ => Expr.not_ a) inN inT oF"),
    // spec (B1A-13): a split with the count, the order or the binder placement mutated; a
    // refused spec accepted, an accepted one refused; a fuel, size or depth with the
    // depth counted in edges or off by one; a StateWf decider on a short state.
    ("spec", "Trust.Model.Sanity", "Nat.beq (List.length (Spec.actions petri)) 1"),
    ("spec", "Trust.Model.Sanity", "actionsEq (Spec.actions petri) [one t1, one t0]"),
    (
        "spec",
        "Trust.Model.Sanity",
        "actionsEq (Act.split (Act.ex [dom] (Act.disj [aA, aB]))) [Action.mk [dom] aA, Action.mk [dom] aB]",
    ),
    ("spec", "Trust.Model.Sanity", "Nat.beq (List.length (Act.split appGuarded)) 2"),
    (
        "spec",
        "Trust.Model.Sanity",
        "Nat.beq (List.length (Act.split (Act.conj [Act.pred (le (lit 1) (Expr.cur 0)), Act.disj [aB, t1]]))) 1",
    ),
    ("spec", "Trust.Model.Sanity", "Spec.wf (withDefs [(0, Expr.app 1 []), (0, Expr.app 0 [])])"),
    ("spec", "Trust.Model.Sanity", "Spec.wf (withNext IntMode.tlc32 (lit 2147483648))"),
    (
        "spec",
        "Trust.Model.Sanity",
        "Spec.wf (spec 1 IntMode.tlc32 [] [] curDef [] (Act.conj [Act.prime 0 (lit 0), Act.pred (Expr.app 0 [])]) (Act.prime 0 (lit 1)) [])",
    ),
    (
        "spec",
        "Trust.Model.Sanity",
        "Spec.wf (spec 1 IntMode.tlc32 [\"a\", \"b\", \"a\"] [] [] [] (Act.prime 0 (lit 0)) (Act.prime 0 (lit 1)) [])",
    ),
    ("spec", "Trust.Model.Sanity", "rejects rich"),
    ("spec", "Trust.Model.Sanity", "Nat.beq (Spec.fuel petri) 38"),
    ("spec", "Trust.Model.Sanity", "Nat.beq (Spec.callDepth chain) 1"),
    ("spec", "Trust.Model.Sanity", "Nat.beq (Spec.fuel chain) 17"),
    ("spec", "Trust.Model.Sanity", "Nat.beq (Spec.size petri) 34"),
    ("spec", "Trust.Model.Sanity", "Spec.stateWfB petri [int 1]"),
    // primops (B1A-15): one mutated row per truth table (B1A-D11, through evalE), 0^0 still
    // pending, natSuccU wrapping, EXCEPT outside the domain extending f, Assert's argument, RemoveAt
    // and SubSeq's edges, TLC's answer where the EP refuses (B1A-D96) and the eager class, an
    // untyped model value in Nat, a mixed-kind application as a TLC class, the INT_MIN \div -1
    // wrap as overflow, Spec.wf accepting no binder or a wrong operand count, an unnormalized
    // union, Cardinality(Nat) as typeErr.
    ("primops", "Trust.Model.Sanity", "table (fun a _ => Expr.not_ a) [(inN, inT, oF)]"),
    ("primops", "Trust.Model.Sanity", "table Expr.and_ [(inF, inN, oTE)]"),
    ("primops", "Trust.Model.Sanity", "table Expr.or_ [(inT, inE, oDZ)]"),
    ("primops", "Trust.Model.Sanity", "table Expr.implies_ [(inF, inE, oDZ)]"),
    ("primops", "Trust.Model.Sanity", "table Expr.equiv_ [(inN, inE, oTE)]"),
    ("primops", "Trust.Model.Sanity", "isPending (ev (op PrimOp.intPow [num 0, num 0]))"),
    ("primops", "Trust.Model.Sanity", "isOverflow (ev (op PrimOp.natSuccU [num 2147483647]))"),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.funcExcept [tupE [num 5, num 6], num 3, num 7])) (tup [int 5, int 6, int 7])",
    ),
    ("primops", "Trust.Model.Sanity", "isAssertFailed (ev (op PrimOp.assert [num 1, strE 1])) 0"),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.seqRemoveAt [s567, num 4])) (tup [int 5, int 6])",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.seqSubseq [s567, num 3, num 2])) (tup [int 7])",
    ),
    ("primops", "Trust.Model.Sanity", "okV (ev (op PrimOp.setIn [tE, setE [tE, num 1]])) vT"),
    ("primops", "Trust.Model.Sanity", "isIncomparable (ev (setE [tE, num 1]))"),
    ("primops", "Trust.Model.Sanity", "okV (ev (op PrimOp.setIn [mE, natE])) vT"),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotInDomain (ev (op PrimOp.funcApply [tupE [num 5], strE 378]))",
    ),
    ("primops", "Trust.Model.Sanity", "isOverflow (ev (dv intMin (neg (num 1))))"),
    ("primops", "Trust.Model.Sanity", "Spec.wf (spInv (Expr.quant QKind.qEx [] tt))"),
    ("primops", "Trust.Model.Sanity", "Spec.wf (spInv (op PrimOp.intAdd [num 1]))"),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.setUnion [setE [num 3, num 1], setE [num 2, num 1]])) (setV [int 3, int 1, int 2])",
    ),
    ("primops", "Trust.Model.Sanity", "isTypeErr (ev (op PrimOp.setCard [natE]))"),
    // primops, B1A-15 repair round 1: the classes it corrected, each mutated back to the
    // pre-repair answer or to a wrong value (IsFiniteSet of a function, an eager UNION of a
    // non-set element, SetOfFcnsValue.size()'s three early answers and an infinite operand's
    // size() error, a quantifier over [{} -> Nat], set.in against a tuple and a record).
    ("primops", "Trust.Model.Sanity", "isTypeErr (ev (op PrimOp.setIsFinite [tupE [num 1]]))"),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setBigUnion [setE [num 1]]))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setIn [num 0, op PrimOp.setBigUnion [setE [natE]]]))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.setCard [fnSetE (setE []) natE])) (int 0)",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isTypeErr (ev (op PrimOp.setCard [fnSetE natE (setE [num 7])]))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "okV (ev (op PrimOp.setCard [fnSetE natE (setE [])])) (int 1)",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setCard [fnSetE intE (setE [num 1, num 2])]))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (Expr.quant QKind.qEx [fnSetE (setE []) natE] (op PrimOp.valueEq [Expr.bvar 0, tupE []])))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setIn [num 1, tupE [num 1]]))",
    ),
    ("primops", "Trust.Model.Sanity", "okV (ev (op PrimOp.intAdd [num 2, num 3])) (int 6)"),
    // primops, B1A-15 repair round 2: set.subseteq of [{} -> Nat] (an infSet fnSet, which TLC
    // enumerates) mutated back to the pre-repair `notEnumerable`, and a UserValue first
    // operand mutated to the pending answer.
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setSubseteq [fnSetE (setE []) natE, setE [tupE []]]))",
    ),
    (
        "primops",
        "Trust.Model.Sanity",
        "isNotEnumerable (ev (op PrimOp.setSubseteq [fnSetE (setE []) natE, setE [num 1]]))",
    ),
    ("primops", "Trust.Model.Sanity", "isPending (ev (op PrimOp.setSubseteq [natE, intE]))"),
    // tlc_core (B1A-14b): a quantifier's answer flipped, the LAST binder fastest, CHOOSE's
    // last element, a filter or set-of-all that keeps or makes the wrong elements, a domain
    // error read as a body error, CASE falling past OTHER or reading a guard after the first
    // TRUE one, a LET or an unread pool entry evaluated, a capturing substitution, swapped
    // parameters, an unassigned primed read answered, an ite that costs no fuel.
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qEx [bools] (Expr.bvar 0))) (Value.bool false)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qAll [empty] ff)) (Value.bool false)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qEx [bools, bools] (Expr.ite (Expr.bvar 1) (num 1) (Expr.bvar 0)))) (Value.bool true)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qChoose [setOf [int 1, int 2, int 3]] tt)) (int 3)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qFilter [bools] (Expr.bvar 0))) (Value.set [Value.bool false, Value.bool true])",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qMap [bools, setOf [int 1, int 2]] (Expr.ite (Expr.bvar 1) (Expr.bvar 0) (num 0)))) (Value.set [int 1, int 2])",
    ),
    ("tlc_core", "Trust.Model.Sanity", "isTypeErr (ev (Expr.quant QKind.qEx [empty, num 3] tt))"),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "isChooseFailed (ev (Expr.quant QKind.qEx [setOf [int 1]] (Expr.bvar 0)))",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.caseOf [(ff, num 1)] (Option.some (num 2)))) (int 1)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "isTypeErr (ev (Expr.caseOf [(tt, num 1), (num 3, num 2)] Option.none))",
    ),
    ("tlc_core", "Trust.Model.Sanity", "isChooseFailed (ev (Expr.letLazy bad (num 5)))"),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qEx [setOf [Value.bool true]] (Expr.letLazy (Expr.bvar 0) (Expr.quant QKind.qAll [setOf [Value.bool false]] (Expr.bvar 1))))) (Value.bool false)",
    ),
    ("tlc_core", "Trust.Model.Sanity", "okV (ev (Expr.app 1 [tt, num 7])) (int 0)"),
    ("tlc_core", "Trust.Model.Sanity", "isChooseFailed (ev (Expr.ite tt (num 1) (Expr.pool 0)))"),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "isOkWith (evX [] [int 0] [Option.none] (Expr.nxt 0)) (fun x => Nat.beq (xTag x) 0)",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "isFuel (evalX spC 2 false [] [int 0] [] (Expr.ite tt (num 1) (num 2)))",
    ),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "Spec.wf (spWith (Expr.quant QKind.qChoose [bools, bools] tt))",
    ),
    // tlc_skeleton (B1A-14a): a wrapper's fuel-0 or fuel-1 answer swapped, a mismatched
    // answer read as the skeleton's todo, a rule given its FX-prelude-variants alternative
    // (a forced value, an eager or materializing answer, a forced membership), a malformed
    // executable value accepted.
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isFuel (sigEvalX sp1 1 false [] [int 0] [Option.none] tt)",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isUnmodeled (sigForce sp1 0 [int 0] (XVal.val set12)) Code.todo",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isUnmodeled (sigTlcHoldsF sp1 1 [] (Act.prime 0 tt) [int 0] [int 1]) Code.lazyArg",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isUnmodeled (Tlc.goEvalX (fun _ => Res.ok (Out.bool true)) false [] [] [] tt) Code.todo",
    ),
    ("tlc_skeleton", "Trust.Model.Sanity", "Tlc.rule.materializeQFn true [XVal.val set12]"),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "Tlc.rule.materializeQFn false [XVal.val (Value.infSet InfKind.nat [])]",
    ),
    ("tlc_skeleton", "Trust.Model.Sanity", "Tlc.rule.keepLazyReset true"),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isOkWith (Tlc.rule.forceAtAssign raise (XVal.lazySet gSet)) (fun x => Nat.beq (xTag x) 0)",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isOkWith (Tlc.rule.forceCtorDomains raise [XVal.lazySet gSet]) (fun ds => Nat.beq (xTag (Temporal.nthD ds 0 (XVal.val set12))) 0)",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "Tlc.rule.eagerFilter (XVal.lazySet (SetGen.subset gSet))",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isOkWith (Tlc.rule.memByForcing raise raiseMem (Res.ok true) (XVal.lazySet (SetGen.subset gSet)) set12) (fun b => Bool.not b)",
    ),
    ("tlc_skeleton", "Trust.Model.Sanity", "XVal.wfB sp1 (XVal.val (Value.set [int 2, int 1]))"),
    ("tlc_skeleton", "Trust.Model.Sanity", "XVal.wfB sp1 (XVal.lazyFn [gSet] (Expr.bvar 2) ctxOk)"),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "XVal.wfB sp1 (XVal.fnX [(int 2, XVal.val set12), (int 1, XVal.val set12)])",
    ),
    ("tlc_skeleton", "Trust.Model.Sanity", "Ctx.wfB sp1 (Ctx.mk [int 3] [])"),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "SetGen.wfB sp1 (SetGen.filter gSet (Expr.bvar 1) ctx0)",
    ),
    // B1A-16: laziness I (lazy_fn.lean), one per fact or edge; tlc_core's restated qFn door
    // (a swapped value); tlc_skeleton's restated applyX (the skeleton's todo).
    ("lazy_fn", "Trust.Model.Sanity", "okV (ev (app (Expr.pool 1) (num 1))) (int 0)"),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (ev (app (Expr.pool 1) (num 1)))"),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (ev (app (tupE [Expr.pool 1, num 1]) (num 2)))"),
    ("lazy_fn", "Trust.Model.Sanity", "okV (ev (app (tupE [ctor, num 1]) (num 2))) (int 2)"),
    ("lazy_fn", "Trust.Model.Sanity", "isChooseFailed (ev (tupE [ctor, bad]))"),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isChooseFailed (Tlc.rhsX (Tlc.run spL 64) true [] [int 0] [Option.none] (tupE [ctor, bad]))",
    ),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "okV (evS [int 2] (app (Expr.pool 2) (add (Expr.cur 0) (num 1)))) (int 4)",
    ),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (evX false (app (tupE [ctor, num 1]) (num 1)))"),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isUnmodeled (ev (exc (qfn [natE] (Expr.bvar 0)) (num 0) (num 7))) Code.lazyArg",
    ),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (ev ctorOrder)"),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (ev (app (app fTup (num 1)) (num 2)))"),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isTypeErr (ev (app (qfn [natE] (Expr.bvar 0)) (neg (num 1))))",
    ),
    ("lazy_fn", "Trust.Model.Sanity", "isDivZero (ev (app (num 3) (dv (num 1) (num 0))))"),
    ("lazy_fn", "Trust.Model.Sanity", "isNotInDomain (ev (app fTwo (tupE [num 5, num 2, num 9])))"),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isDivZero (ev (op PrimOp.setIn [num 0, dom (qfn [natE] (dv (num 1) (Expr.bvar 0)))]))",
    ),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isDivZero (ev (app (op (PrimOp.recGet 378) [op (PrimOp.recNew [378, 380]) [ctor, num 2]]) (num 1)))",
    ),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isDivZero (ev (exc (tupE [num 1]) (num 5) (dv (num 1) (num 0))))",
    ),
    ("lazy_fn", "Trust.Model.Sanity", "isTypeErr (ev (exc (num 3) (dv (num 1) (num 0)) (num 2)))"),
    ("lazy_fn", "Trust.Model.Sanity", "okV (ev (app (tl (tupE [ctor, num 1])) (num 1))) (int 2)"),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isDivZero (ev (app (hd (tupE [tupE [ctor, num 2], num 1])) (num 2)))",
    ),
    (
        "lazy_fn",
        "Trust.Model.Sanity",
        "isDivZero (ev (app (tupE [qfn [setE [num 1, num 2]] (Expr.ite (eqE (Expr.bvar 0) (num 1)) (qfn [setE [num 0]] (dv (num 1) (Expr.bvar 0))) bad)]) (num 1)))",
    ),
    ("lazy_fn", "Trust.Model.Sanity", "isPending (ev (qfn [natE] (Expr.bvar 0)))"),
    (
        "tlc_core",
        "Trust.Model.Sanity",
        "okV (ev (Expr.quant QKind.qFn [bools] (Expr.bvar 0))) (Value.fn [(Value.bool false, Value.bool true), (Value.bool true, Value.bool false)])",
    ),
    (
        "tlc_skeleton",
        "Trust.Model.Sanity",
        "isUnmodeled (sigApplyX sp1 1 true [int 0] (XVal.val (Value.fn [(int 1, int 5)])) (int 1)) Code.todo",
    ),
];

/// Every sanity file elaborates after the whole model prelude and declares exactly its
/// listed theorems, each accepted by `check_model_theorem` (kernel re-check,
/// constructive, axiom-free, audited); every mutated-literal door over it is refuted
/// (class Definite); and the sanity directory holds exactly the listed files.
#[test]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn sanity_files() {
    let directory =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/model_prelude/sanity");
    let mut on_disk: Vec<String> = std::fs::read_dir(&directory)
        .expect("the sanity directory is readable")
        .map(|entry| entry.expect("a sanity entry").file_name().to_string_lossy().into_owned())
        .collect();
    on_disk.sort();
    let mut listed: Vec<String> =
        SANITY.iter().map(|(file, _, _)| format!("{file}.lean")).collect();
    listed.sort();
    assert_eq!(on_disk, listed, "the sanity directory and SANITY differ");
    for (file, _, _) in SANITY_MUTANTS {
        assert!(
            SANITY.iter().any(|(listed, _, _)| listed == file),
            "mutant of unlisted file {file}"
        );
    }

    let (log, failures) = with_model_prelude(|base| {
        let mut log: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        let base_names = prelude_added_constants(base.environment());
        for (file, source, expected) in SANITY {
            let mut prelude = base.clone();
            if let Err(error) = elaborate_model_suffix(&mut prelude, source, "sanity file") {
                failures.push(format!("{file}: refused: {error}"));
                continue;
            }
            let theorems = added_theorems(&prelude, &base_names);
            if theorems != *expected {
                failures.push(format!("{file}: theorems {theorems:?}, expected {expected:?}"));
            }
            for theorem in &theorems {
                if let Err(error) = check_model_theorem(prelude.environment(), theorem) {
                    failures.push(format!("{file}: {theorem} refused: {error}"));
                }
            }
            log.push(format!("sanity {file}: {} theorems accepted", theorems.len()));
            for (index, (_, namespace, door)) in
                SANITY_MUTANTS.iter().filter(|(mutant_file, _, _)| mutant_file == file).enumerate()
            {
                let statement = DoorStatement { namespace, binders: "", door };
                let name = format!("sanity_mutant_{index}");
                let (result, class) = try_door(&prelude, &statement, &name);
                log.push(format!("sanity {file} mutant `{door}`: class {class:?}"));
                if class != Some(Rejection::Definite) {
                    failures.push(format!(
                        "{file}: mutant `{door}` class {class:?}, expected Definite: {result:?}"
                    ));
                }
            }
        }
        (log, failures)
    })
    .expect("the model prelude elaborates");
    for line in &log {
        println!("{line}");
    }
    assert!(failures.is_empty(), "sanity files:\n{}", failures.join("\n"));
}

/// What B1A-02a's plan expected of a capability file (TASKS.md B1A-02a, from the
/// Sep 19 Clean CLI scratch runs): the planned row of the matrix.
#[cfg(feature = "test-support")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Planned {
    /// A required pass.
    Pass,
    /// An expected failure.
    Fail,
    /// The workaround of an expected failure, or a required pass's fallback.
    Workaround,
}

/// What trust's Clean pin does with a capability file: the measured row.
#[cfg(feature = "test-support")]
#[derive(Debug, Clone, Copy)]
enum Measured {
    /// It elaborates on a fresh base prelude, it adds exactly `theorems` as
    /// theorems, every one is accepted by `check_model_theorem` (the temporal
    /// surface's `checked_theorem`, audit included), each of `reducible` is a
    /// `Reducible` definition, and each mutant (a door theorem with a wrong literal,
    /// elaborated after the file) is refused.
    Pass {
        theorems: &'static [&'static str],
        reducible: &'static [&'static str],
        mutants: &'static [&'static str],
    },
    /// Clean refuses it while elaborating it (no theorem is ever checked), with a
    /// detail containing `detail`; `workaround` is the file that differs from it only
    /// in the feature, and must be a `Pass` row.
    Fail { detail: &'static str, workaround: &'static str },
}

#[cfg(feature = "test-support")]
struct Capability {
    file: &'static str,
    source: &'static str,
    planned: Planned,
    measured: Measured,
}

#[cfg(feature = "test-support")]
macro_rules! capability {
    ($file:literal, $planned:ident, $measured:expr) => {
        Capability {
            file: $file,
            source: include_str!(concat!("model_prelude/capabilities/", $file, ".lean")),
            planned: Planned::$planned,
            measured: $measured,
        }
    };
}

#[cfg(feature = "test-support")]
const fn pass(theorems: &'static [&'static str]) -> Measured {
    Measured::Pass { theorems, reducible: &[], mutants: &[] }
}

/// B1A-02a's capability matrix, first measured at Clean `08084daa09`.
/// The multi-argument mutual and partial List.rec rows are re-measured at
/// `feee691d2520`; their historical planned-failure and encoding-policy labels stay.
/// Decisions it records: B1A-D04 (the alias form), D07 (the block), D21 (Ctx: the
/// single-constructor fallback, since a structure cannot sit in a mutual block), D70
/// (the coding rules). A drift in any row, either way, fails this test: the matrix
/// is re-measured and the decisions re-taken on a Clean bump.
#[cfg(feature = "test-support")]
const CAPABILITIES: &[Capability] = &[
    // ---- the plan's required passes ----
    capability!(
        "nested_value",
        Pass,
        Measured::Pass {
            theorems: &["Trust.Model.nested_value_door", "Trust.Model.nested_value_match"],
            reducible: &[],
            mutants: &["theorem nested_value_mutant : Nat.beq (Value.sizeF 10 v1) 5 = true := rfl"],
        }
    ),
    capability!(
        "mutual_expr_act",
        Pass,
        pass(&[
            "Trust.Model.mutual_expr_act_door",
            "Trust.Model.mutual_expr_act_expr",
            "Trust.Model.mutual_expr_act_casesOn_door",
        ])
    ),
    capability!(
        "mutual_structure_ctx",
        Pass,
        Measured::Fail {
            detail: "mutual block mixing `inductive` with other declaration kinds",
            workaround: "mutual_ctx_single_ctor",
        }
    ),
    capability!(
        "mutual_ctx_single_ctor",
        Workaround,
        pass(&["Trust.Model.mutual_ctx_single_ctor_door", "Trust.Model.mutual_ctx_casesOn_door"])
    ),
    capability!(
        "structure_15_fields",
        Pass,
        Measured::Pass {
            theorems: &[
                "Trust.Model.structure_15_fields_door",
                "Trust.Model.structure_15_fields_last",
                "Trust.Model.structure_15_fields_bool",
            ],
            reducible: &[],
            mutants: &["theorem structure_15_fields_mutant : Nat.beq sp1.next 7 = true := rfl"],
        }
    ),
    capability!(
        "fuel_block_go",
        Pass,
        Measured::Pass {
            theorems: &[
                "Trust.Model.fuel_block_sum",
                "Trust.Model.fuel_block_out_of_fuel",
                "Trust.Model.fuel_block_100000",
            ],
            reducible: &[],
            mutants: &[
                "theorem fuel_block_mutant : \
                 Res.isOkNat (Tlc.run 100000 (Job.sum [1])) 3 = true := rfl",
                "theorem fuel_block_fuel_mutant : Res.isFuel (Tlc.run 5 (Job.sum [1])) = true := rfl",
            ],
        }
    ),
    capability!(
        "string_field",
        Pass,
        pass(&["Trust.Model.string_field_tokens", "Trust.Model.string_field_door"])
    ),
    capability!(
        "int_floor_divmod",
        Pass,
        Measured::Pass {
            theorems: &[
                "Trust.Model.div_neg",
                "Trust.Model.mod_neg",
                "Trust.Model.div_neg_exact",
                "Trust.Model.mod_neg_exact",
                "Trust.Model.div_pos",
                "Trust.Model.mod_pos",
            ],
            reducible: &[],
            // Truncating division's answers, which TLC's floor division is not.
            mutants: &[
                "theorem div_truncating : tlcDiv (-7) 2 = -3 := rfl",
                "theorem mod_truncating : tlcMod (-7) 2 = -1 := rfl",
            ],
        }
    ),
    capability!(
        "rfl_decide",
        Pass,
        pass(&[
            "Trust.Model.rfl_double",
            "Trust.Model.decide_lt",
            "Trust.Model.decide_eq",
            "Trust.Model.decide_ne",
        ])
    ),
    capability!(
        "reducible_alias_member",
        Pass,
        Measured::Pass {
            theorems: &[
                "Trust.Temporal.member_bridge_to",
                "Trust.Temporal.member_head",
                "Trust.Temporal.member_tail",
                "Trust.Model.abbrev_door",
            ],
            reducible: &["Trust.Temporal.Member", "Trust.Model.State", "Trust.Model.Slots"],
            mutants: &["theorem member_mutant : Trust.Temporal.Member 3 [2, 5] := \
                        Trust.Temporal.FiniteModel.Member.head [5]"],
        }
    ),
    capability!(
        "section_variable",
        Pass,
        Measured::Fail {
            detail: "Constructor Trust.Temporal.Reach.init return type parameter at index 0 does \
                     not match declared parameter of Trust.Temporal.Reach",
            workaround: "section_variable_explicit",
        }
    ),
    capability!(
        "section_variable_def",
        Workaround,
        pass(&["Trust.Temporal.last_door", "Trust.Temporal.terminal_none"])
    ),
    capability!("section_variable_explicit", Workaround, pass(&["Trust.Temporal.reach_two"])),
    capability!("root_extension", Pass, pass(&["Trust.Model.root_extension_door"])),
    capability!(
        "field_notation_receiver",
        Pass,
        pass(&["Trust.Model.field_notation_receiver", "Trust.Model.field_notation_receiver_door"])
    ),
    capability!(
        "relative_temporal_member",
        Pass,
        Measured::Pass {
            theorems: &["Trust.Model.state_ok", "Trust.Model.relative_member"],
            reducible: &["Trust.Temporal.Member"],
            mutants: &[],
        }
    ),
    capability!(
        "qualified_in_finite_model",
        Pass,
        pass(&[
            "Trust.Temporal.FiniteModel.qualified_door",
            "Trust.Temporal.FiniteModel.shadowed_value_is_finite_models",
            "Trust.Temporal.FiniteModel.qualified_value",
        ])
    ),
    // ---- the plan's expected failures, each with the workaround that differs only in it ----
    capability!(
        "nested_ctor_pattern",
        Fail,
        // Measured: it elaborates at 08084daa09 (it failed on the Sep 19 CLI). B1A-D70
        // still forbids it: ty's diverged Clean pin is unmeasured (B1A-48), and it
        // compiles to match auxiliaries (B1A-D61).
        Measured::Pass {
            theorems: &["Trust.Model.pattern_door"],
            reducible: &[],
            mutants: &[
                "theorem pattern_mutant : Nat.beq (Outer.val (Outer.wrap Inner.b)) 7 = true := rfl",
            ],
        }
    ),
    capability!("nested_match", Workaround, pass(&["Trust.Model.pattern_door"])),
    capability!(
        "where_clause",
        Fail,
        // Measured: it elaborates at 08084daa09 (it failed on the Sep 19 CLI); still
        // forbidden by B1A-D70, as nested_ctor_pattern.
        pass(&["Trust.Model.total_door"])
    ),
    capability!("where_hoisted", Workaround, pass(&["Trust.Model.total_door"])),
    capability!(
        "mutual_def_multi_arg",
        Fail,
        // Measured support at feee691d2520; the historical Planned::Fail and
        // B1A-D70 encoding policy remain distinct from this checked capability.
        Measured::Pass {
            theorems: &[
                "Trust.Model.sumE.eq_1",
                "Trust.Model.sumL.eq_1",
                "Trust.Model.mutual_door",
                "Trust.Model.mutual_zero_e",
                "Trust.Model.mutual_zero_l",
                "Trust.Model.mutual_one_e",
                "Trust.Model.mutual_one_l",
                "Trust.Model.mutual_two_e",
                "Trust.Model.mutual_empty_e",
                "Trust.Model.mutual_empty_l",
                "Trust.Model.mutual_cross_l",
            ],
            reducible: &[],
            mutants: &[
                "theorem mutual_wrong_base : Nat.beq (sumE 0 [3, 4]) 1 = true := rfl",
                "theorem mutual_wrong_fuel : Nat.beq (sumE 1 [3, 4]) 4 = true := rfl",
                "theorem mutual_wrong_cross : Nat.beq (sumL 1 [3, 4]) 4 = true := rfl",
                "theorem mutual_wrong_args : Nat.beq (sumE 2 [3, 4]) 5 = true := rfl",
                "theorem mutual_wrong_empty_e : Nat.beq (sumE 20 []) 0 = true := rfl",
                "theorem mutual_wrong_empty_l : Nat.beq (sumL 20 []) 1 = true := rfl",
            ],
        }
    ),
    capability!("mutual_def_packed", Workaround, pass(&["Trust.Model.mutual_door"])),
    capability!(
        "monad_instance_res",
        Fail,
        Measured::Fail { detail: "fields: [\"map\"]", workaround: "res_bind_plain" }
    ),
    capability!("res_bind_plain", Workaround, pass(&["Trust.Model.res_door"])),
    capability!(
        "rec_binder",
        Fail,
        Measured::Fail { detail: "ParseError(", workaround: "go_binder" }
    ),
    capability!("go_binder", Workaround, pass(&["Trust.Model.binder_door"])),
    capability!(
        "list_rec_partial",
        Fail,
        // Partial eliminator application is measured kernel capability, not a
        // change to B1A-D70's historical encoding rule or a Lean codegen claim.
        Measured::Pass {
            theorems: &[
                "Trust.Model.sum_door",
                "Trust.Model.sum_nil",
                "Trust.Model.sum_singleton",
                "Trust.Model.sum_repeat",
            ],
            reducible: &[],
            mutants: &[
                "theorem sum_wrong_result : Nat.beq (sumList [1, 2, 3]) 7 = true := rfl",
                // These propositions deliberately are not Bool doors: each must
                // fail for TypeMismatch, never an unknown name or parse error.
                "theorem sum_bad_step : (@List.rec Nat (fun _ => Nat) 0 \
                 (fun h _ acc => true)) [1] = 0 := rfl",
                "theorem sum_bad_domain : (@List.rec Nat (fun _ => Nat) 0 \
                 (fun (h : Bool) _ acc => acc)) [1] = 0 := rfl",
            ],
        }
    ),
    capability!("list_rec_eta", Workaround, pass(&["Trust.Model.sum_door"])),
    capability!(
        "frame_before_mutual",
        Fail,
        Measured::Fail {
            detail: "declaration `Trust.Model.Frame` failed: UnknownIdentWithSuggestions { name: \
                     \"XVal\"",
            workaround: "frame_after_mutual",
        }
    ),
    capability!("frame_after_mutual", Workaround, pass(&["Trust.Model.frame_door"])),
];

/// The measured outcome of one capability file, compared with its row by the test.
#[cfg(feature = "test-support")]
#[derive(Debug)]
enum Observed {
    Elaborated {
        /// The theorems the file added, sorted, each with its acceptance result.
        theorems: Vec<(String, Result<(), ModelPreludeError>)>,
        /// The `reducible` names that are not `Reducible` definitions.
        not_reducible: Vec<String>,
        /// Explicit type, value, closure and audit failures for the two newly
        /// supported ordinary-definition fixtures (not `Reducible` aliases).
        ordinary_definition_issues: Vec<String>,
        /// Each mutant with its elaboration-plus-check result and, for a refused Bool
        /// door, its B1A-D54 class.
        mutants: Vec<(String, Result<(), ModelPreludeError>, Option<Rejection>)>,
    },
    Refused(ModelPreludeError),
}

/// The two newly supported fixtures are authored ordinary `def`s, not aliases.
/// Pin their data types independently of elaboration and audit their stored values;
/// the positive equations and Definite mutants below pin the intended observations.
/// This does not alter the existing `reducible` checks for alias fixtures.
#[cfg(feature = "test-support")]
fn ordinary_capability_definition_issues(
    file: &str,
    environment: &clean_kernel::env::Environment,
) -> Vec<String> {
    use clean_kernel::TypeChecker;
    use clean_kernel::env::{CertificationIssue, Reducibility};
    use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
    use clean_kernel::level::Level;

    let nat = Expr::const_str("Nat");
    let list_nat = Expr::app(Expr::const_str_levels("List", vec![Level::zero()]), nat.clone());
    let list_to_nat = Expr::arrow(list_nat.clone(), nat.clone());
    let definitions: Vec<(&str, Expr, &str)> = match file {
        "mutual_def_multi_arg" => vec![
            ("Trust.Model.sumE", Expr::arrow(nat.clone(), list_to_nat.clone()), "Nat.rec"),
            ("Trust.Model.sumL", Expr::arrow(nat.clone(), list_to_nat.clone()), "Nat.rec"),
        ],
        "list_rec_partial" => vec![("Trust.Model.sumList", list_to_nat.clone(), "List.rec")],
        _ => return Vec::new(),
    };
    let mut issues = Vec::new();
    let tc = TypeChecker::new(environment);
    let data_sort = Level::succ(Level::zero());
    for (definition, expected_type, recursor) in definitions {
        let name = Name::from_string(definition);
        let Some(constant) = environment.get_const(&name) else {
            issues.push(format!("{definition}: missing ordinary definition"));
            continue;
        };
        if constant.kind != ConstantKind::Definition
            || !matches!(constant.reducibility, Reducibility::Regular(_))
            || constant.is_reducible
            || !constant.level_params.is_empty()
        {
            issues.push(format!(
                "{definition}: expected monomorphic Definition/Regular, got {:?}/{:?}, \
                 is_reducible={}, level_params={:?}",
                constant.kind, constant.reducibility, constant.is_reducible, constant.level_params
            ));
        }
        if constant.type_ != expected_type {
            issues.push(format!(
                "{definition}: type {:?}, independently expected {expected_type:?}",
                constant.type_
            ));
        }
        if !matches!(tc.infer_sort(&constant.type_), Ok(sort) if sort == data_sort) {
            issues.push(format!("{definition}: its type must live in Sort 1"));
        }
        let Some(value) = constant.value.as_ref() else {
            issues.push(format!("{definition}: missing definition value"));
            continue;
        };
        if value.has_fvar_quick()
            || value.has_expr_mvar_quick()
            || value.has_level_mvar_quick()
            || value.has_level_param_quick()
            || value.has_loose_bvars()
        {
            issues.push(format!("{definition}: stored value is not closed and monomorphic"));
        }
        match tc.infer_type(value) {
            Ok(inferred) if tc.is_def_eq(&inferred, &expected_type) => {}
            result => issues.push(format!(
                "{definition}: value does not have the independently expected type: {result:?}"
            )),
        }
        let references = value.collect_constants();
        if !references.contains(&Name::from_string(recursor)) {
            issues.push(format!("{definition}: stored value does not use {recursor}"));
        }
        // The SCC lowering must discharge its forward declarations, never leave
        // either original member as circular support in an emitted member body.
        if file == "mutual_def_multi_arg" {
            for member in ["Trust.Model.sumE", "Trust.Model.sumL"] {
                if references.contains(&Name::from_string(member)) {
                    issues.push(format!(
                        "{definition}: stored value still calls SCC member {member}"
                    ));
                }
            }
        }
        match environment.axiom_deps(&name) {
            Some(dependencies) if dependencies.is_empty() => {}
            result => {
                issues.push(format!("{definition}: axiom dependencies are not empty: {result:?}"))
            }
        }
        let audit = environment.audit_certification(&constant.type_, &Expr::const_(name, vec![]));
        // A data function is not a proposition. Require exactly that independently
        // established Sort-1 diagnostic; an inference error or any closure issue
        // must fail. This follows the existing definition audit's data boundary.
        let data_issue = CertificationIssue::GoalNotProposition {
            error: format!("goal lives in Sort {data_sort:?}, not Prop"),
        };
        if audit.issues != [data_issue] {
            issues.push(format!("{definition}: unexpected definition audit: {:?}", audit.issues));
        }
        if file == "list_rec_partial" {
            // Independently construct the four-argument partial recursor. The
            // major premise is still absent, so this is a function List Nat -> Nat.
            let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), nat.clone());
            let step = Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    list_nat.clone(),
                    Expr::lam(
                        BinderInfo::Default,
                        nat.clone(),
                        Expr::apps(Expr::const_str("Nat.add"), [Expr::bvar(2), Expr::bvar(0)]),
                    ),
                ),
            );
            let expected_value = Expr::apps(
                Expr::const_str_levels("List.rec", vec![data_sort.clone(), Level::zero()]),
                [nat.clone(), motive, Expr::nat_lit(0), step],
            );
            if !matches!(value.get_app_fn().kind(), ExprKind::Const(name, levels)
                if name == &Name::from_string("List.rec")
                    && levels.as_slice() == [data_sort.clone(), Level::zero()])
                || value.get_app_num_args() != 4
            {
                issues.push(format!(
                    "{definition}: expected List.rec.{{1,0}} with exactly four arguments"
                ));
            }
            match tc.infer_type(&expected_value) {
                Ok(inferred) if tc.is_def_eq(&inferred, &expected_type) => {}
                result => issues.push(format!(
                    "{definition}: independent recursor reference is ill-typed: {result:?}"
                )),
            }
            if !tc.is_def_eq(value, &expected_value) {
                issues.push(format!(
                    "{definition}: value differs from the independently constructed List.rec"
                ));
            }
        }
    }
    issues
}

/// B1A-02a: Clean's language features at trust's pin, one Clean file per feature,
/// each elaborated on a fresh copy of the base prelude (Trust.Temporal and
/// Trust.FiniteModel, the modules every Trust.Model module is elaborated after), against
/// the planned and measured matrix above.
#[test]
#[cfg(feature = "test-support")]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn clean_capabilities_features() {
    use trust_spec_temporal::model_prelude::with_model_prelude_prefix;

    // Every capability file is a row, and every row's file exists (include_str!).
    let directory = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/model_prelude/capabilities");
    let mut on_disk: Vec<String> = std::fs::read_dir(directory)
        .expect("the capability directory exists")
        .map(|entry| entry.expect("readable entry").file_name().to_string_lossy().into_owned())
        .collect();
    on_disk.sort();
    let mut rows: Vec<String> = CAPABILITIES
        .iter()
        .map(|row| row.file)
        .chain(DOOR_FILES.iter().map(|(file, _)| *file))
        .map(|file| format!("{file}.lean"))
        .collect();
    rows.sort();
    assert_eq!(on_disk, rows, "capability files and matrix rows differ");
    rows.dedup();
    assert_eq!(rows.len(), CAPABILITIES.len() + DOOR_FILES.len(), "a capability file has two rows");

    let inputs: Vec<(&'static str, &'static str, Measured)> =
        CAPABILITIES.iter().map(|row| (row.file, row.source, row.measured)).collect();
    let observed = with_model_prelude_prefix("Trust.FiniteModel", move |base| {
        assert_eq!(base.module_names(), ["Trust.Temporal", "Trust.FiniteModel"]);
        let base_names = prelude_added_constants(base.environment());
        inputs
            .into_iter()
            .map(|(file, source, measured)| {
                let mut prelude = base.clone();
                if let Err(error) = elaborate_model_suffix(&mut prelude, source, file) {
                    return (file, Observed::Refused(error));
                }
                let environment = prelude.environment();
                let mut theorems: Vec<(String, Result<(), ModelPreludeError>)> =
                    prelude_added_constants(environment)
                        .into_iter()
                        .filter(|name| !base_names.contains(name))
                        .filter(|name| {
                            environment
                                .get_const(name)
                                .is_some_and(|constant| constant.kind == ConstantKind::Theorem)
                        })
                        .map(|name| {
                            let name = name.to_string();
                            let accepted = check_model_theorem(environment, &name);
                            (name, accepted)
                        })
                        .collect();
                theorems.sort_by(|left, right| left.0.cmp(&right.0));
                let (reducible, mutants): (&[&str], &[&str]) = match measured {
                    Measured::Pass { reducible, mutants, .. } => (reducible, mutants),
                    Measured::Fail { .. } => (&[], &[]),
                };
                let not_reducible = reducible
                    .iter()
                    .filter(|name| {
                        environment.get_const(&Name::from_string(name)).is_none_or(|constant| {
                            constant.kind != ConstantKind::Definition
                                || constant.reducibility
                                    != clean_kernel::env::Reducibility::Reducible
                        })
                    })
                    .map(|name| (*name).to_owned())
                    .collect();
                let mutants = mutants
                    .iter()
                    .map(|mutant| {
                        let mut mutated = prelude.clone();
                        let source = format!(
                            "namespace Trust\nnamespace Model\n{mutant}\nend Model\nend Trust\n"
                        );
                        let name = mutant
                            .split_whitespace()
                            .nth(1)
                            .expect("a mutant is `theorem <name> ...`")
                            .to_owned();
                        let result = elaborate_model_suffix(&mut mutated, &source, "mutant")
                            .and_then(|()| {
                                check_model_theorem(
                                    mutated.environment(),
                                    &format!("Trust.Model.{name}"),
                                )
                            });
                        let class = match (&result, mutant_door(mutant)) {
                            (Err(error), Some(door)) => Some(classify_rejection(
                                &prelude,
                                &DoorStatement { namespace: "Trust.Model", binders: "", door },
                                error,
                            )),
                            _ => None,
                        };
                        ((*mutant).to_owned(), result, class)
                    })
                    .collect();
                let ordinary_definition_issues =
                    ordinary_capability_definition_issues(file, environment);
                (
                    file,
                    Observed::Elaborated {
                        theorems,
                        not_reducible,
                        ordinary_definition_issues,
                        mutants,
                    },
                )
            })
            .collect::<Vec<_>>()
    })
    .expect("the base prelude elaborates");

    // The matrix, measured, for the evidence log (`--nocapture`).
    for (row, (file, outcome)) in CAPABILITIES.iter().zip(&observed) {
        assert_eq!(row.file, *file);
        let measured = match outcome {
            Observed::Elaborated { theorems, .. } => {
                format!(
                    "pass ({} theorems accepted)",
                    theorems.iter().filter(|t| t.1.is_ok()).count()
                )
            }
            Observed::Refused(error) => format!("fail: {error}"),
        };
        println!("capability {file}: planned {:?}; measured {measured}", row.planned);
    }

    let mut failures = Vec::new();
    for (row, (file, outcome)) in CAPABILITIES.iter().zip(&observed) {
        match (row.measured, outcome) {
            (
                Measured::Pass { theorems: expected, .. },
                Observed::Elaborated {
                    theorems,
                    not_reducible,
                    ordinary_definition_issues,
                    mutants,
                },
            ) => {
                let mut expected: Vec<&str> = expected.to_vec();
                expected.sort_unstable();
                let added: Vec<&str> = theorems.iter().map(|(name, _)| name.as_str()).collect();
                if added != expected {
                    failures
                        .push(format!("{file}: added theorems {added:?}, expected {expected:?}"));
                }
                for (name, accepted) in theorems {
                    if let Err(error) = accepted {
                        failures.push(format!("{file}: {name} refused: {error}"));
                    }
                }
                if !not_reducible.is_empty() {
                    failures.push(format!("{file}: not reducible definitions: {not_reducible:?}"));
                }
                for issue in ordinary_definition_issues {
                    failures.push(format!("{file}: {issue}"));
                }
                // A mutant counts only when it is refused as its kind of statement requires
                // (B1A-D54; B1A-02b). A Bool door must be a Definite refutation: its
                // complement is a kernel-checked theorem. Any other statement (the Int
                // division and Member mutants) must be refused as a type mismatch, never for
                // an unknown name, a parse error or anything else; that shape alone does not
                // tell a wrong literal from a stuck reduction, so it is not a refutation:
                // what shows the reduction runs is the file's positive theorems over the
                // same terms with the right literal (div_neg, mod_neg, member_head), which
                // the row requires to be accepted.
                for (mutant, result, class) in mutants {
                    let refused_as_required = match (mutant_door(mutant), result, class) {
                        (Some(_), Err(_), Some(class)) => *class == Rejection::Definite,
                        (None, Err(error), None) => is_type_mismatch(error),
                        _ => false,
                    };
                    if !refused_as_required {
                        let required = if mutant_door(mutant).is_some() {
                            "a Definite refutation"
                        } else {
                            "a type-mismatch refusal"
                        };
                        failures.push(format!(
                            "{file}: mutant `{mutant}` was not {required}: {result:?} (class {class:?})"
                        ));
                    }
                }
            }
            (Measured::Fail { detail, workaround }, Observed::Refused(error)) => {
                let refused_while_elaborating = matches!(
                    error,
                    ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate { unit, detail: text })
                        if unit == file && text.contains(detail)
                );
                if !refused_while_elaborating {
                    failures.push(format!("{file}: refused for another reason: {error}"));
                }
                let workaround_passes =
                    CAPABILITIES.iter().zip(&observed).any(|(other, (_, seen))| {
                        other.file == workaround
                            && matches!(other.measured, Measured::Pass { .. })
                            && matches!(seen, Observed::Elaborated { .. })
                    });
                if !workaround_passes {
                    failures.push(format!("{file}: workaround {workaround} is not a passing row"));
                }
            }
            (Measured::Pass { .. }, Observed::Refused(error)) => {
                failures.push(format!("{file}: measured pass, now refused: {error}"));
            }
            (Measured::Fail { .. }, Observed::Elaborated { .. }) => {
                failures.push(format!("{file}: measured failure, now elaborates"));
            }
        }
    }
    assert!(failures.is_empty(), "the capability matrix drifted:\n{}", failures.join("\n"));
}

/// B1A-02b's capability files: the Bool door (B1A-D54), the certification audit's reach,
/// and the auxiliary constants Clean generates (B1A-D61). They sit beside B1A-02a's
/// feature files and are tested by `clean_capabilities_doors`.
#[cfg(feature = "test-support")]
const DOOR_FILES: &[(&str, &str)] = &[
    ("door_bool_check", include_str!("model_prelude/capabilities/door_bool_check.lean")),
    ("audit_reach", include_str!("model_prelude/capabilities/audit_reach.lean")),
    ("aux_constants", include_str!("model_prelude/capabilities/aux_constants.lean")),
];

/// The source of a capability file, from either matrix.
#[cfg(feature = "test-support")]
fn capability_source(file: &str) -> &'static str {
    CAPABILITIES
        .iter()
        .map(|row| (row.file, row.source))
        .chain(DOOR_FILES.iter().copied())
        .find(|(name, _)| *name == file)
        .map(|(_, source)| source)
        .unwrap_or_else(|| panic!("no capability file {file}"))
}

/// The door expression of a mutant `theorem <name> : <door> = true := rfl`, if it is a
/// closed Bool door; `None` for any other statement.
#[cfg(feature = "test-support")]
fn mutant_door(mutant: &str) -> Option<&str> {
    let rest = mutant.strip_prefix("theorem ")?;
    let (name, statement) = rest.split_once(" : ")?;
    if name.contains(char::is_whitespace) {
        return None;
    }
    statement.strip_suffix(" = true := rfl")
}

/// A refusal while elaborating whose detail is Clean's type-mismatch shape: the
/// statement elaborated up to its proof, and the proof does not have its type.
#[cfg(feature = "test-support")]
fn is_type_mismatch(error: &ModelPreludeError) -> bool {
    matches!(
        error,
        ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate { detail, .. })
            if detail.contains(DEFINITE_MISMATCH)
    )
}

/// Elaborate door statement `statement` as theorem `name` (`= true`) in a clone of
/// `prelude` and check it; the refusal, if any, with its B1A-D54 class.
fn try_door(
    prelude: &ModelPrelude,
    statement: &DoorStatement<'_>,
    name: &str,
) -> (Result<(), ModelPreludeError>, Option<Rejection>) {
    let mut attempt = prelude.clone();
    let result = elaborate_model_suffix(&mut attempt, &statement.source(name, true), "door")
        .and_then(|()| check_model_theorem(attempt.environment(), &statement.qualified(name)));
    let class = result.as_ref().err().map(|error| classify_rejection(prelude, statement, error));
    (result, class)
}

/// Whether `name` is a constant, inductive, constructor or recursor of `environment`.
#[cfg(feature = "test-support")]
fn has_name(environment: &clean_kernel::env::Environment, name: &Name) -> bool {
    environment.get_const(name).is_some()
        || environment.get_inductive(name).is_some()
        || environment.get_constructor(name).is_some()
        || environment.get_recursor(name).is_some()
}

/// The theorems a capability or sanity file added to `base`, sorted.
fn added_theorems(prelude: &ModelPrelude, base: &[Name]) -> Vec<String> {
    let environment = prelude.environment();
    let mut theorems: Vec<String> = prelude_added_constants(environment)
        .into_iter()
        .filter(|name| !base.contains(name))
        .filter(|name| {
            environment
                .get_const(name)
                .is_some_and(|constant| constant.kind == ConstantKind::Theorem)
        })
        .map(|name| name.to_string())
        .collect();
    theorems.sort();
    theorems
}

/// The complete constant closure Clean's certification audit walks for `theorem`
/// (`Environment::audit_certification`, the audit `checked_theorem` applies), and
/// whether it certified.
#[cfg(feature = "test-support")]
fn audited_closure(prelude: &ModelPrelude, theorem: &str) -> (bool, Vec<String>) {
    let environment = prelude.environment();
    let constant =
        environment.get_const(&Name::from_string(theorem)).expect("the theorem is registered");
    let proof = constant.value.as_ref().expect("a theorem has a proof");
    let audit = environment.audit_certification(&constant.type_, proof);
    (audit.is_certified(), audit.dependencies.iter().map(ToString::to_string).collect())
}

/// Recursor motive counts, measured: one motive per type of the block plus one per
/// distinct nested instantiation (List X, Option X, X × Y, ... of a block type), the
/// rule Clean shares with Lean's nested elimination. For the design's Expr/Act
/// (10:126-162) the rule gives 12 and for its Ctx/SetGen/XVal (10:230-249, Frame
/// inlined) 10; those blocks are declared and measured by B1A-12 and B1A-14a. B1A-12
/// declared Expr/Act (now 10:130-161) and measured 12 (`syntax_recursor_motives`).
#[cfg(feature = "test-support")]
const MOTIVES: &[(&str, &str, u32)] = &[
    ("nested_value", "Trust.Model.Value.rec", 4),
    ("mutual_expr_act", "Trust.Model.Expr.rec", 10),
    ("mutual_expr_act", "Trust.Model.Act.rec", 10),
    ("mutual_expr_act", "Trust.Model.Expr.casesOn", 10),
    ("mutual_ctx_single_ctor", "Trust.Model.Ctx.rec", 8),
    ("audit_reach", "Trust.Model.Value.rec", 4),
    ("audit_reach", "Trust.Model.Value.rec_2", 4),
    ("audit_reach", "Trust.Model.Expr.rec", 2),
];

/// Each audit theorem of `audit_reach.lean` and constants its audited closure must
/// contain, so the audit is not passed vacuously.
#[cfg(feature = "test-support")]
const AUDIT_REACH: &[(&str, &[&str])] = &[
    ("Trust.Model.audit_nested", &["Trust.Model.Value.count", "Trust.Model.Value.rec"]),
    ("Trust.Model.audit_nested_aux", &["Trust.Model.Value.countList", "Trust.Model.Value.rec_1"]),
    (
        "Trust.Model.audit_nested_aux_pairs",
        &["Trust.Model.Value.countPairs", "Trust.Model.Value.rec_2"],
    ),
    ("Trust.Model.audit_mutual", &["Trust.Model.Expr.depth", "Trust.Model.Expr.rec"]),
    ("Trust.Model.audit_mutual_act", &["Trust.Model.Act.depth", "Trust.Model.Act.rec"]),
    // Field notation is the kernel's projection node on Spec: the closure reaches the
    // structure and its constructor, and the audit type-checks the projections.
    ("Trust.Model.audit_projection", &["Trust.Model.Spec", "Trust.Model.Spec.mk"]),
    // Naming the projection function reaches the projection definition.
    ("Trust.Model.audit_projection_fn", &["Trust.Model.Spec.next", "Trust.Model.Spec.mk"]),
    ("Trust.Model.audit_fuel", &["Trust.Model.runFuel", "Nat.rec"]),
    ("Trust.Model.audit_match", &["Trust.Model.Value.isSet", "Trust.Model.Value.casesOn"]),
];

/// B1A-02b: Clean capability matrix II at trust's Clean pin (`08084daa09`): the Bool door
/// and the rejection classes (B1A-D54), the certification audit on nested, mutual,
/// projection, fuel and match-compiled closures, recursor motive counts, and the
/// auxiliary constants Clean generates, classified against `Environment::with_prelude()`
/// (B1A-D61). Each file is elaborated on a fresh copy of the base prelude.
#[test]
#[cfg(feature = "test-support")]
#[cfg_attr(debug_assertions, ignore = "release-only: kernel reduction")]
fn clean_capabilities_doors() {
    use trust_spec_temporal::model_prelude::with_model_prelude_prefix;

    let (log, failures) = with_model_prelude_prefix("Trust.FiniteModel", |base| {
        let mut log: Vec<String> = Vec::new();
        let mut failures: Vec<String> = Vec::new();
        let base_names = prelude_added_constants(base.environment());
        let kernel_prelude = clean_kernel::env::Environment::with_prelude();
        let elaborated = |file: &'static str| {
            let mut prelude = base.clone();
            elaborate_model_suffix(&mut prelude, capability_source(file), file).map(|()| prelude)
        };
        // Every theorem of a file is accepted by the acceptance path (audit included).
        let accept_all = |file: &str, prelude: &ModelPrelude, failures: &mut Vec<String>| {
            let theorems = added_theorems(prelude, &base_names);
            for theorem in &theorems {
                if let Err(error) = check_model_theorem(prelude.environment(), theorem) {
                    failures.push(format!("{file}: {theorem} refused: {error}"));
                }
            }
            theorems
        };

        // ---- (1) the door and the rejection classes ----
        match elaborated("door_bool_check") {
            Err(error) => failures.push(format!("door_bool_check: refused: {error}")),
            Ok(doors) => {
                let theorems = accept_all("door_bool_check", &doors, &mut failures);
                let expected = [
                    "Trust.Model.chain_door_long",
                    "Trust.Model.chain_door_short",
                    "Trust.Model.door_pass",
                ];
                if theorems != expected {
                    failures.push(format!("door_bool_check: theorems {theorems:?}"));
                }
                // (statement, theorem name, expected class, expected refusal shape)
                let cases: [(DoorStatement<'_>, &str, Rejection, Option<&str>); 8] = [
                    (model("", "checkSum 100 5051"), "door_mutated", Rejection::Definite, Some(DEFINITE_MISMATCH)),
                    (model("(n : Nat)", "checkSum n 0"), "door_stuck_fvar", Rejection::Stuck, Some(DEFINITE_MISMATCH)),
                    // Under an empty binder type the complement `∀ h, door = false` is
                    // provable (the door is closed and false) but refutes nothing: the
                    // statement `∀ h : False, door = true` is vacuously true. Not Definite.
                    (model("(h : False)", "checkSum 100 5051"), "door_vacuous_binder", Rejection::Stuck, Some(DEFINITE_MISMATCH)),
                    (model("", "chain 20000"), "door_lazy_delta", Rejection::Stuck, Some(STUCK)),
                    (model("", "checkSumX 100 5050"), "door_unknown_name", Rejection::Other, None),
                    // An unbound name in a binder-free door. With Clean's default
                    // `autoImplicit` it would become a hidden `∀ {h : False}`: the false door
                    // `checkSum 100 5051 && _` would then have a provable complement that
                    // refutes nothing, and be classified Definite. `DoorStatement::source`
                    // turns `autoImplicit` off, so it is an unknown identifier: Other (B1A-09).
                    (model("", "Bool.and (checkSum 100 5051) ((fun (_ : False) => true) h)"), "door_auto_bound_empty", Rejection::Other, None),
                    (model("", "checkSum 100 true"), "door_ill_typed", Rejection::Other, None),
                    (model("", "checkSum 100 = ="), "door_parse_error", Rejection::Other, None),
                ];
                for (statement, name, class, shape) in &cases {
                    let (result, measured) = try_door(&doors, statement, name);
                    log.push(format!("door {name} `{}`: class {measured:?}; {result:?}", statement.door));
                    if measured != Some(*class) {
                        failures.push(format!("door {name}: class {measured:?}, expected {class:?}: {result:?}"));
                    }
                    if let Some(shape) = shape {
                        let shaped = matches!(&result, Err(ModelPreludeError::Clean(
                            CleanTemporalCertificateError::Elaborate { detail, .. })) if detail.contains(shape));
                        if !shaped {
                            failures.push(format!("door {name}: refusal is not of shape {shape:?}: {result:?}"));
                        }
                    }
                }
                // The non-door chain is accepted while it is short: the give-up is the
                // lazy-delta cap, not the statement.
                let (short, _) = try_door(&doors, &model("", "chain 100"), "chain_nondoor_short");
                if short.is_err() {
                    failures.push(format!("chain 100 (non-door) refused: {short:?}"));
                }

                // Budget: the ticks the door costs, then the same door under half of them.
                let budget_door = model("", "checkSum 2000 2001000");
                let (used, unstarved) = {
                    let _outer = OuterBudget::arm(MODEL_DECL_BUDGET);
                    let (result, _) = try_door(&doors, &budget_door, "door_budget_full");
                    (clean_kernel::tc::declaration_budget_used(), result)
                };
                log.push(format!("door door_budget_full: {used} ticks; {unstarved:?}"));
                if unstarved.is_err() || used < 2 {
                    failures.push(format!("door_budget_full: {unstarved:?} with {used} ticks"));
                } else {
                    let (starved, latch) = {
                        let _outer = OuterBudget::arm(used / 2);
                        let mut attempt = doors.clone();
                        let result = elaborate_model_suffix(
                            &mut attempt,
                            &budget_door.source("door_budget_starved", true),
                            "starved door",
                        );
                        (result, clean_kernel::tc::declaration_budget_exhausted())
                    };
                    let class = starved.as_ref().err().map(|error| classify_rejection(&doors, &budget_door, error));
                    log.push(format!("door door_budget_starved ({} ticks): class {class:?}; latch {latch}; {starved:?}", used / 2));
                    let told_apart = matches!(&starved, Err(error @ ModelPreludeError::BudgetExhausted { .. })
                        if error.to_string().contains("ran out") && !error.to_string().contains("TypeMismatch"));
                    if !(latch && told_apart && class == Some(Rejection::Budget)) {
                        failures.push(format!("starved door not told apart: latch {latch}, class {class:?}: {starved:?}"));
                    }
                    let starved_check = {
                        let _outer = OuterBudget::arm(1);
                        check_model_theorem(doors.environment(), "Trust.Model.door_pass")
                    };
                    if !matches!(starved_check, Err(ModelPreludeError::BudgetExhausted { .. })) {
                        failures.push(format!("starved check of door_pass: {starved_check:?}"));
                    }
                }

                // A heartbeat stop that carries Clean's heartbeat text: under `set_option
                // maxHeartbeats 1` the kernel check that registers a true door runs out of
                // heartbeats. It is Budget. (At the default limit the elaborator's own
                // def-eq gives up first and reports the door's TypeMismatch instead, with
                // no heartbeat text: `budget_calibration`'s heartbeat probe.)
                let heartbeat_door = model("", "checkSum 100 5050");
                let mut attempt = doors.clone();
                let heartbeat = elaborate_model_suffix(
                    &mut attempt,
                    "namespace Trust\nnamespace Model\nset_option maxHeartbeats 1 in\n\
                     theorem door_heartbeat : (checkSum 100 5050) = true := rfl\nend Model\nend Trust\n",
                    "heartbeat door",
                )
                .and_then(|()| check_model_theorem(attempt.environment(), "Trust.Model.door_heartbeat"));
                let class = heartbeat.as_ref().err().map(|error| classify_rejection(&doors, &heartbeat_door, error));
                log.push(format!("door door_heartbeat (maxHeartbeats 1): class {class:?}; {heartbeat:?}"));
                let carries_heartbeat = matches!(&heartbeat, Err(error)
                    if { let text = error.to_string(); text.contains(HEARTBEAT_EXCEEDED) || text.contains(HEARTBEAT_EXCEEDED_VARIANT) });
                if !(carries_heartbeat && class == Some(Rejection::Budget)) {
                    failures.push(format!("heartbeat door: class {class:?}, expected Budget with heartbeat text: {heartbeat:?}"));
                }
            }
        }

        // ---- (2) the certification audit on nested, mutual, projection, fuel, match ----
        let mut prelude_leaves: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
        let mut leaves_of = |prelude: &ModelPrelude, theorem: &str, failures: &mut Vec<String>| {
            let (certified, closure) = audited_closure(prelude, theorem);
            if !certified {
                failures.push(format!("{theorem}: audit_certification did not certify"));
            }
            // Structural recursion compiles to `X.rec` at this pin, so no audited closure
            // reaches a generated `below`/`brecOn` (B1A-D61).
            for name in closure.iter().filter(|name| matches!(name.rsplit('.').next(), Some("below" | "brecOn"))) {
                failures.push(format!("{theorem}: audited closure reaches {name}"));
            }
            for name in closure.iter().filter(|name| !name.starts_with("Trust.")) {
                if has_name(&kernel_prelude, &Name::from_string(name)) {
                    prelude_leaves.insert(name.clone());
                } else {
                    failures.push(format!("{theorem}: closure constant {name} is neither Trust.* nor in with_prelude()"));
                }
            }
            closure
        };
        match elaborated("audit_reach") {
            Err(error) => failures.push(format!("audit_reach: refused: {error}")),
            Ok(audit) => {
                let theorems = accept_all("audit_reach", &audit, &mut failures);
                let mut expected: Vec<&str> = AUDIT_REACH.iter().map(|(theorem, _)| *theorem).collect();
                expected.sort_unstable();
                if theorems != expected {
                    failures.push(format!("audit_reach: theorems {theorems:?}, expected {expected:?}"));
                }
                for (theorem, required) in AUDIT_REACH {
                    let closure = leaves_of(&audit, theorem, &mut failures);
                    let missing: Vec<&&str> = required.iter().filter(|name| !closure.iter().any(|c| c == **name)).collect();
                    let own: Vec<&String> = closure.iter().filter(|name| name.starts_with("Trust.")).collect();
                    log.push(format!(
                        "audit {theorem}: certified closure of {} constants, requires {required:?}; Trust.*: {own:?}",
                        closure.len()
                    ));
                    if !missing.is_empty() {
                        failures.push(format!("{theorem}: audited closure lacks {missing:?}"));
                    }
                }
            }
        }

        // ---- motive counts ----
        for (file, recursor, motives) in MOTIVES {
            match elaborated(file) {
                Err(error) => failures.push(format!("{file}: refused: {error}")),
                Ok(prelude) => {
                    let measured = prelude
                        .environment()
                        .get_recursor(&Name::from_string(recursor))
                        .map(|recursor| recursor.num_motives);
                    log.push(format!("motives {recursor} ({file}): {measured:?}"));
                    if measured != Some(*motives) {
                        failures.push(format!("{recursor} ({file}): {measured:?} motives, expected {motives}"));
                    }
                }
            }
        }

        // ---- (3) the base prelude's own additions, classified against with_prelude() ----
        // Every name the base prelude (Trust.Temporal, Trust.FiniteModel) adds is outside
        // `with_prelude()` by construction (`prelude_added_constants`). The elaborator
        // adds `PProd` and its auxiliaries itself (for FiniteModel's directly recursive
        // `ScalarExpr`, whose `below`/`brecOn` need it): kernel-prelude-like constants that
        // are not `with_prelude()` constants, hence not closure-coverage leaves.
        {
            let foreign: Vec<String> = base_names
                .iter()
                .map(ToString::to_string)
                .filter(|name| !name.starts_with("Trust."))
                .collect();
            log.push(format!("base prelude: {} added names; outside Trust.*: {foreign:?}", base_names.len()));
            if foreign != BASE_FOREIGN_ADDED {
                failures.push(format!("base prelude: names outside Trust.* {foreign:?}, expected {BASE_FOREIGN_ADDED:?}"));
            }
            if has_name(&kernel_prelude, &Name::from_string("PProd")) {
                failures.push("PProd is now a with_prelude() constant: re-classify BASE_FOREIGN_ADDED".to_owned());
            }
            let below: Vec<String> = base_names
                .iter()
                .map(ToString::to_string)
                .filter(|name| matches!(name.rsplit('.').next(), Some("below" | "brecOn")))
                .collect();
            let auxiliaries = base_names.iter().filter(|name| is_auxiliary(&name.to_string())).count();
            log.push(format!("base prelude: {auxiliaries} generated auxiliaries; below/brecOn: {below:?}"));
            if below != BASE_BELOW_BRECON {
                failures.push(format!("base prelude: below/brecOn {below:?}, expected {BASE_BELOW_BRECON:?}"));
            }
        }

        // ---- (4) auxiliary constants and `++`, classified against with_prelude() ----
        match elaborated("aux_constants") {
            Err(error) => failures.push(format!("aux_constants: refused: {error}")),
            Ok(aux) => {
                let theorems = accept_all("aux_constants", &aux, &mut failures);
                let environment = aux.environment();
                let added: Vec<Name> = prelude_added_constants(environment)
                    .into_iter()
                    .filter(|name| !base_names.contains(name))
                    .collect();
                let mut generated = Vec::new();
                for name in &added {
                    let text = name.to_string();
                    let kind = if environment.get_inductive(name).is_some() {
                        "inductive"
                    } else if environment.get_constructor(name).is_some() {
                        "constructor"
                    } else if environment.get_recursor(name).is_some() {
                        "recursor"
                    } else {
                        match environment.get_const(name).map(|constant| constant.kind) {
                            Some(ConstantKind::Theorem) => "theorem",
                            Some(ConstantKind::Definition) => "definition",
                            other => {
                                failures.push(format!("aux: {text} has kind {other:?}"));
                                "other"
                            }
                        }
                    };
                    let in_kernel_prelude = has_name(&kernel_prelude, name);
                    let body: Vec<String> = environment
                        .get_const(name)
                        .filter(|constant| constant.kind == ConstantKind::Definition)
                        .and_then(|constant| constant.value.as_ref())
                        .map(|value| {
                            let mut names: Vec<String> =
                                value.collect_constants().into_iter().map(|name| name.to_string()).collect();
                            names.sort();
                            names
                        })
                        .unwrap_or_default();
                    log.push(format!(
                        "aux {text}: {kind}; in with_prelude(): {in_kernel_prelude}; body constants {body:?}"
                    ));
                    if in_kernel_prelude {
                        failures.push(format!("aux: {text} shadows a with_prelude() constant"));
                    }
                    if is_auxiliary(&text) {
                        generated.push(format!("{text} ({kind})"));
                    }
                }
                let expected: Vec<String> = AUX_GENERATED.iter().map(|name| (*name).to_owned()).collect();
                if generated != expected {
                    failures.push(format!("aux: generated auxiliaries {generated:#?}, expected {expected:#?}"));
                }
                // `List ++`: the constants appendAll's body elaborates to.
                let body = environment
                    .get_const(&Name::from_string("Trust.Model.appendAll"))
                    .and_then(|constant| constant.value.as_ref())
                    .map(|value| {
                        let mut names: Vec<String> = value.collect_constants().into_iter().map(|name| name.to_string()).collect();
                        names.sort();
                        names
                    });
                log.push(format!("aux `++` (appendAll body): {body:?}"));
                if body.as_deref() != Some(&APPEND_CONSTANTS.iter().map(|name| (*name).to_owned()).collect::<Vec<_>>()[..]) {
                    failures.push(format!("aux: `++` elaborates to {body:?}, expected {APPEND_CONSTANTS:?}"));
                }
                for name in APPEND_CONSTANTS {
                    if !has_name(&kernel_prelude, &Name::from_string(name)) {
                        failures.push(format!("aux: `++` constant {name} is not in with_prelude()"));
                    }
                }
                // Structural recursion by equations compiles to the recursor, not brecOn.
                let size_body = environment
                    .get_const(&Name::from_string("Trust.Model.Tree.size"))
                    .and_then(|constant| constant.value.as_ref())
                    .map(|value| {
                        let mut names: Vec<String> = value.collect_constants().into_iter().map(|name| name.to_string()).collect();
                        names.sort();
                        names
                    })
                    .unwrap_or_default();
                log.push(format!("aux Tree.size body: {size_body:?}"));
                let reaches_brec = size_body.iter().any(|name| matches!(name.rsplit('.').next(), Some("below" | "brecOn")));
                if !size_body.iter().any(|name| name == "Trust.Model.Tree.rec") || reaches_brec {
                    failures.push(format!("aux: Tree.size's body is not compiled to Tree.rec alone: {size_body:?}"));
                }
                // Nested proofs (B1A-09): a Subtype literal's proof term, at the top of a
                // body and under a binder. The measured result is pinned: the proof stays
                // inline in the definition's own body (no `<def>.proof_N` is generated;
                // AUX_GENERATED would list one), so the body names `Subtype.mk` and the
                // proof's own constants.
                for (definition, required) in NESTED_PROOF_BODIES {
                    let body = environment
                        .get_const(&Name::from_string(definition))
                        .and_then(|constant| constant.value.as_ref())
                        .map(|value| {
                            let mut names: Vec<String> = value.collect_constants().into_iter().map(|name| name.to_string()).collect();
                            names.sort();
                            names
                        })
                        .unwrap_or_default();
                    log.push(format!("aux {definition} body: {body:?}"));
                    if body.iter().any(|name| is_auxiliary(name)) || required.iter().any(|name| !body.iter().any(|b| b == name)) {
                        failures.push(format!("aux: {definition}'s body {body:?} does not hold its proof inline (requires {required:?})"));
                    }
                }
                for theorem in &theorems {
                    let closure = leaves_of(&aux, theorem, &mut failures);
                    // The recursive equation definition is certified through its recursor.
                    if theorem == "Trust.Model.aux_tree_size" {
                        for required in ["Trust.Model.Tree.size", "Trust.Model.Tree.rec"] {
                            if !closure.iter().any(|name| name == required) {
                                failures.push(format!("{theorem}: audited closure lacks {required}"));
                            }
                        }
                    }
                }
            }
        }
        // Every non-Trust constant an audited closure reaches is a with_prelude() constant:
        // the kernel-prelude leaves closure coverage classifies (B1A-D61).
        log.push(format!("with_prelude() leaves reached ({}): {prelude_leaves:?}", prelude_leaves.len()));
        (log, failures)
    })
    .expect("the base prelude elaborates");
    for line in &log {
        println!("{line}");
    }
    assert!(failures.is_empty(), "the capability matrix II drifted:\n{}", failures.join("\n"));
}

/// A door statement in namespace `Trust.Model`.
#[cfg(feature = "test-support")]
fn model<'a>(binders: &'a str, door: &'a str) -> DoorStatement<'a> {
    DoorStatement { namespace: "Trust.Model", binders, door }
}

/// The auxiliary constants Clean generates for `aux_constants.lean` at trust's Clean pin
/// (`08084daa09`), with their kind: the measured classification input of closure
/// coverage (B1A-D61). None is in `Environment::with_prelude()`. Per inductive Clean
/// generates casesOn and recOn (recursor-table entries) and, except for a Prop former,
/// the definitions noConfusion and noConfusionType; rec_N per nested instantiation; and
/// the definitions below and brecOn for a directly recursive type that is not mutual,
/// not nested and not a Prop former (Tree; clean-kernel env/inductive_builder.rs Pass 3,
/// env/inductive_below.rs `should_generate_below`), which need PProd: the elaborator
/// adds PProd and its auxiliaries itself (`BASE_FOREIGN_ADDED`, already present after
/// the base prelude). No match_N or proof_N: a `match` (nested constructor patterns
/// included) compiles to casesOn applications in the definition's own body, a `where`
/// helper with structural recursion to List.rec in the body, structural recursion by
/// equations (Tree.size) to Tree.rec, never to brecOn, `if` to the kernel prelude's
/// `ite`, and field notation to the kernel's projection node.
#[cfg(feature = "test-support")]
const AUX_GENERATED: &[&str] = &[
    "Trust.Model.Kind.casesOn (recursor)",
    "Trust.Model.Kind.noConfusion (definition)",
    "Trust.Model.Kind.noConfusionType (definition)",
    "Trust.Model.Kind.recOn (recursor)",
    "Trust.Model.Leftmost.casesOn (recursor)",
    "Trust.Model.Leftmost.recOn (recursor)",
    "Trust.Model.MEven.casesOn (recursor)",
    "Trust.Model.MEven.noConfusion (definition)",
    "Trust.Model.MEven.noConfusionType (definition)",
    "Trust.Model.MEven.recOn (recursor)",
    "Trust.Model.MOdd.casesOn (recursor)",
    "Trust.Model.MOdd.noConfusion (definition)",
    "Trust.Model.MOdd.noConfusionType (definition)",
    "Trust.Model.MOdd.recOn (recursor)",
    "Trust.Model.Pair.casesOn (recursor)",
    "Trust.Model.Pair.noConfusion (definition)",
    "Trust.Model.Pair.noConfusionType (definition)",
    "Trust.Model.Pair.recOn (recursor)",
    "Trust.Model.Tree.below (definition)",
    "Trust.Model.Tree.brecOn (definition)",
    "Trust.Model.Tree.casesOn (recursor)",
    "Trust.Model.Tree.noConfusion (definition)",
    "Trust.Model.Tree.noConfusionType (definition)",
    "Trust.Model.Tree.recOn (recursor)",
    "Trust.Model.Value.casesOn (recursor)",
    "Trust.Model.Value.noConfusion (definition)",
    "Trust.Model.Value.noConfusionType (definition)",
    "Trust.Model.Value.recOn (recursor)",
    "Trust.Model.Value.rec_1 (recursor)",
];

/// The names the base prelude (Trust.Temporal, Trust.FiniteModel) adds outside `Trust.*`,
/// measured at trust's Clean pin: `PProd` and its auxiliaries, which the elaborator adds
/// itself (they are not `Environment::with_prelude()` constants) so that FiniteModel's
/// `ScalarExpr` gets `below`/`brecOn`. They are not closure-coverage leaves: a closure
/// that reaches one fails the walk (B1A-D61).
#[cfg(feature = "test-support")]
const BASE_FOREIGN_ADDED: &[&str] = &[
    "PProd",
    "PProd.casesOn",
    "PProd.fst",
    "PProd.mk",
    "PProd.noConfusion",
    "PProd.noConfusionType",
    "PProd.rec",
    "PProd.recOn",
    "PProd.snd",
    "PProd.swap",
];

/// The `below`/`brecOn` definitions the base prelude adds: its one directly recursive,
/// non-mutual, non-nested, non-Prop inductive, FiniteModel.lean's `ScalarExpr`.
#[cfg(feature = "test-support")]
const BASE_BELOW_BRECON: &[&str] = &[
    "Trust.Temporal.FiniteModel.ScalarExpr.below",
    "Trust.Temporal.FiniteModel.ScalarExpr.brecOn",
];

/// The definitions of `aux_constants.lean` whose bodies hold a proof term, and constants
/// their bodies must name: the proof stays inline (measured at trust's Clean pin, B1A-09).
#[cfg(feature = "test-support")]
const NESTED_PROOF_BODIES: &[(&str, &[&str])] = &[
    ("Trust.Model.boundedTwo", &["Subtype.mk", "rfl"]),
    ("Trust.Model.boundedOf", &["Subtype.mk", "Bool.rec", "rfl"]),
];

/// The constants `xs ++ ys` on `List Nat` elaborates to (every one a
/// `with_prelude()` constant).
#[cfg(feature = "test-support")]
const APPEND_CONSTANTS: &[&str] = &["HAppend.hAppend", "List", "Nat", "instHAppendListList"];

/// Whether `name` is an auxiliary constant generated by Clean's elaborator, by its last
/// component: casesOn, recOn, below, brecOn, noConfusion(Type), rec_N, match_N, proof_N.
#[cfg(feature = "test-support")]
fn is_auxiliary(name: &str) -> bool {
    let last = name.rsplit('.').next().unwrap_or(name);
    let numbered = |prefix: &str| {
        last.strip_prefix(prefix)
            .is_some_and(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
    };
    matches!(last, "casesOn" | "recOn" | "below" | "brecOn" | "noConfusion" | "noConfusionType")
        || numbered("rec_")
        || numbered("match_")
        || numbered("proof_")
}

/// The calibration loop: the B1A-D07 block's shape (a non-recursive step taking `go`,
/// `Nat.rec` over fuel), where `Job.count k` takes `k` more steps, so
/// `Tlc.run (n + 1) (Job.count n)` takes `n + 1` steps, behind a Bool door.
#[cfg(feature = "test-support")]
const CALIBRATION_LOOP: &str = "namespace Trust
namespace Model
inductive Job where
  | count : Nat → Job
inductive Res where
  | ok   : Nat → Res
  | fuel : Res
def Tlc.step (go : Job → Res) (j : Job) : Res :=
  @Job.rec (fun _ => Res)
    (fun k => @Nat.rec (fun _ => Res) (Res.ok 0) (fun k' _ => go (Job.count k')) k) j
def Tlc.run (n : Nat) : Job → Res :=
  @Nat.rec (fun _ => Job → Res) (fun _ => Res.fuel) (fun _ go => Tlc.step go) n
def Res.isOk (r : Res) : Bool := @Res.rec (fun _ => Bool) (fun _ => true) false r
end Model
end Trust
";

/// The calibration sizes: steps of the loop, doubling up to 200 000.
#[cfg(feature = "test-support")]
const CALIBRATION_STEPS: &[u64] = &[3_125, 6_250, 12_500, 25_000, 50_000, 100_000, 200_000];

/// The heartbeat probe: the same loop, doubling on past the calibration until the first
/// resource stop, so a real stop is produced and classified (B1A-02b repair round).
#[cfg(feature = "test-support")]
const HEARTBEAT_PROBE_STEPS: &[u64] = &[400_000, 800_000, 1_600_000];

/// One calibration size: its outcome, ticks, wall seconds, the RSS after its calls
/// (post-call, read with `ps`), and the process's peak RSS so far (`ru_maxrss`, which
/// includes the peak during its calls).
#[cfg(feature = "test-support")]
#[derive(Debug)]
struct CalibrationRow {
    steps: u64,
    outcome: String,
    elaboration_ticks: u64,
    check_ticks: u64,
    elaboration_s: f64,
    check_s: f64,
    post_call_rss_kib: Option<u64>,
    max_rss_kib: Option<u64>,
}

/// This process's peak resident set size so far, in KiB: `getrusage(RUSAGE_SELF)`'s
/// `ru_maxrss` (bytes on macOS, KiB on Linux), the high-water mark that a sample taken
/// after a call misses (B1A-09, carried verifier finding on D37). `None` if the call fails.
#[cfg(feature = "test-support")]
fn max_rss_kib() -> Option<u64> {
    /// `struct rusage`: two `struct timeval`s (16 bytes each on 64-bit macOS and Linux),
    /// then 14 `long`s, the first `ru_maxrss`.
    #[repr(C)]
    struct RUsage {
        utime: [i64; 2],
        stime: [i64; 2],
        maxrss: i64,
        rest: [i64; 13],
    }
    extern "C" {
        fn getrusage(who: i32, usage: *mut RUsage) -> i32;
    }
    const RUSAGE_SELF: i32 = 0;
    let mut usage = RUsage { utime: [0; 2], stime: [0; 2], maxrss: 0, rest: [0; 13] };
    // SAFETY: `usage` is a live, writable `struct rusage` of the platform's layout, and
    // getrusage writes only into it.
    let status = unsafe { getrusage(RUSAGE_SELF, &mut usage) };
    if status != 0 {
        return None;
    }
    let maxrss = u64::try_from(usage.maxrss).ok()?;
    Some(if cfg!(target_os = "macos") { maxrss / 1024 } else { maxrss })
}

/// This process's resident set size now, in KiB, read with `ps` (`None` if unreadable).
#[cfg(feature = "test-support")]
fn rss_kib() -> Option<u64> {
    let output = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &std::process::id().to_string()])
        .output()
        .ok()?;
    String::from_utf8(output.stdout).ok()?.trim().parse().ok()
}

/// Run the calibration door at `steps` steps on a clone of `prelude` (which holds the
/// calibration loop): elaborate it, then kernel-check it, each phase under
/// `MODEL_DECL_BUDGET` armed here so the ticks it spends can be read. The outcome is
/// `pass`, `stop: DeclarationBudgetExhausted` (the API's `BudgetExhausted`), `stop:
/// HeartbeatExceeded` (class Budget, a refusal carrying Clean's heartbeat text), `stop:
/// Stuck` (a door-shaped refusal whose complement is refused too: the door is true by
/// construction, so only a resource can have stopped it; `budget_calibration` confirms
/// which), or `FAIL (<class>): <error>` for anything else (Definite or Other).
#[cfg(feature = "test-support")]
fn calibration_row(prelude: &ModelPrelude, steps: u64) -> CalibrationRow {
    let door = format!("Res.isOk (Tlc.run {} (Job.count {}))", steps + 1, steps);
    let statement = model("", &door);
    let name = format!("calibration_{steps}");
    let mut attempt = prelude.clone();
    let started = std::time::Instant::now();
    let (elaborated, elaboration_ticks) = {
        let _outer = OuterBudget::arm(MODEL_DECL_BUDGET);
        let result =
            elaborate_model_suffix(&mut attempt, &statement.source(&name, true), "calibration");
        (result, clean_kernel::tc::declaration_budget_used())
    };
    let elaboration_s = started.elapsed().as_secs_f64();
    let started = std::time::Instant::now();
    let (checked, check_ticks) = match &elaborated {
        Ok(()) => {
            let _outer = OuterBudget::arm(MODEL_DECL_BUDGET);
            let result = check_model_theorem(attempt.environment(), &statement.qualified(&name));
            (result, clean_kernel::tc::declaration_budget_used())
        }
        Err(error) => (Err(error.clone()), 0),
    };
    let check_s = started.elapsed().as_secs_f64();
    let outcome = match &checked {
        Ok(()) => "pass".to_owned(),
        Err(error) => match classify_rejection(prelude, &statement, error) {
            Rejection::Budget if matches!(error, ModelPreludeError::BudgetExhausted { .. }) => {
                "stop: DeclarationBudgetExhausted".to_owned()
            }
            Rejection::Budget if is_heartbeat_stop(error) => "stop: HeartbeatExceeded".to_owned(),
            Rejection::Stuck => "stop: Stuck".to_owned(),
            other => format!("FAIL ({other:?}): {error}"),
        },
    };
    if let Err(error) = &checked {
        let text = error.to_string();
        println!("calibration {steps}: refusal: {}", text.chars().take(600).collect::<String>());
    }
    CalibrationRow {
        steps,
        outcome,
        elaboration_ticks,
        check_ticks,
        elaboration_s,
        check_s,
        post_call_rss_kib: rss_kib(),
        max_rss_kib: max_rss_kib(),
    }
}

/// Whether `error` is Clean's per-type-checker heartbeat stop, in either of the forms a
/// refusal detail carries it (Display, `HEARTBEAT_EXCEEDED`; or Debug,
/// `HEARTBEAT_EXCEEDED_VARIANT`).
#[cfg(feature = "test-support")]
fn is_heartbeat_stop(error: &ModelPreludeError) -> bool {
    let text = error.to_string();
    text.contains(HEARTBEAT_EXCEEDED) || text.contains(HEARTBEAT_EXCEEDED_VARIANT)
}

/// What a kernel type checker says about the calibration door at a probe size.
#[cfg(feature = "test-support")]
#[derive(Debug)]
struct HeartbeatEvidence {
    steps: u64,
    /// `is_def_eq(door, true)` under `DEFAULT_HEARTBEAT_LIMIT`.
    default_limit_equal: bool,
    /// The same checker's next `infer_type`: its error, Display and Debug.
    default_limit_after: Option<(String, String)>,
    /// `is_def_eq(door, true)` with the heartbeat disabled (limit 0).
    unlimited_equal: bool,
}

#[cfg(feature = "test-support")]
impl HeartbeatEvidence {
    /// The door is true, and only the default heartbeat limit stopped the checker.
    fn is_heartbeat_stop(&self) -> bool {
        !self.default_limit_equal
            && self.unlimited_equal
            && self.default_limit_after.as_ref().is_some_and(|(display, debug)| {
                display.contains(HEARTBEAT_EXCEEDED) && debug.contains(HEARTBEAT_EXCEEDED_VARIANT)
            })
    }
}

/// Reduce the calibration door at `steps` steps with Clean's kernel type checker
/// directly, at the default heartbeat limit and with it disabled. The door is declared
/// as a Bool definition (no reduction while elaborating) in a clone of `prelude`.
#[cfg(feature = "test-support")]
fn heartbeat_evidence(prelude: &ModelPrelude, steps: u64) -> HeartbeatEvidence {
    use clean_kernel::expr::Expr;
    use clean_kernel::tc::TypeChecker;

    let mut declared = prelude.clone();
    let source = format!(
        "namespace Trust\nnamespace Model\ndef calibration_value : Bool := Res.isOk (Tlc.run {} (Job.count {}))\nend Model\nend Trust\n",
        steps + 1,
        steps
    );
    elaborate_model_suffix(&mut declared, &source, "calibration value")
        .expect("the door's value is declared");
    let environment = declared.environment();
    let value = environment
        .get_const(&Name::from_string("Trust.Model.calibration_value"))
        .and_then(|constant| constant.value.clone())
        .expect("the door's value is a definition");
    let truth = Expr::const_str("Bool.true");
    let checker = TypeChecker::new(environment);
    let default_limit_equal = checker.is_def_eq(&value, &truth);
    let default_limit_after =
        checker.infer_type(&truth).err().map(|error| (error.to_string(), format!("{error:?}")));
    let mut unlimited = TypeChecker::new(environment);
    unlimited.set_heartbeat_limit(0);
    let unlimited_equal = unlimited.is_def_eq(&value, &truth);
    HeartbeatEvidence { steps, default_limit_equal, default_limit_after, unlimited_equal }
}

/// B1A-02b budget calibration (B1A-D37), run alone under the probe lock
/// (`b1a_ignored model_prelude_kernel budget_calibration`): the calibration loop at
/// doubling sizes up to 200 000 steps (`calibration_row`), then the heartbeat probe,
/// doubling on until the first resource stop. Per size it records pass or the stop, the
/// ticks, the wall time and the RSS. A size whose door is refused for any other reason
/// fails the test: the loop is right by construction, so only a resource may stop it.
/// The sizes after a stop are not run. It prints the RSS growth per tick and the peak
/// RSS projected at the frozen budget under B1A-D37's bound, and asserts that bound.
#[test]
#[cfg(feature = "test-support")]
#[ignore = "B1A-02b measurement: run alone with b1a_ignored (probe lock)"]
fn budget_calibration() {
    use trust_spec_temporal::model_prelude::with_model_prelude_prefix;

    let (baseline_kib, rows, probe, evidence, evidence_max_kib) =
        with_model_prelude_prefix("Trust.FiniteModel", |base| {
            let mut prelude = base.clone();
            elaborate_model_suffix(&mut prelude, CALIBRATION_LOOP, "calibration loop")
                .expect("the calibration loop elaborates");
            let baseline_kib = rss_kib();
            let mut rows: Vec<CalibrationRow> = Vec::new();
            for &steps in CALIBRATION_STEPS {
                let row = calibration_row(&prelude, steps);
                let stopped = row.outcome != "pass";
                rows.push(row);
                if stopped {
                    break;
                }
            }
            let mut probe: Vec<CalibrationRow> = Vec::new();
            if rows.iter().all(|row| row.outcome == "pass") {
                for &steps in HEARTBEAT_PROBE_STEPS {
                    let row = calibration_row(&prelude, steps);
                    let stopped = row.outcome != "pass";
                    probe.push(row);
                    if stopped {
                        break;
                    }
                }
            }
            let evidence = probe
                .last()
                .filter(|row| row.outcome != "pass")
                .map(|row| heartbeat_evidence(&prelude, row.steps));
            (baseline_kib, rows, probe, evidence, max_rss_kib())
        })
        .expect("the base prelude elaborates");

    println!(
        "budget_calibration: MODEL_DECL_BUDGET={MODEL_DECL_BUDGET} \
         DEFAULT_HEARTBEAT_LIMIT=2000000 (clean tc/mod.rs:233) baseline_rss_kib={}",
        baseline_kib.map_or_else(|| "?".to_owned(), |kib| kib.to_string())
    );
    println!(
        "steps\toutcome\telab_ticks\tcheck_ticks\telab_s\tcheck_s\tpost_call_rss_kib\tmax_rss_kib"
    );
    for (label, row) in
        rows.iter().map(|row| ("", row)).chain(probe.iter().map(|row| ("heartbeat probe ", row)))
    {
        let kib = |value: Option<u64>| value.map_or_else(|| "?".to_owned(), |kib| kib.to_string());
        println!(
            "{label}{}\t{}\t{}\t{}\t{:.2}\t{:.2}\t{}\t{}",
            row.steps,
            row.outcome,
            row.elaboration_ticks,
            row.check_ticks,
            row.elaboration_s,
            row.check_s,
            kib(row.post_call_rss_kib),
            kib(row.max_rss_kib)
        );
    }
    let failed: Vec<&String> = rows
        .iter()
        .chain(&probe)
        .map(|row| &row.outcome)
        .filter(|outcome| outcome.starts_with("FAIL"))
        .collect();
    assert!(
        failed.is_empty(),
        "a calibration door was refused for a non-resource reason: {failed:?}"
    );
    assert!(
        rows.len() == CALIBRATION_STEPS.len() && rows.iter().all(|row| row.outcome == "pass"),
        "every calibration size up to 200 000 steps must pass: {rows:?}"
    );
    // The heartbeat probe must end in a resource stop before the declaration budget, and
    // that stop must be Clean's per-type-checker heartbeat: a kernel type checker at the
    // default limit answers "not equal" for the door at that size and then refuses with
    // `HeartbeatExceeded` (whose Display and Debug forms carry `HEARTBEAT_EXCEEDED` and
    // `HEARTBEAT_EXCEEDED_VARIANT`), while one with the heartbeat disabled finds the door
    // true. Measured at clean 08084daa09: the in-process elaborator reports this stop as
    // the door's own `TypeMismatch` (it gives no heartbeat text), so the refusal is
    // classified Stuck, never Definite and never a pass.
    println!("heartbeat probe evidence: {evidence:?}");
    let stop = probe.last().map(|row| row.outcome.as_str());
    assert!(
        matches!(stop, Some("stop: Stuck" | "stop: HeartbeatExceeded")),
        "the heartbeat probe did not end in a resource stop: {probe:?}"
    );
    assert!(
        evidence.as_ref().is_some_and(|evidence| {
            Some(evidence.steps) == probe.last().map(|row| row.steps)
                && evidence.is_heartbeat_stop()
        }),
        "the heartbeat probe's stop is not Clean's heartbeat stop: {evidence:?}"
    );
    // The RSS growth per tick (elaboration plus check) between consecutive calibration
    // sizes, at the worst of them, and B1A-D37's bound on the peak RSS at the frozen
    // budget. Growth is measured twice: on the post-call RSS, and on the peak so far
    // (`ru_maxrss`, which sees the peak during a call that a post-call sample misses); the
    // worse rate is used. The bound is per step (B1A-D37 as corrected by B1A-09): a door's
    // elaboration spends 8 ticks per step, so one call reaches at most MODEL_DECL_BUDGET / 8
    // steps, and a step grows memory by at most 12 x worst (its 12 ticks of elaboration
    // plus check). A refused and classified door makes at most four budgeted calls (the
    // door's elaboration and check, the complement's elaboration and check), two
    // reductions of at most MODEL_DECL_BUDGET / 8 steps each: 2 x 12 x worst x
    // MODEL_DECL_BUDGET / 8 = 3 x worst x MODEL_DECL_BUDGET, on top of the baseline. The
    // ceiling is 24 GiB, and every peak observed in this run must sit under the projection.
    let rate_of = |pair: &[CalibrationRow], rss: fn(&CalibrationRow) -> Option<u64>| {
        let ticks = (pair[1].elaboration_ticks + pair[1].check_ticks)
            .checked_sub(pair[0].elaboration_ticks + pair[0].check_ticks)?;
        let grown = rss(&pair[1])?.checked_sub(rss(&pair[0])?)?;
        #[allow(clippy::cast_precision_loss)]
        let rate = grown as f64 / ticks as f64;
        Some(rate)
    };
    let rates: Vec<f64> =
        rows.windows(2).filter_map(|pair| rate_of(pair, |row| row.post_call_rss_kib)).collect();
    let peak_rates: Vec<f64> =
        rows.windows(2).filter_map(|pair| rate_of(pair, |row| row.max_rss_kib)).collect();
    let worst = rates.iter().chain(&peak_rates).copied().fold(0.0_f64, f64::max);
    let gib = |kib: f64| kib / (1024.0 * 1024.0);
    #[allow(clippy::cast_precision_loss)]
    let baseline_gib = gib(baseline_kib.expect("the baseline RSS is readable") as f64);
    #[allow(clippy::cast_precision_loss)]
    let growth_gib = gib(3.0 * worst * MODEL_DECL_BUDGET as f64);
    let peak_gib = baseline_gib + growth_gib;
    let observed_max_kib = rows
        .iter()
        .chain(&probe)
        .filter_map(|row| row.max_rss_kib)
        .chain(evidence_max_kib)
        .max()
        .expect("ru_maxrss is readable");
    #[allow(clippy::cast_precision_loss)]
    let observed_max_gib = gib(observed_max_kib as f64);
    println!(
        "post_call_rss_kib_per_tick={rates:.4?} max_rss_kib_per_tick={peak_rates:.4?} \
         worst={worst:.4} baseline_gib={baseline_gib:.2} projected_growth_gib={growth_gib:.2} \
         projected_peak_gib={peak_gib:.2} observed_max_rss_kib={observed_max_kib} \
         (heartbeat evidence included) observed_max_gib={observed_max_gib:.2} ceiling_gib=24"
    );
    assert!(
        rates.len() + 1 == CALIBRATION_STEPS.len()
            && peak_rates.len() + 1 == CALIBRATION_STEPS.len()
            && worst > 0.0,
        "the RSS rates were not measured: {rates:?} {peak_rates:?}"
    );
    assert!(
        observed_max_gib <= peak_gib,
        "an observed peak RSS ({observed_max_gib:.2} GiB) exceeds the projected peak \
         ({peak_gib:.2} GiB): the D37 bound does not hold"
    );
    assert!(
        peak_gib <= 24.0,
        "MODEL_DECL_BUDGET's projected peak RSS {peak_gib:.2} GiB exceeds the 24 GiB ceiling (B1A-D37)"
    );
    // Ticks are deterministic: 8 elaboration and 4 check ticks per step, plus a fixed
    // cost (measured at clean 08084daa09; a Clean bump that moves them re-measures and
    // re-freezes MODEL_DECL_BUDGET), and the largest calibrated call fits 10 times.
    for row in rows.iter().chain(&probe).filter(|row| row.outcome == "pass") {
        let (steps, elaboration_ticks, check_ticks) =
            (row.steps, row.elaboration_ticks, row.check_ticks);
        assert!(
            elaboration_ticks.abs_diff(8 * steps + 134) <= 1 && check_ticks == 4 * steps + 88,
            "ticks drifted at {steps} steps: elaboration {elaboration_ticks}, check {check_ticks}"
        );
    }
    for row in &rows {
        assert!(
            10 * row.elaboration_ticks <= MODEL_DECL_BUDGET,
            "MODEL_DECL_BUDGET leaves under 10x headroom over {} steps",
            row.steps
        );
    }
}

/// Trust (Clean R80 item 2; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): an authored
/// suffix is a NEW elaboration run over the prelude it is handed, so the command form
/// of `[implemented_by]` on a served module's declaration is refused with Lean's text,
/// and on one of the suffix's own declarations it binds. The prefix prelude holds
/// `Trust.Temporal` alone, so this elaborates `Temporal.lean` and nothing heavier
/// (B1A-D42's cost). Before the fix the prelude was handed out in the run that built
/// it, and the command bound `Trust.Temporal.drop`.
#[test]
#[cfg(feature = "test-support")]
fn suffix_cannot_rebind_a_served_declaration() {
    use trust_spec_temporal::model_prelude::with_model_prelude_prefix;

    const REBIND: &str = "def myDrop {State : Type} (b : Trust.Temporal.Behavior State) \
                          (n : Nat) : Trust.Temporal.Behavior State := b\n\
                          attribute [implemented_by myDrop] Trust.Temporal.drop\n";
    const OWN: &str = "def mySlow (n : Nat) : Nat := n + 2\n\
                       def myFast (n : Nat) : Nat := n + 1\n\
                       attribute [implemented_by myFast] mySlow\n";
    let (refused, bound) = with_model_prelude_prefix("Trust.Temporal", |mut prelude| {
        let mut own = prelude.clone();
        let refused = prelude.elaborate_suffix(REBIND, "authored suffix");
        let bound = own
            .elaborate_suffix(OWN, "authored suffix")
            .map(|()| own.environment().get_implemented_by(&Name::from_string("mySlow")).cloned());
        (refused, bound)
    })
    .expect("the Trust.Temporal prefix prelude elaborates");
    assert_eq!(
        refused,
        Err(ModelPreludeError::Clean(CleanTemporalCertificateError::Elaborate {
            unit: "authored suffix",
            detail: "Cannot add attribute `[implemented_by]` to declaration \
                     `Trust.Temporal.drop` because it is in an imported module"
                .to_owned(),
        }))
    );
    assert_eq!(bound, Ok(Some(Name::from_string("myFast"))));
}
