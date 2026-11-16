// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright 2026 Andrew Yates

//! Request-local replay regression fixtures, not actual resource-source evidence.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, Weak};

use trust_ir::{
    Block, BlockId, Constant, FuncId, FuncTy, FuncTyId, Function, Inst, InstrNode, Module, Ty,
    ValueId,
};

use super::*;

// Observe the actual public replay across its worker dispatches. Exact unique
// fixture source prevents unrelated parallel tests from changing the count.
static OBSERVERS: Mutex<Vec<(String, Weak<AtomicUsize>)>> = Mutex::new(Vec::new());

struct PrefixProbe {
    source: String,
    count: Arc<AtomicUsize>,
}

impl PrefixProbe {
    fn new(source: &str) -> Self {
        let count = Arc::new(AtomicUsize::new(0));
        let mut observers = OBSERVERS.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        assert!(!observers.iter().any(|(active, _)| active == source));
        observers.push((source.to_owned(), Arc::downgrade(&count)));
        Self { source: source.to_owned(), count }
    }

    fn calls(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}

impl Drop for PrefixProbe {
    fn drop(&mut self) {
        let mut observers = OBSERVERS.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
        observers.retain(|(source, _)| source != &self.source);
    }
}

pub(super) fn record_prefix(source: &str) {
    let observers = OBSERVERS.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    for (_, count) in observers.iter().filter(|(active, _)| active == source) {
        if let Some(count) = count.upgrade() {
            count.fetch_add(1, Ordering::SeqCst);
        }
    }
}

const MODEL: &str = r#"
namespace FrontierFixture
open Trust.Temporal.FiniteModel
def X : ScalarExpr := ScalarExpr.var "x"
def Model : Trust.Temporal.FiniteModel.Model :=
  Trust.Temporal.FiniteModel.Model.mk "FrontierFixture" []
    [StateVar.mk "x" 0] []
    [Action.mk "Stutter" Guard.always [Update.mk "x" X]]
    [Invariant.mk "Reflexive" (ScalarExpr.eq X X)]
end FrontierFixture
"#;

const REFINEMENT: &str = r#"
namespace FrontierFixture
open Trust.Temporal.FiniteModel
def Zero : State := State.mk (fun _ => 0) (fun _ _ => false)
def Projection (_ : IRConfig) : State := Zero
def I (_ : IRConfig) : Prop := True
theorem initialZero : Initial Model Zero :=
  And.intro (And.intro (fun _ _ => rfl) (fun _ _ _ => rfl))
    (And.intro
      (fun entry found => @everyMember StateVar
        (fun x : StateVar => Zero.scalar x.name = x.init)
        entry (_root_.Trust.Temporal.FiniteModel.Model.variables _root_.FrontierFixture.Model)
        ⟨rfl, True.intro⟩ found)
      (fun entry found => False.elim (memberNilFalse found)))
theorem refines : Trust.Temporal.InvariantForwardRefinement
    Trust.LiteralRefinement.Model (StateMachine Model) Projection I :=
  { init_invariant := fun _ _ => True.intro
    preserve_invariant := fun _ _ _ _ => True.intro
    init := fun _ _ => initialZero
    next := fun _ _ _ _ => Or.inr rfl }
end FrontierFixture
"#;

const SUPPORT: &str = r#"
namespace FrontierFixture
def FreshName : Nat := 1
theorem supportReady : True := True.intro
end FrontierFixture
"#;

const PROPERTY: &str = r#"
namespace FrontierFixture
theorem checked (behavior : Trust.Temporal.Behavior IRConfig)
    (runs : Trust.Temporal.Runs Trust.LiteralRefinement.Model behavior) :
    Trust.Temporal.Runs (Trust.Temporal.FiniteModel.StateMachine Model)
      (fun n => Projection (behavior n)) ∧ True :=
  And.intro (Trust.Temporal.invariantForwardRefinementRuns
    Trust.LiteralRefinement.Model (Trust.Temporal.FiniteModel.StateMachine Model)
    Projection I refines behavior runs) supportReady
end FrontierFixture
"#;

struct Fixture {
    module: Vec<u8>,
    invocation: LiteralInvocation,
    refinement: String,
    certificate: InvariantModelProgramPropertyCertificate,
}

impl Fixture {
    fn new(unique_source: &str) -> Self {
        let mut module = Module::new("frontier_replay_fixture");
        module.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        });
        let mut function =
            Function::new(FuncId::new(0), "answer", FuncTyId::new(0), BlockId::new(0));
        let mut block = Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(0)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![ValueId::new(0)] }));
        function.blocks.push(block);
        module.functions.push(function);
        let module = trust_ir::binary::serialize_module(&module).unwrap();
        let invocation = LiteralInvocation::closed(vec![], 0);
        let refinement = format!("{REFINEMENT}\n-- unique observer source: {unique_source}\n");
        let certificate = certify_invariant_model_program_property(
            &module,
            0,
            &invocation,
            MODEL,
            "FrontierFixture.Model",
            &refinement,
            "FrontierFixture.I",
            "FrontierFixture.Projection",
            "FrontierFixture.refines",
            SUPPORT,
            PROPERTY,
            "FrontierFixture.checked",
        )
        .unwrap();
        Self { module, invocation, refinement, certificate }
    }

    fn replay(
        &self,
        certificate: &InvariantModelProgramPropertyCertificate,
        support: &str,
        property: &str,
    ) -> Result<(), ModelProgramRefinementError> {
        recheck_invariant_model_program_property(
            certificate,
            &self.module,
            0,
            &self.invocation,
            MODEL,
            "FrontierFixture.Model",
            &self.refinement,
            "FrontierFixture.I",
            "FrontierFixture.Projection",
            "FrontierFixture.refines",
            support,
            property,
            "FrontierFixture.checked",
        )
    }
}

#[test]
fn public_property_replay_elaborates_exactly_one_composed_prefix() {
    let fixture = Fixture::new("prefix-count-only");
    // Certification is deliberately outside the observation: producer checks
    // remain independent, while this assertion counts one public replay.
    let observer = PrefixProbe::new(&fixture.refinement);
    fixture.replay(&fixture.certificate, SUPPORT, PROPERTY).unwrap();
    assert_eq!(observer.calls(), 1, "one property replay rebuilt its composed prefix");
}

#[test]
fn failed_extension_is_discarded_before_an_honest_replay() {
    let fixture = Fixture::new("failed-extension-isolation");
    const FAILED: &str = r#"
namespace FrontierFixture
def FreshName : Nat := 0
def FailedOnlyName : Nat := 7
theorem broken : Nat.zero = Nat.succ Nat.zero := rfl
end FrontierFixture
"#;
    let mut changed = fixture.certificate.clone();
    changed.support_source = FAILED.to_owned();
    let error = fixture.replay(&changed, FAILED, PROPERTY).unwrap_err();
    let ModelProgramRefinementError::Clean(CleanTemporalCertificateError::Elaborate {
        detail, ..
    }) = error
    else {
        panic!("expected failure after partially elaborating the support unit: {error}");
    };
    assert!(detail.starts_with("declaration `FrontierFixture.broken` failed: "), "{detail}");
    assert!(detail.contains("TypeMismatch"), "{detail}");

    // Reintroducing FreshName=1 must not collide with the failed request's
    // FreshName=0. This checks isolation between public replay requests;
    // it does not assert which persistent worker handles each request.
    fixture.replay(&fixture.certificate, SUPPORT, PROPERTY).unwrap();

    let mut leaked = fixture.certificate.clone();
    // An unknown name in a theorem type can become an auto-implicit binder.
    // Its use in a definition body must instead resolve an actual declaration.
    leaked.property_source = PROPERTY.replacen(
        "namespace FrontierFixture",
        "namespace FrontierFixture\ndef LeakedValue : Nat := FailedOnlyName",
        1,
    );
    let error = fixture.replay(&leaked, SUPPORT, &leaked.property_source).unwrap_err();
    let ModelProgramRefinementError::Clean(CleanTemporalCertificateError::Elaborate {
        detail, ..
    }) = error
    else {
        panic!("failed-only names must remain unavailable in a later request: {error}");
    };
    assert!(detail.contains("UnknownIdent"), "{detail}");
    assert!(detail.contains("FailedOnlyName"), "{detail}");
    fixture.replay(&fixture.certificate, SUPPORT, PROPERTY).unwrap();
}
