// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! §6.4: the Clean-origin `Nat` carrier is a NOMINAL OPAQUE HANDLE, and its
//! runtime callees are PINNED.
//!
//! The design of record
//! (`docs/design/2026-08-27-two-language-direct-to-trust-ir.md` §6.4) requires,
//! before any `Nat` shape reaches a codegen exit, "a nominal opaque handle type
//! (never bare `Ty::Ptr`, so two opaque runtimes cannot exchange handles),
//! validate-time pinning of `NatRuntime` callee identities against the pinned
//! `("Nat", "trust_bignum::Nat")` pairing". trust-ir v43 supplies the type
//! (`Ty::Handle`), the pin registry (`TRUSTED_HANDLE_RUNTIMES`) and the
//! validator rules; this file is the producer side of the same requirement.
//!
//! WHY A BARE `Ty::Ptr` WAS NOT ENOUGH, which is what these tests are really
//! about. A pointer carrier is weaker in two independent ways, and both are
//! measured below:
//!
//! * it is POINTER-LIKE (`Ty::is_pointer_like`), so `GEP`, `Load`, `PtrToInt`
//!   and every cast are well-typed on a `Nat` and nothing in the format says a
//!   bignum must not be dereferenced;
//! * it is the SAME TYPE every other opaque runtime would pick, so runtime A's
//!   value satisfied runtime B's entry point by construction — there was no
//!   type-level statement that the two do not interchange.
//!
//! WHAT THIS FILE DOES NOT CLAIM. The pinned symbols are a TRUSTED-BASE row:
//! `validate_module` guarantees a validated module never FORGES a handle, so
//! every handle a pinned entry point receives came from another pinned entry
//! point of the same runtime. It does not make the shims correct, and nothing
//! here links against them. The crate-level `GATING` section still governs
//! whether an emitted body may be trusted.

use clean_kernel::Environment;
use trust_clean_ir::{
    CleanIrRefusal, NAT_HANDLE_NAME, NAT_HANDLE_RUNTIME, NAT_RELEASE_ROLE, NAT_RUNTIME_ROLES,
    NatCarrier, NatRuntime, declare_pinned_nat_runtime, emit_clean_origin_function_with_nat,
    nat_handle_ty, pinned_nat_runtime, trust_ir_func_ty_with_nat,
};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::inst::Inst;
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    Block, CallingConv, Endianness, Function, Linkage, Module, StructPassingPolicy, TargetInfo,
};
use trust_ir_build::{
    HandleEntryPoint, HandleRegistry, HandleRuntimePin, ModuleBuilder, PinnedTy, ValidationError,
    validate_module, validate_module_for_codegen, validate_module_with_handle_registry,
};

/// The one source spelling the planner admits as a recursion shape, taken
/// verbatim from `nat_recursion.rs` so both files track the same real boundary.
const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// A concrete target, because a module carrying a bodyless EXTERNAL declaration
/// must name one.
///
/// This is not test scaffolding that production can skip: a pinned entry point
/// is an ABI boundary, so `validate_module` refuses a module that declares one
/// without `Module::target_info` (`TargetInfoRequired`). `declare_pinned_nat_runtime`
/// deliberately does not invent a target — which target a Clean island is being
/// compiled for is the compilation session's fact, and a producer guessing it
/// would be a layout claim nobody made. The value here is this machine's.
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn substitute(ty: Ty) -> NatRuntime {
    NatRuntime {
        carrier: NatCarrier::ExecutableSubstitute(ty),
        from_u64: FuncId::new(10),
        add: FuncId::new(11),
        sub: FuncId::new(12),
        is_zero: FuncId::new(13),
        // No release callee: a substitute carrier models `Nat` as a VALUE, so
        // there is no allocation to release. The tests here are about the
        // CARRIER's authority, not about ownership.
        release: None,
        self_id: FuncId::new(0),
    }
}

/// Build the production module: the five pinned declarations (the RELEASE entry
/// point included), then the emitted recursion, appended at the id the
/// declarations left free.
///
/// This IS the order a real seam must use, and it is why
/// `declare_pinned_nat_runtime` does not take `self_id`: the declarations take
/// ids of their own, so the emitted function's id is only knowable afterwards.
fn pinned_module(decl: &str, name: &str) -> (Module, NatRuntime, FuncId) {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).expect("must plan as a recursion shape");

    let mut builder = ModuleBuilder::new_with_target_info("clean_origin_nat", target());
    let declared = declare_pinned_nat_runtime(&mut builder).expect("the pin row must be present");
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");

    let self_id = FuncId::new(u32::try_from(module.functions.len()).expect("small module"));
    let nat = declared.for_function(self_id).expect("a fresh id cannot alias a declaration");
    let signature = trust_ir_func_ty_with_nat(plan.signature(), Some(&nat_handle_ty()))
        .expect("`Nat -> Nat` carries at the pinned handle");
    let ty = module.add_func_type(signature).expect("Module::add_func_type: test fixture");
    let function = emit_clean_origin_function_with_nat(&plan, self_id, ty, Some(nat.clone()))
        .expect("the recursion emits against the pinned runtime");
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
    (module, nat, self_id)
}

fn function_mut<'m>(module: &'m mut Module, name: &str) -> &'m mut Function {
    module
        .functions
        .iter_mut()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function named `{name}`"))
}

// ── the carrier itself ────────────────────────────────────────────────────

/// The production carrier is the pinned NOMINAL handle, and it is not a
/// pointer. Both halves matter: the first is the §6.4 requirement, the second
/// is what the requirement buys.
#[test]
fn the_production_carrier_is_the_pinned_nominal_handle_and_is_not_pointer_like() {
    let carrier = NatCarrier::PinnedHandle.ty();
    assert_eq!(carrier, nat_handle_ty());
    assert_ne!(carrier, Ty::Ptr, "a handle is never equal to a bare pointer");
    assert!(carrier.is_handle(), "{carrier:?} must be the nominal handle");
    assert!(
        !carrier.is_pointer_like(),
        "a handle must not be pointer-like, or `GEP`/`Load`/`PtrToInt` would be well-typed on a \
         `Nat`: {carrier:?}",
    );

    let identity = carrier.handle_ty().expect("a handle carries its identity");
    assert_eq!(
        (identity.name.as_str(), identity.runtime.as_str()),
        (NAT_HANDLE_NAME, NAT_HANDLE_RUNTIME)
    );
}

/// The pairing this producer spells is the validator's own row, not a private
/// copy of it — including every role the emitted body calls.
#[test]
fn the_pinned_pairing_and_every_role_come_from_the_validators_registry() {
    let pin = pinned_nat_runtime().expect("the validator pins `trust_bignum::Nat`");
    assert_eq!(pin.handle_ty(), nat_handle_ty(), "one spelling of the pinned handle");
    assert_eq!(pin.calling_conv, CallingConv::C);
    for role in NAT_RUNTIME_ROLES {
        let entry = pin
            .entry_points
            .iter()
            .find(|entry| entry.role == role)
            .unwrap_or_else(|| panic!("the pin row must pin the `{role}` entry point"));
        assert!(
            entry.symbol.starts_with("trust_bignum_nat_"),
            "role `{role}` must resolve to a `trust_bignum` C shim, got `{}`",
            entry.symbol,
        );
    }
}

// ── the emitted module ────────────────────────────────────────────────────

/// THE PAYOFF. The emitted module VALIDATES: the handle occurs in the emitted
/// signature and body, its only origins are the five pinned declarations, and
/// every call edge resolves to the pinned shim for its role.
///
/// Since 2026-09-17 the emitted body also RELEASES, so this is the test that
/// puts the release calls in front of the real validator: a release `Call` is
/// `(H) -> ()` with an empty result list, which is admitted transport only
/// because the DECLARATION is pinned — one wrong byte in that signature is
/// `HandleEntryPointSignatureMismatch` and lands here.
#[test]
fn the_emitted_pinned_module_validates_and_its_call_edges_are_the_pinned_shims() {
    let (module, nat, self_id) = pinned_module(COUNTDOWN_SUM, "countdownSum");

    let errors = validate_module(&module);
    assert!(errors.is_empty(), "the pinned module must validate, got {errors:#?}");

    // WHAT THE STRICTER GATE SAYS, and it is not "yes".
    // `validate_module_for_codegen` is the interlock a backend must run instead
    // of `validate_module`, and it is the boundary §6.4 names ("before any Nat
    // shape reaches a codegen exit"), so it is measured here rather than
    // assumed. It refuses — for the BODY GATE, which is a pre-existing fact
    // about this producer and not about the carrier: `Function::body_gate` is
    // `None` (the pre-v41 "no licensing claim" state) and the interlock admits
    // only `Gated { authority }`. This crate is not proof authority and not a
    // gate; the crate-level GATING section says only the narrow W2
    // `WrappingBinOp` slice carries body authority, and a recursion shape does
    // not. Minting a `Gated` here to make this line green would be the invented
    // claim the whole lane exists to prevent.
    //
    // So the assertion is the exact residue: the interlock's ONLY complaint is
    // the missing license, and NOTHING about the handle, its origins or its
    // transport. That is the §6.4 payoff stated as a measurement — the carrier
    // is no longer what stands between a Clean-origin `Nat` recursion and a
    // codegen exit.
    let codegen_errors = validate_module_for_codegen(&module);
    let unlicensed: Vec<_> = codegen_errors
        .iter()
        .filter(|error| {
            matches!(
                error,
                ValidationError::UnlicensedBodyForCodegen { function, .. }
                    if *function == self_id.index()
            )
        })
        .collect();
    assert_eq!(unlicensed.len(), 1, "expected exactly the body-gate refusal: {codegen_errors:#?}");
    assert_eq!(
        codegen_errors.len(),
        1,
        "the codegen interlock must have NOTHING to say about the handle: {codegen_errors:#?}",
    );

    nat.check_pinned_callees(&module).expect("every callee id must resolve to its pinned shim");

    // The handle is really in the emitted function, not merely in the
    // declarations: its parameter is carried at the handle.
    let emitted = module
        .functions
        .iter()
        .find(|function| function.id == self_id)
        .expect("the emitted function is in the module");
    let entry = emitted.blocks.first().expect("the emitted body has an entry block");
    assert_eq!(
        entry.params.first().map(|(_, ty)| ty.clone()),
        Some(nat_handle_ty()),
        "the `Nat` parameter must be carried at the pinned handle",
    );

    // And the declarations are the exact shape the validator pins: bodyless,
    // `External`, C. Over the roles this producer CALLS, not the whole row: the
    // row also pins roles no emitted body calls, and those are not declared
    // (`declaring_the_pinned_runtime_twice_is_idempotent` pins that).
    let pin = pinned_nat_runtime().unwrap();
    for role in NAT_RUNTIME_ROLES {
        let entry = pin
            .entry_points
            .iter()
            .find(|entry| entry.role == role)
            .unwrap_or_else(|| panic!("the pin row must pin `{role}`"));
        let declaration = module
            .functions
            .iter()
            .find(|function| function.name == entry.symbol)
            .unwrap_or_else(|| panic!("`{}` must be declared", entry.symbol));
        assert!(declaration.is_declaration(), "`{}` must be bodyless", entry.symbol);
        assert_eq!(declaration.linkage, Linkage::External);
        assert_eq!(declaration.calling_conv, CallingConv::C);
    }
}

/// PRODUCTION RELEASES, and through the PINNED symbol.
///
/// `PinnedNatRuntime::for_function` always supplies the release callee, so a
/// production emission cannot silently keep leaking — and the callee it
/// supplies is the declaration `declare_pinned_nat_runtime` wrote, which is
/// the one `validate_module` admits. This test resolves the actual call edges
/// back to `Function::name`, so it would catch a release routed to any other
/// function in the module: a `FuncId` is a positional index with no nominal
/// content, and "the release edge points at the release shim" has to be
/// measured somewhere or it is not stated at all.
#[test]
fn the_production_emission_releases_through_the_pinned_release_symbol() {
    let (module, nat, self_id) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let release = nat.release.expect("the pinned row supplies the release callee");

    // The callee is the pinned declaration, by SYMBOL.
    let pin = pinned_nat_runtime().unwrap();
    let expected = pin
        .entry_points
        .iter()
        .find(|entry| entry.role == NAT_RELEASE_ROLE)
        .expect("the pin row pins a release entry point");
    let declaration = module
        .functions
        .iter()
        .find(|function| function.id == release)
        .expect("the release callee resolves in the module");
    assert_eq!(declaration.name, expected.symbol, "the release edge must reach the pinned shim");
    assert!(declaration.is_declaration(), "and it is linked trusted base, not a local body");

    // And the emitted body really calls it.
    let emitted = module
        .functions
        .iter()
        .find(|function| function.id == self_id)
        .expect("the emitted function is in the module");
    let released: Vec<Vec<ValueId>> = emitted
        .blocks
        .iter()
        .flat_map(|block| block.body.iter())
        .filter_map(|node| match &node.inst {
            Inst::Call { callee, args } if *callee == release => {
                assert!(node.results.is_empty(), "release has no result");
                Some(args.clone())
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        released.len(),
        3,
        "`countdownSum` is return-fresh, so its nonzero arm releases the literal, \
         the predecessor and the self-call's result: {released:?}",
    );
    for args in &released {
        assert_eq!(args.len(), 1, "one handle per release: {args:?}");
        assert_ne!(args[0], ValueId::new(0), "and never the PARAMETER, which the caller owns",);
    }
}

/// Declaring the runtime twice yields ONE declaration per symbol. A link
/// expects that, and a producer emitting several `Nat` declarations into one
/// module would otherwise accumulate duplicates.
///
/// And the declarations are EXACTLY the roles this producer calls
/// ([`NAT_RUNTIME_ROLES`]), never the whole pin row, which grows (trust-ir
/// WS3.2 added fourteen `Nat` roles no emitted body calls). The symbols are
/// compared by name rather than counted: a bare `19 != 5` reads as a
/// duplication bug, and it was a scope bug — each extra was declared once.
#[test]
fn declaring_the_pinned_runtime_twice_is_idempotent() {
    let mut builder = ModuleBuilder::new_with_target_info("twice", target());
    let first = declare_pinned_nat_runtime(&mut builder).unwrap();
    let second = declare_pinned_nat_runtime(&mut builder).unwrap();
    assert_eq!(first, second, "the second declaration must reuse the first");
    let module = builder.build().expect("ModuleBuilder::build: test fixture");

    let pin = pinned_nat_runtime().unwrap();
    let mut expected: Vec<&str> = NAT_RUNTIME_ROLES
        .iter()
        .map(|role| {
            pin.entry_points
                .iter()
                .find(|entry| entry.role == *role)
                .unwrap_or_else(|| panic!("the pin row must pin `{role}`"))
                .symbol
        })
        .collect();
    let mut declared: Vec<&str> =
        module.functions.iter().map(|function| function.name.as_str()).collect();
    expected.sort_unstable();
    declared.sort_unstable();
    assert_eq!(declared, expected, "one declaration per role this producer calls, and no other");
    assert!(validate_module(&module).is_empty());
}

/// A handle produced by ANYTHING ELSE is refused. The declarations are the only
/// origins, so an unpinned bodyless declaration reaching the handle is an
/// unpinned origin — this is the rule that makes the pinning worth having.
#[test]
fn an_unpinned_declaration_cannot_be_a_handle_origin() {
    let (mut module, _, _) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let forged = module
        .add_func_type(FuncTy {
            params: vec![nat_handle_ty(), nat_handle_ty()],
            returns: vec![nat_handle_ty()],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(u32::try_from(module.functions.len()).unwrap());
    let mut declaration = Function::new(id, "my_own_nat_add", forged, BlockId::new(0));
    declaration.linkage = Linkage::External;
    declaration.calling_conv = CallingConv::C;
    module.try_add_function(declaration).expect("Module::try_add_function: test fixture");

    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::HandleForeignDeclaration { name, .. } if name == "my_own_nat_add"
        )),
        "an unpinned handle origin must be refused, got {errors:#?}",
    );
}

/// A LOCAL definition of a pinned symbol is refused: the runtime is a linked
/// trusted-base row, and a body here would let the module mint every handle the
/// symbol produces.
#[test]
fn a_local_definition_of_a_pinned_shim_is_refused() {
    let (mut module, _, _) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let pin = pinned_nat_runtime().unwrap();
    let symbol = pin
        .entry_points
        .iter()
        .find(|entry| entry.role == "add")
        .expect("the pin row pins `add`")
        .symbol;
    let shim = function_mut(&mut module, symbol);
    let mut body = Block::new(BlockId::new(0));
    body = body.with_param(ValueId::new(0), nat_handle_ty());
    body = body.with_param(ValueId::new(1), nat_handle_ty());
    body.body.push(InstrNode {
        inst: Inst::Return { values: vec![ValueId::new(0)] },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    shim.blocks = vec![body];

    let errors = validate_module(&module);
    assert!(
        errors.iter().any(|error| matches!(
            error,
            ValidationError::HandleEntryPointDefinedLocally { symbol: got, .. } if got == symbol
        )),
        "a locally defined pinned shim must be refused, got {errors:#?}",
    );
}

// ── a non-handle carrier where a handle is required ───────────────────────

/// The §6.4 gate. An executable substitute is admitted for EMISSION (that is
/// what lets the recursion be run against the kernel) and REFUSED where the
/// pinned handle is required.
#[test]
fn a_non_handle_carrier_is_refused_where_the_pinned_handle_is_required() {
    let nat = substitute(Ty::U64);
    let refusal = nat.require_pinned_handle_carrier().unwrap_err();
    assert_eq!(
        refusal,
        CleanIrRefusal::NatCarrierIsNotThePinnedHandle { carrier: Ty::U64.to_string() }
    );
    let text = refusal.to_string();
    assert!(text.contains("PINNED handle is required"), "must say what was required: {text}");
    assert!(text.contains("Options:"), "must name the fix: {text}");

    // The ability itself is NOT deleted: the same runtime still emits.
    let env = env_with(COUNTDOWN_SUM);
    let plan = plan_clean_origin_body(&env, "countdownSum").unwrap();
    let emitted =
        emit_clean_origin_function_with_nat(&plan, FuncId::new(0), FuncTyId::new(0), Some(nat));
    assert!(
        emitted.is_ok(),
        "a DECLARED substitute must still emit -- deleting that ability would delete the \
         kernel-agreement evidence for these two shapes: {emitted:?}",
    );
}

/// `check_pinned_callees` is the carrier gate too, because a substitute's
/// callees are not the pinned declarations by construction.
#[test]
fn checking_pinned_callees_refuses_a_substitute_carrier() {
    let (module, _, _) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let refusal = substitute(Ty::U64).check_pinned_callees(&module).unwrap_err();
    assert!(
        matches!(refusal, CleanIrRefusal::NatCarrierIsNotThePinnedHandle { .. }),
        "got {refusal:?}",
    );
}

// ── a callee whose name is not the pinned shim ────────────────────────────

/// VALIDATE-TIME PINNING of the callee identities. A `FuncId` is a positional
/// index with no nominal content, so a runtime whose `add` resolves to some
/// other function emits a well-formed, well-typed body that computes something
/// the declaration does not say. `validate_module` cannot see it — the call edge
/// is type-correct — so the producer states the fact.
#[test]
fn a_callee_that_is_not_the_pinned_shim_is_refused() {
    let (mut module, nat, _) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let unrelated_ty = module
        .add_func_type(FuncTy {
            params: vec![nat_handle_ty(), nat_handle_ty()],
            returns: vec![nat_handle_ty()],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let unrelated_id = FuncId::new(u32::try_from(module.functions.len()).unwrap());
    let mut unrelated = Function::new(
        unrelated_id,
        "trust_bignum_nat_add_but_not_really",
        unrelated_ty,
        BlockId::new(0),
    );
    unrelated.linkage = Linkage::External;
    unrelated.calling_conv = CallingConv::C;
    module.try_add_function(unrelated).expect("Module::try_add_function: test fixture");

    let mut mispointed = nat.clone();
    mispointed.add = unrelated_id;
    let refusal = mispointed.check_pinned_callees(&module).unwrap_err();
    assert_eq!(
        refusal,
        CleanIrRefusal::NatRuntimeCalleeIsNotThePinnedShim {
            role: "add",
            expected: "trust_bignum_nat_add",
            actual: "trust_bignum_nat_add_but_not_really".to_owned(),
            id: unrelated_id.index(),
        },
        "the refusal must name the role, the pinned symbol and what the id really is",
    );
    let text = refusal.to_string();
    assert!(text.contains("not the declaration"), "must say why it matters: {text}");
    assert!(text.contains("Options:"), "must name the fix: {text}");

    // The coherent runtime still passes, so this is refusing a real
    // distinction rather than refusing everything.
    assert!(nat.check_pinned_callees(&module).is_ok());
}

/// An id that resolves to nothing is named as such, not reported as a wrong
/// symbol.
#[test]
fn a_callee_id_that_resolves_to_nothing_is_refused() {
    let (module, nat, _) = pinned_module(COUNTDOWN_SUM, "countdownSum");
    let mut dangling = nat;
    dangling.sub = FuncId::new(4_000);
    assert_eq!(
        dangling.check_pinned_callees(&module).unwrap_err(),
        CleanIrRefusal::NatRuntimeCalleeIsNotInTheModule { role: "sub", id: 4_000 }
    );
}

// ── two runtimes cannot exchange handles ──────────────────────────────────

/// The producer half: a carrier belonging to ANOTHER runtime is refused, named
/// as a foreign handle rather than as a generic carrier failure. The emitted
/// body calls `trust_bignum::Nat`'s pinned entry points, which never produced
/// that value and cannot be asked to consume it.
#[test]
fn a_foreign_runtimes_handle_is_refused_as_a_nat_carrier() {
    let foreign = Ty::handle("Nat", "other_bignum::Nat");
    let nat = substitute(foreign);
    let refusal = nat.carrier.check().expect_err("a foreign handle must refuse");
    assert_eq!(
        refusal,
        CleanIrRefusal::NatCarrierIsAForeignHandle {
            name: "Nat".to_owned(),
            runtime: "other_bignum::Nat".to_owned(),
        }
    );
    let text = refusal.to_string();
    assert!(text.contains("must not"), "must state the rule: {text}");
    assert!(text.contains("other_bignum::Nat"), "must name the foreign runtime: {text}");

    // And it refuses at EMISSION, not only at the exit gate: a body carrying a
    // handle no pinned declaration produces must never be assembled.
    let env = env_with(COUNTDOWN_SUM);
    let plan = plan_clean_origin_body(&env, "countdownSum").unwrap();
    assert!(
        emit_clean_origin_function_with_nat(&plan, FuncId::new(0), FuncTyId::new(0), Some(nat))
            .is_err(),
        "emission must refuse a foreign handle carrier",
    );
}

/// A substitute that IS the pinned handle is a constructor mistake, and is said
/// to be one: the pinned carrier has its own spelling, and a handle is exactly
/// what the interpreter cannot compute on.
#[test]
fn a_substitute_that_is_the_pinned_handle_is_refused_as_a_constructor_mistake() {
    let refusal = substitute(nat_handle_ty()).carrier.check().expect_err("must refuse");
    assert_eq!(refusal, CleanIrRefusal::NatSubstituteCarrierIsThePinnedHandle);
    assert!(refusal.to_string().contains("NatCarrier::PinnedHandle"), "{refusal}");
}

/// The VALIDATOR half, over a registry with TWO trusted runtimes: handing
/// runtime B's handle to runtime A's pinned entry point is refused. With one
/// row in the real registry a second runtime's handle is merely unpinned, which
/// proves less — so the exchange is modelled explicitly.
#[test]
fn two_trusted_runtimes_cannot_exchange_handles() {
    const OTHER: HandleRuntimePin = HandleRuntimePin {
        name: "Nat",
        runtime: "other_bignum::Nat",
        calling_conv: CallingConv::C,
        entry_points: &[HandleEntryPoint {
            role: "from_u64",
            symbol: "other_bignum_nat_from_u64",
            def_path: "other_bignum::Nat::from_u64",
            params: &[PinnedTy::Scalar(Ty::U64)],
            returns: &[PinnedTy::Handle],
        }],
    };

    let nat_pin = pinned_nat_runtime().unwrap().clone();
    let registry = HandleRegistry::from_pins(&[nat_pin, OTHER]).expect("two well-formed rows");

    // A module that declares both runtimes, then passes the OTHER runtime's
    // handle to `trust_bignum::Nat`'s own zero test.
    let mut module = Module::new("exchange");
    module.target_info = Some(target());
    let other_handle = Ty::handle("Nat", "other_bignum::Nat");

    let from_u64_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![other_handle.clone()],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut other_from_u64 =
        Function::new(FuncId::new(0), "other_bignum_nat_from_u64", from_u64_ty, BlockId::new(0));
    other_from_u64.linkage = Linkage::External;
    other_from_u64.calling_conv = CallingConv::C;
    other_from_u64.display_path = Some("other_bignum::Nat::from_u64".to_owned());
    module.try_add_function(other_from_u64).expect("Module::try_add_function: test fixture");

    let is_zero_ty = module
        .add_func_type(FuncTy {
            params: vec![nat_handle_ty()],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut nat_is_zero =
        Function::new(FuncId::new(1), "trust_bignum_nat_is_zero", is_zero_ty, BlockId::new(0));
    nat_is_zero.linkage = Linkage::External;
    nat_is_zero.calling_conv = CallingConv::C;
    nat_is_zero.display_path = Some("trust_bignum::Nat::is_zero".to_owned());
    module.try_add_function(nat_is_zero).expect("Module::try_add_function: test fixture");

    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![other_handle.clone()],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Block::new(BlockId::new(0));
    entry = entry.with_param(ValueId::new(0), other_handle);
    entry.body.push(InstrNode {
        // The exchange: runtime B's handle into runtime A's entry point.
        inst: Inst::Call { callee: FuncId::new(1), args: vec![ValueId::new(0)] },
        results: vec![ValueId::new(1)],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    entry.body.push(InstrNode {
        inst: Inst::Return { values: vec![ValueId::new(1)] },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    let mut caller = Function::new(FuncId::new(2), "exchange", caller_ty, BlockId::new(0));
    caller.blocks = vec![entry];
    module.try_add_function(caller).expect("Module::try_add_function: test fixture");

    // Both rows are PINNED and both spell the name `Nat`, so nothing but the
    // nominal inequality of the RUNTIME PATH can refuse this — which is exactly
    // what a bare `Ty::Ptr` carrier could not say. Measured: the call edge's
    // argument type check names both identities.
    let errors = validate_module_with_handle_registry(&module, &registry);
    assert_eq!(errors.len(), 1, "the exchange must be refused, and refused once: {errors:#?}");
    let ValidationError::CallArgTypeMismatch { callee, arg_index, expected, actual, .. } =
        &errors[0]
    else {
        panic!("expected the call edge to refuse the foreign handle, got {errors:#?}");
    };
    assert_eq!(callee, "trust_bignum_nat_is_zero");
    assert_eq!(*arg_index, 0);
    assert_eq!(expected, "handle<\"Nat\", \"trust_bignum::Nat\">");
    assert_eq!(actual, "handle<\"Nat\", \"other_bignum::Nat\">");
}
