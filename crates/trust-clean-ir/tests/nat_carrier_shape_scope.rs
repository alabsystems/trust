// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WHICH SHAPES MAY CARRY A `Nat` AT THE OPAQUE HANDLE, and why the emitter's
//! unconditional threading of that carrier is safe.
//!
//! `emit_planned_function` computes `nat_ty` once and hands it to
//! `trust_ir_func_ty_with_nat` for EVERY shape, not only the two recursion
//! shapes the runtime was introduced for. So `CleanType::Nat` in ANY plan's
//! signature becomes `Ty::Handle(("Nat", "trust_bignum::Nat"))` — including, on
//! the face of it, a `WrappingBinOp` plan, whose body would then be
//! `BinOp::Add` over two opaque runtime pointers: a wrong binary, not a
//! refusal.
//!
//! This file is the measurement that was missing when that was written down as
//! a suspicion. The witness attempt and its result:
//!
//! ```text
//! def natAdd   (a b : Nat) : Nat    := a + b     -- PLAN REFUSED (recognition)
//! def mixedAdd (a : Nat) (b : UInt64) : UInt64 := b + b
//!                                                -- PLAN REFUSED (single-domain signature)
//! def natId    (n : Nat) : Nat      := n         -- PLANS, EMITS `Return v0`, VALIDATES
//! ```
//!
//! The pairing is UNCONSTRUCTIBLE, and not by accident — `CleanOriginPlan` is
//! sealed (constructible only by `plan_clean_origin_body`), and the planner
//! refuses a bignum carrier for every COMPUTING shape. For the arithmetic and
//! select family — the shapes a `Nat` could plausibly reach — two refusals do
//! that work, and BOTH of them are in the recognizer:
//!
//! 1. **Recognition declines the fragment.** `recognise_wrapping_expr` opens
//!    with a hard-coded `let CleanType::UInt(width) = signature.result().clean()
//!    else { return Ok(None) }` (`trust-clean-origin/src/emit.rs`), so a `Nat`
//!    RESULT never enters the arithmetic fragment at all; every other arm
//!    declines for its own reason and the body reaches the fall-through `Err`,
//!    whose text cites the missing selection row.
//! 2. **The sealed-plan re-check.** `check_arith_signature` requires the result
//!    carrier to be `Ty::Int { signed: false, width: 8|16|32|64 }` and EVERY
//!    argument position — used or not — to carry at that same type. `Nat`'s
//!    only carrier is `Ty::BignumNat`, so a `Nat` anywhere in an
//!    arithmetic/select/raw-binop signature is refused by name. This is the
//!    refusal that catches a body whose ARITHMETIC is at a machine width and
//!    whose `Nat` sits in some other position.
//!
//! The other computing shapes never see a `Nat` for their own typing reasons,
//! not for these two: `DecideComparison` demands a `Bool` result over arguments
//! at one unsigned machine width, and `BoolNot` / `BoolConnective` demand
//! `CleanType::Bool` in every position.
//!
//! THE SELECTION TABLE IS NOT ONE OF THEM — a correction. An earlier draft of
//! this file (and of the commit that added it) called
//! `trust_clean_origin::ROWS` the first of two INDEPENDENT layers, with
//! `no_selection_row` as its refusal. Measured, that is wrong in mechanism:
//! `no_selection_row` is a pure message FORMATTER (it maps `ROWS` names into a
//! list and prints the count and the carrier's label), reached from exactly one
//! place — the fall-through `Err` arm, AFTER recognition has already declined
//! — and the two carrier-keyed row iterators (`arith_operator_rows`,
//! `raw_binop_rows`) have six callers, every one of them hard-coding
//! `CarrierClass::MachineUInt`. No `CarrierClass::BignumNat` row is consulted
//! while a body is being recognised. Measured the other way too: adding a
//! whole-`Body` row at `CarrierClass::BignumNat` to `ROWS` fires
//! `no_whole_body_selection_row_is_stated_at_the_bignum_carrier` and changes
//! NOTHING else — `natAdd` is still refused, with the same text. The table is
//! the REGISTRY a refusal cites so the reader learns the work item; it is a
//! statement of intent that a landing pairs with a recognizer arm, not the gate
//! that decides.
//!
//! What DOES reach the emitter at a handle carrier is the projection lane
//! (`param`, the one whole-body row stated at `CarrierClass::AnyExact` that
//! carries a value): `Projection` / `InductiveProjection` emit `Return
//! <parameter>` and nothing else — exact-typed transport, which is precisely
//! what trust-ir v43 ratified a handle FOR. The emitted pinned module
//! validates with zero errors.
//!
//! And if the pairing were ever constructed anyway, it still fails closed
//! downstream: `validate_module` refuses `BinOp`/`ICmp` at a handle twice over
//! (`BinOpRequiresInteger` + `InvalidHandleUse`). That is measured here too,
//! because it is the backstop the emitter's silence relies on.
//!
//! THE POINT OF PINNING ALL FOUR, stated at the right strength. Two of the four
//! are BEHAVIORAL: the planner tests drive real Clean source and fail if either
//! recognizer refusal is relaxed, and the validator test fails if the
//! handle-use rule is. Two are LEDGERS on `ROWS`: a row addition cannot be a
//! quiet one-line edit, because a row is the statement that a head is meant to
//! be selectable and it must be paired with a verdict about the bignum carrier
//! at the emitter. A ledger is not a gate, and neither ledger would notice the
//! dangerous edit — relaxing `recognise_wrapping_expr` — which is exactly why
//! the emitter now carries its own check rather than relying on any of them.

use clean_kernel::Environment;
use trust_clean_ir::{
    CleanIrRefusal, NatCarrier, declare_pinned_nat_runtime, emit_clean_origin_function,
    emit_clean_origin_function_with_nat, nat_handle_ty, trust_ir_func_ty_with_nat,
};
use trust_clean_origin::emit::plan_standalone_clean_origin_body;
use trust_clean_origin::{CarrierClass, EmitRefusal, ROWS, RowContext, plan_clean_origin_body};
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CallingConv, Endianness, Function, StructPassingPolicy, TargetInfo};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

// ── the sources, and what each one is here to measure ─────────────────────

/// Whole-body `Nat` arithmetic. No selection row exists at the bignum carrier.
const NAT_ADD: &str = "def natAdd (a b : Nat) : Nat := a + b";

/// THE WITNESS ATTEMPT. A genuine `WrappingBinOp` body at `UInt64` — the shape
/// the flagged concern names — with a `Nat` parameter that the body never
/// mentions. Recognition is happy (the body IS `b + b` at one machine width);
/// what refuses it is the signature, which is why the "used or not" clause in
/// `check_arith_signature` is the load-bearing half rather than an over-strict
/// convenience.
const MIXED_ADD: &str = "def mixedAdd (a : Nat) (b : UInt64) : UInt64 := b + b";

/// The same attempt at the constant shape, so the refusal is measured as a
/// property of the arithmetic FAMILY rather than of one arm.
const NAT_CONST: &str = "def natConst (n : Nat) : UInt64 := 7";

/// The projection lane at the bignum carrier: what actually gets there.
const NAT_ID: &str = "def natId (n : Nat) : Nat := n";

/// The projection lane with a MIXED signature — a handle parameter the body
/// drops, and a machine-width result. `Projection` keeps its mixed-width
/// capability, so this is the widest reach a handle carrier has today.
const NAT_MIXED_FST: &str = "def natMixedFst (a : Nat) (b : UInt64) : UInt64 := b";

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// A concrete target, because a module carrying a bodyless EXTERNAL
/// declaration must name one (`TargetInfoRequired`).
fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn plan_refusal(decl: &str, name: &str) -> EmitRefusal {
    let env = env_with(decl);
    match plan_clean_origin_body(&env, name) {
        Ok(plan) => panic!(
            "`{name}` was expected to be refused at plan time, but it planned as {:?}",
            plan.shape()
        ),
        Err(refusal) => refusal,
    }
}

fn not_emittable_reason(refusal: &EmitRefusal) -> &str {
    match refusal {
        EmitRefusal::NotEmittable { reason, .. } => reason,
        other => panic!("expected `NotEmittable`, got {other:?}"),
    }
}

// ── the selection table: a ledger of stated intent, not a gate ────────

/// A LEDGER: the instruction-selection table states the bignum carrier as a
/// RECURSION-ONLY carrier, and a landing that changes that must say so here.
///
/// Every `CarrierClass::BignumNat` row is a recursion scheme or one node inside
/// a scheme's arm; not one of them realizes a whole `Body`. WHAT THAT IS AND IS
/// NOT: a row is the table's statement that a head is MEANT to be selectable at
/// a carrier, which a landing pairs with the recognizer arm that realizes it
/// (`docs/design/2026-08-04-two-language-compiler-architecture.md` §6f). It is
/// not consulted while a body is recognised — measured: adding a whole-`Body`
/// row at `CarrierClass::BignumNat` fires this test and changes nothing else,
/// `natAdd` still refusing with the same text. So this is a review tripwire on
/// the stated intent, and `whole_body_nat_arithmetic_has_no_selection_row`
/// below is the pin on the mechanism.
///
/// Adding a whole-body `Nat` row is a legitimate thing to want (`nat.add`
/// already exists for recursion arms). The tripwire is here so that doing it
/// cannot be a quiet one-line table edit: the row must be paired with a
/// decision about what `emit_planned_function` does when a computing shape
/// arrives at a handle carrier — which, as of this landing, it refuses.
#[test]
fn no_whole_body_selection_row_is_stated_at_the_bignum_carrier() {
    let bignum_body: Vec<&str> = ROWS
        .iter()
        .filter(|row| row.carrier == CarrierClass::BignumNat && row.context == RowContext::Body)
        .map(|row| row.name)
        .collect();
    assert!(
        bignum_body.is_empty(),
        "a whole-body row at the bignum carrier makes a non-recursion shape selectable at the \
         opaque handle, and `emit_planned_function` threads that carrier into EVERY shape's \
         signature: {bignum_body:?}",
    );

    // The bignum rows that DO exist, so the test states the positive fact too
    // rather than only an absence that an empty table would satisfy.
    let bignum: Vec<&str> =
        ROWS.iter().filter(|row| row.carrier == CarrierClass::BignumNat).map(|r| r.name).collect();
    assert_eq!(
        bignum,
        vec![
            "nat.rec.structural",
            "nat.wf.fix",
            "nat.param",
            "nat.sub",
            "nat.mod",
            "nat.self",
            "nat.lit",
            "nat.add",
            "nat.mul",
        ],
        "the bignum carrier's rows are the two recursion schemes and the nodes of their arms",
    );
}

/// The OTHER half of the same fact: the carrier-AGNOSTIC whole-body rows.
///
/// A `CarrierClass::AnyExact` `Body` row is selectable at a `Nat` carrier, so
/// this list is exactly the set of non-recursion shapes that can reach the
/// emitter with a handle in the signature. Each one's disposition, measured
/// below:
///
/// * `param` — reaches the emitter and EMITS. Its body is `Return <parameter>`:
///   exact-typed transport, the ratified use of a handle
///   (`the_projection_lane_carries_a_handle_and_computes_nothing_on_it`).
/// * `bool.not` / `bool.and` / `bool.or` — the sealed plan requires `Bool` in
///   every position, so a `Nat` never reaches the emitter through them.
/// * `rust.call` — `emit_planned_function` refuses `RustCallChain` outright
///   (`ShapeNotYetSpelled`), and the separate Rust-call entry point threads no
///   runtime at all, so `Nat` refuses there as `CarrierHasNoTrustIrType`.
///
/// A NEW `AnyExact` body row lands here as a failure, on purpose. Same standing
/// as the ledger above: the row itself selects nothing, but it is the one class
/// of table edit whose paired recognizer arm would hand the emitter a handle
/// carrier, so it must not land without a stated disposition.
#[test]
fn the_carrier_agnostic_whole_body_rows_are_the_measured_set() {
    let agnostic: Vec<&str> = ROWS
        .iter()
        .filter(|row| row.carrier == CarrierClass::AnyExact && row.context == RowContext::Body)
        .map(|row| row.name)
        .collect();
    assert_eq!(
        agnostic,
        vec!["param", "bool.not", "bool.and", "bool.or", "rust.call"],
        "a carrier-agnostic whole-body row is selectable at a `Nat`, so each one needs a stated \
         disposition at the opaque handle — see this test's doc comment",
    );
}

// ── the recognizer: where the refusal is actually decided ──────────

/// THE WITNESS. A real `WrappingBinOp` body with a `Nat` in a parameter
/// position it never mentions is refused at plan time, by name, and the refusal
/// names the bignum carrier.
///
/// This is the construction the flagged concern asked for, and the answer is
/// that `check_arith_signature`'s "EVERY signature position — used or not"
/// clause is what closes it. The clause was written for the single-domain
/// reflection, not for this; measuring it here is what makes the emitter's
/// silence a reliance rather than a coincidence.
#[test]
fn a_wrapping_binop_plan_cannot_carry_a_nat_in_any_signature_position() {
    let refusal = plan_refusal(MIXED_ADD, "mixedAdd");
    let reason = not_emittable_reason(&refusal);
    assert!(
        reason.contains("it is a single wrapping op"),
        "the refusal must come from the `WrappingBinOp` arm: {reason}",
    );
    assert!(
        reason.contains("parameter 0 carries at `BignumNat`"),
        "the refusal must name the bignum carrier it refused: {reason}",
    );
    assert!(
        reason.contains("EVERY signature position — used or not"),
        "the UNUSED position is the whole point — a used one would be caught by typing: {reason}",
    );

    // The same refusal at a second arm of the family, so this is a property of
    // `check_arith_signature` rather than of one shape.
    let constant = plan_refusal(NAT_CONST, "natConst");
    let constant_reason = not_emittable_reason(&constant);
    assert!(
        constant_reason.contains("it is a constant body")
            && constant_reason.contains("`BignumNat`"),
        "the constant arm shares the single-domain signature check: {constant_reason}",
    );
}

/// Whole-body `Nat` arithmetic is refused by RECOGNITION: every arm declines
/// — `recognise_wrapping_expr` at its hard-coded `CleanType::UInt` RESULT gate
/// — the body reaches the fall-through `Err`, and that arm's text cites the
/// missing selection row and names the carrier class by its own label.
///
/// This is a pin on the MECHANISM, and the assertion is deliberately on the
/// refusal text: any relaxation that makes `natAdd` refuse somewhere else, or
/// not refuse at all, fails it. Together with
/// `a_wrapping_binop_plan_cannot_carry_a_nat_in_any_signature_position` it
/// covers both recognizer refusals — not two independent layers, but the two
/// arms of one recognizer, reached by different bodies: this one by arithmetic
/// whose RESULT is at the bignum carrier, that one by arithmetic at a machine
/// width with a `Nat` in some other position.
#[test]
fn whole_body_nat_arithmetic_has_no_selection_row() {
    let refusal = plan_refusal(NAT_ADD, "natAdd");
    let reason = not_emittable_reason(&refusal);
    assert!(
        reason.contains("no selection row for `HAdd.hAdd`"),
        "the refusal must name the head it could not select: {reason}",
    );
    assert!(
        reason.contains(CarrierClass::BignumNat.label()),
        "the refusal must name the carrier class, which is how the table is keyed: {reason}",
    );
}

// ── what actually reaches the emitter ─────────────────────────────────────

/// The projection lane DOES reach the emitter at a handle carrier, and what it
/// emits is transport: one `Return` of a block parameter, no arithmetic, no
/// cast, no memory operation. The emitted pinned module validates.
///
/// Also measured: the same plan REFUSES without a runtime
/// (`CarrierHasNoTrustIrType`). So the unconditional threading is not merely
/// harmless here — it is what admits a `Nat`-to-`Nat` projection at all, and
/// that is a capability, not an accident.
#[test]
fn the_projection_lane_carries_a_handle_and_computes_nothing_on_it() {
    for (name, decl, returned) in [("natId", NAT_ID, 0_u32), ("natMixedFst", NAT_MIXED_FST, 1_u32)]
    {
        let env = env_with(decl);
        let plan = plan_clean_origin_body(&env, name).expect("the projection lane plans");

        let mut builder = ModuleBuilder::new_with_target_info("clean_origin_nat_scope", target());
        let declared =
            declare_pinned_nat_runtime(&mut builder).expect("the pin row must be present");
        let mut module = builder.build().expect("ModuleBuilder::build: test fixture");
        let self_id = FuncId::new(u32::try_from(module.functions.len()).expect("small module"));
        let nat = declared.for_function(self_id).expect("a fresh id cannot alias a declaration");

        let func_ty = trust_ir_func_ty_with_nat(plan.signature(), Some(&nat_handle_ty()))
            .expect("a `Nat` position carries at the pinned handle");
        assert!(
            func_ty.params.contains(&nat_handle_ty()),
            "{name}: the handle must really be in the signature, or this measures nothing: \
             {func_ty:?}",
        );
        let ty = module.add_func_type(func_ty).expect("Module::add_func_type: test fixture");

        // WITHOUT the runtime the same plan refuses: the threading is the
        // admission, and it is the only one.
        match emit_clean_origin_function(&plan, self_id, ty) {
            Err(CleanIrRefusal::CarrierHasNoTrustIrType { position, clean }) => {
                assert_eq!(position, Some(0), "{name}: the refusal names the `Nat` position");
                assert_eq!(format!("{clean:?}"), "Nat");
            }
            other => panic!("{name}: a `Nat` carrier with no runtime must refuse, got {other:?}"),
        }

        let function = emit_clean_origin_function_with_nat(&plan, self_id, ty, Some(nat))
            .expect("the projection emits against the pinned runtime");
        assert_eq!(function.blocks.len(), 1, "{name}: a projection is one block");
        let body = &function.blocks[0].body;
        assert_eq!(
            body.len(),
            1,
            "{name}: a projection emits ONE instruction; anything else would be a computation on \
             a carrier that may be an opaque handle: {body:#?}",
        );
        match &body[0].inst {
            Inst::Return { values } => assert_eq!(
                values,
                &vec![ValueId::new(returned)],
                "{name}: it must return the projected block parameter verbatim",
            ),
            other => panic!("{name}: expected a `Return`, got {other:?}"),
        }

        module.try_add_function(function).expect("Module::try_add_function: test fixture");
        let errors = validate_module(&module);
        assert!(errors.is_empty(), "{name}: the emitted module must validate, got {errors:#?}");
    }
}

/// The standalone entry point cannot be given a runtime at all, so a `Nat`
/// carrier refuses there for every shape — including the projection that the
/// with-runtime entry admits.
#[test]
fn the_standalone_entry_refuses_a_nat_carrier_outright() {
    let env = env_with(NAT_ID);
    let plan = plan_standalone_clean_origin_body(&env, "natId").expect("the projection plans");
    match trust_clean_ir::emit_standalone_clean_origin_function(
        &plan,
        FuncId::new(0),
        FuncTyId::new(0),
    ) {
        Err(CleanIrRefusal::CarrierHasNoTrustIrType { position, .. }) => {
            assert_eq!(position, Some(0));
        }
        other => panic!("the standalone entry threads no runtime, so `Nat` must refuse: {other:?}"),
    }
}

// ── the downstream backstop ───────────────────────────────────────────────

/// THE BACKSTOP, measured rather than assumed: the body a computing shape at a
/// handle carrier WOULD have emitted is refused by `validate_module`.
///
/// Hand-built, because the planner will not produce the plan — that is the
/// finding, and this is what it would cost if it did. Two errors, not one, and
/// they are independent: the type rule (`BinOp` needs an integer) and the v43
/// handle rule (a handle may only be transported). Pinned BY NAME so that
/// widening the ratified transport set cannot silently make arithmetic on a
/// bignum handle well-formed.
#[test]
fn arithmetic_at_a_handle_carrier_is_refused_by_the_validator() {
    let handle = nat_handle_ty();

    let binop = handle_body("natWrappingAdd", &handle, |lhs, rhs, out| InstrNode {
        inst: Inst::BinOp { op: BinOp::Add, ty: handle.clone(), lhs, rhs },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    assert!(
        binop.iter().any(|error| matches!(error, ValidationError::BinOpRequiresInteger { .. })),
        "arithmetic on a handle must fail the type rule: {binop:#?}",
    );
    assert!(
        binop.iter().any(|error| matches!(
            error,
            ValidationError::InvalidHandleUse { location, detail }
                if location == "natWrappingAdd" && detail.contains("`BinOp`")
        )),
        "and it must fail the v43 handle rule, naming the instruction: {binop:#?}",
    );

    let icmp = handle_body("natLt", &handle, |lhs, rhs, out| InstrNode {
        inst: Inst::ICmp { op: ICmpOp::Ult, ty: handle.clone(), lhs, rhs },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    assert!(
        icmp.iter().any(|error| matches!(error, ValidationError::ICmpRequiresIntegerOrPtr { .. })),
        "a comparison on a handle must fail the type rule: {icmp:#?}",
    );
    assert!(
        icmp.iter().any(|error| matches!(
            error,
            ValidationError::InvalidHandleUse { location, detail }
                if location == "natLt" && detail.contains("`ICmp`")
        )),
        "and the handle rule, naming the instruction: {icmp:#?}",
    );

    // THE CONTROL. The same module shape with the handle merely COPIED
    // validates, so the two refusals above are the handle-use rule
    // discriminating between transport and computation — not a blanket refusal
    // of every module that mentions a handle.
    let copy = handle_body("natCopy", &handle, |lhs, _rhs, out| InstrNode {
        inst: Inst::Copy { ty: handle.clone(), operand: lhs },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    assert!(copy.is_empty(), "exact-typed transport of a handle is the ratified use: {copy:#?}");
}

/// AND THE HALF THAT DOES NOT FAIL CLOSED, which is why the emitter refuses
/// rather than leaning on the validator.
///
/// `NatCarrier::ExecutableSubstitute` is a DECLARED machine carrier — the
/// kernel-agreement harness passes `Ty::U64` so the emitted recursion can be
/// RUN. Under that carrier the same mistake emits `BinOp { ty: U64 }` over two
/// `u64` parameters: a 64-bit WRAP of an unbounded `Nat`, and a module that
/// validates without a single error. There is no downstream layer that can see
/// it, so `CleanIrRefusal::ShapeMayNotCarryNat` is the only thing standing
/// between a computing shape at a `Nat` carrier and a wrong answer.
#[test]
fn the_substitute_carriers_wrap_is_invisible_to_the_validator() {
    let errors = handle_body("natWrappingAdd", &Ty::U64, |lhs, rhs, out| InstrNode {
        inst: Inst::BinOp { op: BinOp::Add, ty: Ty::U64, lhs, rhs },
        results: vec![out],
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    assert!(
        errors.is_empty(),
        "a `u64` add is well-typed whatever it was MEANT to compute; the validator has nothing \
         to say about a wrapped `Nat`: {errors:#?}",
    );
}

/// One pinned-runtime module whose single function takes two handles, runs
/// `node(v0, v1, v2)`, and returns `v2`. The result carrier is the handle for
/// every instruction this is called with except `ICmp`, whose `Bool` result is
/// supplied by `returns`.
fn handle_body(
    name: &str,
    handle: &Ty,
    node: impl FnOnce(ValueId, ValueId, ValueId) -> InstrNode,
) -> Vec<ValidationError> {
    let mut builder = ModuleBuilder::new_with_target_info("handle_backstop", target());
    declare_pinned_nat_runtime(&mut builder).expect("the pin row must be present");
    let mut module = builder.build().expect("ModuleBuilder::build: test fixture");

    let node = node(ValueId::new(0), ValueId::new(1), ValueId::new(2));
    let result_ty = match &node.inst {
        Inst::ICmp { .. } => Ty::Bool,
        _ => handle.clone(),
    };
    let ty = module
        .add_func_type(FuncTy {
            params: vec![handle.clone(), handle.clone()],
            returns: vec![result_ty],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(u32::try_from(module.functions.len()).expect("small module"));
    let entry = BlockId::new(0);
    let mut block = Block::new(entry)
        .with_param(ValueId::new(0), handle.clone())
        .with_param(ValueId::new(1), handle.clone());
    block.body.push(node);
    block.body.push(InstrNode {
        inst: Inst::Return { values: vec![ValueId::new(2)] },
        results: Vec::new(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    });
    let mut function = Function::new(id, name, ty, entry);
    function.calling_conv = CallingConv::Rust;
    function.blocks.push(block);
    module.try_add_function(function).expect("Module::try_add_function: test fixture");
    validate_module(&module)
}

/// The carrier type itself cannot say "not for a computing shape".
///
/// [`NatCarrier`] has two variants and BOTH can be a handle for typing
/// purposes: `PinnedHandle` IS the handle, and `ExecutableSubstitute` is
/// whatever the caller declared. `NatCarrier::check` — called at the top of
/// `emit_planned_function`, just above the threading — decides only whether a
/// SUBSTITUTE wears a handle, which is a question about the caller's claim, not
/// about the shape. So the carrier type constrains nothing per-shape, and this
/// test records that as a measured fact rather than leaving it to be rediscovered.
#[test]
fn the_carrier_check_says_nothing_about_which_shape_may_use_it() {
    // The production carrier passes `check` unconditionally: it is the handle.
    NatCarrier::PinnedHandle.check().expect("the pinned handle is always well-formed");
    assert!(NatCarrier::PinnedHandle.ty().is_handle());

    // A substitute that is not a handle also passes — and is a type a
    // `BinOp` would be well-formed at. Neither answer mentions a shape.
    NatCarrier::ExecutableSubstitute(Ty::U64).check().expect("a machine carrier is a substitute");

    // The only thing `check` refuses is a substitute wearing handle authority.
    let foreign = NatCarrier::ExecutableSubstitute(Ty::handle("Blob", "other::Runtime"));
    assert!(matches!(foreign.check(), Err(CleanIrRefusal::NatCarrierIsAForeignHandle { .. })));
}
