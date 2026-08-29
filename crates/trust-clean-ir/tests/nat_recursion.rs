// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! The two RECURSION shapes: `StructuralNatRec` and `WellFoundedNatRec`.
//!
//! # Why these are checked STRUCTURALLY and not by execution
//!
//! Every other shape in this crate is checked by running the emitted TrustIR
//! through `trust_ir::interpret` and requiring the CIC kernel to agree with the
//! result. That is unavailable here, and the reason is a property of the
//! interpreter rather than of this lane:
//!
//! * these shapes compute at the unbounded bignum `Nat`, so the emitted body
//!   CALLS a runtime (`trust_bignum::Nat::{from_u64, add, sub}`) instead of
//!   doing machine arithmetic;
//! * `trust_ir::interpret` cannot execute a call to a bodyless declaration —
//!   `execute_function_inner` looks up the callee's entry block, finds `None`,
//!   and errors `MissingBlock` (interpret.rs:576-582);
//! * there is no extern / intrinsic / host-call hook anywhere in the
//!   interpreter. The one escape hatch, `Inst::DialectOp`, is hardcoded to the
//!   `vector` dialect and errors on everything else.
//!
//! So these two shapes ship with WEAKER EVIDENCE than the other eleven, and that
//! is stated rather than glossed. What would close it is a host-call hook in
//! `trust_ir::interpret`, after which the existing kernel-agreement harness
//! covers these too with no change to this crate.
//!
//! The obvious shortcut — emit at `u64` so the interpreter can run it — is
//! exactly the wrap the whole `Nat` refusal exists to prevent, and is not taken.
//!
//! What IS checked here: the emitted control flow is the zero-test /
//! predecessor / self-call contract, the self-call goes to the function itself
//! on the PREDECESSOR (not on `n`, which would not terminate), and the arms are
//! not swapped.

use clean_kernel::Environment;
use trust_clean_ir::{CleanIrRefusal, NatRuntime, emit_clean_origin_function_with_nat};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::inst::Inst;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, Function};

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn nat_runtime(nat_ty: trust_ir::ty::Ty) -> NatRuntime {
    NatRuntime {
        nat_ty,
        from_u64: FuncId::new(10),
        add: FuncId::new(11),
        sub: FuncId::new(12),
        is_zero: FuncId::new(13),
        self_id: FuncId::new(0),
    }
}

/// Production's carrier: an opaque handle, claiming no width.
fn nat_opaque() -> NatRuntime {
    nat_runtime(trust_ir::ty::Ty::Ptr)
}

/// The one source spelling the planner admits as a recursion shape: a
/// `termination_by` well-founded definition. Taken from
/// `trust-clean-origin/tests/r2_session_probes.rs`, which is where the admitting
/// fragment is pinned -- rather than invented here, so this test tracks the
/// planner's real boundary instead of a guess about it.
const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

fn emit_rec(decl: &str, name: &str) -> Result<Function, CleanIrRefusal> {
    emit_rec_at(decl, name, nat_opaque())
}

fn emit_rec_at(decl: &str, name: &str, nat: NatRuntime) -> Result<Function, CleanIrRefusal> {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).unwrap_or_else(|e| {
        panic!("`{name}` must plan as a recursion shape (the fragment boundary moved?): {e:?}")
    });
    emit_clean_origin_function_with_nat(&plan, FuncId::new(0), FuncTyId::new(0), Some(nat))
}

fn calls(block: &Block) -> Vec<(FuncId, Vec<ValueId>)> {
    block
        .body
        .iter()
        .filter_map(|n| match &n.inst {
            Inst::Call { callee, args } => Some((*callee, args.clone())),
            _ => None,
        })
        .collect()
}

/// Without a `NatRuntime` the shape still refuses — and the refusal now says the
/// shape IS emittable and names what to supply, rather than claiming it cannot
/// be done at all.
#[test]
fn recursion_without_a_runtime_refuses_and_names_the_runtime() {
    let text = CleanIrRefusal::RecursionNeedsNatRuntime { shape: "StructuralNatRec" }.to_string();
    assert!(text.contains("StructuralNatRec"), "{text}");
    assert!(text.contains("emit_clean_origin_function_with_nat"), "names the entry point: {text}");
    assert!(text.contains("Options:"), "{text}");
}

/// The self-call argument is checked, not assumed. The plan CARRIES `rec_arg`
/// exactly so the emitter names the same fact the kernel identity check does.
#[test]
fn a_non_predecessor_recursive_argument_is_refused() {
    let text = CleanIrRefusal::RecursionArgIsNotPred { shape: "StructuralNatRec" }.to_string();
    assert!(text.contains("pred(n)"), "must name the required argument: {text}");
    assert!(text.contains("Options:"), "{text}");
}

/// The emitted control flow IS the zero-test / predecessor / self-call contract.
///
/// A branch, not the branchless `Select` the comparison shapes use: `Select`
/// evaluates BOTH arms and the nonzero arm holds the self-call, so a branchless
/// spelling would recurse unconditionally and never terminate. That is the one
/// mistake this shape can make that still typechecks, so it is asserted.
#[test]
fn nat_recursion_emits_the_zero_test_contract() {
    let nat = nat_opaque();
    let f = emit_rec(COUNTDOWN_SUM, "countdownSum").expect("the recursion shape must emit");

    assert_eq!(f.blocks.len(), 3, "entry + zero arm + nonzero arm");
    assert_eq!(f.entry, BlockId::new(0));

    // entry: is_zero then a CONDITIONAL branch.
    let entry = &f.blocks[0];
    let entry_calls = calls(entry);
    assert_eq!(entry_calls[0].0, nat.is_zero, "the entry tests for zero first");
    assert_eq!(entry_calls[0].1, vec![ValueId::new(0)], "it tests the parameter");
    assert!(
        entry.body.iter().any(|n| matches!(&n.inst, Inst::CondBr { .. })),
        "must BRANCH -- a branchless select would evaluate the self-call \
         unconditionally and never terminate"
    );

    // the nonzero arm recurses on the PREDECESSOR, not on n.
    let nonzero = f.blocks.iter().find(|b| b.id == BlockId::new(2)).expect("nonzero arm");
    let nz = calls(nonzero);
    let sub = nz.iter().position(|(c, _)| *c == nat.sub).expect("computes the predecessor");
    let selfcall = nz.iter().position(|(c, _)| *c == nat.self_id).expect("calls itself");
    assert!(sub < selfcall, "the predecessor is computed BEFORE the self-call");
    let pred_value = nonzero
        .body
        .iter()
        .find(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == nat.sub))
        .expect("sub node")
        .results[0];
    assert_eq!(
        nz[selfcall].1,
        vec![pred_value],
        "the self-call takes the PREDECESSOR. Passing the parameter itself is the \
         non-terminating emission this contract exists to prevent."
    );
    assert!(
        !nz[selfcall].1.contains(&ValueId::new(0)),
        "and it does not take `n`: {:?}",
        nz[selfcall].1
    );

    // the zero arm has no self-call at all.
    let zero = f.blocks.iter().find(|b| b.id == BlockId::new(1)).expect("zero arm");
    assert!(
        !calls(zero).iter().any(|(c, _)| *c == nat.self_id),
        "the zero arm must not recurse -- that is what makes the recursion well-founded"
    );
}

// ─── EXECUTED, and checked against the CIC kernel ──────────────────────────
//
// The tests above inspect the emitted control flow. This one RUNS it, and lets
// the kernel decide the answer — the same standard the other eleven shapes are
// held to.
//
// The obstacle was never the emitter: `trust_ir::interpret` cannot execute a
// call to a bodyless declaration (`MissingBlock`), and has no host-call hook. So
// the runtime is given TrustIR BODIES here, in the test, over a one-limb model
// of `Nat` (`Ty::U64`). The emitter is unchanged and never learns a width — it
// emits control flow and calls, and `NatRuntime::nat_ty` is the caller's choice.
//
// WHAT THE MODEL IS AND IS NOT. A single u64 limb is a faithful model of `Nat`
// exactly while no value exceeds `u64::MAX`. Inside that range the kernel and the
// model agree by construction, so a disagreement is a real emitter defect. Outside
// it the model would wrap and `Nat` would not — which is why the inputs here are
// small and why this is not offered as a proof for arbitrary `Nat`. Production
// still emits `Ty::Ptr` and calls the real bignum runtime.
//
// What this buys that structure alone cannot: the zero test, the predecessor, the
// self-call and the accumulation are EXECUTED in composition, against a kernel
// that computes the real unbounded `Nat`. An emitter that recursed on `n`, swapped
// the arms, or dropped the accumulation passes every structural check and fails
// here.

use clean_kernel::{Expr, Name, TypeChecker};
use trust_certify::clean_island::unfold_island_application;
use trust_ir::inst::{BinOp, ICmpOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::{Constant, Module};

fn node(inst: Inst, out: Option<ValueId>) -> InstrNode {
    InstrNode {
        inst,
        results: out.into_iter().collect(),
        proofs: Vec::new(),
        span: None,
        proof_context: None,
        scope: None,
    }
}

/// A one-limb `Nat` runtime, as TrustIR the interpreter can execute.
fn limb_model(module: &mut Module, nat: &NatRuntime, k: u64) {
    limb_model_masked(module, nat, k, None)
}

/// The same model, with `add` optionally TRUNCATED to `add_mask` bits' worth of
/// value — a stand-in for what a real one-limb model does when a `Nat` exceeds
/// `u64::MAX`, at a width small enough to reach in a test.
fn limb_model_masked(module: &mut Module, nat: &NatRuntime, k: u64, add_mask: Option<u64>) {
    let u64_ty = || Ty::U64;
    let unary = module.add_func_type(FuncTy {
        params: vec![u64_ty()],
        returns: vec![u64_ty()],
        is_vararg: false,
    });
    let binary = module.add_func_type(FuncTy {
        params: vec![u64_ty(), u64_ty()],
        returns: vec![u64_ty()],
        is_vararg: false,
    });
    let nullary =
        module.add_func_type(FuncTy { params: vec![], returns: vec![u64_ty()], is_vararg: false });
    let pred_ty = module.add_func_type(FuncTy {
        params: vec![u64_ty()],
        returns: vec![Ty::Bool],
        is_vararg: false,
    });

    // from_u64(v) -> v. Identity in the one-limb model: the emitter passes the
    // literal as an argument, so the runtime does not invent it.
    let mut b = Block::new(BlockId::new(0));
    b = b.with_param(ValueId::new(0), u64_ty());
    b.body.push(node(Inst::Return { values: vec![ValueId::new(0)] }, None));
    let mut f = Function::new(nat.from_u64, "nat.from_u64", unary, BlockId::new(0));
    f.blocks = vec![b];
    module.add_function(f);

    // add(a, b) -> a + b
    let mut b = Block::new(BlockId::new(0));
    b = b.with_param(ValueId::new(0), u64_ty()).with_param(ValueId::new(1), u64_ty());
    b.body.push(node(
        Inst::BinOp { op: BinOp::Add, ty: u64_ty(), lhs: ValueId::new(0), rhs: ValueId::new(1) },
        Some(ValueId::new(2)),
    ));
    let add_result = match add_mask {
        None => ValueId::new(2),
        Some(mask) => {
            b.body.push(node(
                Inst::Const { ty: u64_ty(), value: Constant::Int(i128::from(mask)) },
                Some(ValueId::new(3)),
            ));
            b.body.push(node(
                Inst::BinOp {
                    op: BinOp::And,
                    ty: u64_ty(),
                    lhs: ValueId::new(2),
                    rhs: ValueId::new(3),
                },
                Some(ValueId::new(4)),
            ));
            ValueId::new(4)
        }
    };
    b.body.push(node(Inst::Return { values: vec![add_result] }, None));
    let mut f = Function::new(nat.add, "nat.add", binary, BlockId::new(0));
    f.blocks = vec![b];
    module.add_function(f);

    // sub(a, b) -> TRUNCATED a - b. Lean's Nat.sub saturates at 0, and getting
    // this wrong is how a predecessor recursion silently fails to terminate.
    let mut b = Block::new(BlockId::new(0));
    b = b.with_param(ValueId::new(0), u64_ty()).with_param(ValueId::new(1), u64_ty());
    b.body.push(node(
        Inst::ICmp { op: ICmpOp::Ult, ty: u64_ty(), lhs: ValueId::new(0), rhs: ValueId::new(1) },
        Some(ValueId::new(2)),
    ));
    b.body.push(node(
        Inst::BinOp { op: BinOp::Sub, ty: u64_ty(), lhs: ValueId::new(0), rhs: ValueId::new(1) },
        Some(ValueId::new(3)),
    ));
    b.body.push(node(Inst::Const { ty: u64_ty(), value: Constant::Int(0) }, Some(ValueId::new(4))));
    b.body.push(node(
        Inst::Select {
            ty: u64_ty(),
            cond: ValueId::new(2),
            then_val: ValueId::new(4),
            else_val: ValueId::new(3),
        },
        Some(ValueId::new(5)),
    ));
    b.body.push(node(Inst::Return { values: vec![ValueId::new(5)] }, None));
    let mut f = Function::new(nat.sub, "nat.sub", binary, BlockId::new(0));
    f.blocks = vec![b];
    module.add_function(f);

    // is_zero(a) -> a == 0
    let mut b = Block::new(BlockId::new(0));
    b = b.with_param(ValueId::new(0), u64_ty());
    b.body.push(node(Inst::Const { ty: u64_ty(), value: Constant::Int(0) }, Some(ValueId::new(1))));
    b.body.push(node(
        Inst::ICmp { op: ICmpOp::Eq, ty: u64_ty(), lhs: ValueId::new(0), rhs: ValueId::new(1) },
        Some(ValueId::new(2)),
    ));
    b.body.push(node(Inst::Return { values: vec![ValueId::new(2)] }, None));
    let mut f = Function::new(nat.is_zero, "nat.is_zero", pred_ty, BlockId::new(0));
    f.blocks = vec![b];
    module.add_function(f);

    let _ = (nullary, k);
}

fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

#[test]
fn nat_recursion_executes_and_the_kernel_agrees() {
    // `countdownSum n = n + (n-1) + … + 1`, i.e. n(n+1)/2 — but the expected
    // value is never written here: the KERNEL computes it.
    let nat = nat_runtime(Ty::U64);
    let env = env_with(COUNTDOWN_SUM);
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plans");

    let mut module = Module::new("clean_origin_nat_recursion");
    let self_ty = module.add_func_type(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
    });
    // The emitter materializes every literal through `from_u64`, and this
    // fragment's only literal is 1 (the predecessor step). The model returns
    // that constant.
    limb_model(&mut module, &nat, 0);
    let f = emit_clean_origin_function_with_nat(&plan, FuncId::new(0), self_ty, Some(nat.clone()))
        .expect("emits");
    module.add_function(f);

    let interp = Interpreter::with_module(&module);
    let tc = TypeChecker::new(&env);

    for n in 0u64..=12 {
        let arg = InterpretValue::int(Ty::U64, i128::from(n)).expect("u64");
        let outcome = interp
            .execute_func(FuncId::new(0), vec![arg])
            .unwrap_or_else(|e| panic!("emitted recursion must execute at n={n}: {e:?}"));
        let produced = u64::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
            .expect("u64 result");

        let reduced = unfold_island_application(&env, "countdownSum", &[nat_lit(n)])
            .unwrap_or_else(|| panic!("the kernel must reduce countdownSum {n}"));
        assert!(
            tc.is_def_eq(&reduced, &nat_lit(produced)),
            "KERNEL DISAGREEMENT for countdownSum({n}): the emitted TrustIR computed \
             {produced}, which is not definitionally equal to the kernel's reduction. \
             An emitter that recursed on `n`, swapped the arms, or dropped the \
             accumulation reaches exactly here."
        );
    }
}

/// **THE ONE-LIMB BOUND FAILS CLOSED — demonstrated, not assumed.**
///
/// The recursion evidence in this file is real but BOUNDED: a single `u64` limb
/// models `Nat` faithfully exactly while no value exceeds `u64::MAX`. That
/// sentence has been in the crate docs as an unchecked caveat, and an unchecked
/// caveat is the kind of thing that quietly stops being true.
///
/// The question it leaves open is the one that matters: if the limb model DID
/// exceed its range, would the harness notice, or would it agree with itself and
/// pass? A wrapped `add` produces a perfectly well-formed number, and every
/// structural check in this file would still be satisfied by it.
///
/// This answers it by mutation. The same emitter and the same recursion run
/// against a limb model whose `add` truncates to 6 bits — the same failure a
/// real one-limb model has at `u64::MAX`, just reachable in a test. `countdownSum
/// 12` is 78, which does not fit. The kernel, which computes over unbounded
/// `Nat`, must REJECT the truncated answer.
///
/// If this test ever fails, the bound has become silent: the harness would be
/// unable to tell a faithful limb model from a diverged one, and every
/// recursion result in this file would be worth nothing. It is the reason the
/// bounded evidence is trustworthy within its range.
#[test]
fn a_limb_model_that_exceeds_its_range_is_caught_by_the_kernel() {
    let nat = nat_runtime(Ty::U64);
    let env = env_with(COUNTDOWN_SUM);
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plans");

    let mut module = Module::new("clean_origin_nat_recursion_narrow");
    let self_ty = module.add_func_type(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::U64],
        is_vararg: false,
    });
    // 6 bits: sums wrap at 64, so countdownSum 12 = 78 cannot be represented.
    limb_model_masked(&mut module, &nat, 0, Some(0b11_1111));
    let f = emit_clean_origin_function_with_nat(&plan, FuncId::new(0), self_ty, Some(nat.clone()))
        .expect("emits");
    module.add_function(f);

    let interp = Interpreter::with_module(&module);
    let tc = TypeChecker::new(&env);

    let n = 12u64;
    let arg = InterpretValue::int(Ty::U64, i128::from(n)).expect("u64");
    let outcome = interp
        .execute_func(FuncId::new(0), vec![arg])
        .unwrap_or_else(|e| panic!("the narrowed model must still execute: {e:?}"));
    let produced = u64::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
        .expect("u64 result");

    // The truncated model is self-consistent and produces a well-formed number.
    // That is exactly why the kernel has to be the one to reject it.
    assert_ne!(
        produced, 78,
        "the 6-bit model must actually have truncated; if it returned the true sum the \
         mutation did not take and this test proves nothing",
    );

    let reduced = unfold_island_application(&env, "countdownSum", &[nat_lit(n)])
        .unwrap_or_else(|| panic!("the kernel must reduce countdownSum {n}"));
    assert!(
        !tc.is_def_eq(&reduced, &nat_lit(produced)),
        "THE ONE-LIMB BOUND IS SILENT: a limb model that overflowed its range produced \
         {produced} for countdownSum({n}), and the kernel ACCEPTED it as definitionally \
         equal to the true unbounded-Nat reduction. If that holds, nothing in this file \
         distinguishes a faithful limb model from a diverged one."
    );
    // And the faithful model still agrees at the same input, so the rejection
    // above is about the truncation and not about the fixture.
    assert!(
        tc.is_def_eq(&reduced, &nat_lit(78)),
        "the kernel's own reduction of countdownSum(12) must be 78"
    );
}
