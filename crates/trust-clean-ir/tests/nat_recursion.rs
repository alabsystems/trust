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
use trust_clean_ir::{
    CleanIrRefusal, NatCarrier, NatRuntime, callee_edges, emit_clean_origin_function_with_nat,
};
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

/// A runtime at a DECLARED executable substitute carrier: the lane that lets
/// the emitted recursion be RUN against the kernel. It makes no handle claim.
fn nat_runtime(nat_ty: trust_ir::ty::Ty) -> NatRuntime {
    nat_runtime_at(NatCarrier::ExecutableSubstitute(nat_ty))
}

fn nat_runtime_at(carrier: NatCarrier) -> NatRuntime {
    NatRuntime {
        carrier,
        from_u64: FuncId::new(10),
        add: FuncId::new(11),
        sub: FuncId::new(12),
        is_zero: FuncId::new(13),
        // No release callee by default. Under a substitute carrier `Nat` is a
        // VALUE and there is nothing to release; the tests that are about
        // release call `with_release` below.
        release: None,
        self_id: FuncId::new(0),
    }
}

/// The same runtime with the RELEASE callee supplied.
///
/// Id 14, after the four the model occupies, so it is distinct from every other
/// entry point and from the emitted function — the distinctness
/// `check_identities` requires.
fn with_release(mut nat: NatRuntime) -> NatRuntime {
    nat.release = Some(FuncId::new(14));
    nat
}

/// Production's carrier: the PINNED nominal opaque handle
/// `handle<"Nat", "trust_bignum::Nat">`, which claims no width and is not a
/// pointer. Was a bare `Ty::Ptr` before trust-ir v43 supplied `Ty::Handle`.
fn nat_opaque() -> NatRuntime {
    nat_runtime_at(NatCarrier::PinnedHandle)
}

/// The one source spelling the planner admits as a recursion shape: a
/// `termination_by` well-founded definition. Taken from
/// `trust-clean-origin/tests/r2_session_probes.rs`, which is where the admitting
/// fragment is pinned -- rather than invented here, so this test tracks the
/// planner's real boundary instead of a guess about it.
const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

/// A recursion whose ZERO ARM RETURNS ITS PARAMETER, so the body is NOT
/// return-fresh: `countdownId n = n`, computed the long way round.
///
/// Measured plan (2026-09-17):
/// `WellFoundedNatRec { zero_value: Decreasing, nonzero_value: Rec, .. }`.
/// `Decreasing` at the root of an arm is the whole point — it is the one shape
/// where the self-call may hand its own argument straight back, and therefore
/// the one where the emitter must NOT release the predecessor or the result.
const COUNTDOWN_ID: &str = "def countdownId (n : Nat) : Nat := \
                            if h : 0 < n then countdownId (n - 1) else n\n\
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

// ─── RELEASE: what the emitted body frees, and what it deliberately LEAKS ──
//
// These are STRUCTURAL, and they have to be: "released exactly once" is a
// property of every execution path, `trust_ir::interpret` cannot execute a
// handle at all, and neither `validate_module` nor trust-cg decides liveness.
// So the emitter's classification is the only thing standing between this
// producer and a use-after-free in a trusted runtime, and these tests are what
// hold it to its stated rule — one test per DECISION, including the decisions
// to leak.

/// The block with this id, which the emitter numbers 0 (entry) / 1 (zero arm)
/// / 2 (nonzero arm).
fn block_of(function: &Function, id: u32) -> &Block {
    function
        .blocks
        .iter()
        .find(|block| block.id == BlockId::new(id))
        .unwrap_or_else(|| panic!("no block bb{id}"))
}

/// Every RELEASE call in `block`, in emission order, as the handle each frees.
///
/// Asserts the CALL SHAPE while it is here: exactly one argument and NO result.
/// The pin spells release's result as an EMPTY return list, which is a
/// different `FuncTy` from a one-element `Unit` return, and a `results` vector
/// with an entry in it would be an off-pin call the validator refuses.
fn releases(block: &Block, nat: &NatRuntime) -> Vec<ValueId> {
    let release = nat.release.expect("this helper is for runtimes that DO release");
    block
        .body
        .iter()
        .filter_map(|node| match &node.inst {
            Inst::Call { callee, args } if *callee == release => {
                assert_eq!(args.len(), 1, "release takes exactly one handle: {args:?}");
                assert!(
                    node.results.is_empty(),
                    "release produces NOTHING -- the pinned return list is empty",
                );
                Some(args[0])
            }
            _ => None,
        })
        .collect()
}

/// The results of every call to `callee` in `block`, in order.
fn results_of(block: &Block, callee: FuncId) -> Vec<ValueId> {
    block
        .body
        .iter()
        .filter(|node| matches!(&node.inst, Inst::Call { callee: c, .. } if *c == callee))
        .map(|node| node.results[0])
        .collect()
}

fn result_of(block: &Block, callee: FuncId) -> ValueId {
    let all = results_of(block, callee);
    assert_eq!(all.len(), 1, "expected exactly one call here, got {all:?}");
    all[0]
}

/// The value `block` returns.
fn returned_value(block: &Block) -> ValueId {
    block
        .body
        .iter()
        .find_map(|node| match &node.inst {
            Inst::Return { values } => Some(values[0]),
            _ => None,
        })
        .expect("every arm block returns")
}

/// A RETURN-FRESH body releases every handle it allocated except the one it
/// hands back — the predecessor and the self-call's result included.
///
/// `countdownSum` roots its arms at `NatConst` and `Add`, so neither can return
/// the parameter, so the self-call (whose callee IS this function) cannot hand
/// its argument back. That is what makes `pred` and `rec` releasable, and it is
/// the difference between leaking O(n) allocations across a recursion and
/// leaking none.
#[test]
fn a_return_fresh_recursion_releases_every_handle_it_owns_and_nothing_else() {
    let nat = with_release(nat_opaque());
    let f = emit_rec_at(COUNTDOWN_SUM, "countdownSum", nat.clone()).expect("emits");

    // ── the zero arm: `0`, materialized and RETURNED ───────────────────────
    let zero = block_of(&f, 1);
    let zero_literal = result_of(zero, nat.from_u64);
    assert_eq!(returned_value(zero), zero_literal);
    assert_eq!(
        releases(zero, &nat),
        Vec::<ValueId>::new(),
        "the only handle the zero arm makes is the one it RETURNS, and returning \
         TRANSFERS ownership -- releasing it would hand the caller a dangling word",
    );

    // ── the nonzero arm: `n + countdownSum (n - 1)` ────────────────────────
    let nonzero = block_of(&f, 2);
    let literal = result_of(nonzero, nat.from_u64); // the `1` of the predecessor
    let pred = result_of(nonzero, nat.sub);
    let rec = result_of(nonzero, nat.self_id);
    let sum = result_of(nonzero, nat.add);
    assert_eq!(returned_value(nonzero), sum, "the arm returns the accumulated sum");

    assert_eq!(
        releases(nonzero, &nat),
        vec![literal, pred, rec],
        "a return-fresh body releases the literal, the predecessor it passed to \
         the self-call, and the result the self-call handed back",
    );

    // The two handles it must NEVER release, stated as their own assertions
    // because each is a different kind of mistake.
    let freed = releases(nonzero, &nat);
    assert!(
        !freed.contains(&ValueId::new(0)),
        "the PARAMETER is the caller's allocation: releasing a borrowed handle \
         corrupts the runtime rather than merely losing memory",
    );
    assert!(!freed.contains(&sum), "the RETURNED value belongs to the caller now");

    // Placement: every release is past the `add` that read its operands and
    // immediately before the `Return`. Releasing `pred` before the self-call
    // read it, or `rec` before the `add` did, would be a use-after-free that
    // every structural count above would still be satisfied by.
    let body = &nonzero.body;
    let add_at = body
        .iter()
        .position(|n| matches!(&n.inst, Inst::Call { callee, .. } if *callee == nat.add))
        .expect("the add is in the body");
    let first_release = body
        .iter()
        .position(|n| matches!(&n.inst, Inst::Call { callee, .. } if Some(*callee) == nat.release))
        .expect("there are releases");
    assert!(add_at < first_release, "releases come AFTER the arithmetic that read the handles");
    assert!(
        matches!(&body[body.len() - 1].inst, Inst::Return { .. }),
        "the block still ends in its terminator",
    );
    assert_eq!(
        body.len() - 1 - first_release,
        3,
        "the releases are the three nodes immediately before the `Return`",
    );
}

/// A body that CAN RETURN ITS PARAMETER withholds the self-call pair, and
/// leaks — on purpose.
///
/// `countdownId`'s zero arm is `Decreasing`: at the innermost frame the callee
/// hands its own argument straight back, so the self-call's result and the
/// predecessor passed to it may be ONE allocation. Releasing either would
/// dangle the other, and which of them it is is a runtime fact no syntactic
/// rule decides. So the predecessor is withheld and the result is never
/// recorded, and a frame leaks its own predecessor — one allocation per
/// frame.
///
/// This is the test that would fail if someone "optimized" the emitter by
/// dropping the return-freshness condition, and the failure it prevents is a
/// use-after-free in trusted code rather than a wrong answer.
#[test]
fn a_recursion_that_can_return_its_parameter_withholds_the_self_call_pair() {
    let nat = with_release(nat_opaque());
    let f = emit_rec_at(COUNTDOWN_ID, "countdownId", nat.clone()).expect("emits");

    // ── the zero arm returns the PARAMETER: that is the whole premise ──────
    let zero = block_of(&f, 1);
    assert_eq!(
        returned_value(zero),
        ValueId::new(0),
        "the zero arm returns `n` itself -- which is what makes this body not return-fresh",
    );
    assert_eq!(
        releases(zero, &nat),
        Vec::<ValueId>::new(),
        "it allocated nothing, so it has nothing to release",
    );

    // ── the nonzero arm: `countdownId (n - 1)` ─────────────────────────────
    let nonzero = block_of(&f, 2);
    let literal = result_of(nonzero, nat.from_u64);
    let pred = result_of(nonzero, nat.sub);
    let rec = result_of(nonzero, nat.self_id);
    assert_eq!(returned_value(nonzero), rec);

    assert_eq!(
        releases(nonzero, &nat),
        vec![literal],
        "only the literal `1` is released: it is fresh, and nothing the self-call \
         can return aliases it",
    );
    let freed = releases(nonzero, &nat);
    assert!(
        !freed.contains(&pred),
        "the PREDECESSOR is withheld: the self-call may have returned this very \
         allocation, and releasing it would dangle the value being returned",
    );
    assert!(
        !freed.contains(&rec),
        "the self-call's RESULT is withheld: it is also the returned value here, \
         and in general its provenance is the callee's business",
    );
    assert!(!freed.contains(&ValueId::new(0)), "and never the parameter");
}

/// Without a release callee NOTHING is released, and the body is otherwise
/// BYTE-IDENTICAL to the releasing one.
///
/// Two facts in one test, because they are one design claim: release is purely
/// ADDITIVE. `None` is a request to leak (the pre-2026-09-17 behaviour, and
/// what the executable-substitute harness passes, since a modelled `Nat` is a
/// value with no allocation), and it must not perturb a single other
/// instruction — otherwise the evidence the leaking lane carries would not
/// transfer to the releasing one.
#[test]
fn without_a_release_callee_nothing_is_released_and_the_rest_is_unchanged() {
    let leaking = emit_rec_at(COUNTDOWN_SUM, "countdownSum", nat_opaque()).expect("emits");
    let nat = with_release(nat_opaque());
    let releasing = emit_rec_at(COUNTDOWN_SUM, "countdownSum", nat.clone()).expect("emits");

    let release = nat.release.expect("supplied");
    assert!(
        !callee_edges(&leaking).contains(&release),
        "a runtime with no release callee must emit no call to one",
    );

    // Strip the release nodes from the releasing body; what is left must be
    // the leaking body, node for node.
    for id in 0..3 {
        let stripped: Vec<_> = block_of(&releasing, id)
            .body
            .iter()
            .filter(|node| !matches!(&node.inst, Inst::Call { callee, .. } if *callee == release))
            .cloned()
            .collect();
        assert_eq!(
            stripped,
            block_of(&leaking, id).body,
            "bb{id} must differ from the leaking emission ONLY by release calls",
        );
    }
}

/// The release callee is a CALL EDGE, so `callee_edges` reports it.
///
/// Not a formality: `callee_edges` is the publication precondition a join seam
/// checks before appending an emitted record, because a seam that re-mints the
/// function's `FuncId` without rewriting the edges inside it leaves each one
/// pointing at whatever function now occupies the old index. A release edge
/// missed by that rewrite would call some other function to free a handle.
#[test]
fn the_release_callee_is_reported_as_a_call_edge() {
    let nat = with_release(nat_opaque());
    let f = emit_rec_at(COUNTDOWN_SUM, "countdownSum", nat.clone()).expect("emits");
    let edges = callee_edges(&f);
    let release = nat.release.expect("supplied");
    assert!(edges.contains(&release), "the release edge must be reported: {edges:?}");
    // Every other runtime edge is still reported too, so the release edge was
    // added to the answer rather than substituted into it.
    for (label, id) in [
        ("from_u64", nat.from_u64),
        ("sub", nat.sub),
        ("add", nat.add),
        ("is_zero", nat.is_zero),
        ("self", nat.self_id),
    ] {
        assert!(edges.contains(&id), "the `{label}` edge must still be reported: {edges:?}");
    }
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
    let unary = module
        .add_func_type(FuncTy {
            params: vec![u64_ty()],
            returns: vec![u64_ty()],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let binary = module
        .add_func_type(FuncTy {
            params: vec![u64_ty(), u64_ty()],
            returns: vec![u64_ty()],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let nullary = module.add_func_type(FuncTy {
        params: vec![],
        returns: vec![u64_ty()],
        is_vararg: false,
        abi: None,
    });
    let pred_ty = module
        .add_func_type(FuncTy {
            params: vec![u64_ty()],
            returns: vec![Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");

    // from_u64(v) -> v. Identity in the one-limb model: the emitter passes the
    // literal as an argument, so the runtime does not invent it.
    let mut b = Block::new(BlockId::new(0));
    b = b.with_param(ValueId::new(0), u64_ty());
    b.body.push(node(Inst::Return { values: vec![ValueId::new(0)] }, None));
    let mut f = Function::new(nat.from_u64, "nat.from_u64", unary, BlockId::new(0));
    f.blocks = vec![b];
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

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
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

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
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

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
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

    // release(a) -> (). A NO-OP in the one-limb model, and that is faithful to
    // what it models: the model carries `Nat` as a VALUE, so there is no
    // allocation for a release to free. What the model DOES supply is the
    // executable call, so the emitted release instructions are really run —
    // which is how this harness can say the releases do not disturb the
    // computation instead of only that they are in the right place.
    //
    // `returns: []`, not `[Unit]`: that is the pinned release signature, and a
    // one-element `Unit` return would be a different `FuncTy`.
    if let Some(release) = nat.release {
        let release_ty = module
            .add_func_type(FuncTy {
                params: vec![u64_ty()],
                returns: vec![],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut b = Block::new(BlockId::new(0));
        b = b.with_param(ValueId::new(0), u64_ty());
        b.body.push(node(Inst::Return { values: vec![] }, None));
        let mut f = Function::new(release, "nat.release", release_ty, BlockId::new(0));
        f.blocks = vec![b];
        module.try_add_function(f).expect("Module::try_add_function: test fixture");
    }

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
    let self_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    // The emitter materializes every literal through `from_u64`, and this
    // fragment's only literal is 1 (the predecessor step). The model returns
    // that constant.
    limb_model(&mut module, &nat, 0);
    let f = emit_clean_origin_function_with_nat(&plan, FuncId::new(0), self_ty, Some(nat.clone()))
        .expect("emits");
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

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

/// The emitted RELEASES are EXECUTED, and the kernel still agrees.
///
/// The structural tests above say which handles are released and where. They
/// cannot say the releases are harmless to the computation: a release emitted
/// one node too early, or over a value the body still reads, is a placement
/// defect every structural count is satisfied by. This runs the body WITH the
/// releases in it — same emitter, same fragment, same kernel standard as
/// `nat_recursion_executes_and_the_kernel_agrees` — and requires the answers to
/// be unchanged.
///
/// WHAT IT DOES NOT SHOW, stated because the gap is the whole difficulty: the
/// model's `Nat` is a VALUE, so its release frees nothing and a
/// use-after-release would be invisible here. Only the classification argument
/// (crate docs, `body_returns_a_fresh_allocation`) and the ownership facts
/// measured in `trust-bignum`'s own tests carry that. What this adds is that
/// the releases are well-typed, in-scope, dominated, dataflow-neutral and
/// actually reachable — which is the half a reader would otherwise have to take
/// on trust.
#[test]
fn the_emitted_releases_execute_and_the_kernel_still_agrees() {
    let nat = with_release(nat_runtime(Ty::U64));
    let env = env_with(COUNTDOWN_SUM);
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("plans");

    let mut module = Module::new("clean_origin_nat_recursion_release");
    let self_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    limb_model(&mut module, &nat, 0);
    let f = emit_clean_origin_function_with_nat(&plan, FuncId::new(0), self_ty, Some(nat.clone()))
        .expect("emits");

    // The releases really are in the body being executed; without this the
    // test could pass by running a release-free emission.
    let released: usize = f.blocks.iter().map(|block| releases(block, &nat).len()).sum();
    assert_eq!(released, 3, "the nonzero arm releases the literal, the predecessor and the ih");

    module.try_add_function(f).expect("Module::try_add_function: test fixture");

    let interp = Interpreter::with_module(&module);
    let tc = TypeChecker::new(&env);

    for n in 0u64..=12 {
        let arg = InterpretValue::int(Ty::U64, i128::from(n)).expect("u64");
        let outcome = interp
            .execute_func(FuncId::new(0), vec![arg])
            .unwrap_or_else(|e| panic!("the releasing recursion must execute at n={n}: {e:?}"));
        let produced = u64::try_from(outcome.returns[0].as_int().expect("integer").as_unsigned())
            .expect("u64 result");

        let reduced = unfold_island_application(&env, "countdownSum", &[nat_lit(n)])
            .unwrap_or_else(|| panic!("the kernel must reduce countdownSum {n}"));
        assert!(
            tc.is_def_eq(&reduced, &nat_lit(produced)),
            "KERNEL DISAGREEMENT for countdownSum({n}) WITH RELEASES: the emitted \
             TrustIR computed {produced}. A release emitted over a value the body \
             still reads, or one node too early, reaches exactly here."
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
    let self_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    // 6 bits: sums wrap at 64, so countdownSum 12 = 78 cannot be represented.
    limb_model_masked(&mut module, &nat, 0, Some(0b11_1111));
    let f = emit_clean_origin_function_with_nat(&plan, FuncId::new(0), self_ty, Some(nat.clone()))
        .expect("emits");
    module.try_add_function(f).expect("Module::try_add_function: test fixture");

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
