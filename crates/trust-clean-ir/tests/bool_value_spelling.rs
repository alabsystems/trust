// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! WS5.13 (F-033, producer half): the Clean `Bool` value shapes are spelled in
//! TrustIR's ONE boolean vocabulary.
//!
//! * `Bool.not b`  -> `bxor bool %b, true`
//! * `a && b`      -> `band bool %a, %b`
//! * `a || b`      -> `bor bool %a, %b`
//!
//! THE HOLE. The producer used to spell negation `UnOp::Not` at scalar `bool`.
//! The trust-ir validator's `not` rule admits integer / integer-vector /
//! bool-vector only, so the join seam's per-function validation refused the
//! emitted body (`BinOpRequiresInteger { op: "not", ty: "bool" }`; since WS2.21,
//! `UnOpNotOnScalarBool`), the row was
//! SKIPPED, and `neg` reached the module as a body-less declaration the
//! reference interpreter trapped at. The connectives were spelled with the
//! INTEGER `And`/`Or`, which validate at scalar `bool` only as the second
//! spelling trust-ir's `B*` ops (4b069189) exist to remove.
//!
//! Every function here comes from REAL Clean source through a real island
//! session, planned and emitted by the production entry points. The probe is
//! the proof program's `p12b_lean_bool_connective`
//! (`reports/2026-09-17-two-language-proof-program/parta/probes/`), whose
//! `program()` is `neg(false) + 2*conj(true,true) + 4*disj(false,false) == 3`.
//!
//! KERNEL-TV, MEASURED (not assumed), re-measured 2026-09-28: the MINT's
//! denotation copy (`clean_reflect::denote_function`, the compiler's) has no
//! `bool` carrier and no `B*` rule, so these rows stay tier `structural` (the
//! compiler's mint pre-filter records a disclosed skip). The RE-CHECKER's copy
//! (trust-ir-build's `clean_backend_tv`) moved ahead of it at the current
//! trust-ir pin: it denotes `Bool` and `band`/`bor`/`bxor`, so a TV certificate
//! over one of these rows is judged on its payload, and one that proves
//! nothing is REFUSED — never a pass. The last test pins both halves.

use clean_kernel::{BinderInfo, Environment, Expr};
use trust_clean_ir::{emit_clean_origin_function, trust_ir_func_ty};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::inst::{BinOp, Inst, UnOp};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::node::InstrNode;
use trust_ir::proof::{
    CleanCicKernelRecheck, KERNEL_ANCHOR_CLEAN_BACKEND_TV, ObligationKind, ProofCertificate,
    ProofEvidence, ProofObligation, ProofStatus, clean_cic_lineage_digest, encode_clean_expr_v1,
};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ProofId, ValueId};
use trust_ir::{Block, CallingConv, Constant, Function, Module, Producer};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

const NEG: &str = "def neg (b : Bool) : Bool := not b";
const CONJ: &str = "def conj (a : Bool) (b : Bool) : Bool := a && b";
const DISJ: &str = "def disj (a : Bool) (b : Bool) : Bool := a || b";

fn env_with(decls: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(decls);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// Plan + emit one declaration at `(id, ty)`, returning the function and its
/// interned signature.
fn emit_at(
    env: &Environment,
    name: &str,
    id: FuncId,
    ty: FuncTyId,
) -> (Function, trust_ir::ty::FuncTy) {
    let plan = plan_clean_origin_body(env, name).expect("the Bool value shape must plan");
    let sig = trust_ir_func_ty(plan.signature()).expect("`Bool` has a TrustIR carrier");
    let f = emit_clean_origin_function(&plan, id, ty).expect("the Bool value shape must emit");
    (f, sig)
}

fn emit_one(decl: &str, name: &str) -> (Function, trust_ir::ty::FuncTy) {
    emit_at(&env_with(&[decl]), name, FuncId::new(0), FuncTyId::new(0))
}

/// The join seam's own rule (`validate_standalone`): the emitted function in a
/// one-function mini-module carrying only its signature.
fn mini_module(function: &Function, sig: &trust_ir::ty::FuncTy) -> Module {
    let mut mini = Module::new(format!("clean-origin-validate::{}", function.name));
    mini.func_types.push(sig.clone());
    let mut f = function.clone();
    f.id = FuncId::new(0);
    f.ty = FuncTyId::new(0);
    mini.functions.push(f);
    mini
}

fn run_bool(f: &Function, args: &[bool]) -> bool {
    let outcome = Interpreter::new()
        .execute_function(f, args.iter().map(|b| InterpretValue::bool(*b)))
        .unwrap_or_else(|e| panic!("the emitted TrustIR must execute: {e:?}"));
    assert_eq!(outcome.returns.len(), 1, "a Bool value function returns one value");
    outcome.returns[0].as_bool().expect("a `bool` result")
}

fn node(inst: Inst, results: Vec<ValueId>) -> InstrNode {
    InstrNode { inst, results, proofs: Vec::new(), span: None, proof_context: None, scope: None }
}

// ── positive ─────────────────────────────────────────────────────────────

/// `neg` is spelled `bxor %b, true`, publishes under the join seam's
/// per-function validation, and executes to `not b` at both inputs.
#[test]
fn neg_publishes_as_bxor_true_validates_and_executes() {
    let (f, sig) = emit_one(NEG, "neg");
    let body = &f.blocks[0].body;
    match &body[..] {
        [
            InstrNode {
                inst: Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) },
                results: t,
                ..
            },
            InstrNode {
                inst: Inst::BinOp { op: BinOp::BXor, ty: Ty::Bool, lhs, rhs },
                results: out,
                ..
            },
            InstrNode { inst: Inst::Return { values }, .. },
        ] => {
            assert_eq!(*lhs, ValueId::new(0), "the operand is the parameter");
            assert_eq!(rhs, &t[0], "xor'd against the `true` constant");
            assert_eq!(values, out, "and the xor is what is returned");
        }
        other => panic!("`not b` must be `bxor %b, true`; got {other:#?}"),
    }
    assert!(
        !body.iter().any(|n| matches!(n.inst, Inst::UnOp { op: UnOp::Not, .. })),
        "no scalar `not` may survive"
    );
    let errors = validate_module(&mini_module(&f, &sig));
    assert!(errors.is_empty(), "`neg` must publish (validate): {errors:#?}");
    assert!(run_bool(&f, &[false]), "neg(false) == true");
    assert!(!run_bool(&f, &[true]), "neg(true) == false");
}

/// `&&` / `||` are spelled with the BOOLEAN connectives `band` / `bor`, not the
/// overloaded integer `and` / `or`, and each validates and computes its full
/// truth table.
#[test]
fn connectives_validate_as_band_and_bor() {
    for (decl, name, want, table) in [
        (CONJ, "conj", BinOp::BAnd, [false, false, false, true]),
        (DISJ, "disj", BinOp::BOr, [false, true, true, true]),
    ] {
        let (f, sig) = emit_one(decl, name);
        match &f.blocks[0].body[..] {
            [
                InstrNode { inst: Inst::BinOp { op, ty: Ty::Bool, lhs, rhs }, .. },
                InstrNode { inst: Inst::Return { .. }, .. },
            ] => {
                assert_eq!(*op, want, "{name}: the Bool connective, not the integer op");
                assert_eq!(
                    (*lhs, *rhs),
                    (ValueId::new(0), ValueId::new(1)),
                    "{name}: operand order"
                );
            }
            other => panic!("{name}: expected one connective + return, got {other:#?}"),
        }
        let errors = validate_module(&mini_module(&f, &sig));
        assert!(errors.is_empty(), "{name} must validate: {errors:#?}");
        for (i, (a, b)) in
            [(false, false), (false, true), (true, false), (true, true)].into_iter().enumerate()
        {
            assert_eq!(run_bool(&f, &[a, b]), table[i], "{name}({a},{b})");
        }
    }
}

// ── adversarial shapes (batch review) ───────────────────────────────────

/// Negation of a parameter that is NOT the first one. The respell mints a `true`
/// constant, so its id must come from above EVERY parameter (`%2` here, never `%0`/`%1`),
/// and the xor must read `%1` — a mix-up of the two is well-typed at `bool` and would
/// validate, so only the operand ids and the full truth table can catch it.
#[test]
fn negating_the_second_parameter_reads_it_and_mints_the_constant_above_both() {
    let (f, sig) = emit_one("def negSnd (a : Bool) (b : Bool) : Bool := not b", "negSnd");
    match &f.blocks[0].body[..] {
        [
            InstrNode {
                inst: Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) },
                results: t,
                ..
            },
            InstrNode { inst: Inst::BinOp { op: BinOp::BXor, ty: Ty::Bool, lhs, rhs }, .. },
            InstrNode { inst: Inst::Return { .. }, .. },
        ] => {
            assert_eq!(t[0], ValueId::new(2), "the constant is minted above both parameters");
            assert_eq!(*lhs, ValueId::new(1), "the negated operand is the SECOND parameter");
            assert_eq!(*rhs, t[0], "xor'd against the `true` constant");
        }
        other => panic!("`not b` must be `bxor %1, true`; got {other:#?}"),
    }
    assert!(validate_module(&mini_module(&f, &sig)).is_empty(), "negSnd must validate");
    for a in [false, true] {
        for b in [false, true] {
            assert_eq!(run_bool(&f, &[a, b]), !b, "negSnd({a},{b}) == not {b}");
        }
    }
}

/// Operand order is preserved even where it cannot change the value: `b && a` is
/// `band %1, %0`, so an emitter that re-sorted operands (harmless for the commutative
/// connectives, fatal the day a non-commutative Bool op joins the table) shows here.
#[test]
fn reversed_connective_operands_are_emitted_in_source_order() {
    for (decl, name, want, table) in [
        (
            "def conjRev (a : Bool) (b : Bool) : Bool := b && a",
            "conjRev",
            BinOp::BAnd,
            [false, false, false, true],
        ),
        (
            "def disjRev (a : Bool) (b : Bool) : Bool := b || a",
            "disjRev",
            BinOp::BOr,
            [false, true, true, true],
        ),
    ] {
        let (f, sig) = emit_one(decl, name);
        match &f.blocks[0].body[..] {
            [
                InstrNode { inst: Inst::BinOp { op, ty: Ty::Bool, lhs, rhs }, .. },
                InstrNode { inst: Inst::Return { .. }, .. },
            ] => {
                assert_eq!(*op, want, "{name}");
                assert_eq!((*lhs, *rhs), (ValueId::new(1), ValueId::new(0)), "{name}: b, then a");
            }
            other => panic!("{name}: expected one connective + return, got {other:#?}"),
        }
        assert!(validate_module(&mini_module(&f, &sig)).is_empty(), "{name} must validate");
        for (i, (a, b)) in
            [(false, false), (false, true), (true, false), (true, true)].into_iter().enumerate()
        {
            assert_eq!(run_bool(&f, &[a, b]), table[i], "{name}({a},{b})");
        }
    }
}

/// A connective whose two operands are the SAME parameter: `band %0, %0` / `bor %0, %0`
/// (the identity), never a spelling that silently reads a second, nonexistent operand.
#[test]
fn a_connective_over_one_parameter_twice_is_the_identity() {
    for (decl, name, want) in [
        ("def andSelf (a : Bool) : Bool := a && a", "andSelf", BinOp::BAnd),
        ("def orSelf (a : Bool) : Bool := a || a", "orSelf", BinOp::BOr),
    ] {
        let (f, sig) = emit_one(decl, name);
        match &f.blocks[0].body[..] {
            [
                InstrNode { inst: Inst::BinOp { op, ty: Ty::Bool, lhs, rhs }, .. },
                InstrNode { inst: Inst::Return { .. }, .. },
            ] => {
                assert_eq!(*op, want, "{name}");
                assert_eq!((*lhs, *rhs), (ValueId::new(0), ValueId::new(0)), "{name}");
            }
            other => panic!("{name}: expected one connective + return, got {other:#?}"),
        }
        assert!(validate_module(&mini_module(&f, &sig)).is_empty(), "{name} must validate");
        for a in [false, true] {
            assert_eq!(run_bool(&f, &[a]), a, "{name}({a}) is the identity");
        }
    }
}

// ── the proof program's GAP rows, ported ────────────────────────────────

/// Assemble the `p12b` probe as ONE module: the three Clean bodies at the
/// declared ids, plus a `program` that computes the probe's expression.
fn p12b_module() -> (Module, FuncId) {
    let env = env_with(&[NEG, CONJ, DISJ]);
    let mut mb = ModuleBuilder::new("p12b_lean_bool_connective");
    let ft_un = mb.add_func_type(vec![Ty::Bool], vec![Ty::Bool]);
    let ft_bin = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    let ft_prog = mb.add_func_type(vec![], vec![Ty::U64]);
    let neg = mb.declare_function("neg", ft_un);
    let conj = mb.declare_function("conj", ft_bin);
    let disj = mb.declare_function("disj", ft_bin);

    let mut fb = mb.function("program", ft_prog);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let t = fb.const_value(Ty::Bool, Constant::Bool(true));
    let n = fb.call(neg, vec![f]);
    let c = fb.call(conj, vec![t, t]);
    let d = fb.call(disj, vec![f, f]);
    let n = fb.zext(Ty::Bool, Ty::U64, n);
    let c = fb.zext(Ty::Bool, Ty::U64, c);
    let d = fb.zext(Ty::Bool, Ty::U64, d);
    let two = fb.uconst(Ty::U64, 2);
    let four = fb.uconst(Ty::U64, 4);
    let c2 = fb.mul(Ty::U64, c, two);
    let d4 = fb.mul(Ty::U64, d, four);
    let s = fb.add(Ty::U64, n, c2);
    let s = fb.add(Ty::U64, s, d4);
    fb.ret(vec![s]);
    let program = fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // The probe's `program` is a Rust fn calling Rust-ABI Clean-origin items;
    // a ccc -> rustcc edge would need target info this probe does not model.
    let slot = module.functions.iter().position(|g| g.id == program).expect("built");
    module.functions[slot].calling_conv = CallingConv::Rust;

    for (name, id, ty) in [("neg", neg, ft_un), ("conj", conj, ft_bin), ("disj", disj, ft_bin)] {
        let (mut emitted, sig) = emit_at(&env, name, id, ty);
        // Exactly as `append_clean_origin` stamps it at the join seam.
        emitted.producer = Some(Producer::Clean);
        assert_eq!(module.func_types[ty.index() as usize], sig, "{name}: the interned signature");
        let slot = module.functions.iter().position(|g| g.id == id).expect("declared");
        module.functions[slot] = emitted;
    }
    (module, program)
}

/// Row `a.lean.bool_connective.carried`: all three Clean defs arrive as
/// `Producer::Clean` BODIES that pass the join seam's per-function validation
/// — none is skipped to a body-less declaration (the pre-WS5.13 `neg`).
#[test]
fn a_lean_bool_connective_carried() {
    let (module, _) = p12b_module();
    for name in ["neg", "conj", "disj"] {
        let f = module.functions.iter().find(|f| f.name == name).expect("present");
        assert!(!f.blocks.is_empty(), "{name}: carried as a BODY, not a declaration");
        let sig = &module.func_types[f.ty.index() as usize];
        let errors = validate_module(&mini_module(f, sig));
        assert!(errors.is_empty(), "{name}: per-function validation must admit it: {errors:#?}");
    }
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "the whole probe module validates: {errors:#?}");
}

/// Row `a.lean.bool_connective.exec`: the probe's `program()` executes in the
/// reference interpreter to the native answer, 3 (it trapped at `@neg` before).
#[test]
fn a_lean_bool_connective_exec() {
    let (module, program) = p12b_module();
    let outcome = Interpreter::with_module(&module)
        .execute_func(program, [])
        .unwrap_or_else(|e| panic!("program() must execute (native = 3): {e:?}"));
    let got = outcome.returns[0].as_int().expect("a u64 result").as_unsigned();
    assert_eq!(got, 3, "neg(false) + 2*conj(true,true) + 4*disj(false,false) == 3 == native");
}

// ── negative twin ───────────────────────────────────────────────────────

/// `not` on a Bool VECTOR is unchanged: still admitted by the validator. The
/// respell is about scalar `bool` only; this twin fails if the fix were made
/// by narrowing the vector rule instead.
#[test]
fn not_on_a_bool_vector_is_unchanged() {
    let v = Ty::Vector(Box::new(Ty::Bool), 4);
    let mut module = Module::new("bool_vector_not");
    module.func_types.push(trust_ir::ty::FuncTy {
        params: vec![v.clone()],
        returns: vec![v.clone()],
        is_vararg: false,
        abi: None,
    });
    let mut f = Function::new(FuncId::new(0), "vnot", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(ValueId::new(0), v.clone())];
    block.body.push(node(
        Inst::UnOp { op: UnOp::Not, ty: v, operand: ValueId::new(0) },
        vec![ValueId::new(1)],
    ));
    block.body.push(node(Inst::Return { values: vec![ValueId::new(1)] }, vec![]));
    f.blocks.push(block);
    module.functions.push(f);
    let errors = validate_module(&module);
    assert!(errors.is_empty(), "`not` on <4 x bool> must stay admitted: {errors:#?}");
}

// ── mutation controls ───────────────────────────────────────────────────

/// Re-emitting the OLD spelling (`UnOp::Not` at scalar `bool`) is refused, BY
/// NAME. Before WS2.21 the name was the generic `BinOpRequiresInteger { op:
/// "not", ty: "bool" }`; since the trust-ir pin of train T8 (5dbbf177) it is
/// `UnOpNotOnScalarBool`, the refusal's OWN name, and the generic one is no
/// longer reported for this shape.
#[test]
fn reemitting_scalar_unop_not_is_refused_by_name() {
    let (mut f, sig) = emit_one(NEG, "neg");
    let block = &mut f.blocks[0];
    block.body = vec![
        node(
            Inst::UnOp { op: UnOp::Not, ty: Ty::Bool, operand: ValueId::new(0) },
            vec![ValueId::new(1)],
        ),
        node(Inst::Return { values: vec![ValueId::new(1)] }, vec![]),
    ];
    let errors = validate_module(&mini_module(&f, &sig));
    assert!(
        errors.iter().any(|e| matches!(e, ValidationError::UnOpNotOnScalarBool { block: 0 })),
        "scalar `not` must be refused as UnOpNotOnScalarBool in block 0: {errors:#?}"
    );
    assert!(
        !errors.iter().any(|e| matches!(
            e,
            ValidationError::BinOpRequiresInteger { op, .. } if op == "not"
        )),
        "scalar `not` is refused by its own name, not the generic integer rule: {errors:#?}"
    );
}

/// The emitted negation with its constant flipped to `false`.
fn neg_with_false_constant() -> (Function, trust_ir::ty::FuncTy) {
    let (mut f, sig) = emit_one(NEG, "neg");
    let mut flipped = 0;
    for n in &mut f.blocks[0].body {
        if let Inst::Const { ty: Ty::Bool, value } = &mut n.inst {
            *value = Constant::Bool(false);
            flipped += 1;
        }
    }
    assert_eq!(flipped, 1, "the respell carries exactly one `true` constant");
    (f, sig)
}

/// `bxor %b, false` is the identity, not negation. It is structurally
/// well-formed (the validator is a typing check and says so) — which is
/// exactly why the constant is pinned by the shape test above AND caught here
/// by execution against Clean's meaning of `not b`.
#[test]
fn bxor_false_mutation_computes_the_identity_and_is_caught() {
    let (f, sig) = neg_with_false_constant();
    assert!(validate_module(&mini_module(&f, &sig)).is_empty(), "typing alone cannot see it");
    for b in [false, true] {
        let got = run_bool(&f, &[b]);
        assert_ne!(got, !b, "the mutant must DISAGREE with `not {b}` — it is the identity");
        assert_eq!(got, b);
    }
}

/// Validate `function` in a mini-module carrying ONE `Certified` kernel-TV
/// certificate whose comparand is `fun (b : <binder>) => b` and whose proof term
/// is that same lambda — a well-formed payload that proves nothing — and return
/// every `CertifiedCleanCicKernelRecheckFailed` reason.
fn tv_recheck_refusals(f: &Function, sig: &trust_ir::ty::FuncTy, binder: &str) -> Vec<String> {
    let mut module = mini_module(f, sig);
    let payload = Expr::lam(BinderInfo::Default, Expr::const_str(binder), Expr::bvar(0));
    let encoded = encode_clean_expr_v1(&payload).expect("encodes");
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::TranslationValidation,
        ProofStatus::Certified,
        "clean-origin kernel-tv: 'neg' denotes its Clean definition".to_string(),
    )
    .with_function(FuncId::new(0));
    let lineage = clean_cic_lineage_digest(&obligation);
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "trustc.clean-origin-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term: encoded.clone(),
            context: encoded,
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "CleanCompiler.BackendTV".to_string(),
                theorems: vec!["CleanTV.neg.denotes".to_string()],
                anchor: KERNEL_ANCHOR_CLEAN_BACKEND_TV.to_string(),
                allowed_axioms: Vec::new(),
                // UNBOUND (the default lanes' meaning since WS1.12a).
                binding: None,
            }),
        },
        assurance: None,
    });
    validate_module(&module)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. } => Some(reason),
            _ => None,
        })
        .collect()
}

/// Neither the respelled `neg` nor its `bxor false` mutant is CERTIFIED by a
/// payload that does not prove it — and the refusal comes from where the
/// current pin puts it.
///
/// MEASURED 2026-09-28 at the trust-ir pin this branch carries: the
/// re-checker's side has MOVED since WS5.13 was written. `clean_backend_tv`
/// now admits `Bool` and denotes `band`/`bor`/`bxor` as
/// `Bool.and`/`Bool.or`/`Bool.xor` (its S1 slice), so a bool row is no longer
/// refused "outside the TV fragment" before the payload is read; it is
/// RE-DERIVED, and the certificate is judged against it. The old assertion
/// (that refusal text) failed there, which is what this rewrite answers. What
/// keeps these rows `structural` is the MINT (`clean_reflect::denote_function`,
/// the compiler's copy, still refuses a `bool` return) — the compiler's
/// pre-filter text says so — and what keeps a forged certificate from passing is
/// the judgment this test pins, in two classes:
///
/// * a comparand whose binder is NOT `Bool` is refused at the binder-sort check —
///   a check the re-checker reaches only AFTER it denoted the row at sort `Bool`;
/// * a comparand of the RIGHT sort with a proof term that proves nothing is
///   refused by the kernel judgment itself, past both earlier checks.
#[test]
fn kernel_tv_recheck_denotes_bool_rows_and_refuses_a_payload_that_proves_nothing() {
    for (label, (f, sig)) in
        [("bxor-true", emit_one(NEG, "neg")), ("bxor-false mutant", neg_with_false_constant())]
    {
        let missorted = tv_recheck_refusals(&f, &sig, "Nat");
        assert!(
            missorted.iter().any(|reason| reason.contains(
                "comparand param binder 0 is not `Bool`-typed (the re-derived param sort is Bool)"
            )),
            "{label}: a `Nat`-binder comparand must be refused at the binder-sort check, which \
             the re-checker reaches only after denoting the row at sort Bool: {missorted:#?}"
        );
        assert!(
            missorted.iter().all(|reason| !reason.contains("outside the TV fragment")),
            "{label}: the re-checker denotes `bool` rows at this pin; a fragment refusal means \
             the pin moved back and the compiler's pre-filter text is wrong again: {missorted:#?}"
        );

        let unproved = tv_recheck_refusals(&f, &sig, "Bool");
        assert!(
            !unproved.is_empty(),
            "{label}: a `Bool`-binder comparand with a proof term that proves nothing was \
             CERTIFIED — a forged kernel-TV certificate passed"
        );
        assert!(
            unproved.iter().all(|reason| !reason.contains("outside the TV fragment")
                && !reason.contains("comparand param binder")),
            "{label}: the refusal must come from the kernel judgment, past the fragment and \
             binder-sort checks: {unproved:#?}"
        );
        assert!(
            unproved.iter().any(|reason| reason.contains(
                "in-process kernel REJECTED the translation-validation equation for 'neg'"
            )),
            "{label}: the kernel judgment itself must be what refuses it, by name: {unproved:#?}"
        );
    }
}
