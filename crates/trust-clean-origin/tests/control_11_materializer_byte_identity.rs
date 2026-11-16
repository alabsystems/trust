// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 11 — THE MATERIALIZER'S BYTE-IDENTITY ACCEPTANCE** (§6f landing 4).
//!
//! Landings 1, 2 and 3 each deferred the emitter half of §6f with the same
//! recorded reason: collapsing the hand-written builders (six when landing 1
//! wrote it, NINE by the time they were deleted) *"cannot be
//! validated on the fast lane"*, and *"a landing that cannot run x.py must not
//! restructure the code that emits binaries."* This file is what makes the
//! validation available on the fast lane, and therefore what retires that
//! deferral.
//!
//! # THE ACCEPTANCE, stated exactly
//!
//! For every shape the nine builders emitted, the ONE table-driven body builder
//! ([`trust_clean_origin::materialize::body_template`]) must describe the
//! **IDENTICAL** body — not an equivalent one, not a tidier one. The emitter is
//! the WRONG-BINARY side: a materializer that emits subtly different MIR is
//! exactly the failure the gate exists to catch, and the gate refuses AFTER the
//! fact and only for bodies that reach it. So identity is proved here, BEFORE.
//!
//! Two layers, because one is not enough on its own:
//!
//! 1. **The RENDERED body.** [`render`] turns a template into the `trust_types`
//!    MIR vocabulary `trust_mir_extract::extract_function` produces, and each
//!    half compares it against the body measured off the SHIPPED builder in
//!    `control_5`..`control_10` — block order, local numbering (including the
//!    locals R1/R2 leave DECLARED AND DEAD), `Copy` versus `Move` in every
//!    position, `SwitchInt` polarity, the per-call unwind edge, and the callee
//!    paths the extractor actually renders.
//! 2. **The TEMPLATE fields the extractor cannot see.** `WithRetag::Yes`,
//!    `LocalDecl::immutable()` and the carrier POSITION each local is typed at
//!    survive no round trip through `VerifiableFunction`, so a control that
//!    only compared rendered bodies would be blind to them. [`half_8`] and
//!    [`half_10`] assert them on the template directly.
//!
//! Then, for every shape whose environment is reachable on this lane, the
//! rendered body goes through the REAL `admit_lowering` — side B's independent
//! reader, side B's producer and the kernel gate. A template that drifted is
//! therefore refused in two seconds rather than in a binary.
//!
//! # WHAT THIS FILE DOES **NOT** COVER — read before quoting it
//!
//! [`render`] is a TEST-SIDE renderer. It is not the materializer; the
//! materializer lives in `compiler/rustc_mir_transform/src/clean_origin_mir.rs`
//! because it needs a `TyCtxt`, is x.py-only, and ships unverified by any build
//! exactly as every `compiler/` edit in landings 1–3 did. What this file
//! establishes is that **the DESCRIPTION is byte-identical to what the nine
//! builders emitted**; what remains unvalidated on this lane is the ~175-line
//! translation from that description into `mir::Body`, which carries no shape
//! knowledge and one arm per template variant.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! Same standing prohibition as control_3..control_10. `trust_types::
//! admissible_body` and `trust_spec_elab::admit_*_function` are frozen against
//! this lane. If a rendered template ever fails to admit, the defect is in the
//! template or the gate — never in side B.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::materialize::{
    BodyTemplate, TemplateCallee, TemplateOperand, TemplateRefusal, TemplateRvalue,
    TemplateTerminator, TemplateTy, TemplateUnwind, body_template, zero_test_rec_template,
};
use trust_clean_origin::table::{MirShape, UnwindDiscipline, ladder_row, row};
use trust_clean_origin::{
    CleanOriginPlan, CleanOriginShape, admit_lowering, plan_clean_origin_body,
};
use trust_types::admissible_body::{
    ArithBinOp, ArithExpr, ArithOperand, PrimitiveCallee, RecBodyExpr, SelectCmp,
    recognize_structural_rec,
};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, UnOp, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════ THE TEST-SIDE REFERENCE RENDERER ══════════════════

/// What a template needs to become a `VerifiableFunction`: the three `TyCtxt`
/// facts the real materializer resolves, supplied here as data.
struct Rendering {
    name: &'static str,
    def_path: &'static str,
    result_ty: Ty,
    param_tys: Vec<Ty>,
}

impl Rendering {
    fn machine(name: &'static str, bits: u32, arity: usize) -> Self {
        let ty = Ty::Int { width: bits, signed: false };
        Self {
            name,
            def_path: "crate::m::probe",
            result_ty: ty.clone(),
            param_tys: vec![ty; arity],
        }
    }
}

/// The def path the extractor renders for a resolved primitive.
///
/// **This mirrors SIDE B's measured table, and it is TEST-SIDE for exactly that
/// reason.** `resolve_bignum_method`'s standing note — *"Do NOT mirror side B's
/// table here: side A asserting what side B will accept is exactly the
/// independence the gate exists to have"* — governs the EMITTER, which hands
/// over a `DefId` and never a path. A control is where the two renderings are
/// allowed to meet, and `control_7`/`control_8` already carry these strings for
/// the same reason: rustc's inherent-impl printer emits `Type::method` when the
/// `impl` sits in the type's own module and `module::<impl Type>::method` when
/// it does not, so `is_zero`/`from_u64` render co-located out of trust-bignum's
/// root while `sub`/`add` render module-qualified out of `mod arith`.
fn extracted_callee_path(callee: PrimitiveCallee) -> String {
    match callee {
        PrimitiveCallee::NatSub => "trust_bignum::arith::<impl trust_bignum::Nat>::sub".to_owned(),
        PrimitiveCallee::NatAdd => "trust_bignum::arith::<impl trust_bignum::Nat>::add".to_owned(),
        // The wrapping primitives and the two root-module bignum methods render
        // exactly as the ONE identity spells them.
        other => other.canonical_path(),
    }
}

fn render_operand(operand: TemplateOperand) -> Operand {
    match operand {
        TemplateOperand::Copy(local) => Operand::Copy(Place::local(local)),
        TemplateOperand::Move(local) => Operand::Move(Place::local(local)),
        TemplateOperand::ResultScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::U64Scalar(value) => {
            Operand::Constant(ConstValue::Uint(u128::from(value), 64))
        }
        // §6f landing 6. The extractor turns a `bool`-typed MIR constant into
        // `ConstValue::Bool` (`convert_const_operand`'s `TyKind::Bool` arm,
        // through `try_to_bool`), never into a one-byte `Uint` — which is why
        // the emitter spells it `Scalar::from_bool` and side B matches a
        // boolean rather than an integer it would have to interpret.
        TemplateOperand::UIntScalar { value, width } => {
            Operand::Constant(ConstValue::Uint(value, width))
        }
        TemplateOperand::BoolScalar(value) => Operand::Constant(ConstValue::Bool(value)),
    }
}

fn render_binop(cmp: SelectCmp) -> BinOp {
    match cmp {
        SelectCmp::Lt => BinOp::Lt,
        SelectCmp::Le => BinOp::Le,
        SelectCmp::Eq => BinOp::Eq,
    }
}

/// Turn a template into the body the extractor hands the recognizer.
fn render(template: &BodyTemplate, rendering: &Rendering) -> VerifiableFunction {
    let local_ty = |ty: TemplateTy| match ty {
        TemplateTy::Result => rendering.result_ty.clone(),
        TemplateTy::Param { index } => rendering.param_tys[index].clone(),
        TemplateTy::Bool => Ty::Bool,
        TemplateTy::RustCalleeResult { .. } => {
            panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement")
        }
        TemplateTy::ResultRef => {
            Ty::Ref { mutable: false, inner: Box::new(rendering.result_ty.clone()) }
        }
    };
    let locals = template
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| LocalDecl { index, ty: local_ty(local.ty), name: None })
        .collect();
    let blocks = template
        .blocks
        .iter()
        .enumerate()
        .map(|(index, block)| BasicBlock {
            id: BlockId(index),
            stmts: block
                .stmts
                .iter()
                .map(|stmt| Statement::Assign {
                    place: Place::local(stmt.place),
                    rvalue: match stmt.rvalue {
                        TemplateRvalue::Use(operand) => Rvalue::Use(render_operand(operand)),
                        TemplateRvalue::Compare { cmp, left, right } => Rvalue::BinaryOp(
                            render_binop(cmp),
                            render_operand(left),
                            render_operand(right),
                        ),
                        // §6f landing 7: the raw binary operator at the result
                        // carrier. Unreachable from the nine pre-landing-4
                        // shapes this control compares byte for byte — none of
                        // them realizes one — and present because the match is
                        // wildcard-free by design.
                        TemplateRvalue::RawBin { op, left, right } => Rvalue::BinaryOp(
                            op.mir_binop(),
                            render_operand(left),
                            render_operand(right),
                        ),
                        TemplateRvalue::SharedRef(of) => {
                            Rvalue::Ref { mutable: false, place: Place::local(of) }
                        }
                        // W6 (Rust-calls-Clean): boolean negation.
                        TemplateRvalue::BoolNot(op) => {
                            Rvalue::UnaryOp(UnOp::Not, render_operand(op))
                        }
                    },
                    span: SourceSpan::default(),
                })
                .collect(),
            terminator: match &block.terminator {
                TemplateTerminator::Return => Terminator::Return,
                TemplateTerminator::Goto(target) => Terminator::Goto(BlockId(*target)),
                TemplateTerminator::SwitchIntZero { discr, zero, otherwise } => {
                    Terminator::SwitchInt {
                        discr: render_operand(*discr),
                        targets: vec![(0, BlockId(*zero))],
                        otherwise: BlockId(*otherwise),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    }
                }
                TemplateTerminator::Call { callee, args, dest, target, unwind } => {
                    Terminator::Call {
                        func: match callee {
                            TemplateCallee::Primitive(identity) => extracted_callee_path(*identity),
                            TemplateCallee::RustFn { .. } => panic!("W5: this probe plans no Rust-call chain; control_23 is that lane's measurement"),
                            TemplateCallee::SelfDef => rendering.def_path.to_owned(),
                        },
                        args: args.iter().map(|arg| render_operand(*arg)).collect(),
                        dest: Place::local(*dest),
                        target: Some(BlockId(*target)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        unwind: match unwind {
                            TemplateUnwind::Unreachable => UnwindEdge::Unreachable,
                            TemplateUnwind::Continue => UnwindEdge::Continue,
                        },
                        callee_identity: None,
                        callee_key: None,
                    }
                }
            },
        })
        .collect();
    VerifiableFunction {
        name: rendering.name.into(),
        def_path: rendering.def_path.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: template.arg_count,
            return_ty: rendering.result_ty.clone(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// **THE COMPARISON.** `VerifiableFunction` and everything under it derive
/// `Debug` but not `PartialEq` (and `trust-types` is not this landing's to
/// change), so identity is taken on the pretty-printed structure — which is the
/// STRICTER comparison anyway: it sees every field of every local, statement,
/// operand and terminator, including the ones a hand-written `PartialEq` would
/// be free to skip, and it prints the disagreement rather than a bare `false`.
fn body_picture(func: &VerifiableFunction) -> String {
    format!(
        "name = {}\ndef_path = {}\narg_count = {}\nreturn_ty = {:?}\nlocals = {:#?}\n\
         blocks = {:#?}\n",
        func.name,
        func.def_path,
        func.body.arg_count,
        func.body.return_ty,
        func.body.locals,
        func.body.blocks,
    )
}

/// Assert byte identity between a rendered template and the body a shipped
/// builder was MEASURED to produce.
fn assert_identical(rendered: &VerifiableFunction, expected: &VerifiableFunction, what: &str) {
    assert_eq!(
        body_picture(rendered),
        body_picture(expected),
        "{what}: the template does not describe the body the shipped builder emitted. A \
         materializer that emits subtly different MIR is the wrong-binary failure the gate \
         exists to catch, and the gate refuses AFTER the fact. Do NOT fix this by editing \
         side B's producers."
    );
}

/// Plan `name` and build its template through the ladder row the emitter
/// selects — the exact two steps `build_gated_body` takes.
fn template_for(env: &Environment, name: &str) -> (CleanOriginPlan, BodyTemplate) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    let selected = ladder_row(plan.shape()).expect("every ladder rung maps onto a row");
    let template = body_template(selected, &plan)
        .unwrap_or_else(|refusal| panic!("`{name}` must template: {refusal:?}"));
    (plan, template)
}

// ═══════════════════════════ side A environments ═══════════════════════════

/// The pipeline `clean_origin_mir` really drives — landing 3's method, and
/// `control_10`'s: a hand-built side A is a probe fiction, and R2/C9 paid for
/// that lesson once already.
fn island(source: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn nat() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

/// `def tozero (n : Nat) : Nat := Nat.rec 0 (fun k ih => ih) n` — the r3
/// EQUATION-FORM spelling `control_7` measures, hand-built because it is the
/// recursor spine the island's own elaborator produces.
fn env_with_tozero() -> Environment {
    let step =
        Expr::lam(BinderInfo::Default, nat(), Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)));
    let rec_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![Level::succ(Level::zero())]),
        [
            Expr::lam(BinderInfo::Default, nat(), nat()),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            step,
            Expr::bvar(0),
        ],
    );
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Definition {
        name: Name::from_string("tozero"),
        level_params: vec![],
        type_: Expr::arrow(nat(), nat()),
        value: Expr::lam(BinderInfo::Default, nat(), rec_app),
        is_reducible: true,
    })
    .expect("`tozero` must kernel-check as written");
    env
}

// ══════════════════ the shipped builders' measured emissions ═══════════════
//
// Every expectation below is the body the SHIPPED builder produced, restated
// from the control that measured it. Restated rather than imported, because
// re-pointing an existing control at this landing's producer would be exactly
// the co-authorship the whole file exists to avoid: a byte-identity claim
// checked against a picture this landing wrote is not a byte-identity claim.

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";
const WMUL: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_mul";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";

fn u64_locals(count: usize) -> Vec<LocalDecl> {
    (0..count).map(|index| LocalDecl { index, ty: Ty::u64(), name: None }).collect()
}

fn assign(place: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(place), rvalue, span: SourceSpan::default() }
}

fn vf(arg_count: usize, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `control_5`'s two-block call shape, and `control_6_composed`'s chain.
fn unreachable_call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Unreachable,
        callee_identity: None,
        callee_key: None,
    }
}

/// `control_7`/`control_8`'s bignum call: every call the recursion emitter
/// builds carries `UnwindAction::Continue`.
fn unwinding_call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    }
}

/// `control_6_select` / `control_7_select_literal` / `control_10`'s four-block
/// diamond, over two `u64` parameters.
fn expected_diamond(
    cmp: BinOp,
    cmp_right: Operand,
    then_arm: Operand,
    else_arm: Operand,
) -> VerifiableFunction {
    let mut locals = u64_locals(4);
    locals.push(LocalDecl { index: 4, ty: Ty::Bool, name: None });
    vf(
        2,
        locals,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    4,
                    Rvalue::BinaryOp(cmp, Operand::Copy(Place::local(1)), cmp_right),
                )],
                terminator: Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(4)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![assign(3, Rvalue::Use(then_arm))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![assign(3, Rvalue::Use(else_arm))],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
                stmts: vec![assign(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                terminator: Terminator::Return,
            },
        ],
    )
}

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_adt_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: nat_adt(), name: None }
}

fn nat_adt_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }, name: None }
}

fn nat_rendering(name: &'static str, def_path: &'static str) -> Rendering {
    Rendering { name, def_path, result_ty: nat_adt(), param_tys: vec![nat_adt()] }
}

// ═══════════════════════════════ the halves ════════════════════════════════

/// **HALF 0 — the projection.** `build_projection_body`: one block,
/// `_0 = move _{i+1}`, `return`, at any arity, with the parameters immutable.
/// Two ladder rungs share it; the InductiveProjection rung emits the same MIR
/// and differs only in how side A found it, which is what makes them one row.
#[test]
fn half_0_the_projection_template_is_the_shipped_projection_body() {
    let env = island("def fst (a : UInt64) (b : UInt64) : UInt64 := a");
    let (plan, template) = template_for(&env, "fst");
    assert_eq!(plan.shape(), &CleanOriginShape::Projection { projected: 0 });

    let expected = vf(
        2,
        u64_locals(3),
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(0, Rvalue::Use(Operand::Move(Place::local(1))))],
            terminator: Terminator::Return,
        }],
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(&rendered, &expected, "the projection");

    // …and through the REAL gate, not merely against a picture.
    admit_lowering(&env, &plan, &rendered).expect("the rendered projection must pass the gate");

    // The SECOND projection rung must produce the byte-identical template. It
    // cannot be planned from an island here (its side A is an induction proof),
    // so the identity is taken at the row + shape level, which is where it
    // lives: `ladder_row` maps both rungs onto `param`, and `body_template`
    // matches them in ONE arm.
    for projected in [0usize, 1] {
        let direct = body_template(
            row("param").expect("the projection row"),
            &plan_clean_origin_body(
                &island(&format!(
                    "def p{projected} (a : UInt64) (b : UInt64) : UInt64 := {}",
                    if projected == 0 { "a" } else { "b" }
                )),
                &format!("p{projected}"),
            )
            .expect("plan"),
        )
        .expect("template");
        assert_eq!(
            direct.blocks[0].stmts[0].rvalue,
            TemplateRvalue::Use(TemplateOperand::Move(projected + 1)),
            "the projected SOURCE parameter must land on local {} — the de Bruijn inversion \
             is the one-construct mistranslation this lane can make",
            projected + 1
        );
    }
}

/// **HALF 1 — the constant body.** `build_constant_body`: one block,
/// `_0 = const v_u{w}; return`, ARITY-AGNOSTIC. At arity 0 the body is one
/// local, which is the shape landing 2 added and the shape `control_9`
/// measures.
#[test]
fn half_1_the_constant_template_is_the_shipped_constant_body() {
    for (source, name, arity) in
        [("def six : UInt64 := 6", "six", 0usize), ("def k (a : UInt64) : UInt64 := 6", "k", 1)]
    {
        let env = island(source);
        let (plan, template) = template_for(&env, name);
        assert_eq!(plan.shape(), &CleanOriginShape::ConstantUint { value: 6 });

        let expected = vf(
            arity,
            u64_locals(arity + 1),
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(0, Rvalue::Use(Operand::Constant(ConstValue::Uint(6, 64))))],
                terminator: Terminator::Return,
            }],
        );
        let rendered = render(&template, &Rendering::machine("probe", 64, arity));
        assert_identical(&rendered, &expected, &format!("the constant body at arity {arity}"));
        admit_lowering(&env, &plan, &rendered)
            .unwrap_or_else(|e| panic!("the rendered constant at arity {arity} must admit: {e:?}"));
    }
}

/// **HALF 2 — the single wrapping op.** `build_wrapping_binop_body`:
/// `bb0: _0 = Call(u{w}::wrapping_{op}, [l, r]) -> bb1; bb1: Return`, operands
/// `Copy` (never `Move`: `a + a` names one local twice) and numerals inline.
///
/// This half also pins the landing's sharpest structural finding: the
/// one-step call chain IS the single binop, byte for byte, which is why two
/// builders became one skeleton rather than two arms of one function.
#[test]
fn half_2_the_wrapping_binop_template_is_the_shipped_two_block_call() {
    let env = island("def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b");
    let (plan, template) = template_for(&env, "wsum");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        }
    );

    let expected = vf(
        2,
        u64_locals(3),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: unreachable_call(
                    WADD,
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    0,
                    1,
                ),
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(&rendered, &expected, "the single wrapping op");
    admit_lowering(&env, &plan, &rendered).expect("the rendered binop must pass the gate");

    // A numeral operand is an inline scalar at the RESULT carrier's width —
    // never a promoted constant, which is what keeps `required_consts` honest.
    let env = island("def inc (a : UInt64) : UInt64 := a + 1");
    let (plan, template) = template_for(&env, "inc");
    let rendered = render(&template, &Rendering::machine("probe", 64, 1));
    assert_identical(
        &rendered,
        &vf(
            1,
            u64_locals(2),
            vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: Vec::new(),
                    terminator: unreachable_call(
                        WADD,
                        vec![
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(1, 64)),
                        ],
                        0,
                        1,
                    ),
                },
                BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
            ],
        ),
        "the single wrapping op with a NUMERAL operand",
    );
    admit_lowering(&env, &plan, &rendered).expect("the rendered numeral binop must admit");
}

/// **HALF 3 — the composed tree.** `build_composed_body`: one `Call` per node
/// in POST-ORDER, each non-root writing a fresh temporary at `arg_count+1+k`,
/// the root writing `_0`, then `Return`. For `fun a b => (a + b) * a`:
///
/// ```text
/// bb0: _3 = Call(wrapping_add, [copy _1, copy _2]) -> bb1
/// bb1: _0 = Call(wrapping_mul, [copy _3, copy _1]) -> bb2
/// bb2: Return
/// ```
#[test]
fn half_3_the_composed_template_is_the_shipped_post_order_chain() {
    let env = island("def wmix (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a");
    let (plan, template) = template_for(&env, "wmix");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::Composed {
            expr: ArithExpr::Bin {
                op: ArithBinOp::Mul,
                left: Box::new(ArithExpr::Bin {
                    op: ArithBinOp::Add,
                    left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                    right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
                }),
                right: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
            },
        }
    );

    let expected = vf(
        2,
        u64_locals(4),
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: unreachable_call(
                    WADD,
                    vec![Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2))],
                    3,
                    1,
                ),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: Vec::new(),
                terminator: unreachable_call(
                    WMUL,
                    vec![Operand::Copy(Place::local(3)), Operand::Copy(Place::local(1))],
                    0,
                    2,
                ),
            },
            BasicBlock { id: BlockId(2), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(&rendered, &expected, "the composed post-order chain");
    admit_lowering(&env, &plan, &rendered).expect("the rendered chain must pass the gate");
}

/// **HALF 4 — the three select rungs, ONE diamond.** `build_select_body`,
/// `build_select_literal_body` and `build_select_operands_body` differed in
/// nothing but which of three operand vocabularies filled four positions. Each
/// is compared against the diamond its own control measured.
#[test]
fn half_4_the_three_select_templates_are_the_shipped_diamonds() {
    // R2/C5a — every position a parameter (`control_6_select`).
    let env = island("def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b");
    let (plan, template) = template_for(&env, "min2");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::Select {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        }
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(
        &rendered,
        &expected_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        "the parameter select (R2/C5a)",
    );
    admit_lowering(&env, &plan, &rendered).expect("the rendered parameter select must admit");

    // R2/C9 — the comparison's RIGHT operand a literal
    // (`control_7_select_literal`).
    let env = island("def capped (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b");
    let (plan, template) = template_for(&env, "capped");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::SelectLiteral {
            cmp: SelectCmp::Lt,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        }
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(
        &rendered,
        &expected_diamond(
            BinOp::Lt,
            Operand::Constant(ConstValue::Uint(10, 64)),
            Operand::Copy(Place::local(1)),
            Operand::Copy(Place::local(2)),
        ),
        "the select-vs-literal (R2/C9)",
    );
    admit_lowering(&env, &plan, &rendered).expect("the rendered select-literal must admit");

    // §6f landing 3 — a NUMERAL arm (`control_10`).
    let env = island("def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0");
    let (plan, template) = template_for(&env, "clampz");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::SelectOperands {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        }
    );
    let rendered = render(&template, &Rendering::machine("probe", 64, 2));
    assert_identical(
        &rendered,
        &expected_diamond(
            BinOp::Lt,
            Operand::Copy(Place::local(2)),
            Operand::Copy(Place::local(1)),
            Operand::Constant(ConstValue::Uint(0, 64)),
        ),
        "the general select (landing 3)",
    );
    admit_lowering(&env, &plan, &rendered).expect("the rendered general select must admit");
}

/// **HALF 5 — R1's zero-test recursion, INCLUDING the dead temps.**
/// `control_7`'s `emitted_tozero_as_extracted` is the MEASURED emission (the
/// picture in the builder's own doc rounds it off, and the first R1 fixture run
/// refused on exactly that difference). Ten locals, two of them declared and
/// dead — `_4`, the zero arm's `from_u64` temp, and `_9`, the self-call's —
/// because `lower_arm` re-points an arm's last call at `_0` AFTER its temporary
/// was allocated, so the succ arm's numbering starts at `_5`.
#[test]
fn half_5_the_structural_rec_template_is_the_shipped_measured_emission() {
    const SELF_PATH: &str = "clean_origin_structural_rec::tozero";
    let env = env_with_tozero();
    let (plan, template) = template_for(&env, "tozero");
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::StructuralNatRec {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        }
    );

    let expected_locals = vec![
        nat_adt_local(0),
        nat_adt_local(1),
        nat_adt_ref_local(2),
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        // dead: the zero arm's from_u64 temp, re-pointed at `_0`.
        nat_adt_local(4),
        nat_adt_local(5),
        nat_adt_ref_local(6),
        nat_adt_ref_local(7),
        nat_adt_local(8),
        // dead: the self-call's temp, re-pointed at `_0`.
        nat_adt_local(9),
    ];
    let expected_blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(2, Rvalue::Ref { mutable: false, place: Place::local(1) })],
            terminator: unwinding_call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(2))],
                3,
                1,
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(0, 64))],
                0,
                6,
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                5,
                4,
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(6, Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(7, Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: unwinding_call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                8,
                5,
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: unwinding_call(SELF_PATH, vec![Operand::Move(Place::local(8))], 0, 6),
        },
        BasicBlock { id: BlockId(6), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    let mut expected = vf(1, expected_locals, expected_blocks);
    expected.name = "tozero".into();
    expected.def_path = SELF_PATH.into();
    expected.body.return_ty = nat_adt();

    let rendered = render(&template, &nat_rendering("tozero", SELF_PATH));
    assert_identical(&rendered, &expected, "R1's zero-test recursion (control_7's measurement)");

    // Side B's own reading, first and separately, then the whole route to the
    // per-defining-equation kernel gate.
    assert_eq!(
        recognize_structural_rec(&rendered),
        Some(trust_types::admissible_body::StructuralRecBody {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        }),
        "the rendered template must read back as the planned recursion"
    );
    let faithful = admit_lowering(&env, &plan, &rendered)
        .expect("the rendered recursion must pass the per-defining-equation gate");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
}

/// **HALF 6 — R2's emission is the SAME emitter, and the proof is the
/// template.** `control_8` measured `countdownSum` as thirteen locals and eight
/// blocks, with `_4` and `_12` declared and dead. The shipped
/// `build_structural_rec_body` was already a one-line call into
/// `build_nat_zero_test_rec_body`, so R1 and R2 shared an emitter before this
/// landing; what this half pins is that the SHARED skeleton still produces R2's
/// measured body exactly.
///
/// Taken on [`zero_test_rec_template`] directly rather than through
/// `body_template`: reaching the `WellFoundedNatRec` arm needs a kernel-checked
/// `WellFounded.fix` declaration (`control_8`'s hundred-line environment) that
/// adds no byte-level evidence, and the arm itself — arity, `rec_arg`, the
/// row's unwind discipline — is exercised by half_5 and half_7.
#[test]
fn half_6_the_wf_rec_template_is_the_shipped_measured_emission() {
    const SELF_PATH: &str = "clean_origin_wf_rec::countdownSum";
    let template = zero_test_rec_template(
        &RecBodyExpr::NatConst(0),
        &RecBodyExpr::Add(Box::new(RecBodyExpr::Decreasing), Box::new(RecBodyExpr::Rec)),
        &[RecBodyExpr::Pred],
        0,
        TemplateUnwind::Continue,
    );

    let expected_locals = vec![
        nat_adt_local(0),
        nat_adt_local(1),
        nat_adt_ref_local(2),
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        // dead: the zero arm's from_u64 temp, re-pointed at `_0`.
        nat_adt_local(4),
        nat_adt_local(5),
        nat_adt_ref_local(6),
        nat_adt_ref_local(7),
        nat_adt_local(8),
        nat_adt_local(9),
        nat_adt_ref_local(10),
        nat_adt_ref_local(11),
        // dead: the root `add`'s temp, re-pointed at `_0`.
        nat_adt_local(12),
    ];
    let expected_blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(2, Rvalue::Ref { mutable: false, place: Place::local(1) })],
            terminator: unwinding_call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(2))],
                3,
                1,
            ),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: Operand::Move(Place::local(3)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(0, 64))],
                0,
                7,
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: unwinding_call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                5,
                4,
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(6, Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(7, Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: unwinding_call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                8,
                5,
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: unwinding_call(SELF_PATH, vec![Operand::Move(Place::local(8))], 9, 6),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![
                assign(10, Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(11, Rvalue::Ref { mutable: false, place: Place::local(9) }),
            ],
            terminator: unwinding_call(
                BIGNUM_ADD,
                vec![Operand::Move(Place::local(10)), Operand::Move(Place::local(11))],
                0,
                7,
            ),
        },
        BasicBlock { id: BlockId(7), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    let mut expected = vf(1, expected_locals, expected_blocks);
    expected.name = "countdownSum".into();
    expected.def_path = SELF_PATH.into();
    expected.body.return_ty = nat_adt();

    assert_identical(
        &render(&template, &nat_rendering("countdownSum", SELF_PATH)),
        &expected,
        "R2's zero-test recursion (control_8's measurement)",
    );
}

/// **HALF 7 — H-G, discharged AT THE EMITTER rather than described by it.**
///
/// Until this landing the unwind edge was hand-written in each builder and the
/// row's `UnwindDiscipline` merely described it — two places one fact lived,
/// which is the shape of every drift hazard in this tree. The template DERIVES
/// the edge from the selected row, so this half is the constraint:
/// **every emitted call carries the discipline its row declares.**
#[test]
fn half_7_every_emitted_call_carries_the_selected_rows_unwind_discipline() {
    let cases: Vec<(&str, &str)> = vec![
        ("def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b", "wsum"),
        ("def wmix (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a", "wmix"),
    ];
    let mut calls_seen = 0usize;
    for (source, name) in cases {
        let env = island(source);
        let plan = plan_clean_origin_body(&env, name).expect("plan");
        let selected = ladder_row(plan.shape()).expect("row");
        let template = body_template(selected, &plan).expect("template");
        for (block, _, unwind) in template.calls() {
            assert_eq!(
                unwind.discipline(),
                selected.unwind,
                "`{name}` bb{block} emits an unwind edge the row `{}` does not declare",
                selected.name
            );
            calls_seen += 1;
        }
    }
    // The recursion lane, whose rows declare `Continue` — the half of H-G that
    // a global "every edge is Unreachable" assertion would have got wrong.
    let env = env_with_tozero();
    let plan = plan_clean_origin_body(&env, "tozero").expect("plan");
    let selected = ladder_row(plan.shape()).expect("row");
    assert_eq!(selected.unwind, UnwindDiscipline::Continue);
    let template = body_template(selected, &plan).expect("template");
    for (block, _, unwind) in template.calls() {
        assert_eq!(
            unwind.discipline(),
            UnwindDiscipline::Continue,
            "the recursion lane's bb{block} must carry the abortable edge the row declares"
        );
        calls_seen += 1;
    }
    assert!(calls_seen >= 8, "the discipline must actually have been checked over calls");

    // The shapes whose rows declare `NoCall` must emit NO call at all — the
    // converse, without which the assertion above is vacuous for them.
    for (source, name) in [
        ("def fst (a : UInt64) (b : UInt64) : UInt64 := a", "fst"),
        ("def six : UInt64 := 6", "six"),
        ("def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b", "min2"),
    ] {
        let env = island(source);
        let plan = plan_clean_origin_body(&env, name).expect("plan");
        let selected = ladder_row(plan.shape()).expect("row");
        assert_eq!(selected.unwind, UnwindDiscipline::NoCall);
        assert!(
            body_template(selected, &plan).expect("template").calls().is_empty(),
            "`{name}` selects a `NoCall` row and must emit no call"
        );
    }
}

/// **HALF 8 — the template fields the extractor CANNOT see.**
///
/// `WithRetag::Yes`, `LocalDecl::immutable()` and the carrier POSITION each
/// local is typed at survive no round trip through `VerifiableFunction`, so
/// half_0..half_6 are blind to them. A materializer that dropped `immutable()`
/// or emitted `WithRetag::No` would pass every one of them and change the
/// emitted binary.
#[test]
fn half_8_retag_immutability_and_carrier_positions_are_pinned() {
    for (source, name) in [
        ("def fst (a : UInt64) (b : UInt64) : UInt64 := a", "fst"),
        ("def six : UInt64 := 6", "six"),
        ("def wsum (a : UInt64) (b : UInt64) : UInt64 := a + b", "wsum"),
        ("def wmix (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a", "wmix"),
        ("def min2 (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b", "min2"),
        ("def capped (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b", "capped"),
        ("def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0", "clampz"),
    ] {
        let env = island(source);
        let plan = plan_clean_origin_body(&env, name).expect("plan");
        let selected = ladder_row(plan.shape()).expect("row");
        let template = body_template(selected, &plan).expect("template");
        let arity = plan.signature().arity();

        assert_eq!(template.arg_count, arity);
        assert_eq!(
            template.locals[0],
            trust_clean_origin::materialize::TemplateLocal {
                ty: TemplateTy::Result,
                immutable: false,
            },
            "`{name}`: `_0` is the return place, at the RESULT carrier, and mutable"
        );
        for index in 0..arity {
            assert_eq!(
                template.locals[index + 1],
                trust_clean_origin::materialize::TemplateLocal {
                    ty: TemplateTy::Param { index },
                    immutable: true,
                },
                "`{name}`: `_{}` must be the {index}-th parameter, IMMUTABLE exactly as \
                 `local_decls_for_sig` makes a shim's",
                index + 1
            );
        }
        for local in &template.locals[arity + 1..] {
            assert!(!local.immutable, "`{name}`: a temporary is written, so it is not immutable");
            assert!(
                matches!(local.ty, TemplateTy::Result | TemplateTy::Bool),
                "`{name}`: a non-recursive temporary is at the result carrier or `bool`"
            );
        }
    }

    // The recursion lane's own local discipline, which differs deliberately:
    // `_1` is typed at the RESULT carrier (the shipped emitter used `nat_ty`
    // for both), `_2` is the shared borrow and `_3` the zero test's bool.
    let template = zero_test_rec_template(
        &RecBodyExpr::NatConst(0),
        &RecBodyExpr::Rec,
        &[RecBodyExpr::Pred],
        0,
        TemplateUnwind::Continue,
    );
    assert_eq!(template.locals[1].ty, TemplateTy::Result);
    assert!(template.locals[1].immutable, "the recursion parameter is immutable");
    assert_eq!(template.locals[2].ty, TemplateTy::ResultRef);
    assert_eq!(template.locals[3].ty, TemplateTy::Bool);
    for local in &template.locals[4..] {
        assert!(!local.immutable, "an arm temporary is written, so it is not immutable");
    }

    // `WithRetag::Yes` is UNIFORM across every `Use` in every shape, which is
    // why it is not a template field. This is what pins that it stays so: the
    // only rvalues the fragment builds are `Use`, `Compare` and `SharedRef`.
    let env = island("def fst (a : UInt64) (b : UInt64) : UInt64 := a");
    let plan = plan_clean_origin_body(&env, "fst").expect("plan");
    let template = body_template(ladder_row(plan.shape()).expect("row"), &plan).expect("template");
    assert_eq!(
        template.blocks[0].stmts[0].rvalue,
        TemplateRvalue::Use(TemplateOperand::Move(1)),
        "the projection writes `_0` from a MOVE of the projected parameter"
    );
}

/// **HALF 9 — the refusals, and their exact text.**
///
/// Every `TemplateRefusal` is a compiler defect with no degraded mode. The
/// strings moved out of `clean_origin_mir.rs` and onto this lane with the
/// decision that produces them, so they are pinned here rather than reviewed.
#[test]
fn half_9_the_template_refusals_are_named_and_fatal() {
    let env = island("def fst (a : UInt64) (b : UInt64) : UInt64 := a");
    let plan = plan_clean_origin_body(&env, "fst").expect("plan");

    // A row whose realization is a RECURSION-ARM node can never serve a whole
    // body: `nat.sub` realizes `Call(Fixed(NatSub))` and `nat.self` a
    // `SelfCall`. Both must refuse rather than guess a skeleton.
    for arm_row in ["nat.sub", "nat.self", "nat.lit"] {
        assert_eq!(
            body_template(row(arm_row).expect("row"), &plan),
            Err(TemplateRefusal::RealizationDisagrees),
            "the arm-only row `{arm_row}` must not build a whole body"
        );
    }
    // …and a whole-body row whose realization does not describe THIS plan.
    assert_eq!(
        body_template(row("uint.add").expect("row"), &plan),
        Err(TemplateRefusal::RealizationDisagrees),
        "the arithmetic row must not build a projection"
    );
    assert_eq!(
        body_template(row("select.lt").expect("row"), &plan),
        Err(TemplateRefusal::RealizationDisagrees)
    );

    let selected = row("param").expect("row");
    let note = TemplateRefusal::RealizationDisagrees.note("fst", selected, plan.shape());
    assert!(note.contains("selected the row `param`"), "must name the row: {note}");
    assert!(note.contains("NOTHING WAS EMITTED"), "must say nothing shipped: {note}");
    assert!(note.contains("compiler defect"), "must not send the user to fix it: {note}");

    let note =
        TemplateRefusal::NonMachineResultCarrier { shape: "WrappingBinOp", carrier: Ty::BignumNat }
            .note("wsum", selected, plan.shape());
    assert!(
        note.contains("a WrappingBinOp plan carries result carrier `BignumNat`"),
        "must name the shape and the carrier: {note}"
    );
    assert!(note.contains("`plan_clean_origin_body` is required to refuse"), "{note}");

    let note =
        TemplateRefusal::DegenerateComposedTree { steps: 1 }.note("wmix", selected, plan.shape());
    assert!(note.contains("flattened to 1 call step(s)"), "{note}");

    let note = TemplateRefusal::RecursionOutsideFragment.note("f", selected, plan.shape());
    assert!(note.contains("single-parameter/predecessor class"), "{note}");

    let note = TemplateRefusal::UndeclaredUnwindEdge.note("f", selected, plan.shape());
    assert!(note.contains("declares the unwind discipline `NoCall`"), "{note}");
    assert!(note.contains("h_g_the_unwind_discipline_matches_the_realization"), "{note}");
}

/// **HALF 10 — the collapse, counted.**
///
/// Six hand-written builders became FIVE skeletons, and the count is asserted
/// rather than described so a future landing that quietly adds a sixth has to
/// say so. The mapping is `MirShape`-keyed, which is what "adding a row adds a
/// table entry rather than a builder" means operationally: every row in the
/// table already resolves to one of these five, and a `MirShape` variant with
/// no skeleton is a compile error in `body_template`.
#[test]
fn half_10_every_row_realization_resolves_to_one_of_five_skeletons() {
    use std::collections::BTreeSet;
    let skeletons: BTreeSet<&str> = trust_clean_origin::table::ROWS
        .iter()
        .map(|candidate| match candidate.mir {
            MirShape::OperandCopy => "single-assignment",
            MirShape::InlineScalar => "single-assignment",
            MirShape::Call(_) => "call-chain",
            MirShape::ComparisonBranch(_) => "diamond",
            // §6f landing 6 — the SIXTH skeleton, and it is a landing rather
            // than a refactor exactly as this control demanded. It is a
            // separate skeleton and not a parameter on "diamond" because the
            // ENTRY BLOCK differs: two comparisons and a branch on the second.
            // Everything below the `SwitchInt` is the diamond's contract byte
            // for byte, which is why side B reads the arms and the join of both
            // shapes with one function.
            MirShape::BoolDecisionBranch => "two-step diamond",
            // §6f landing 7 — and it is NOT a seventh skeleton, which is the
            // finding. `_0 = <op>(l, r); return` is ONE block with ONE
            // statement and a `Return`: the same locals, the same block count
            // and the same terminator `single_assignment_body` builds, with a
            // different rvalue in the one statement it has. The arm in
            // `body_template` calls that helper's own `signature_locals` for
            // exactly that reason. What landing 7 adds is a realization
            // PRIMITIVE (`TemplateRvalue::RawBin`), not a body SHAPE — the
            // sharpest available statement of landing 6's qualification that
            // the two are different kinds of cost.
            MirShape::RawBinOp(_) => "single-assignment",
            // W6 (Rust-calls-Clean): the comparison-to-`Bool` value is ALSO the
            // single-assignment skeleton — `_0 = <cmp>(l, r); return`, one block
            // with one statement and a `Return`, `single_assignment_body`'s
            // locals and terminator with a `Compare` rvalue. Like landing 7's
            // raw-binop, it adds a realization PRIMITIVE reuse, not a body
            // SHAPE, so the skeleton count does not move.
            MirShape::ComparisonValue(_) => "single-assignment",
            // W6 (Rust-calls-Clean): the boolean connective/negation is also the
            // single-assignment skeleton — one block, one statement into `_0`
            // (a `RawBin` at the `bool` carrier for `&&`/`||`, a `BoolNot` for
            // negation), a `Return`. A realization primitive reuse (`&&`/`||`)
            // or one new primitive (`BoolNot`), not a body shape.
            MirShape::BoolConnValue(_) | MirShape::BoolNotValue => "single-assignment",
            MirShape::ZeroTestBranch => "zero-test-recursion",
            MirShape::SelfCall => "arm-node (never a whole body)",
            // W5 (Lean-calls-Rust): the SAME call-chain skeleton — one `Call`
            // per node in post-order through fresh temporaries, the root
            // writing `_0` — with a table-indexed callee and per-callee
            // temporary types. A row, not a skeleton.
            MirShape::RustCallChain => "call-chain",
        })
        .collect();
    assert_eq!(
        skeletons,
        BTreeSet::from([
            "single-assignment",
            "call-chain",
            "diamond",
            "two-step diamond",
            "zero-test-recursion",
            "arm-node (never a whole body)",
        ]),
        "the skeleton set moved. Six is the measured number for the twenty shipped rows (five \
         for the first fifteen; §6f landing 6 added the two-step `==` diamond with its row, and \
         landing 7 added FOUR rows and NO skeleton — its raw-binop body is the \
         single-assignment skeleton with a different rvalue); a seventh is a landing, not a \
         refactor."
    );

    // And the ladder: ten rungs, five of which now share two skeletons.
    let rungs: Vec<CleanOriginShape> = vec![
        CleanOriginShape::Projection { projected: 0 },
        CleanOriginShape::InductiveProjection { projected: 0 },
        CleanOriginShape::ConstantUint { value: 6 },
        CleanOriginShape::WrappingBinOp {
            op: ArithBinOp::Add,
            left: ArithOperand::Param(0),
            right: ArithOperand::Param(1),
        },
        CleanOriginShape::Composed {
            expr: ArithExpr::Bin {
                op: ArithBinOp::Mul,
                left: Box::new(ArithExpr::Operand(ArithOperand::Param(0))),
                right: Box::new(ArithExpr::Operand(ArithOperand::Param(1))),
            },
        },
        CleanOriginShape::Select {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: 1,
            then_param: 0,
            else_param: 1,
        },
        CleanOriginShape::SelectLiteral {
            cmp: SelectCmp::Lt,
            cmp_param: 0,
            literal: 10,
            then_param: 0,
            else_param: 1,
        },
        CleanOriginShape::SelectOperands {
            cmp: SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        },
        // §6f landing 6 — the ELEVENTH rung.
        CleanOriginShape::SelectBeq {
            cmp_left: 0,
            cmp_right: ArithOperand::Param(1),
            then_arm: ArithOperand::Param(0),
            else_arm: ArithOperand::Const(0),
        },
        CleanOriginShape::StructuralNatRec {
            base: RecBodyExpr::NatConst(0),
            step: RecBodyExpr::Rec,
            rec_arg: RecBodyExpr::Pred,
        },
        CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::NatConst(0),
            nonzero_value: RecBodyExpr::Rec,
            rec_args: vec![RecBodyExpr::Pred],
            measure_index: 0,
            lowering: trust_clean_origin::WfLowering::OnParameter,
        },
    ];
    assert_eq!(rungs.len(), 11, "the ladder is eleven rungs");
    for rung in &rungs {
        assert!(ladder_row(rung).is_some(), "the rung {rung:?} maps onto no row");
    }
}
