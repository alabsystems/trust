// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 9 — THE CONSTANT-BODY EMITTER MUTATION FIXTURE** (§6f landing 2).
//!
//! `control_5`/`control_6`/`control_7` are the emitter-mutation discipline
//! pointed at the arithmetic, select and select-literal shapes. This file is the
//! same discipline pointed at [`CleanOriginShape::ConstantUint`] — the shape
//! landing 2 admitted, on the kernel measurements in
//! `tests/landing2_selection_probes.rs` (l2_p1..l2_p3b), taken BEFORE the route
//! existed.
//!
//! The route and the soundness argument are control_3's, unchanged:
//!
//! ```text
//! emitted body (as read back out of MIR by trust_mir_extract)
//!   -> trust_types::recognize_admissible_body          (ConstantUint)
//!   -> trust_spec_elab::admit_expr_function            (side B, "6", at arg_count params)
//!   -> check_faithful                                   (against side A)
//! ```
//!
//! and the mutation is injected into **the emitted body**, never into side B.
//!
//! # THE MUTATION THIS SHAPE EXISTS TO BE CONTROLLED FOR
//!
//! `AdmissibleBody::ConstantUint` **erases the arity**
//! (`fragment_widening_probes::probe_e3`): `fn() -> u64 {6}` and
//! `fn(u64) -> u64 {6}` read back as the same value. Landing 2 did not repair
//! that and must not pretend to — what it did was route the reflection through
//! a producer that takes its arity from the EMITTED body. So the arity is a
//! side-B fact in two independent places, and this file mutates BOTH:
//!
//! * [`half_4_a_WRONG_ARITY_emission_is_refused_in_both_directions`] — the
//!   structural catch (`arg_count == signature.arity()`, before any reflection);
//! * [`half_4b_the_kernel_alone_catches_the_arity_in_both_directions`] — the
//!   same two mutations put to the KERNEL directly, so the structural check is
//!   not the only thing standing between an arity skew and a wrong binary.
//!
//! # AND THE ONE THE SHARED ROW OPENS
//!
//! `uint.lit` now serves TWO positions — a numeral as an arithmetic OPERAND and
//! a numeral as the whole BODY. `table_controls::h_c_…` is satisfied because
//! there is one row rather than two aliased ones, but the substantive question
//! is whether side B can still tell the positions apart. It can, off the MIR
//! alone, and [`half_7_the_two_POSITIONS_of_the_numeral_row_are_not_interchangeable`]
//! is that measurement: each position's emission is REFUSED against the other's
//! declaration.
//!
//! # DO NOT "FIX" A FAILURE HERE BY EDITING SIDE B'S PRODUCERS
//!
//! `trust_types::admissible_body` and `trust_spec_elab::admit_*_function` are
//! frozen against this lane. If a mutated body ever passes, the defect is in the
//! emitter or the gate — never in this fixture.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, admit_lowering, check_faithful,
    plan_clean_origin_body,
};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn rust_ty(bits: u32) -> Ty {
    Ty::Int { width: bits, signed: false }
}

fn env_uint() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith().expect("UInt8/16/32/64 + arithmetic must init");
    env
}

fn define(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{name}` must kernel-check as written: {e:?}"));
}

fn arrows(bits: u32, n: usize) -> Expr {
    (0..n).fold(uint_ty(bits), |acc, _| Expr::arrow(uint_ty(bits), acc))
}

/// `UInt{bits}.ofNat v` — the carrier numeral.
fn carrier_lit(bits: u32, v: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(&format!("UInt{bits}.ofNat")), vec![]),
        Expr::nat_lit(v),
    )
}

/// `OfNat.ofNat UInt{bits} v (instOfNatUInt{bits} v)` — the surface numeral a
/// real island literal elaborates to.
fn surface_lit(bits: u32, v: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            uint_ty(bits),
            Expr::nat_lit(v),
            Expr::app(
                Expr::const_(Name::from_string(&format!("instOfNatUInt{bits}")), vec![]),
                Expr::nat_lit(v),
            ),
        ],
    )
}

/// `def <name> : UInt{bits} … := <numeral>` under `arity` IGNORED binders.
fn define_constant(env: &mut Environment, name: &str, bits: u32, arity: usize, numeral: Expr) {
    let body =
        (0..arity).fold(numeral, |acc, _| Expr::lam(BinderInfo::Default, uint_ty(bits), acc));
    define(env, name, arrows(bits, arity), body);
}

// ─────────────── the emitter's MIR, as extracted, and its mutants ───────────────

const WADD: &str = "@trust-rustc-total-primitive-method::core::num::<impl u64>::wrapping_add";

fn vf(
    name: &str,
    arg_count: usize,
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: name.into(),
        def_path: format!("crate::m::{name}"),
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

/// The whole-body inline scalar the constant emitter produces:
/// `_0 = const <value>_u{const_bits}; return`, in a body whose locals are at
/// `local_bits`. The two widths are separate knobs so half_5 can skew them.
fn emitted_constant(
    name: &str,
    arg_count: usize,
    local_bits: u32,
    value: u128,
    const_bits: u32,
) -> VerifiableFunction {
    let locals = (0..=arg_count)
        .map(|index| LocalDecl { index, ty: rust_ty(local_bits), name: None })
        .collect();
    vf(
        name,
        arg_count,
        locals,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(value, const_bits))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// `_0 = move _1; return` — a PROJECTION where a constant was planned.
fn emitted_projection(name: &str, arg_count: usize) -> VerifiableFunction {
    let locals =
        (0..=arg_count).map(|index| LocalDecl { index, ty: rust_ty(64), name: None }).collect();
    vf(
        name,
        arg_count,
        locals,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Move(Place::local(1))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

/// `_0 = wrapping_add(_1, const 6); return` — the OPERAND position of the same
/// numeral row, for half_7.
fn emitted_add_const(name: &str) -> VerifiableFunction {
    let locals = (0..2).map(|index| LocalDecl { index, ty: rust_ty(64), name: None }).collect();
    vf(
        name,
        1,
        locals,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: Vec::new(),
                terminator: Terminator::Call {
                    func: WADD.into(),
                    args: vec![
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(6, 64)),
                    ],
                    dest: Place::local(0),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Unreachable,
                    callee_identity: None,
                    callee_key: None,
                },
            },
            BasicBlock { id: BlockId(1), stmts: Vec::new(), terminator: Terminator::Return },
        ],
    )
}

/// Reflect a spec-syntax body directly through the frozen expr mint — the
/// kernel half of a mutation, bypassing the structural check on purpose so the
/// KERNEL's own verdict is measured (control_3 half_3's rationale).
fn reflect_expr(env: &Environment, body: &str, n_params: usize) -> Expr {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    let mut scratch = env.clone();
    let name = "control9_reflection";
    trust_spec_elab::admit_expr_function(
        &mut scratch,
        name,
        body,
        &name_refs,
        &trust_spec_elab::Domain::Machine(trust_spec_elab::MachineUIntWidth::U64),
    )
    .unwrap_or_else(|e| panic!("`{body}` over {n_params} params must reflect: {e}"));
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .expect("a minted definition carries a value")
}

/// `Result::unwrap_err` with a message naming the mutation. A refusal that
/// passes anonymously measures nothing, and an ADMIT here is a wrong binary —
/// so the panic text says which one, rather than printing a bare `Ok`.
trait UnwrapErrNamed<E> {
    fn unwrap_err_named(self, what: &str) -> E;
}
impl<T: std::fmt::Debug, E> UnwrapErrNamed<E> for Result<T, E> {
    fn unwrap_err_named(self, what: &str) -> E {
        match self {
            Ok(value) => panic!(
                "{what} was ADMITTED (got {value:?}). Every call site was type-checked \
                 against the declaration and the emitted body says something else — a WRONG \
                 BINARY. Do NOT fix this by editing side B's producers."
            ),
            Err(refusal) => refusal,
        }
    }
}

fn carrier(bits: u32) -> trust_clean_carrier::Carrier {
    trust_clean_carrier::carrier_at(&uint_ty(bits), &rust_ty(bits))
        .expect("UIntN -> uN is the exact-width carrier")
}

// ═══════════════════════════════ the halves ═══════════════════════════════

#[test]
fn half_0_the_plan_reads_both_numeral_spellings_at_every_arity() {
    let mut env = env_uint();
    for arity in [0usize, 1, 2] {
        define_constant(&mut env, &format!("c{arity}"), 64, arity, carrier_lit(64, 6));
        define_constant(&mut env, &format!("c{arity}_s"), 64, arity, surface_lit(64, 6));
    }
    for arity in [0usize, 1, 2] {
        for name in [format!("c{arity}"), format!("c{arity}_s")] {
            let plan = plan_clean_origin_body(&env, &name).expect("a constant body plans");
            assert_eq!(
                plan.shape(),
                &CleanOriginShape::ConstantUint { value: 6 },
                "`{name}` must read as the constant 6 — the numeral spelling and the arity \
                 are both invisible to the SHAPE, deliberately"
            );
            assert_eq!(plan.signature().arity(), arity);
            assert_eq!(plan.return_ty(), &Ty::u64());
        }
    }
}

#[test]
fn half_1_the_gate_admits_the_faithful_emission_at_every_arity() {
    let mut env = env_uint();
    for arity in [0usize, 1, 2] {
        define_constant(&mut env, &format!("c{arity}"), 64, arity, carrier_lit(64, 6));
    }
    for arity in [0usize, 1, 2] {
        let name = format!("c{arity}");
        let plan = plan_clean_origin_body(&env, &name).expect("plannable");
        let admitted = admit_lowering(&env, &plan, &emitted_constant(&name, arity, 64, 6, 64))
            .unwrap_or_else(|refusal| {
                panic!("`_0 = const 6` IS `{name}`; the gate must admit it: {refusal:?}")
            });
        assert_eq!(admitted.name(), name);
        assert_eq!(
            admitted.admitted_at(),
            &Ty::u64(),
            "admitted AT THE CARRIER TYPE, never the Clean type"
        );
    }
}

#[test]
fn half_1b_the_gate_admits_at_every_machine_width() {
    // The width is derived from the EMITTED body's return type, so every width
    // the fragment claims must actually round-trip, not just u64.
    for bits in [8u32, 16, 32, 64] {
        let mut env = env_uint();
        define_constant(&mut env, "k", bits, 0, carrier_lit(bits, 6));
        let plan = plan_clean_origin_body(&env, "k").expect("plannable");
        let admitted = admit_lowering(&env, &plan, &emitted_constant("k", 0, bits, 6, bits))
            .unwrap_or_else(|refusal| panic!("u{bits} constant must admit: {refusal:?}"));
        assert_eq!(admitted.admitted_at(), &rust_ty(bits));
    }
}

#[test]
fn half_2_an_emitter_that_baked_in_the_WRONG_VALUE_is_refused() {
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    let plan = plan_clean_origin_body(&env, "six").expect("plannable");

    // ONE construct changed: the scalar. Same block, same terminator, same
    // arity, same types — a body returning 7 for a def that says 6.
    let refusal = admit_lowering(&env, &plan, &emitted_constant("six", 0, 64, 7, 64)).expect_err(
        "THE GATE IS DECORATION IF THIS PASSES: a body returning 7 was accepted for a \
         definition that says 6 — a WRONG BINARY. Do NOT fix this by editing side B's \
         producers; they are frozen against this lane.",
    );
    assert!(refusal.is_compiler_defect(), "a mistranslation is a compiler defect: {refusal:?}");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "the structural catch fires first; got {refusal:?}"
    );
}

#[test]
fn half_3_the_kernel_alone_catches_the_wrong_value_too() {
    // half_2 is the STRUCTURAL catch. Put the same mutation to the kernel
    // directly: if the kernel identified `6` with `7`, everything above is
    // theatre.
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    let wrong = reflect_expr(&env, "7", 0);
    let refusal = check_faithful(&env, "six", &wrong, &carrier(64))
        .expect_err("the kernel must separate `6` from `7`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_4_a_WRONG_ARITY_emission_is_refused_in_both_directions() {
    // THE mutation this shape exists for. `recognize_admissible_body` reports
    // the SAME `ConstantUint` for both bodies below, so nothing the recognizer
    // says can tell them apart — what refuses them is `admit_lowering`'s
    // `arg_count == signature.arity()`, read off the emitted body.
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    define_constant(&mut env, "k1", 64, 1, carrier_lit(64, 6));

    for (declaration, emitted_arity, what) in [
        ("six", 1usize, "a UNARY body for a nullary declaration"),
        ("k1", 0, "a NULLARY body for a unary declaration"),
    ] {
        let plan = plan_clean_origin_body(&env, declaration).expect("plannable");
        let refusal =
            admit_lowering(&env, &plan, &emitted_constant(declaration, emitted_arity, 64, 6, 64))
                .unwrap_err_named(what);
        assert!(refusal.is_compiler_defect(), "{what}: {refusal:?}");
        assert!(
            matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
            "{what}: the arity check reports a shape mismatch; got {refusal:?}"
        );
    }
}

#[test]
fn half_4b_the_kernel_alone_catches_the_arity_in_both_directions() {
    // The structural check above is not the only thing standing between an
    // arity skew and a wrong binary: the reflected TERMS differ too, because
    // the reflection's lambda count is the emitted body's `arg_count`. This is
    // probe_e3's route-1 refusal plus its converse, re-pinned under this
    // control's honesty rules so the control stands alone.
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    define_constant(&mut env, "k1", 64, 1, carrier_lit(64, 6));

    for (declaration, side_b_arity, what) in [
        ("six", 1usize, "a unary side B for a nullary declaration"),
        ("k1", 0, "a nullary side B for a unary declaration"),
    ] {
        let wrong = reflect_expr(&env, "6", side_b_arity);
        let refusal =
            check_faithful(&env, declaration, &wrong, &carrier(64)).unwrap_err_named(what);
        assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "{what}: got {refusal:?}");
    }
}

#[test]
fn half_5_a_WIDTH_SKEWED_scalar_is_refused() {
    // The emitted scalar's encoded width and the emitted body's return width
    // must agree, because the reflection's DOMAIN is derived from the return
    // type. A `const 6u32` written into a u64 return place is a body whose two
    // side-B facts disagree, and `recognize_single_block` cannot see it — it
    // reads the rvalue, not the type.
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    let plan = plan_clean_origin_body(&env, "six").expect("plannable");

    let refusal = admit_lowering(&env, &plan, &emitted_constant("six", 0, 64, 6, 32)).expect_err(
        "a u32-encoded scalar in a u64 return place must refuse: the reflection would be \
         minted at the RETURN type's domain and would not be the constant the body holds",
    );
    assert!(refusal.is_compiler_defect(), "{refusal:?}");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // And the kernel half: a u8-domain reflection is not the u64 declaration.
    let mut narrow = env_uint();
    define_constant(&mut narrow, "six8", 8, 0, carrier_lit(8, 6));
    let wide = reflect_expr(&env, "6", 0); // minted at u64
    let refusal = check_faithful(&narrow, "six8", &wide, &carrier(8))
        .expect_err("`UInt64.ofNat 6` is not `UInt8.ofNat 6`");
    assert!(matches!(refusal, GateRefusal::Disagreement { .. }), "got {refusal:?}");
}

#[test]
fn half_6_a_body_that_is_not_a_constant_at_all_is_refused() {
    let mut env = env_uint();
    define_constant(&mut env, "k1", 64, 1, carrier_lit(64, 6));
    let plan = plan_clean_origin_body(&env, "k1").expect("plannable");

    // The emitter returned the parameter instead of the constant. Both bodies
    // are valid `fn(u64) -> u64`; only one of them is `k1`.
    let refusal = admit_lowering(&env, &plan, &emitted_projection("k1", 1))
        .expect_err("a projection emitted for a constant declaration must refuse");
    assert!(refusal.is_compiler_defect(), "{refusal:?}");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_7_the_two_POSITIONS_of_the_numeral_row_are_not_interchangeable() {
    // §6f landing 2 gave `uint.lit` a SECOND side-A route, so one row now
    // covers a numeral in OPERAND position and a numeral as the whole BODY.
    // `table_controls::h_c_…` is satisfied structurally (one row, not two
    // aliased ones); this is the substantive half — side B still tells the two
    // positions apart off the MIR alone, with no help from the table.
    let mut env = env_uint();
    define_constant(&mut env, "six", 64, 0, carrier_lit(64, 6));
    define(
        &mut env,
        "winc6",
        arrows(64, 1),
        Expr::lam(
            BinderInfo::Default,
            uint_ty(64),
            Expr::apps(
                Expr::const_(Name::from_string("UInt64.add"), vec![]),
                [Expr::bvar(0), carrier_lit(64, 6)],
            ),
        ),
    );

    // The operand emission against the BODY declaration…
    let body_plan = plan_clean_origin_body(&env, "six").expect("plannable");
    let refusal = admit_lowering(&env, &body_plan, &emitted_add_const("six"))
        .expect_err("`a + 6` emitted for a def that says `6` must refuse");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");

    // …and the body emission against the OPERAND declaration.
    let operand_plan = plan_clean_origin_body(&env, "winc6").expect("plannable");
    let refusal = admit_lowering(&env, &operand_plan, &emitted_constant("winc6", 1, 64, 6, 64))
        .expect_err("`6` emitted for a def that says `a + 6` must refuse");
    assert!(matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }), "got {refusal:?}");
}

#[test]
fn half_8_an_OUT_OF_RANGE_numeral_refuses_at_plan_time_naming_the_boundary() {
    // `ArithOperand::Const` cannot carry a width, so the range is a plan-time
    // re-check on the sealed plan — and the refusal must name the boundary
    // rather than reporting the generic "outside the fragment" (v7/D3).
    let mut env = env_uint();
    define_constant(&mut env, "big8", 8, 0, carrier_lit(8, 300));
    let refusal = plan_clean_origin_body(&env, "big8")
        .expect_err("300 does not fit u8; the compiler must not silently reduce it mod 256");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect(), "a range boundary is a capability refusal");
    let note = refusal.note();
    assert!(note.contains("options:"), "v7/D3: {note}");
    assert!(note.contains("300"), "the refusal must name the numeral: {note}");
}

#[test]
fn half_9_a_MIXED_WIDTH_signature_refuses_at_plan_time() {
    // The reflected side B (`admit_expr_function`) is single-domain over ALL
    // parameters, used or not — so a constant behind a parameter at a DIFFERENT
    // width has no reflection and must refuse before anything is emitted. That
    // the parameter is ignored by the body does not change it: the reflection's
    // type is built from every position.
    let mut env = env_uint();
    define(
        &mut env,
        "mixed",
        Expr::arrow(uint_ty(8), uint_ty(64)),
        Expr::lam(BinderInfo::Default, uint_ty(8), carrier_lit(64, 6)),
    );
    let refusal = plan_clean_origin_body(&env, "mixed")
        .expect_err("a u8 parameter with a u64 result has no single-domain reflection");
    assert!(matches!(refusal, EmitRefusal::NotEmittable { .. }), "got {refusal:?}");
    assert!(!refusal.is_compiler_defect());
    assert!(refusal.note().contains("options:"), "v7/D3: {}", refusal.note());
}

#[test]
fn half_10_the_row_preflight_agrees_with_the_shape_the_emitter_dispatches_on() {
    // The fast-lane half of `clean_origin_mir.rs`'s ROW PREFLIGHT: the ladder
    // rung must select a row, and that row's declared MIR realization must be
    // the one the emitter builds. The compiler-side half is x.py-only; this is
    // the part that can fail in two seconds instead of an hour.
    use trust_clean_origin::table::{MirShape, UnwindDiscipline, ladder_row};

    let row = ladder_row(&CleanOriginShape::ConstantUint { value: 6 })
        .expect("the constant rung must select a row");
    assert_eq!(
        row.name, "uint.lit",
        "the constant body selects the NUMERAL row through its second side-A route; a row of \
         its own would realize `InlineScalar` twice with no legal separation (h_c)"
    );
    assert_eq!(
        row.mir,
        MirShape::InlineScalar,
        "the declared realization is what the emitter must build: `_0 = const v; return`"
    );
    assert_eq!(
        row.unwind,
        UnwindDiscipline::NoCall,
        "a whole-body inline scalar emits no call, so it carries no unwind edge — the H-G \
         property, stated for the position this landing added"
    );
}
