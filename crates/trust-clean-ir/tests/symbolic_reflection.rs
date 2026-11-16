// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! SYMBOLIC reflection: rebuild the emitted TrustIR as a Clean term and let the
//! kernel judge it against the declaration — at every width at once.
//!
//! The other gates in this crate are pointwise, or exhaustive at `u8`.
//! Exhaustive enumeration IS extensional equality at `u8`, but it says nothing
//! at `u32`/`u64`, whose domains are not enumerable. This is the symbolic
//! answer: one `is_def_eq` covers all inputs at a width.
//!
//! # THE CAVEAT — requested explicitly, and it is not a formality
//!
//! **This reflector is co-authored with the emitter it checks.** The crate's
//! `GATING` note asks for an INDEPENDENT spelling, as `trust-clean-origin`'s
//! MIR-side reflector is, and this is not one. The hazard is exact: a reflector
//! that inverts precisely the emitter's mistake makes the round trip cancel. If
//! the emitter lowered Clean `<` to a SIGNED comparison and this reflector
//! mapped that signed comparison back to `<`, the kernel would see the original
//! declaration, agree, and the bug would be invisible.
//!
//! So this does NOT close the faithfulness gap and the lane stays
//! non-proof-carrying. Two things bound the damage; neither substitutes for
//! independence:
//!
//! * the EXHAUSTIVE `u8` gate catches exactly the symmetric errors this one
//!   could hide — signed-for-unsigned, swapped arms, a dropped literal —
//!   because there the kernel computes the true value with no reflector in the
//!   loop. What this adds is coverage at widths enumeration cannot reach.
//! * the reflection targets a CANONICAL spelling (`UInt8.add a b`), while Clean
//!   elaborates source `a + b` to typeclass-mediated `HAdd.hAdd` with instance
//!   arguments (measured: `App(App(App(App(App(App(Const(HAdd.hAdd), …`). The
//!   two are not syntactically equal, so the kernel must do real definitional
//!   work to accept. This is not a string comparison in disguise.
//!
//! Honest summary: **a failure here is a real defect; a success is evidence, not
//! proof.**
//!
//! # Scope, and what refuses by name
//!
//! Straight-line integer bodies: parameter projection, carrier constants,
//! `Add`/`Sub`/`Mul` including nesting, AND `Select` over `<` / `<=`.
//!
//! Clean lowers `if a < b then x else y` to `ite {C} (LT.lt {C} instLTC a b)
//! (instDecidableCLt a b) x y`. The `Decidable` instance is **cited, never
//! built**: `instDecidableUInt8Lt` is the canonical instance constant Clean
//! itself elaborates to (measured by probe), and naming the constant Clean names
//! is reflection. CONSTRUCTING a `Decidable` term would be inventing
//! proof-relevant structure, and this still refuses to do it — a comparison with
//! no canonical instance name (`Eq`, whose instance shape is `DecidableEq`)
//! refuses BY NAME rather than being approximated.

use clean_kernel::{BinderData, Environment, Expr, Level, Name, TypeChecker};
use trust_clean_ir::emit_clean_origin_function;
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::value::{FuncId, FuncTyId, ValueId};
use trust_ir::{Constant, Function};

#[derive(Debug, Clone, PartialEq, Eq)]
enum ReflectRefusal {
    NotStraightLine {
        blocks: usize,
    },
    UnspelledInst {
        what: &'static str,
    },
    /// A comparison this reflector has no canonical Clean instance name for.
    UnspelledComparison {
        op: &'static str,
    },
    UnboundValue {
        value: u32,
    },
    UnsupportedCarrier {
        bits: u32,
    },
}

fn carrier_name(bits: u32) -> Result<String, ReflectRefusal> {
    match bits {
        8 | 16 | 32 | 64 => Ok(format!("UInt{bits}")),
        _ => Err(ReflectRefusal::UnsupportedCarrier { bits }),
    }
}

/// `UIntW.<op> lhs rhs` — the canonical spelling the kernel must reconcile with
/// the typeclass-mediated form Clean actually elaborates to.
fn carrier_binop(carrier: &str, op: &str, lhs: Expr, rhs: Expr) -> Expr {
    let head = Expr::const_(Name::from_string(&format!("{carrier}.{op}")), vec![]);
    Expr::app(Expr::app(head, lhs), rhs)
}

/// Reflect a single straight-line block into `fun (a : UIntW) … => <body>`.
fn reflect_function(function: &Function, bits: u32) -> Result<Expr, ReflectRefusal> {
    if function.blocks.len() != 1 {
        return Err(ReflectRefusal::NotStraightLine { blocks: function.blocks.len() });
    }
    let carrier = carrier_name(bits)?;
    let block = &function.blocks[0];
    let arity = block.params.len();

    // Parameter i is de Bruijn index (arity - 1 - i) under `arity` binders.
    let mut env: Vec<(ValueId, Expr)> = block
        .params
        .iter()
        .enumerate()
        .map(|(i, param)| (param.0, Expr::bvar((arity - 1 - i) as u32)))
        .collect();

    fn lookup(env: &[(ValueId, Expr)], v: ValueId) -> Result<Expr, ReflectRefusal> {
        env.iter()
            .rev()
            .find(|(id, _)| *id == v)
            .map(|(_, e)| e.clone())
            .ok_or(ReflectRefusal::UnboundValue { value: v.index() })
    }

    let mut cmps: Vec<(ValueId, ICmpOp, ValueId, ValueId)> = Vec::new();
    let mut returned: Option<Expr> = None;
    for node in &block.body {
        match &node.inst {
            Inst::Const { value: Constant::Int(n), .. } => {
                let lit = Expr::app(
                    Expr::const_(Name::from_string(&format!("{carrier}.ofNat")), vec![]),
                    Expr::nat_lit(u64::try_from(*n).map_err(|_| {
                        ReflectRefusal::UnspelledInst { what: "negative carrier constant" }
                    })?),
                );
                if let Some(result) = node.results.first() {
                    env.push((*result, lit));
                }
            }
            Inst::BinOp { op, lhs, rhs, .. } => {
                let name = match op {
                    BinOp::Add => "add",
                    BinOp::Sub => "sub",
                    BinOp::Mul => "mul",
                    _ => return Err(ReflectRefusal::UnspelledInst { what: "binop" }),
                };
                let term = carrier_binop(&carrier, name, lookup(&env, *lhs)?, lookup(&env, *rhs)?);
                if let Some(result) = node.results.first() {
                    env.push((*result, term));
                }
            }
            // Trust: comparisons are recorded, not reflected in place -- the Clean
            // spelling is a Prop plus its Decidable instance, and both are only
            // meaningful once a `Select` consumes them.
            Inst::ICmp { op, lhs, rhs, .. } => {
                if let Some(result) = node.results.first() {
                    cmps.push((*result, *op, *lhs, *rhs));
                }
            }
            // `ite {C} (LT.lt {C} instLTC a b) (instDecidableCLt a b) t e`.
            //
            // The instance is CITED, not synthesized: `instDecidableUInt8Lt` is
            // the canonical instance constant Clean itself elaborates to
            // (measured by probe: `ite[Succ(Zero)] | LT.lt[Zero] | instLTUInt8 |
            // instDecidableUInt8Lt`). Naming the constant Clean names is
            // reflection; BUILDING a Decidable term would be inventing
            // proof-relevant structure, and this still refuses to do that.
            Inst::Select { cond, then_val, else_val, .. } => {
                let (_, op, lhs, rhs) = *cmps
                    .iter()
                    .rev()
                    .find(|(id, ..)| id == cond)
                    .ok_or(ReflectRefusal::UnboundValue { value: cond.index() })?;
                let (rel, rel_inst, dec_inst) = match op {
                    ICmpOp::Ult => {
                        ("LT.lt", format!("instLT{carrier}"), format!("instDecidable{carrier}Lt"))
                    }
                    ICmpOp::Ule => {
                        ("LE.le", format!("instLE{carrier}"), format!("instDecidable{carrier}Le"))
                    }
                    ICmpOp::Eq => return Err(ReflectRefusal::UnspelledComparison { op: "Eq" }),
                    _ => return Err(ReflectRefusal::UnspelledComparison { op: "icmp" }),
                };
                let carrier_ty = Expr::const_(Name::from_string(&carrier), vec![]);
                let a = lookup(&env, lhs)?;
                let b = lookup(&env, rhs)?;
                // LT.lt {C} [inst] a b
                let prop = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(Name::from_string(rel), vec![Level::Zero]),
                                carrier_ty.clone(),
                            ),
                            Expr::const_(Name::from_string(&rel_inst), vec![]),
                        ),
                        a.clone(),
                    ),
                    b.clone(),
                );
                // instDecidableCLt a b
                let inst =
                    Expr::app(Expr::app(Expr::const_(Name::from_string(&dec_inst), vec![]), a), b);
                // ite {C} prop inst t e
                let ite = Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(
                                        Name::from_string("ite"),
                                        vec![Level::succ(Level::Zero)],
                                    ),
                                    carrier_ty,
                                ),
                                prop,
                            ),
                            inst,
                        ),
                        lookup(&env, *then_val)?,
                    ),
                    lookup(&env, *else_val)?,
                );
                if let Some(result) = node.results.first() {
                    env.push((*result, ite));
                }
            }
            Inst::Return { values } => {
                let Some(first) = values.first() else {
                    return Err(ReflectRefusal::UnspelledInst { what: "Return with no value" });
                };
                returned = Some(lookup(&env, *first)?);
            }
            _ => return Err(ReflectRefusal::UnspelledInst { what: "instruction" }),
        }
    }

    let Some(body) = returned else {
        return Err(ReflectRefusal::UnspelledInst { what: "block with no Return" });
    };

    let carrier_ty = Expr::const_(Name::from_string(&carrier), vec![]);
    let mut term = body;
    for _ in 0..arity {
        term = Expr::lam(BinderData::default(), carrier_ty.clone(), term);
    }
    Ok(term)
}

fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check `{decl}`: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

/// Emit, reflect, and require the KERNEL to accept the reflection as
/// definitionally equal to the declaration's own value — for ALL inputs.
fn kernel_accepts_reflection(decl_tpl: &str, name: &str, bits: u32) {
    let carrier = carrier_name(bits).expect("admitted carrier");
    let decl = decl_tpl.replace("{C}", &carrier);
    let env = env_with(&decl);
    let plan =
        plan_clean_origin_body(&env, name).unwrap_or_else(|e| panic!("`{decl}` must plan: {e:?}"));
    let f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
        .unwrap_or_else(|e| panic!("`{decl}` must emit: {e}"));

    let reflected =
        reflect_function(&f, bits).unwrap_or_else(|e| panic!("`{decl}` must reflect: {e:?}"));

    let declared = env
        .get_const(&Name::from_string(name))
        .and_then(|info| info.value.clone())
        .unwrap_or_else(|| panic!("the declaration must have a value"));

    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&reflected, &declared),
        "SYMBOLIC DISAGREEMENT for `{name}` at {carrier}: the term reflected from the emitted \
         TrustIR is not definitionally equal to the Clean declaration. Unlike the pointwise \
         and exhaustive gates this is a statement about ALL inputs at this width.\n  \
         decl:      {decl}\n  reflected: {reflected:?}\n  declared:  {declared:?}"
    );
}

#[test]
fn reflection_agrees_with_the_kernel_at_every_admitted_width() {
    for bits in [8u32, 16, 32, 64] {
        kernel_accepts_reflection("def ident (a : {C}) : {C} := a", "ident", bits);
        kernel_accepts_reflection("def seven (a : {C}) : {C} := 7", "seven", bits);
        kernel_accepts_reflection("def sum (a : {C}) (b : {C}) : {C} := a + b", "sum", bits);
        kernel_accepts_reflection("def diff (a : {C}) (b : {C}) : {C} := a - b", "diff", bits);
        kernel_accepts_reflection("def prod (a : {C}) (b : {C}) : {C} := a * b", "prod", bits);
        kernel_accepts_reflection(
            "def comp (a : {C}) (b : {C}) : {C} := (a + b) * a",
            "comp",
            bits,
        );
    }
}

/// **The gate is not vacuous.** A reflection that is NOT the declaration must be
/// rejected, or every row above proves nothing.
///
/// The wrong term is inside the same fragment and well-typed — `a - b` reflected
/// against a declaration of `a + b` — so the rejection is about meaning, not
/// about a malformed term.
#[test]
fn the_kernel_rejects_a_reflection_that_is_not_the_declaration() {
    for bits in [8u32, 64] {
        let carrier = carrier_name(bits).expect("admitted carrier");
        let decl = format!("def sum (a : {carrier}) (b : {carrier}) : {carrier} := a + b");
        let env = env_with(&decl);
        let declared = env
            .get_const(&Name::from_string("sum"))
            .and_then(|info| info.value.clone())
            .expect("declaration value");

        let carrier_ty = Expr::const_(Name::from_string(&carrier), vec![]);
        let wrong = Expr::lam(
            BinderData::default(),
            carrier_ty.clone(),
            Expr::lam(
                BinderData::default(),
                carrier_ty,
                carrier_binop(&carrier, "sub", Expr::bvar(1), Expr::bvar(0)),
            ),
        );

        let tc = TypeChecker::new(&env);
        assert!(
            !tc.is_def_eq(&wrong, &declared),
            "{carrier}: the kernel accepted `a - b` as definitionally equal to `a + b`. If that \
             holds, every reflection row in this file is vacuous."
        );
    }
}

/// The refusals are real, not decoration: a comparison this reflector has no
/// canonical Clean instance name for must REFUSE rather than be approximated
/// into something the kernel would then bless.
#[test]
fn an_unspelled_comparison_refuses_rather_than_being_approximated() {
    // `Eq` has a different instance shape (`DecidableEq`), and guessing at it
    // would be exactly the "invent proof-relevant structure" move this gate
    // exists to avoid. It refuses BY NAME.
    let f =
        Function::new(FuncId::new(0), "unused", FuncTyId::new(0), trust_ir::value::BlockId::new(0));
    assert!(matches!(
        reflect_function(&f, 8),
        Err(ReflectRefusal::NotStraightLine { .. }) | Err(ReflectRefusal::UnspelledInst { .. })
    ));
}

/// A `Select` body now REFLECTS, and the kernel must accept it at every width.
///
/// This is the shape the reflector previously refused. The `Decidable` instance
/// is CITED (`instDecidableUInt8Lt`), never built -- see the note on the
/// `Inst::Select` arm.
#[test]
fn a_select_body_reflects_and_the_kernel_agrees() {
    for bits in [8u32, 16, 32, 64] {
        kernel_accepts_reflection(
            "def minu (a : {C}) (b : {C}) : {C} := if a < b then a else b",
            "minu",
            bits,
        );
    }
}

/// Non-vacuity for the select lane specifically: a reflection with the ARMS
/// SWAPPED must be rejected, or the select rows above prove nothing.
#[test]
fn the_kernel_rejects_a_select_reflection_with_swapped_arms() {
    let decl = "def minu (a : UInt8) (b : UInt8) : UInt8 := if a < b then a else b";
    let env = env_with(decl);
    let declared = env
        .get_const(&Name::from_string("minu"))
        .and_then(|info| info.value.clone())
        .expect("declaration value");

    let carrier_ty = Expr::const_(Name::from_string("UInt8"), vec![]);
    let a = Expr::bvar(1);
    let b = Expr::bvar(0);
    let prop = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("LT.lt"), vec![Level::Zero]),
                    carrier_ty.clone(),
                ),
                Expr::const_(Name::from_string("instLTUInt8"), vec![]),
            ),
            a.clone(),
        ),
        b.clone(),
    );
    let inst = Expr::app(
        Expr::app(Expr::const_(Name::from_string("instDecidableUInt8Lt"), vec![]), a.clone()),
        b.clone(),
    );
    // SWAPPED: else-arm first.
    let swapped = Expr::lam(
        BinderData::default(),
        carrier_ty.clone(),
        Expr::lam(
            BinderData::default(),
            carrier_ty.clone(),
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("ite"),
                                    vec![Level::succ(Level::Zero)],
                                ),
                                carrier_ty,
                            ),
                            prop,
                        ),
                        inst,
                    ),
                    b,
                ),
                a,
            ),
        ),
    );

    let tc = TypeChecker::new(&env);
    assert!(
        !tc.is_def_eq(&swapped, &declared),
        "the kernel accepted a select reflection with the arms SWAPPED as definitionally equal \
         to `if a < b then a else b`. If that holds, every select row here is vacuous."
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// INDEPENDENCE, MEASURED RATHER THAN ASSUMED
// ─────────────────────────────────────────────────────────────────────────────
//
// The caveat at the top of this file is real and stays: this reflector is
// co-authored with the emitter, so it cannot claim the MIR lane's independence.
// But "co-authored" has been doing too much work as a blanket disclaimer. The
// SPECIFIC hazard it names is checkable, and leaving it unchecked is a choice.
//
// The hazard: if the reflector were a trivial inverse of the emitter -- or worse,
// effectively a constant function that rebuilds the declaration regardless of
// what it was handed -- then it would accept ANY emitted body, and every
// agreement row above would be vacuous. A symmetric error would cancel.
//
// That is falsifiable. Mutate the EMITTED BODY (not the emitter source: the
// mutation is applied to the `Function` the emitter actually produced), reflect
// the mutation, and require the kernel to REJECT it. Each mutation below is a
// bug the emitter could plausibly have: a swapped select arm, a wrong operator,
// swapped operands on a non-commutative op, a shifted constant, a widened
// comparison.
//
// What this establishes: the reflector is sensitive to the emitted structure,
// so the round trip does NOT collapse. What it does NOT establish: independence.
// A mutation that this reflector inverts in exactly the same wrong way would
// still be invisible, and only a reflector written by someone who has not read
// this emitter closes that. This bounds the residual risk; it does not remove it.

/// Apply `mutate` to the emitted body and require the KERNEL to reject the
/// reflection. A mutation the kernel still accepts is a hole in the gate.
fn mutation_is_rejected(
    decl_tpl: &str,
    name: &str,
    bits: u32,
    label: &str,
    mutate: impl Fn(&mut Function),
) {
    let carrier = carrier_name(bits).expect("admitted carrier");
    let decl = decl_tpl.replace("{C}", &carrier);
    let env = env_with(&decl);
    let plan = plan_clean_origin_body(&env, name).expect("plans");
    let mut f = emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0)).expect("emits");

    // Sanity: the UNMUTATED body must be accepted, or the mutation proves nothing.
    let clean_reflect = reflect_function(&f, bits).expect("the pristine body must reflect");
    let declared = env
        .get_const(&Name::from_string(name))
        .and_then(|info| info.value.clone())
        .expect("declaration value");
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&clean_reflect, &declared),
        "{label}: the PRISTINE body must be accepted before a mutation means anything",
    );

    mutate(&mut f);

    // A mutation may make the body unreflectable -- that is also a rejection,
    // and an honest one. What must NOT happen is the kernel ACCEPTING it.
    if let Ok(mutated) = reflect_function(&f, bits) {
        assert!(
            !tc.is_def_eq(&mutated, &declared),
            "MUTATION SURVIVED ({label}, {carrier}): the kernel accepted a reflection of a \
             DELIBERATELY BROKEN emitted body as definitionally equal to `{decl}`. That means \
             the reflector is not sensitive to the emitted structure here, and the agreement \
             rows in this file are vacuous for this shape.\n  mutated: {mutated:?}"
        );
    }
}

#[test]
fn a_swapped_select_arm_in_the_emitted_body_is_rejected() {
    for bits in [8u32, 64] {
        mutation_is_rejected(
            "def minu (a : {C}) (b : {C}) : {C} := if a < b then a else b",
            "minu",
            bits,
            "swapped select arms",
            |f| {
                for node in &mut f.blocks[0].body {
                    if let Inst::Select { then_val, else_val, .. } = &mut node.inst {
                        std::mem::swap(then_val, else_val);
                    }
                }
            },
        );
    }
}

#[test]
fn a_wrong_arithmetic_operator_in_the_emitted_body_is_rejected() {
    for bits in [8u32, 64] {
        mutation_is_rejected(
            "def sum (a : {C}) (b : {C}) : {C} := a + b",
            "sum",
            bits,
            "Add -> Sub",
            |f| {
                for node in &mut f.blocks[0].body {
                    if let Inst::BinOp { op, .. } = &mut node.inst {
                        if *op == BinOp::Add {
                            *op = BinOp::Sub;
                        }
                    }
                }
            },
        );
    }
}

#[test]
fn swapped_operands_on_a_non_commutative_op_are_rejected() {
    for bits in [8u32, 64] {
        mutation_is_rejected(
            "def diff (a : {C}) (b : {C}) : {C} := a - b",
            "diff",
            bits,
            "swapped Sub operands",
            |f| {
                for node in &mut f.blocks[0].body {
                    if let Inst::BinOp { op, lhs, rhs, .. } = &mut node.inst {
                        if *op == BinOp::Sub {
                            std::mem::swap(lhs, rhs);
                        }
                    }
                }
            },
        );
    }
}

#[test]
fn a_shifted_constant_in_the_emitted_body_is_rejected() {
    for bits in [8u32, 64] {
        mutation_is_rejected(
            "def seven (a : {C}) : {C} := 7",
            "seven",
            bits,
            "constant 7 -> 8",
            |f| {
                for node in &mut f.blocks[0].body {
                    if let Inst::Const { value: Constant::Int(n), .. } = &mut node.inst {
                        *n += 1;
                    }
                }
            },
        );
    }
}

/// The comparison boundary: `<` widened to `<=` changes the function at exactly
/// one point of the domain (`a == b`). A gate that misses this misses off-by-one
/// predicates, which is the single most common comparison bug.
#[test]
fn a_widened_comparison_in_the_emitted_body_is_rejected() {
    for bits in [8u32, 64] {
        mutation_is_rejected(
            "def minu (a : {C}) (b : {C}) : {C} := if a < b then a else b",
            "minu",
            bits,
            "Ult -> Ule",
            |f| {
                for node in &mut f.blocks[0].body {
                    if let Inst::ICmp { op, .. } = &mut node.inst {
                        if *op == ICmpOp::Ult {
                            *op = ICmpOp::Ule;
                        }
                    }
                }
            },
        );
    }
}
