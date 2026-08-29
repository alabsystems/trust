// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0 or the MIT license.

//! The Clean -> TrustIR lane, driven from REAL kernel-checked Clean source.
//!
//! There is deliberately no way to hand-build a [`CleanOriginPlan`]: its fields
//! are private and `plan_clean_origin_body` is the only constructor, because a
//! plan must rest on a kernel verdict. So these tests do what the production
//! lane does — elaborate actual `clean { … }` source through a real
//! `CleanIslandSession`, kernel-check it, plan it, and only then emit.
//!
//! That is the point: a test that fabricated a plan would prove the emitter
//! maps a struct to a struct. These prove that Clean SOURCE reaches TrustIR.

use clean_kernel::Environment;
use trust_clean_ir::{CleanIrRefusal, emit_clean_origin_function, trust_ir_func_ty};
use trust_clean_origin::plan_clean_origin_body;
use trust_ir::inst::{BinOp, ICmpOp, Inst};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{Constant, Function};

/// Kernel-check one Clean declaration and hand back the environment.
///
/// Mirrors `trust-clean-origin`'s own control-test harness, deliberately: if
/// the island does not kernel-check, no plan exists and there is nothing for
/// this crate to be tested against.
fn env_with(decl: &str) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[decl]);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn emit(decl: &str, name: &str) -> Result<Function, CleanIrRefusal> {
    let env = env_with(decl);
    let plan = plan_clean_origin_body(&env, name).expect("the declaration must plan");
    emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
}

/// A projection: `fun a b => a`. The whole point of the lane — Clean source in,
/// TrustIR out.
#[test]
fn clean_projection_reaches_trust_ir() {
    let f = emit("def pick (a : UInt64) (b : UInt64) : UInt64 := a", "pick")
        .expect("a projection is spelled by this producer");

    assert_eq!(f.name, "pick");
    assert_eq!(f.entry, BlockId::new(0));
    assert_eq!(f.blocks.len(), 1, "a projection is one block");

    let block = &f.blocks[0];
    assert_eq!(
        block.params,
        vec![(ValueId::new(0), Ty::U64), (ValueId::new(1), Ty::U64)],
        "block parameters are the source parameters, in SOURCE order"
    );

    match &block.body[..] {
        [node] => match &node.inst {
            Inst::Return { values } => assert_eq!(
                values,
                &vec![ValueId::new(0)],
                "`fun a b => a` returns source parameter 0. Returning 1 here is the de Bruijn \
                 inversion mistake this lane can make: under n binders, source parameter i is \
                 BVar(n-1-i), and the planner has ALREADY resolved that -- so a producer that \
                 inverts again silently returns the wrong argument."
            ),
            other => panic!("expected a return, got {other:?}"),
        },
        other => panic!("expected exactly one instruction, got {}", other.len()),
    }
}

/// The other projection: `fun a b => b`. Pins the index rather than letting a
/// producer that always returns parameter 0 pass the test above.
#[test]
fn clean_projection_of_the_second_parameter_is_not_the_first() {
    let f = emit("def second (a : UInt64) (b : UInt64) : UInt64 := b", "second").expect("plans");
    let Inst::Return { values } = &f.blocks[0].body[0].inst else { panic!("expected a return") };
    assert_eq!(values, &vec![ValueId::new(1)], "`fun a b => b` is source parameter 1");
}

/// Width is read from the carrier signature, not assumed to be 64.
#[test]
fn clean_carrier_width_selects_the_trust_ir_type() {
    for (decl, name, expected) in [
        ("def w8 (a : UInt8) : UInt8 := a", "w8", Ty::U8),
        ("def w16 (a : UInt16) : UInt16 := a", "w16", Ty::U16),
        ("def w32 (a : UInt32) : UInt32 := a", "w32", Ty::U32),
        ("def w64 (a : UInt64) : UInt64 := a", "w64", Ty::U64),
    ] {
        let f = emit(decl, name).expect("plans");
        assert_eq!(
            f.blocks[0].params,
            vec![(ValueId::new(0), expected.clone())],
            "{name}: the TrustIR type comes from the carrier, so a width change must show here"
        );
    }
}

/// A constant body: `fun _ => 7`.
#[test]
fn clean_constant_reaches_trust_ir() {
    let f = emit("def seven (a : UInt64) : UInt64 := 7", "seven").expect("plans");
    let block = &f.blocks[0];
    assert_eq!(block.body.len(), 2, "a constant is materialize-then-return");

    match &block.body[0].inst {
        Inst::Const { ty, value } => {
            assert_eq!(ty, &Ty::U64);
            match value {
                Constant::Int(v) => assert_eq!(*v, 7),
                other => {
                    panic!("7 is representable in i128, so canonical spelling is Int: {other:?}")
                }
            }
        }
        other => panic!("expected a const, got {other:?}"),
    }

    let konst = block.body[0].results[0];
    let Inst::Return { values } = &block.body[1].inst else { panic!("expected a return") };
    assert_eq!(values, &vec![konst], "the returned value is the materialized constant");
}

/// The function type is derived from the signature and is available without
/// emitting a body — a caller must be able to register the type first.
#[test]
fn func_ty_comes_from_the_carrier_signature() {
    let env = env_with("def pick (a : UInt64) (b : UInt32) : UInt64 := a");
    let plan = plan_clean_origin_body(&env, "pick").expect("plans");
    let ft = trust_ir_func_ty(plan.signature()).expect("both carriers are machine widths");
    assert_eq!(ft.params, vec![Ty::U64, Ty::U32]);
    assert_eq!(ft.returns, vec![Ty::U64]);
    assert!(!ft.is_vararg);
}

/// An unbounded Clean type has no carrier, so it must REFUSE rather than pick a
/// width. Silently choosing 64 here is exactly the wrong-binary outcome: `Nat`
/// is unbounded and any fixed width can wrap.
#[test]
fn unbounded_clean_types_are_refused_not_guessed() {
    let env = env_with("def idn (a : Nat) : Nat := a");
    // A `Nat` declaration has no total carrier, so it may not even plan. If it
    // does plan, this crate must still refuse it -- either way no TrustIR
    // function comes back, which is the property under test.
    let refusal = match plan_clean_origin_body(&env, "idn") {
        Err(_) => return,
        Ok(plan) => emit_clean_origin_function(&plan, FuncId::new(0), FuncTyId::new(0))
            .expect_err("Nat has no fixed-width carrier; emitting one would be a wrong binary"),
    };
    assert!(matches!(refusal, CleanIrRefusal::CarrierHasNoTrustIrType { .. }), "got {refusal:?}");
}

/// A refusal must carry the fix, with options (v7/D3). An "unsupported" with no
/// next step is a defect, so this is asserted rather than reviewed.
#[test]
fn refusals_name_the_construct_and_offer_options() {
    let refusal = CleanIrRefusal::ShapeNotYetSpelled { shape: "WrappingBinOp" };
    let text = refusal.to_string();
    assert!(text.contains("WrappingBinOp"), "the refusal must name the construct: {text}");
    assert!(text.contains("Options:"), "the refusal must offer options: {text}");
    assert!(
        text.contains("MIR lane"),
        "the options must include the lane that DOES handle every recognised shape: {text}"
    );
}

/// A single wrapping op: `fun a b => a + b`.
///
/// TrustIR's `BinOp::Add` IS the wrapping one — its reference interpreter
/// defines it as `raw.wrapping_add` — which is exactly Clean `UInt64`
/// semantics. If TrustIR ever gains trapping arithmetic, this mapping stops
/// being faithful and this test is where that shows.
#[test]
fn clean_wrapping_add_reaches_trust_ir() {
    let f = emit("def sum (a : UInt64) (b : UInt64) : UInt64 := a + b", "sum").expect("plans");
    let block = &f.blocks[0];
    assert_eq!(block.body.len(), 2, "one binop, one return");

    match &block.body[0].inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            assert_eq!(*op, BinOp::Add);
            assert_eq!(ty, &Ty::U64);
            assert_eq!(*lhs, ValueId::new(0), "left operand is source parameter 0");
            assert_eq!(*rhs, ValueId::new(1), "right operand is source parameter 1");
        }
        other => panic!("expected a binop, got {other:?}"),
    }
    let out = block.body[0].results[0];
    let Inst::Return { values } = &block.body[1].inst else { panic!("expected a return") };
    assert_eq!(values, &vec![out]);
}

/// Subtraction is not silently emitted as addition, and operand ORDER is
/// preserved — `a - b` and `b - a` differ, so a producer that sorts or swaps
/// operands is caught here rather than at runtime.
#[test]
fn clean_wrapping_sub_keeps_operand_order() {
    let f = emit("def diff (a : UInt64) (b : UInt64) : UInt64 := a - b", "diff").expect("plans");
    let Inst::BinOp { op, lhs, rhs, .. } = &f.blocks[0].body[0].inst else {
        panic!("expected a binop")
    };
    assert_eq!(*op, BinOp::Sub, "`-` must not be emitted as `+`");
    assert_eq!((*lhs, *rhs), (ValueId::new(0), ValueId::new(1)), "`a - b`, not `b - a`");
}

/// A literal operand is materialized as a `Const` before use.
#[test]
fn clean_literal_operand_is_materialized() {
    let f = emit("def inc (a : UInt64) : UInt64 := a + 1", "inc").expect("plans");
    let block = &f.blocks[0];
    match &block.body[0].inst {
        Inst::Const { ty, value } => {
            assert_eq!(ty, &Ty::U64);
            assert!(matches!(value, Constant::Int(1)), "got {value:?}");
        }
        other => panic!("expected the literal to be materialized first, got {other:?}"),
    }
    let konst = block.body[0].results[0];
    let Inst::BinOp { lhs, rhs, .. } = &block.body[1].inst else { panic!("expected a binop") };
    assert_eq!(*lhs, ValueId::new(0), "the parameter is the block parameter");
    assert_eq!(*rhs, konst, "the literal is the value just materialized");
}

/// A nested composition emits one binop per tree node in post-order, through
/// FRESH values. A producer that reused a temporary would still typecheck, so
/// distinctness is asserted directly.
#[test]
fn clean_composed_expression_emits_post_order_through_fresh_values() {
    let f =
        emit("def comp (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a", "comp").expect("plans");
    let block = &f.blocks[0];

    let binops: Vec<_> = block
        .body
        .iter()
        .filter_map(|n| match &n.inst {
            Inst::BinOp { op, .. } => Some(*op),
            _ => None,
        })
        .collect();
    assert_eq!(binops, vec![BinOp::Add, BinOp::Mul], "post-order: the inner `+` before the `*`");

    let mut produced: Vec<ValueId> = block.body.iter().flat_map(|n| n.results.clone()).collect();
    let count = produced.len();
    produced.sort_by_key(|v| format!("{v}"));
    produced.dedup();
    assert_eq!(produced.len(), count, "every emitted value must be distinct");

    // The `*` consumes the `+`'s result on the left and parameter `a` on the right.
    let add_out = block.body[0].results[0];
    let Inst::BinOp { lhs, rhs, .. } = &block.body[1].inst else { panic!("expected the mul") };
    assert_eq!(*lhs, add_out, "`(a + b) * a` multiplies the SUM, not a parameter");
    assert_eq!(*rhs, ValueId::new(0), "the right factor is `a`");
}

/// `fun a b => if a < b then a else b`.
///
/// TrustIR has a branchless `Inst::Select`, so this is ICmp-then-Select in one
/// block, where the MIR lane emits a four-block diamond. Same value, different
/// idiom — which is exactly why a future TrustIR-side gate must compare
/// semantics rather than block structure.
#[test]
fn clean_select_reaches_trust_ir() {
    let f = emit("def minu (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b", "minu")
        .expect("plans");
    let block = &f.blocks[0];
    assert_eq!(f.blocks.len(), 1, "branchless select is one block");

    let Inst::ICmp { op, ty, lhs, rhs } = &block.body[0].inst else { panic!("expected an icmp") };
    assert_eq!(
        *op,
        ICmpOp::Ult,
        "an unsigned carrier compares UNSIGNED; Slt would reinterpret \
                                  the high bit and silently give a wrong answer"
    );
    assert_eq!(ty, &Ty::U64);
    assert_eq!((*lhs, *rhs), (ValueId::new(0), ValueId::new(1)), "`a < b`, in that order");

    let cond = block.body[0].results[0];
    let Inst::Select { cond: c, then_val, else_val, .. } = &block.body[1].inst else {
        panic!("expected a select")
    };
    assert_eq!(*c, cond);
    assert_eq!(*then_val, ValueId::new(0), "the THEN arm is `a`");
    assert_eq!(*else_val, ValueId::new(1), "the ELSE arm is `b`");
}

/// `<=` is not silently emitted as `<`. Off-by-one in a comparison predicate is
/// the classic silent miscompile, so each predicate is pinned.
#[test]
fn clean_select_predicates_are_distinct() {
    for (decl, name, expected) in [
        ("def l (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b", "l", ICmpOp::Ult),
        ("def le (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b", "le", ICmpOp::Ule),
    ] {
        let f = emit(decl, name).expect("plans");
        let Inst::ICmp { op, .. } = &f.blocks[0].body[0].inst else { panic!("expected an icmp") };
        assert_eq!(*op, expected, "{name}: predicate must survive exactly");
    }
}

/// A constant arm is materialized, and the arms are not swapped.
#[test]
fn clean_select_with_const_arm_keeps_arm_order() {
    let f =
        emit("def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0", "clampz")
            .expect("plans");
    let block = &f.blocks[0];
    let Inst::Select { then_val, else_val, .. } = &block
        .body
        .iter()
        .find_map(|n| match &n.inst {
            Inst::Select { .. } => Some(&n.inst),
            _ => None,
        })
        .expect("a select")
    else {
        unreachable!()
    };
    assert_eq!(*then_val, ValueId::new(0), "THEN is `a`");
    // The ELSE arm is the materialized 0, not a parameter.
    let zero = block
        .body
        .iter()
        .find(|n| matches!(&n.inst, Inst::Const { value: Constant::Int(0), .. }))
        .expect("the 0 arm must be materialized")
        .results[0];
    assert_eq!(*else_val, zero, "ELSE is the constant 0, and the arms are not swapped");
}

/// `/` and `%` are total only at a nonzero divisor. This producer has no
/// divisor evidence, so it must REFUSE rather than emit a partial operation
/// into the one lane that produces a value.
#[test]
fn division_without_divisor_evidence_is_refused() {
    let refusal = CleanIrRefusal::PartialOpWithoutDivisorEvidence { op: "/" };
    let text = refusal.to_string();
    assert!(text.contains("nonzero divisor"), "must name the boundary: {text}");
    assert!(text.contains("Options:"), "must offer options: {text}");
    assert!(
        text.contains("MIR lane"),
        "must point at the lane that carries the accounting: {text}"
    );
}

/// The two recursion shapes are refused for a CARRIER reason, not because the
/// arm is unwritten.
///
/// `RecBodyExpr`'s nodes are `trust_bignum::Nat::{from_u64, add, sub}` — the
/// unbounded bignum — and TrustIR has no `Nat`. Emitting them at a machine
/// width would wrap where Clean does not, which is the same reason
/// `trust_ir_ty` refuses `CleanType::Nat` in a signature. This test exists so
/// that a future contributor reaching for "just use u64 here" reads why not.
#[test]
fn recursion_shapes_refuse_for_a_carrier_reason() {
    for shape in ["StructuralNatRec", "WellFoundedNatRec"] {
        let text = CleanIrRefusal::RecursionAtUnboundedNatCarrier { shape }.to_string();
        assert!(text.contains(shape), "must name the shape: {text}");
        assert!(
            text.contains("unbounded bignum `Nat`"),
            "must give the CARRIER reason, not 'unsupported': {text}"
        );
        assert!(text.contains("WRAP"), "must say what emitting it anyway would do: {text}");
        assert!(text.contains("Options:"), "must offer options: {text}");
        assert!(
            text.contains("trust_bignum::Nat` as a TrustIR type"),
            "must name the concrete work that would close it: {text}"
        );
    }
}

// ─── EXECUTION: the emitted TrustIR is RUN, not just inspected ──────────────
//
// Every test above reads the emitted instruction list. That catches a wrong
// opcode or a swapped operand, but it cannot catch an IR that is malformed in a
// way the shape assertions do not look at — an undefined value, a type that
// does not match its operands, a missing terminator.
//
// These run the emitted function through `trust_ir::interpret`, which is
// TrustIR's OWN reference interpreter and not this crate's code. It is an
// independent oracle in the sense that matters here: it was not written against
// this emitter, and it rejects malformed IR with an error rather than a wrong
// answer.
//
// This is NOT the faithfulness gate. It executes the emitted body at concrete
// inputs and compares against what the Clean declaration means at those inputs;
// it does not put the body back to the CIC kernel. See the crate's GATING
// section. What it does establish is that the IR this crate emits is
// well-formed and computes the stated function — which is the precondition for
// any gate worth writing.

use trust_ir::interpret::{InterpretValue, Interpreter};

/// Emit `decl`, run it on `args` at `u64`, and return the single result.
fn run_u64(decl: &str, name: &str, args: &[u64]) -> u128 {
    let f = emit(decl, name).expect("plans and emits");
    let interp = Interpreter::new();
    let values: Vec<_> = args
        .iter()
        .map(|a| InterpretValue::int(Ty::U64, *a as i128).expect("u64 argument"))
        .collect();
    let outcome = interp
        .execute_function(&f, values)
        .unwrap_or_else(|e| panic!("the emitted TrustIR must execute: {e:?}"));
    assert_eq!(outcome.returns.len(), 1, "these declarations return exactly one value");
    outcome.returns[0].as_int().expect("an integer result").as_unsigned()
}

#[test]
fn emitted_projection_executes_to_the_projected_argument() {
    assert_eq!(run_u64("def pick (a : UInt64) (b : UInt64) : UInt64 := a", "pick", &[7, 9]), 7);
    assert_eq!(run_u64("def snd (a : UInt64) (b : UInt64) : UInt64 := b", "snd", &[7, 9]), 9);
}

#[test]
fn emitted_constant_executes_to_the_numeral() {
    assert_eq!(run_u64("def seven (a : UInt64) : UInt64 := 7", "seven", &[0]), 7);
}

#[test]
fn emitted_arithmetic_executes_and_wraps_like_clean() {
    let add = "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b";
    assert_eq!(run_u64(add, "sum", &[2, 3]), 5);
    // Clean `UInt64` wraps at 2^64 and so must the emitted TrustIR. If TrustIR
    // arithmetic ever became trapping or saturating, THIS is the assertion that
    // fails -- which is the whole reason `BinOp::Add` was checked to be the
    // wrapping one before the mapping was written.
    assert_eq!(run_u64(add, "sum", &[u64::MAX, 1]), 0, "must wrap, not trap or saturate");

    let sub = "def diff (a : UInt64) (b : UInt64) : UInt64 := a - b";
    assert_eq!(run_u64(sub, "diff", &[9, 4]), 5);
    assert_eq!(run_u64(sub, "diff", &[0, 1]), u128::from(u64::MAX), "wrapping sub");
}

#[test]
fn emitted_composed_expression_executes_with_the_right_associativity() {
    // (a + b) * a  at a=3, b=4  ==  (3+4)*3 == 21. A producer that emitted
    // a + (b * a) would give 15, so this pins the tree, not just the opcodes.
    assert_eq!(
        run_u64("def comp (a : UInt64) (b : UInt64) : UInt64 := (a + b) * a", "comp", &[3, 4]),
        21
    );
}

#[test]
fn emitted_select_executes_both_branches() {
    let minu = "def minu (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b";
    assert_eq!(run_u64(minu, "minu", &[3, 9]), 3, "the THEN branch");
    assert_eq!(run_u64(minu, "minu", &[9, 3]), 3, "the ELSE branch");
    assert_eq!(run_u64(minu, "minu", &[5, 5]), 5, "the boundary: `<` is strict");
}

/// The unsigned predicate, executed. A signed `Slt` would read `u64::MAX` as
/// -1 and return it as the minimum; unsigned it is the maximum. This is the
/// wrong-answer this mapping could silently produce, so it is executed rather
/// than only inspected.
#[test]
fn emitted_comparison_is_unsigned_at_the_high_bit() {
    let minu = "def minu (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b";
    assert_eq!(
        run_u64(minu, "minu", &[u64::MAX, 1]),
        1,
        "unsigned: u64::MAX is the LARGEST value, so the min of (MAX, 1) is 1. A signed \
         predicate would read MAX as -1 and answer MAX."
    );
}
