// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **§6f LANDING 2 — the probe battery, measured BEFORE the table moved.**
//!
//! Landing 1 left a ranked MISS list. This file takes it in order and measures
//! each candidate at the kernel, on the fast lane, under landing 1's discipline:
//!
//! * **side A** — the Clean `def`, inserted through the FULL kernel check
//!   (`Environment::add_decl`), in BOTH the carrier spelling and the SURFACE
//!   spelling a real island elaborates to. A malformed hand-built term fails
//!   loudly at `define` rather than measuring the wrong thing.
//! * **side B** — the reflection of the admissible-body form the emitter would
//!   produce, through the FROZEN `trust_spec_elab` producers, minted into a
//!   CLONE of the environment exactly as `emit.rs` does.
//! * **the verdict** — [`check_faithful`], at the carrier.
//! * **a paired MUTATION** — one construct wrong, which must be REFUSED. An
//!   ADMIT with no refused mutation measures a gate that admits everything.
//!
//! # What was measured, and what landed
//!
//! | ranked MISS | measured verdict | landed? |
//! |---|---|---|
//! | 1. nullary `ConstantUint` | **ADMIT** both spellings, through `admit_expr_function` at ZERO parameters; wrong-value and width-skew mutants REFUSED | **YES** — a second side-A route onto the existing `uint.lit` row |
//! | 1b. constant behind IGNORED binders (`fun a => 6`) | **ADMIT** both spellings at arity 1 and 2; wrong-value and ARITY mutants REFUSED | **YES** — same row, same route |
//! | 2. constant `ite` ARM | side A kernel-checks; **NO REFLECTION PATH** — `admit_select_function`'s arms are `usize` parameter indices, and the emitted const-arm diamond does not recognize | no |
//! | 3. COMPUTED `ite` condition | side A kernel-checks; **NO REFLECTION PATH** — `admit_select_function`'s comparison operands are `usize` parameter indices, and the computed-condition diamond does not recognize | no |
//! | 4. numeral on the comparison's LEFT | already measured by `probe_i2_select_literal_on_the_left_refuses_today` | no |
//! | 5. `{C}.div` / `{C}.mod` | already measured by `probe_i` — side A is UNSTATABLE in the pinned clean prelude | no |
//! | 6. `Nat.rec` wrapped to a machine width | already measured by `r1_equation_probes::e2` — the open equations are not definitional | no |
//! | 7/8. two-parameter `WellFounded.fix`, pair-valued recursion | already measured by `recursion_boundary_probes::gcd` / `r1_equation_probes::e4` | no |
//! | NEW: a nullary constant at the `Nat` bignum carrier | side A kernel-checks and `Domain::Nat` CAN mint side B — but **side B's READER has no arm**, and giving it one widens the E6 kernel-import direction | no — recorded as a measured MISS |
//!
//! # THE FINDING THAT PICKED THE ROW (candidate 1)
//!
//! `fragment_widening_probes::probe_e3` located the constant lane's defect
//! **upstream of definitional equality**, in the arity-erasing
//! `ConstantUint -> admit_constant_function` ROUTING: the recognizer reports the
//! same `ConstantUint` for a nullary body and for a body behind ignored binders,
//! and `admit_constant_function` mints a NULLARY term, so a unary side A met a
//! nullary side B and the kernel correctly refused. Its route-2 note is the
//! diagnosis, verbatim: *"The gap is the clean_island ROUTING (ConstantUint ->
//! nullary mint), not the producers."*
//!
//! [`l2_p1_the_two_routes_mint_the_same_nullary_term`] closes that: at ZERO
//! parameters `admit_expr_function` and `admit_constant_function` mint the
//! **same kernel term**, so routing the constant through the expr producer is a
//! routing change and not a semantic one — and the expr producer takes the arity
//! from the EMITTED BODY, which is what makes one route serve both arities.
//!
//! [`l2_p3_the_arity_erasure_is_caught_in_both_directions`] is the paired
//! hazard control: the erasure is REAL and stays real — the row does not fix it
//! and must not pretend to. What binds the arity is `admit_lowering`'s
//! `arg_count == signature.arity()` check plus the emitted body's own parameter
//! list, both of which are side-B facts. This probe measures both wrong
//! pairings and requires both to be refused by the kernel.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Level, Name};
use trust_clean_carrier::{Carrier, carrier_at};
use trust_clean_origin::{
    CleanOriginShape, EmitRefusal, GateRefusal, check_faithful, plan_clean_origin_body,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{AdmissibleBody, recognize_admissible_body};
use trust_types::{
    BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

// ───────────────────────────── side A helpers ─────────────────────────────
//
// Transplanted from `fragment_widening_probes.rs`, deliberately rather than
// shared: a test crate cannot reach another integration test's helpers, and a
// probe battery that depended on a helper crate would acquire a place where the
// side-A construction could be changed for every probe at once.

fn uint_ty(bits: u32) -> Expr {
    Expr::const_(Name::from_string(&format!("UInt{bits}")), vec![])
}

fn uint64() -> Expr {
    uint_ty(64)
}

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn carrier_of(bits: u32) -> Carrier {
    carrier_at(&uint_ty(bits), &Ty::Int { width: bits, signed: false })
        .expect("UIntN -> uN is the exact-width carrier and must be granted")
}

fn u64_carrier() -> Carrier {
    carrier_of(64)
}

fn env_uint() -> Environment {
    let mut env = Environment::new();
    env.init_uint_arith()
        .expect("UInt8/16/32/64 plus wrapping add/sub/mul + HAdd/HSub/HMul + OfNat must init");
    env
}

/// Insert `def name : type_ := value` through the FULL kernel check.
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

/// `UInt{bits} -> … -> UInt{bits}` with `n` arrows.
fn uint_arrows(bits: u32, n: usize) -> Expr {
    (0..n).fold(uint_ty(bits), |acc, _| Expr::arrow(uint_ty(bits), acc))
}

fn u64_arrows(n: usize) -> Expr {
    uint_arrows(64, n)
}

/// The carrier spelling of a numeral: `UInt{bits}.ofNat n`.
fn carrier_lit(bits: u32, n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(&format!("UInt{bits}.ofNat")), vec![]),
        Expr::nat_lit(n),
    )
}

/// The SURFACE spelling of a numeral at `UInt{bits}` — what a real island's
/// literal elaborates to: `OfNat.ofNat UInt{bits} n (instOfNatUInt{bits} n)`.
fn surface_lit(bits: u32, n: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            uint_ty(bits),
            Expr::nat_lit(n),
            Expr::app(
                Expr::const_(Name::from_string(&format!("instOfNatUInt{bits}")), vec![]),
                Expr::nat_lit(n),
            ),
        ],
    )
}

/// `fun _ … _ => <numeral>` — the constant under `arity` IGNORED binders. At
/// arity 0 it is the bare numeral, which is exactly the point: one builder, one
/// side-A shape, the arity varying.
fn constant_body(bits: u32, arity: usize, numeral: Expr) -> Expr {
    (0..arity).fold(numeral, |acc, _| Expr::lam(BinderInfo::Default, uint_ty(bits), acc))
}

// ─────────────── the future emitter's MIR, as extracted ───────────────

fn locals_at(bits: u32, n: usize) -> Vec<LocalDecl> {
    (0..n)
        .map(|index| LocalDecl { index, ty: Ty::Int { width: bits, signed: false }, name: None })
        .collect()
}

fn vf(arg_count: usize, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: "probe".into(),
        def_path: "probe::probe".into(),
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
    }
}

/// `fn f(…) -> u{bits} { V }` as MIR: `_0 = const V; return`. The WHOLE-BODY
/// inline scalar — the realization `uint.lit` declares, in the position landing
/// 1 never put it in.
fn emitted_const(bits: u32, arg_count: usize, value: u128) -> VerifiableFunction {
    vf(
        arg_count,
        locals_at(bits, arg_count + 1),
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(value, bits))),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Return,
        }],
    )
}

// ─────────────────────────── side B reflection ───────────────────────────

/// Mint side B into a CLONE of `env` (mirroring `emit.rs`: a check must not
/// mutate the environment it checks) and return the reflected body term.
fn reflect(
    env: &Environment,
    mint: impl FnOnce(&mut Environment, &str) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let name = "probe_landing2_reflection";
    mint(&mut scratch, name)?;
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .ok_or_else(|| "the reflected definition carries no value".to_owned())
}

/// Side B through the EXPR producer, over `n_params` positional names — the
/// route `admit_lowering` uses, with the arity taken from the emitted body.
fn reflect_expr(
    env: &Environment,
    body: &str,
    n_params: usize,
    domain: &Domain,
) -> Result<Expr, String> {
    let names: Vec<String> = (0..n_params).map(|i| format!("p{i}")).collect();
    let name_refs: Vec<&str> = names.iter().map(String::as_str).collect();
    reflect(env, |scratch, name| {
        trust_spec_elab::admit_expr_function(scratch, name, body, &name_refs, domain)
    })
}

fn machine(bits: u32) -> Domain {
    Domain::Machine(match bits {
        8 => MachineUIntWidth::U8,
        16 => MachineUIntWidth::U16,
        32 => MachineUIntWidth::U32,
        64 => MachineUIntWidth::U64,
        other => panic!("{other} is not a machine width this battery measures"),
    })
}

/// Assert the kernel REFUSES `side_b` for `side_a`, naming the mutation. A
/// refusal that passes anonymously measures nothing.
fn refused(env: &Environment, side_a: &str, side_b: &Expr, carrier: &Carrier, what: &str) {
    match check_faithful(env, side_a, side_b, carrier) {
        Ok(value) => panic!(
            "the `{what}` mutant was ADMITTED against `{side_a}` (got {value:?}); a \
             one-construct-wrong side B must be refused, or the ADMITs in this file measure a \
             gate that admits everything"
        ),
        Err(refusal) => assert!(
            matches!(refusal, GateRefusal::Disagreement { .. }),
            "`{what}` vs `{side_a}`: expected a value-level disagreement, got {refusal:?}"
        ),
    }
}

/// The flipped ratchet: the planner reads this def as EXACTLY this shape.
fn assert_plan_shape(env: &Environment, name: &str, expected: CleanOriginShape) {
    let plan = plan_clean_origin_body(env, name)
        .unwrap_or_else(|refusal| panic!("`{name}` must plan: {refusal:?}"));
    assert_eq!(plan.shape(), &expected, "`{name}` planned the WRONG shape");
}

/// Pin that TODAY's planner refuses this def as a capability boundary.
fn assert_plan_refuses_today(env: &Environment, name: &str) {
    let refusal =
        plan_clean_origin_body(env, name).expect_err("this shape has no row yet; planning refuses");
    assert!(
        matches!(refusal, EmitRefusal::NotEmittable { .. }),
        "expected today's capability refusal for `{name}`; got {refusal:?}"
    );
    assert!(!refusal.is_compiler_defect(), "a fragment boundary is not a compiler defect");
}

// ══════════════ L2-P1 — the two producers agree at ZERO parameters ══════════════

/// **The routing measurement that picked candidate 1.**
///
/// probe_e3 diagnosed the constant lane's failure as the arity-erasing
/// `ConstantUint -> admit_constant_function` routing, not defeq. The repair it
/// pointed at is to route the constant through `admit_expr_function`, which
/// takes its arity from the emitted body — but that is only a ROUTING change if
/// the two producers agree where their domains overlap.
///
/// MEASURED: at zero parameters they mint the **same kernel term**. So the row
/// gives up nothing by reflecting through the expr producer, and it gains the
/// arity the constant producer erases.
#[test]
fn l2_p1_the_two_routes_mint_the_same_nullary_term() {
    let env = env_uint();
    for bits in [8u32, 16, 32, 64] {
        let via_constant = reflect(&env, |scratch, name| {
            trust_spec_elab::admit_constant_function(
                scratch,
                name,
                6,
                match bits {
                    8 => MachineUIntWidth::U8,
                    16 => MachineUIntWidth::U16,
                    32 => MachineUIntWidth::U32,
                    _ => MachineUIntWidth::U64,
                },
            )
        })
        .expect("the nullary constant mint reflects");
        let via_expr = reflect_expr(&env, "6", 0, &machine(bits))
            .expect("MEASURED: the expr producer accepts an EMPTY parameter list");
        assert_eq!(
            via_constant, via_expr,
            "at u{bits} the two producers disagree at zero parameters, so routing the \
             constant row through `admit_expr_function` would be a SEMANTIC change and not \
             the routing repair probe_e3 diagnosed"
        );
    }
    eprintln!(
        "PROBE-ROW | nullary const routing     | admit_constant_function == \
         admit_expr_function(&[]) at u8/u16/u32/u64"
    );
}

// ══════════════════ L2-P2 — the nullary constant BODY ══════════════════

/// `def six : UInt64 := 6` in BOTH side-A spellings, against the reflection of
/// the emitted whole-body inline scalar, through the row's route.
///
/// probe_e/probe_e2 already measured the bare kernel comparison ADMIT for this
/// shape through `admit_constant_function` — with NO paired mutation. This probe
/// adds what a row needs: the row's own route, and refused mutants.
#[test]
fn l2_p2_nullary_constant_admits_through_the_row_route() {
    let mut env = env_uint();
    define(&mut env, "six", uint64(), carrier_lit(64, 6));
    define(&mut env, "six_s", uint64(), surface_lit(64, 6));

    // FLIPPED (§6f landing 2): the planner reads a nullary carrier numeral as
    // the exact ConstantUint value, in BOTH numeral spellings. Every assertion
    // below it was green BEFORE this flip — that is what fast-lane-first means
    // and it is the order this file was written in.
    for side_a in ["six", "six_s"] {
        assert_plan_shape(&env, side_a, CleanOriginShape::ConstantUint { value: 6 });
    }

    // The emitted body, read back. The recognizer — written for the E6
    // direction, unmodified — reads the whole-body inline scalar.
    assert_eq!(
        recognize_admissible_body(&emitted_const(64, 0, 6)),
        Some(AdmissibleBody::ConstantUint { value: 6, width_bits: 64 }),
        "the nullary inline-scalar body must read back as ConstantUint"
    );

    // Side B through the FROZEN expr producer, at the arity the emitted body
    // has (ZERO), and at the domain its return type denotes.
    let side_b = reflect_expr(&env, "6", 0, &machine(64)).expect("the nullary rendering reflects");
    for side_a in ["six", "six_s"] {
        check_faithful(&env, side_a, &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
            panic!("MEASURED ADMIT expected against `{side_a}`: {refusal:?}")
        });
    }

    // PAIRED MUTATION: an emitter that baked in the wrong value.
    let wrong = reflect_expr(&env, "7", 0, &machine(64)).expect("the wrong body still reflects");
    for side_a in ["six", "six_s"] {
        refused(&env, side_a, &wrong, &u64_carrier(), "wrong constant (7 for 6)");
    }
    eprintln!(
        "PROBE-ROW | nullary const 6           | side B: yes (expr route, 0 params) | \
         kernel: ADMIT (both spellings); 7-for-6 REFUSED"
    );
}

/// **The WIDTH-SKEW mutation, at both ends.** The row's reflection derives its
/// domain from the EMITTED body's own return type, never from the plan. This
/// measures that a domain skew in either direction is a kernel refusal, which
/// is what makes taking the domain from side B safe.
#[test]
fn l2_p2b_nullary_constant_width_skew_is_refused() {
    let mut env = env_uint();
    define(&mut env, "six64", uint64(), carrier_lit(64, 6));
    define(&mut env, "six8", uint_ty(8), carrier_lit(8, 6));

    // Each width admits against ITS OWN side A…
    for (bits, side_a) in [(64u32, "six64"), (8, "six8")] {
        let side_b = reflect_expr(&env, "6", 0, &machine(bits)).expect("reflects");
        check_faithful(&env, side_a, &side_b, &carrier_of(bits))
            .unwrap_or_else(|refusal| panic!("MEASURED ADMIT expected at u{bits}: {refusal:?}"));
    }
    // …and refuses against the OTHER. `UInt8.ofNat 6` and `UInt64.ofNat 6` are
    // different constants, so a width-skewed reflection cannot be admitted.
    let side_b_8 = reflect_expr(&env, "6", 0, &machine(8)).expect("reflects");
    refused(&env, "six64", &side_b_8, &u64_carrier(), "u8 side B for a u64 declaration");
    let side_b_64 = reflect_expr(&env, "6", 0, &machine(64)).expect("reflects");
    refused(&env, "six8", &side_b_64, &carrier_of(8), "u64 side B for a u8 declaration");
    eprintln!("PROBE-ROW | nullary const width skew  | REFUSED in both directions");
}

// ══════════ L2-P3 — the constant behind IGNORED binders, and the erasure ══════════

/// `def const6 (a : UInt64) : UInt64 := 6` and its 2-ary sibling, both side-A
/// spellings, through the row's route at the arity the EMITTED body has.
///
/// probe_e3 measured route 2's ADMIT at arity 1 already. What is new here is (a)
/// arity 2, (b) the paired value mutation at both arities, and (c) that the
/// PLANNER now reaches it — probe_e3's `assert_plan_refuses_today` is what this
/// landing flips.
#[test]
fn l2_p3_constant_behind_ignored_binders_admits() {
    let mut env = env_uint();
    for arity in [1usize, 2] {
        define(
            &mut env,
            &format!("k{arity}"),
            u64_arrows(arity),
            constant_body(64, arity, carrier_lit(64, 6)),
        );
        define(
            &mut env,
            &format!("k{arity}_s"),
            u64_arrows(arity),
            constant_body(64, arity, surface_lit(64, 6)),
        );
    }

    for arity in [1usize, 2] {
        for side_a in [format!("k{arity}"), format!("k{arity}_s")] {
            assert_plan_shape(&env, &side_a, CleanOriginShape::ConstantUint { value: 6 });
        }

        // The recognizer ERASES the arity: the same `ConstantUint` a nullary
        // body reports. Re-pinned here because it is the hazard the next probe
        // measures the containment of.
        assert_eq!(
            recognize_admissible_body(&emitted_const(64, arity, 6)),
            Some(AdmissibleBody::ConstantUint { value: 6, width_bits: 64 }),
            "the arity is ERASED by the recognizer, at arity {arity}"
        );

        let side_b = reflect_expr(&env, "6", arity, &machine(64)).expect("the rendering reflects");
        for side_a in [format!("k{arity}"), format!("k{arity}_s")] {
            check_faithful(&env, &side_a, &side_b, &u64_carrier()).unwrap_or_else(|refusal| {
                panic!("MEASURED ADMIT expected against `{side_a}`: {refusal:?}")
            });
        }
        let wrong = reflect_expr(&env, "7", arity, &machine(64)).expect("reflects");
        for side_a in [format!("k{arity}"), format!("k{arity}_s")] {
            refused(&env, &side_a, &wrong, &u64_carrier(), "wrong constant (7 for 6)");
        }
    }
    eprintln!(
        "PROBE-ROW | const behind ignored args | side B: yes (expr route, arity from the \
         EMITTED body) | kernel: ADMIT at arity 1 and 2"
    );
}

/// **THE HAZARD CONTROL FOR THE ARITY ERASURE — both directions.**
///
/// The row does NOT fix the erasure and must not pretend to: `ConstantUint`
/// still carries no arity, and `recognize_admissible_body` still reports the
/// same value for `fn() -> u64 {6}` and `fn(u64) -> u64 {6}`. What contains it
/// is that the arity comes from the EMITTED BODY's own parameter list — side B,
/// twice over: `admit_lowering` requires `arg_count == signature.arity()` before
/// any reflection, and the reflection's own lambda count is `arg_count`.
///
/// This probe measures the containment at the KERNEL, which is the layer that
/// cannot be edited into agreement: a nullary side B against a unary side A, and
/// a unary side B against a nullary side A, must BOTH be refused.
#[test]
fn l2_p3b_the_arity_erasure_is_caught_in_both_directions() {
    let mut env = env_uint();
    define(&mut env, "six", uint64(), carrier_lit(64, 6));
    define(&mut env, "k1", u64_arrows(1), constant_body(64, 1, carrier_lit(64, 6)));

    // The erasure itself: one recognized value, two arities.
    assert_eq!(
        recognize_admissible_body(&emitted_const(64, 0, 6)),
        recognize_admissible_body(&emitted_const(64, 1, 6)),
        "if these ever differ the recognizer has gained an arity and this control's premise \
         has changed — re-measure before relying on it"
    );

    let nullary_b = reflect_expr(&env, "6", 0, &machine(64)).expect("reflects");
    let unary_b = reflect_expr(&env, "6", 1, &machine(64)).expect("reflects");

    // Each admits against its OWN arity…
    check_faithful(&env, "six", &nullary_b, &u64_carrier()).expect("nullary vs nullary ADMITs");
    check_faithful(&env, "k1", &unary_b, &u64_carrier()).expect("unary vs unary ADMITs");
    // …and is REFUSED against the other. This is probe_e3's route-1 refusal,
    // re-measured as a standing control rather than as a one-off finding, plus
    // its converse, which probe_e3 never measured.
    refused(&env, "k1", &nullary_b, &u64_carrier(), "nullary side B for a UNARY declaration");
    refused(&env, "six", &unary_b, &u64_carrier(), "unary side B for a NULLARY declaration");
    eprintln!("PROBE-ROW | const arity erasure       | REFUSED in both directions");
}

// ══════════════ L2-P4 — a nullary constant at `Nat`: MEASURED MISS ══════════════

/// **Candidate: the constant row at the bignum carrier. REFUSED — recorded, not
/// added.**
///
/// Side A is statable and `Domain::Nat` CAN mint side B, so this is NOT a
/// kernel-defeq boundary. It is blocked one layer earlier, and in the layer this
/// landing is forbidden to widen casually: **side B's READER has no whole-body
/// bignum-constant arm.** `AdmissibleBody::ConstantUint` is machine-width by
/// construction (`ConstValue::Uint(value, width_bits)`), and a `Nat` constant is
/// emitted as a CALL to the bignum runtime, which `recognize_single_block` does
/// not read.
///
/// Giving it an arm is a `trust_types::admissible_body` widening, and that
/// reader feeds `trust_certify::clean_island::admit_function_into` as well — the
/// E6 kernel-import direction, where a recognized body becomes a defining
/// equation with NO side A and NO kernel gate (the exact hazard
/// `table_controls::h_i_the_side_b_reader_cannot_name_the_table` guards). So the
/// row is refused here and the demand is recorded as a measured MISS.
#[test]
fn l2_p4_nat_nullary_constant_has_no_reader_arm() {
    let mut env = env_uint();
    define(&mut env, "five_nat", nat_ty(), Expr::nat_lit(5));

    // Half 1: side B's PRODUCER exists — so the boundary is not the producer.
    let side_b = reflect_expr(&env, "5", 0, &Domain::Nat)
        .expect("MEASURED: `Domain::Nat` mints a nullary bignum constant");
    let nat_carrier =
        carrier_at(&nat_ty(), &Ty::BignumNat).expect("Nat carries at the bignum runtime type");
    check_faithful(&env, "five_nat", &side_b, &nat_carrier)
        .expect("MEASURED ADMIT: the kernel identifies the two `Nat` literals");
    // …with its paired mutation, so the ADMIT above is a decision.
    let wrong = reflect_expr(&env, "6", 0, &Domain::Nat).expect("reflects");
    refused(&env, "five_nat", &wrong, &nat_carrier, "wrong Nat constant (6 for 5)");

    // Half 2: side B's READER has no arm, so nothing can reach that producer
    // from an emitted body. `ConstantUint` is machine-width by construction and
    // a bignum constant is not an inline scalar at all.
    let bignum_body = {
        let mut f = emitted_const(64, 0, 5);
        f.body.locals[0].ty = Ty::BignumNat;
        f.body.return_ty = Ty::BignumNat;
        f
    };
    assert_eq!(
        recognize_admissible_body(&bignum_body),
        Some(AdmissibleBody::ConstantUint { value: 5, width_bits: 64 }),
        "the reader still reports a MACHINE constant for a bignum-typed return place — it \
         reads the rvalue, not the type. That is precisely why a bignum constant row would \
         need a reader widening rather than a table row: the vocabulary it would have to be \
         told apart by does not exist on side B."
    );

    // Half 3: TODAY's planner refuses, and must KEEP refusing after landing 2 —
    // the constant row is stated at the machine widths only.
    assert_plan_refuses_today(&env, "five_nat");
    eprintln!(
        "PROBE-ROW | nullary const at Nat      | producer: yes | READER: NO ARM | \
         MISS (recorded, not added)"
    );
}

// ══════════ L2-P5 — ranked MISS 2: a constant `ite` ARM. MEASURED, NOT ADDED ══════════

/// The 4-block O0 select diamond, in extractor shape, with each arm's value
/// supplied by the caller — a parameter local, or an inline constant.
fn select_diamond(then_value: Rvalue, else_value: Rvalue, cmp: Rvalue) -> VerifiableFunction {
    let asn = |p: usize, rv: Rvalue| Statement::Assign {
        place: Place::local(p),
        rvalue: rv,
        span: SourceSpan::default(),
    };
    VerifiableFunction {
        name: "probe".into(),
        def_path: "crate::m::probe".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::u64(), name: None },
                LocalDecl { index: 1, ty: Ty::u64(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: Ty::u64(), name: Some("b".into()) },
                LocalDecl { index: 3, ty: Ty::u64(), name: None },
                LocalDecl { index: 4, ty: Ty::Bool, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![asn(4, cmp)],
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
                    stmts: vec![asn(3, then_value)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![asn(3, else_value)],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![asn(0, Rvalue::Use(Operand::Copy(Place::local(3))))],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            return_ty: Ty::u64(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn lt_params() -> Rvalue {
    Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(Place::local(1)), Operand::Copy(Place::local(2)))
}

/// Side A for `if a < b then a else 0` / `if a + 1 < b then a else b`, built the
/// way `elab_if` mints an `ite` and FULL-kernel-checked by `define`.
fn ite_body(lhs: Expr, rhs: Expr, then_arm: Expr, else_arm: Expr) -> Expr {
    let lt_prop = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            uint64(),
            Expr::const_(Name::from_string("instLTUInt64"), vec![]),
            lhs.clone(),
            rhs.clone(),
        ],
    );
    let dec_inst =
        Expr::apps(Expr::const_(Name::from_string("instDecidableUInt64Lt"), vec![]), [lhs, rhs]);
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [uint64(), lt_prop, dec_inst, then_arm, else_arm],
    )
}

/// **Ranked MISS 2, measured: a CONSTANT `ite` arm. NOT ADDED — and CLOSED BY
/// §6f LANDING 3, which is why the plan assertion below is a SHAPE and no
/// longer a refusal.**
///
/// What landing 2 measured, and what of it still holds:
///
/// * the READER — `recognize_admissible_body`'s chain read both arms through
///   the parameter vocabulary, so the const-arm diamond recognized as `None`.
///   **STILL TRUE, and now load-bearing for a different reason**: landing 3
///   deliberately did NOT widen that chain, because it also feeds the E6
///   kernel-import direction. The capability arrived through the separate
///   entry point `recognize_select_general`, so the assertion below is now the
///   E6 CONTAINMENT rather than a capability boundary
///   (`landing3_selection_probes::l3_p2`).
/// * the PRODUCER — `admit_select_function`/`admit_select_literal_function`
///   take `then_param: usize` / `else_param: usize`, so a constant arm is
///   unrepresentable in THEIR signatures. **STILL TRUE**: landing 3 left both
///   frozen routes untouched and added `admit_select_operands_function` beside
///   them, the same discipline R2/C9 applied. The refusal measured below is
///   still exactly what those routes can do — a DIFFERENT function, refused by
///   the kernel.
///
/// So landing 2's reading was right and its disposition was right for its
/// ownership; what changed is that landing 3 owned `trust-spec-elab` and could
/// add the route. This probe keeps both halves and re-points the one
/// assertion the later measurement superseded — the same treatment landing 2
/// gave `control_3`'s `half_8`.
#[test]
fn l2_p5_constant_ite_arm_has_no_reflection_path() {
    let mut env = Environment::with_prelude();
    define(
        &mut env,
        "clamp0",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                // Under 2 binders: a = bvar 1, b = bvar 0; the ELSE arm is a
                // numeral instead of a parameter.
                ite_body(Expr::bvar(1), Expr::bvar(0), Expr::bvar(1), surface_lit(64, 0)),
            ),
        ),
    );
    // Side A IS statable — the boundary is not here. §6f LANDING 3: and the
    // PLANNER now reads it, as the general select whose else arm is a numeral.
    assert!(env.get_const(&Name::from_string("clamp0")).is_some());
    assert_plan_shape(
        &env,
        "clamp0",
        CleanOriginShape::SelectOperands {
            cmp: trust_types::admissible_body::SelectCmp::Lt,
            cmp_left: 0,
            cmp_right: trust_types::admissible_body::ArithOperand::Param(1),
            then_arm: trust_types::admissible_body::ArithOperand::Param(0),
            else_arm: trust_types::admissible_body::ArithOperand::Const(0),
        },
    );

    // Half 1: the READER — now the E6 CONTAINMENT. The const-arm diamond
    // still does not recognize through `recognize_admissible_body`, which is
    // what keeps the gate-free kernel-import direction's reach where it was.
    let const_arm = select_diamond(
        Rvalue::Use(Operand::Copy(Place::local(1))),
        Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
        lt_params(),
    );
    assert_eq!(
        recognize_admissible_body(&const_arm),
        None,
        "a constant `ite` arm must not recognize; if it does, an arm widening has landed in \
         trust-types and this pin must be rewritten with its own kernel measurement"
    );

    // Half 2: the PRODUCER. The param-arm route is the only one that exists,
    // and it mints the arm as a PARAMETER — so the closest term it can build
    // is a DIFFERENT function, which the kernel then refuses. That is the
    // measurement: the gap is representational, and papering over it would
    // manufacture a verdict about a claim nobody stated.
    let nearest = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_function(
            scratch,
            name,
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
            trust_spec_elab::SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
    })
    .expect("the param-arm producer still mints its own shape");
    refused(&env, "clamp0", &nearest, &u64_carrier(), "a PARAMETER arm for a CONSTANT arm");
    eprintln!(
        "PROBE-ROW | if a < b then a else 0    | reader: NO ARM | producer: \
         UNREPRESENTABLE (usize arms) | MISS (needs a new trust-spec-elab route)"
    );
}

// ══════════ L2-P6 — ranked MISS 3: a COMPUTED `ite` condition. MEASURED, NOT ADDED ══════════

/// **Ranked MISS 3, measured: a COMPUTED `ite` condition. NOT ADDED.**
///
/// The same two-crate finding as L2-P5, at the comparison rather than the arms:
/// `admit_select_function`'s comparison operands are `cmp_left: usize` /
/// `cmp_right: usize`, and `admit_select_literal_function`'s are a `usize` and a
/// numeral. A computed operand (`a + 1`) is unrepresentable in either, and the
/// emitted diamond does not recognize. Side A kernel-checks, so — as with L2-P5
/// — the kernel is never reached and the refusal is NOT a defeq finding.
#[test]
fn l2_p6_computed_ite_condition_has_no_reflection_path() {
    let mut env = Environment::with_prelude();
    // `a + 1` at UInt64, in the carrier spelling; under 2 binders a = bvar 1.
    let a_plus_1 = Expr::apps(
        Expr::const_(Name::from_string("UInt64.add"), vec![]),
        [Expr::bvar(1), carrier_lit(64, 1)],
    );
    define(
        &mut env,
        "shifted_min",
        u64_arrows(2),
        Expr::lam(
            BinderInfo::Default,
            uint64(),
            Expr::lam(
                BinderInfo::Default,
                uint64(),
                ite_body(a_plus_1, Expr::bvar(0), Expr::bvar(1), Expr::bvar(0)),
            ),
        ),
    );
    assert!(env.get_const(&Name::from_string("shifted_min")).is_some());
    assert_plan_refuses_today(&env, "shifted_min");

    // The READER: a computed comparison operand is not a parameter and not a
    // literal, so the diamond does not recognize.
    let computed = select_diamond(
        Rvalue::Use(Operand::Copy(Place::local(1))),
        Rvalue::Use(Operand::Copy(Place::local(2))),
        Rvalue::BinaryOp(
            BinOp::Lt,
            // A temp holding `a + 1` would be a fifth local; using `_3` here is
            // enough to make the point the recognizer checks: the operand is
            // not one of `1..=arg_count`.
            Operand::Copy(Place::local(3)),
            Operand::Copy(Place::local(2)),
        ),
    );
    assert_eq!(
        recognize_admissible_body(&computed),
        None,
        "a computed comparison operand must not recognize; if it does, a condition widening \
         has landed and this pin must be rewritten with its own kernel measurement"
    );

    // The PRODUCER: the nearest representable comparison is over the bare
    // parameters, which is a DIFFERENT function — refused at the kernel.
    let nearest = reflect(&env, |scratch, name| {
        trust_spec_elab::admit_select_function(
            scratch,
            name,
            &[Domain::Machine(MachineUIntWidth::U64), Domain::Machine(MachineUIntWidth::U64)],
            trust_spec_elab::SelectCmp::Lt,
            0,
            1,
            0,
            1,
        )
    })
    .expect("the bare-parameter producer still mints its own shape");
    refused(
        &env,
        "shifted_min",
        &nearest,
        &u64_carrier(),
        "a BARE-PARAMETER condition for a COMPUTED one",
    );
    eprintln!(
        "PROBE-ROW | if a + 1 < b then a else b| reader: NO ARM | producer: \
         UNREPRESENTABLE (usize operands) | MISS (needs a new trust-spec-elab route)"
    );
}
