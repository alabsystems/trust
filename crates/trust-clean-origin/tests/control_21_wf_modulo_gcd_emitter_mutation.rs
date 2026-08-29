// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 21 — the TEXTBOOK MODULO `gcd`'s mutation battery (§R8).**
//!
//! `control_8` is R2's battery at arity 1, `control_16` is R3a's at arity 2,
//! `control_17` is R3b's on the subtractive fuel form, `control_18`/`control_19`
//! are R3d's on the sum measure. This is R8's, on the shape the `nat.mod` row
//! exists for — the Euclidean step written the way a textbook writes it:
//!
//! ```text
//! def gcd (a b : Nat) : Nat := if h : 0 < b then gcd b (a % b) else a
//! termination_by b + a * 0
//! ```
//!
//! Two things are load-bearing here that no earlier battery could test.
//!
//! 1. **The divisor's operand order is observable by the kernel.** `%` is not
//!    commutative — `r8_nat_mod_probes` q1 measures that
//!    `a % b = Nat.mod b a` is REFUSED — so row (b) is a genuine refutation.
//! 2. **The SIBLING op is a live mutation, not a hypothetical.** `Nat::div` and
//!    `Nat::rem` are the two halves of one `checked_div_rem`, resolved by
//!    METHOD NAME on the same `impl` block. Row (c) is the emitter-side twin of
//!    q1's `a % b = Nat.div a b` refusal.
//!
//! # What stands in for panic-freedom here, and why row (f) is the real one
//!
//! **This file must not be read as proving the emitted `%` cannot panic.** It
//! cannot panic, but not for a reason any row below establishes: the emitted
//! operation is `Call(trust_bignum::Nat::rem, [&a, &b])`, `TemplateTerminator`
//! has no `Assert` variant, and `Nat::rem` is total by construction. That is
//! carrier totality, and it is carried by
//! `trust-bignum/tests/kernel_differential.rs` and the `PrimitiveCallee` TCB
//! row — NOT by a `Faithful` token and NOT by the kernel identification, which
//! `r8_nat_mod_probes` q2 shows is VACUOUS at an open dividend.
//!
//! The obligation this lane genuinely discharges is the **DECREASE**, and
//! row (f) is its control: three bodies that differ from the admitted one in
//! the GUARD ALONE — wrong value, non-dominating, absent — and all three are
//! REFUSED. An identification with no undischarged case that fails is not a
//! measurement, which is exactly why (f) is a paired row and not a lone admit.
//!
//! Side A is the REAL elaborated `gcd` through
//! `trust_certify::clean_island::CleanIslandSession`, never a hand-built
//! mirror. Side B is the emitted-MIR contract traced BY HAND, so a materializer
//! defect cannot make this control agree with itself.
//!
//! **WHAT THIS FILE DOES NOT CLAIM.** It does not claim `gcd` is proved
//! correct: `Nat.gcd` is absent from the prelude (`gcd_final_probes` n1), so
//! there is nothing to state correctness against. The VALUES are pinned at the
//! kernel with refuting controls in `r8_nat_mod_probes` q4 and in the run-pass
//! fixture `tests/ui/trust/clean_origin_wf_rec_modulo_gcd.rs`.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Name};
use trust_clean_origin::emit::{CleanOriginShape, plan_clean_origin_body};
use trust_clean_origin::{WfLowering, admit_lowering};
use trust_types::admissible_body::{RecBodyExpr, WfRecBody, recognize_wf_sum_measure_rec};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement, Terminator, Ty,
    UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════════════════════════════════════════════════
// side A — the REAL session
// ═══════════════════════════════════════════════════════════════════════════

/// **THE RATIFIED SIDE A.** The textbook modulo `gcd`.
///
/// `+ a * 0` is not decoration and not a trick: phase 3 (`OnMeasureValue`) is
/// reached only by a measure that mentions both parameters, and `a * 0` is the
/// spelling `first-party/clean`'s cascade closes (`b + 0 * a` is
/// ISLAND-REJECTED — an asymmetry recorded as a v7/D3 wart in this landing's
/// report, since asking a user to write `+ a * 0` is a refusal that does not
/// carry a real fix).
const GCD: &str = "def gcd (a b : Nat) : Nat := \
                   if h : 0 < b then gcd b (a % b) else a\n\
                   termination_by b + a * 0";

const SELF_PATH: &str = "clean_origin_wf_rec_modulo_gcd::gcd";
const BIGNUM_REM: &str = "trust_bignum::divmod::<impl trust_bignum::Nat>::rem";
/// The SIBLING half of the same `checked_div_rem`, on the same `impl` block.
/// Deliberately NOT an authenticated callee — nothing in the emittable fragment
/// names `/`, so `PrimitiveCallee::classify` must return `None` for it.
const BIGNUM_DIV: &str = "trust_bignum::divmod::<impl trust_bignum::Nat>::div";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";
const BIGNUM_MUL: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::mul";

fn island(source: &str) -> Result<Environment, String> {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&[source]);
    if batch.is_rejected() {
        let mut msgs: Vec<String> = batch
            .outcomes
            .iter()
            .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
            .collect();
        msgs.extend(batch.cycles.iter().map(|c| c.message.clone()));
        return Err(msgs.join(" | "));
    }
    Ok(session.environment().expect("an untainted session has an environment").clone())
}

fn gcd_env() -> Environment {
    island(GCD).expect("the textbook modulo `gcd` must elaborate and kernel-check at this pin")
}

/// `a % b` — `Param(0)` is `a`, `Decreasing` is the GUARDED parameter `b`
/// (source index 1, the one the zero test decides).
fn rem_a_b() -> RecBodyExpr {
    RecBodyExpr::Rem(Box::new(RecBodyExpr::Param(0)), Box::new(RecBodyExpr::Decreasing))
}

fn planned_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::Param(0),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![RecBodyExpr::Decreasing, rem_a_b()],
        measure_index: 1,
        lowering: WfLowering::OnMeasureValue,
    }
}

fn recognised_body() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::Param(0),
        nonzero_value: RecBodyExpr::Rec,
        rec_args: vec![RecBodyExpr::Decreasing, rem_a_b()],
        measure_index: 1,
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// side B — the emission, traced BY HAND
// ═══════════════════════════════════════════════════════════════════════════
//
// ```text
// _0 _1 _2 _7 _8 : Nat        _4 : bool        _3 _5 _6 : &Nat
//                             (_8 declared and dead — the root call's temp)
// bb0: _3 = &_2;   is_zero(move _3) -> _4, bb1        // the zero test, on `b`
// bb1: switchInt(move _4) [(0, bb3)] otherwise bb2
// bb2: _0 = move _1; goto bb5                         // zero arm: `a`
// bb3: _5 = &_1; _6 = &_2;  rem(move _5, move _6) -> _7, bb4   // `a % b`
// bb4: gcd(move _2, move _7) -> _0, bb5               // THE call: gcd b (a%b)
// bb5: return
// ```
//
// **Read bb3 and bb4 together — that pair is the whole landing.**
//
// bb3 is a `Call`, NOT an `Rvalue::BinaryOp(Rem)`, so rustc's zero-divisor
// `Assert` is not emitted and there is no panic edge to discharge. At `UInt{N}`
// the same source would lower to the `BinaryOp`, the `Assert` WOULD be there,
// and the faithfulness gate would be blind to it — which is why
// `recognise_raw_binop_expr` still refuses a symbolic divisor at a machine
// width and why row (h) pins that refusal in place.
//
// bb4 moves `_2` (`b`) into the self-call's FIRST slot while bb3 has already
// finished borrowing it. `b` is passed BY ITSELF in slot 0 and used again
// inside slot 1 — the shape the plan's move-aware duplication rule had to
// admit, and it does because bb3's uses are shared borrows that end before the
// move.
//
// The MEASURE is readable straight out of bb0: the zero test borrows `_2`, so
// `measure_index = 1`. Mutation (e) moves exactly that borrow.

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn borrow(place: usize, of: usize) -> Statement {
    Statement::Assign {
        place: Place::local(place),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(of) },
        span: SourceSpan::default(),
    }
}

fn call(callee: &str, args: Vec<Operand>, dest: usize, target: usize) -> Terminator {
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
    }
}

fn mv(local: usize) -> Operand {
    Operand::Move(Place::local(local))
}

fn emitted_gcd() -> VerifiableFunction {
    const REFS: [usize; 3] = [3, 5, 6];
    let locals = (0..9)
        .map(|index| LocalDecl {
            index,
            ty: if index == 4 {
                Ty::Bool
            } else if REFS.contains(&index) {
                Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }
            } else {
                nat_adt()
            },
            name: None,
        })
        .collect();
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![borrow(3, 2)],
            terminator: call("trust_bignum::Nat::is_zero", vec![mv(3)], 4, 1),
        },
        BasicBlock {
            id: BlockId(1),
            stmts: Vec::new(),
            terminator: Terminator::SwitchInt {
                discr: mv(4),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(2),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        },
        BasicBlock {
            id: BlockId(2),
            stmts: vec![Statement::Assign {
                place: Place::local(0),
                rvalue: Rvalue::Use(mv(1)),
                span: SourceSpan::default(),
            }],
            terminator: Terminator::Goto(BlockId(5)),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: vec![borrow(5, 1), borrow(6, 2)],
            terminator: call(BIGNUM_REM, vec![mv(5), mv(6)], 7, 4),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: Vec::new(),
            terminator: call(SELF_PATH, vec![mv(2), mv(7)], 0, 5),
        },
        BasicBlock { id: BlockId(5), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "gcd".into(),
        def_path: SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 2,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

/// Replace the callee of one block's `Call` terminator.
fn with_callee(mut body: VerifiableFunction, block: usize, callee: &str) -> VerifiableFunction {
    if let Terminator::Call { func, .. } = &mut body.body.blocks[block].terminator {
        *func = callee.into();
    }
    body
}

/// Replace the argument list of one block's `Call` terminator.
fn with_args(mut body: VerifiableFunction, block: usize, args: Vec<Operand>) -> VerifiableFunction {
    if let Terminator::Call { args: slot, .. } = &mut body.body.blocks[block].terminator {
        *slot = args;
    }
    body
}

/// Replace the statements of one block.
fn with_stmts(
    mut body: VerifiableFunction,
    block: usize,
    stmts: Vec<Statement>,
) -> VerifiableFunction {
    body.body.blocks[block].stmts = stmts;
    body
}

// ═══════════════════════════════════════════════════════════════════════════
// THE ADMIT
// ═══════════════════════════════════════════════════════════════════════════

/// The whole route, on the textbook modulo shape, against the REAL elaborated
/// side A. Cited by `table.rs`'s `nat.mod` row.
#[test]
fn admits_end_to_end() {
    let env = gcd_env();
    assert!(
        env.get_const(&Name::from_string("Nat.mod")).is_some(),
        "`Nat.mod` must exist at this pin"
    );

    let plan = plan_clean_origin_body(&env, "gcd").expect("the textbook modulo `gcd` must plan");
    assert_eq!(
        plan.shape(),
        &planned_shape(),
        "zero arm `a`, self-call `(b, a % b)` — and `a % b` must be READ in that ORDER, \
         never swapped and never pre-reduced"
    );
    assert_eq!(plan.signature().arity(), 2);

    let extracted = emitted_gcd();
    assert_eq!(
        recognize_wf_sum_measure_rec(&extracted),
        Some(recognised_body()),
        "the emitted-and-extracted body must read back as the planned recursion"
    );

    let faithful =
        admit_lowering(&env, &plan, &extracted).expect("the emission must pass the F-layer gate");
    assert_eq!(faithful.name(), "gcd");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
    eprintln!(
        "CONTROL-21 admit | textbook modulo gcd FAITHFUL by {:?}",
        faithful.method()
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// THE MUTATIONS — an ADMIT with no refused sibling is not a measurement
// ═══════════════════════════════════════════════════════════════════════════

/// (a) THE WRONG OPERATOR. The emitted body computes `a - b` / `a + b` /
/// `a * b` where side A says `a % b`. The emitter-side twin of
/// `r8_nat_mod_probes` q1's kernel mutations.
#[test]
fn a_wrong_operator_at_the_remainder_is_refused() {
    let env = gcd_env();
    let plan = plan_clean_origin_body(&env, "gcd").expect("plans");
    for (tag, callee) in
        [("sub", BIGNUM_SUB), ("add", BIGNUM_ADD), ("mul", BIGNUM_MUL)]
    {
        let refusal = admit_lowering(&env, &plan, &with_callee(emitted_gcd(), 3, callee))
            .expect_err("a wrong operator must never emit");
        assert!(
            refusal.is_compiler_defect(),
            "`{tag}` where the definition says `%` is a compiler defect, got {refusal:?}"
        );
    }
}

/// (b) **THE OPERAND ORDER.** `b % a` where side A says `a % b`.
///
/// This is the row `+` and `*` cannot have and the reason `nat.mod` reads its
/// operands dumbly. It is a GENUINE refutation, not a delicate one: q1
/// measures that the kernel REFUSES `a % b = Nat.mod b a`, so a transposition
/// here is a different function and not a commutativity fact the gate happens
/// to miss.
#[test]
fn b_swapped_remainder_operands_are_refused() {
    let env = gcd_env();
    let plan = plan_clean_origin_body(&env, "gcd").expect("plans");
    // Swap the two BORROWS, which is how a real transposition would appear:
    // `_5 = &_2; _6 = &_1` makes bb3 compute `b % a`.
    let swapped = with_stmts(emitted_gcd(), 3, vec![borrow(5, 2), borrow(6, 1)]);
    let refusal = admit_lowering(&env, &plan, &swapped)
        .expect_err("`b % a` where the definition says `a % b` must never emit");
    assert!(refusal.is_compiler_defect(), "got {refusal:?}");

    // And the same transposition expressed at the ARGUMENTS rather than the
    // borrows, so this is not measuring one accidental representation.
    let swapped_args = with_args(emitted_gcd(), 3, vec![mv(6), mv(5)]);
    assert!(
        admit_lowering(&env, &plan, &swapped_args).is_err(),
        "argument-transposed `%` must not emit either"
    );
}

/// (c) **THE SIBLING OP.** `Nat::div` for `Nat::rem`.
///
/// The two are halves of one `checked_div_rem` on one `impl` block, resolved by
/// METHOD NAME — so "the emitter resolved the wrong name" is the single most
/// plausible defect on this lane, and it is the one the materializer's old
/// `_ => PrimitiveCallee::NatSub` catch-all would have produced silently had
/// `Rem` been added to that pattern without making the match exhaustive.
///
/// It must refuse at the CLASSIFIER, before any gate: `div` is not an
/// authenticated callee at all.
#[test]
fn c_the_sibling_div_is_not_even_an_authenticated_callee() {
    use trust_types::admissible_body::PrimitiveCallee;
    assert_eq!(
        PrimitiveCallee::classify(BIGNUM_DIV),
        None,
        "`Nat::div` must NOT classify — nothing in the emittable fragment names `/`, and an \
         unreachable accepted callee is surface the gate would have to defend for no \
         capability"
    );
    assert_eq!(
        PrimitiveCallee::classify(BIGNUM_REM),
        Some(PrimitiveCallee::NatRem),
        "`Nat::rem`'s module-qualified path MUST classify — its `impl` block is `mod \
         divmod`, so copying `arith` from the add/sub/mul rows would silently fail to \
         classify every real extracted body"
    );
    // The co-located spelling too, per `bignum_callee`'s note.
    assert_eq!(
        PrimitiveCallee::classify("trust_bignum::Nat::rem"),
        Some(PrimitiveCallee::NatRem)
    );
    // Round-trip, the discipline every row carries.
    assert_eq!(
        PrimitiveCallee::classify(&PrimitiveCallee::NatRem.canonical_path()),
        Some(PrimitiveCallee::NatRem)
    );
    assert_eq!(PrimitiveCallee::NatRem.rust_method_name(), "rem");
    assert_eq!(PrimitiveCallee::NatRem.machine_width(), None);

    let env = gcd_env();
    let plan = plan_clean_origin_body(&env, "gcd").expect("plans");
    assert!(
        admit_lowering(&env, &plan, &with_callee(emitted_gcd(), 3, BIGNUM_DIV)).is_err(),
        "`div` where the definition says `%` must never emit"
    );
}

/// (d) THE SELF-CALL ARGUMENT ORDER. `gcd (a % b) b` where side A says
/// `gcd b (a % b)`. Both arguments are in the emitted body already, so this
/// mutation changes nothing about which values are computed — only where they
/// go, which is precisely the defect a shape comparison exists to catch.
#[test]
fn d_transposed_self_call_arguments_are_refused() {
    let env = gcd_env();
    let plan = plan_clean_origin_body(&env, "gcd").expect("plans");
    let refusal = admit_lowering(&env, &plan, &with_args(emitted_gcd(), 4, vec![mv(7), mv(2)]))
        .expect_err("`gcd (a % b) b` must never emit for `gcd b (a % b)`");
    assert!(refusal.is_compiler_defect(), "got {refusal:?}");
}

/// (e) THE ZERO TEST ON THE WRONG PARAMETER. The emitted guard decides `a`
/// where side A guards `b`. This is the mutation that would make the emitted
/// binary descend on the parameter the decrease proof says nothing about.
#[test]
fn e_the_zero_test_on_the_wrong_parameter_is_refused() {
    let env = gcd_env();
    let plan = plan_clean_origin_body(&env, "gcd").expect("plans");
    let moved = with_stmts(emitted_gcd(), 0, vec![borrow(3, 1)]);
    assert!(
        admit_lowering(&env, &plan, &moved).is_err(),
        "a zero test on `a` must not emit for a definition that guards `b`"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (f) THE OBLIGATION THIS LANE DISCHARGES — and its undischarged cases
// ═══════════════════════════════════════════════════════════════════════════

/// **THE ROW THAT MAKES THIS LANDING A MEASUREMENT RATHER THAN A LABEL.**
///
/// The kernel identification `a % b ≡ Nat.mod a b` is discriminating about the
/// VALUE (rows a–c) but says nothing about the zero divisor at an open dividend
/// (`r8_nat_mod_probes` q2) — so it cannot, by itself, be what makes this lane
/// safe. What the compiler genuinely discharges is the DECREASE, and a decrease
/// needs `0 < b` at the point of use.
///
/// These four bodies differ **in the guard alone**. The first is the admitted
/// one; the other three are the ways the positivity fact can be missing, and
/// all three must be REFUSED. Because only the guard varies, a refusal here
/// cannot be attributed to the measure spelling, the arity, the vocabulary or
/// anything else this battery already holds fixed.
#[test]
fn f_only_a_dominating_guard_on_the_divisor_is_admitted() {
    // The discharged case — the same text `admits_end_to_end` uses, restated
    // here so the contrast is visible in one place.
    assert!(
        island(GCD).is_ok(),
        "the DISCHARGED case must elaborate, or the three refusals below are refusing \
         something other than the guard"
    );

    for (tag, src, why) in [
        (
            "guard tests the WRONG value",
            "def g (a b : Nat) : Nat := if h : 0 < a then g b (a % b) else a\n\
             termination_by b + a * 0",
            "`0 < a` says nothing about the divisor `b`, so `Nat.mod_lt` cannot apply",
        ),
        (
            "guard does NOT DOMINATE the division",
            "def g (a b : Nat) : Nat := if h : 0 < b then a else g b (a % b)\n\
             termination_by b + a * 0",
            "in the else branch `b = 0`, so `a % b` is `a` and nothing decreases",
        ),
        (
            "NO guard at all",
            "def g (a b : Nat) : Nat := g b (a % b)\n\
             termination_by b + a * 0",
            "an unguarded self-call has no decrease to prove",
        ),
    ] {
        let outcome = island(src);
        assert!(
            outcome.is_err(),
            "UNDISCHARGED CASE `{tag}` must be REFUSED ({why}). If this starts elaborating, \
             the decrease is being discharged by something other than the dominating \
             positivity guard — and since the decrease is what stands in for panic-freedom \
             on this lane, the `nat.mod` row's accounting would no longer describe the \
             compiler."
        );
        eprintln!("CONTROL-21 (f) {tag:<36} | REFUSED");
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (g) THE CAPABILITY THIS ROW OPENS, stated rather than left to be discovered
// ═══════════════════════════════════════════════════════════════════════════

/// An UNGUARDED `%` in a non-decreasing slot now PLANS, and that is correct
/// rather than an oversight — but it is exactly the row a reader of
/// `fa788aab89` would expect to be refused, so it is written down.
///
/// The divisor here is not provably nonzero and no obligation is discharged
/// about it. That is sound **only** because `Nat::rem` is total and agrees with
/// `Nat.mod` at zero: the emitted call returns the dividend, which is the value
/// the kernel term denotes. Nothing panics and nothing diverges.
///
/// The same body at `UInt{N}` is REFUSED — row (h) — because there the emitted
/// op is an `Rvalue::BinaryOp` that panics while the kernel term stays total.
/// **That contrast is the entire content of this landing**, and if the `Nat`
/// row is ever changed to emit a machine-width `%`, this test and (h) must be
/// read together before doing it.
#[test]
fn g_an_unguarded_remainder_is_admitted_only_because_the_carrier_is_total() {
    let env = island(
        "def u (a b : Nat) : Nat := if h : 0 < a then u (a - 1) (a % b) else b\n\
         termination_by a",
    )
    .expect("elaborates");
    let plan = plan_clean_origin_body(&env, "u").expect(
        "an unguarded `%` in a NON-decreasing slot plans: no decrease is claimed about it, \
         and the carrier is total at a zero divisor",
    );
    assert_eq!(
        plan.shape(),
        &CleanOriginShape::WellFoundedNatRec {
            zero_value: RecBodyExpr::Param(1),
            nonzero_value: RecBodyExpr::Rec,
            rec_args: vec![
                RecBodyExpr::Pred,
                RecBodyExpr::Rem(
                    Box::new(RecBodyExpr::Decreasing),
                    Box::new(RecBodyExpr::Param(1)),
                ),
            ],
            measure_index: 0,
            lowering: WfLowering::OnParameter,
        },
        "the unguarded `%` reads as an ordinary `Rem` node"
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (h) fa788aab89's REFUSALS STAY EXACTLY WHERE THEY ARE
// ═══════════════════════════════════════════════════════════════════════════

/// **The machine-width lane is UNMOVED by this landing.**
///
/// A `nat.mod` row at the bignum carrier is not a licence to admit `%` at a
/// machine width, and the difference is not stylistic: at `UInt{N}` the emitted
/// `Rvalue::BinaryOp(Rem)` carries rustc's zero-divisor `Assert`, the gate
/// compares two total CLEAN terms and cannot see it, and `control_15::half_11`
/// already measures the gate admitting `a % b` at symbolic `b`. The plan-lane
/// refusal is what prevents the false verify, and it must keep firing.
#[test]
fn h_the_machine_width_symbolic_divisor_is_still_refused() {
    let env = island("def uw (a b : UInt64) : UInt64 := a % b").expect("elaborates");
    let refusal = plan_clean_origin_body(&env, "uw")
        .expect_err("a SYMBOLIC divisor at a machine width must still be REFUSED");
    let note = refusal.note();
    assert!(
        note.contains("VARIABLE divisor"),
        "the refusal must still name the variable divisor; got: {note}"
    );
    assert!(
        note.contains("PANIC"),
        "the refusal must still say why — Rust's `%` panics where the kernel term is \
         total; got: {note}"
    );

    // The positive-literal divisor at a machine width is UNCHANGED too: it
    // still plans as a raw binop, so this landing neither widened nor narrowed
    // that lane.
    let lit = island("def ul (a b : UInt64) : UInt64 := a % 7").expect("elaborates");
    assert!(
        plan_clean_origin_body(&lit, "ul").is_ok(),
        "a positive-literal divisor at a machine width must still plan"
    );
}
