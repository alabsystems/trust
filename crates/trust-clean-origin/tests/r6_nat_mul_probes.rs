// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R6 — the subtractive-`gcd` measurement, and the `nat.mul` row it
//! produced.**
//!
//! Every side A here comes from `trust_certify::clean_island::CleanIslandSession`
//! — the exact pipeline `clean_origin_mir` drives — so an ISLAND rejection and a
//! CALL-lane refusal are never confused for one another (the `r2_session_probes`
//! discipline).
//!
//! # The question, and the measured answer
//!
//! `gcd`'s `a % b` cannot be emitted (a symbolic divisor: Clean's `Nat.div`/
//! `.mod` are TOTAL where Rust's `/`/`%` PANIC, and commit `fa788aab89`
//! measured the faithfulness gate BLIND to that divergence). Euclid's ORIGINAL
//! algorithm subtracts instead, and `Nat` subtraction is total on both sides —
//! so the obvious move is a subtractive `gcd`.
//!
//! **It does not elaborate, in any measured spelling** (q2), and the block is
//! not this crate's. A two-branch subtractive Euclid decreases only in `a + b`,
//! and `first-party/clean`'s well-founded lowering refuses a measure naming two
//! parameters *by name and on purpose* — "the `termination_by` measure mentions
//! 2 parameters (`a`, `b`)". Bare and parenthesised spellings give the SAME
//! refusal, so the sibling's `r5-measure-spelling-routing` routing fix (which
//! only widens which *spellings* reach the lowering) would not move it. Single-
//! descent rewrites lose the decrease instead ("no decreasing proof was found").
//!
//! Two corrections to the record fall out, both measured here:
//!
//! * **`gcd` ITSELF elaborates and kernel-checks at this pin** (q1) — R3
//!   (`27a46804e`) widened the signature and R4 (`1852198c0`) added the
//!   Bool-test spelling, and both are in the pin. What refuses `gcd` is THIS
//!   crate's single-parameter well-founded reader, not the elaborator.
//!   **That reader was widened by R3a on 2026-08-26** — see
//!   `r7_arity_widening_probes`, which took this finding as its starting point
//!   — so the arity half of q1's block is paid off and `gcd`'s remaining
//!   blocker is the SYMBOLIC-DIVISOR refusal alone (q10's neighbour, commit
//!   `fa788aab89`). q1/q3/q5 below are left exactly as measured: they were true
//!   when taken, and the way this file stays useful is by recording what it
//!   measured rather than by being rewritten each time the answer moves.
//! * `r2_session_probes` p8 concluded the opposite from a fixture
//!   (`gcdish`) that is rejected for an unrelated reason — its measure does not
//!   decrease (q5). Two-parameter well-founded recursion is supported; a
//!   two-parameter MEASURE is not.
//!
//! # What was landed instead, and why it is the smallest thing
//!
//! With `gcd` out of reach in this slice, the ranked question became: what is
//! the smallest sound extension that makes a genuinely recursive, genuinely
//! useful function RUN from Rust? Measured answer: **`*` in the recursion-arm
//! value vocabulary**, which makes FACTORIAL emittable (q6, q9). It is small in
//! the exact sense that matters — the emitted MIR is `nat.add`'s call chain
//! with ONE authenticated callee changed (`trust_bignum::Nat::mul`, already
//! present in the same `mod arith` as `add`/`sub`), the reflection is the same
//! shared descent with the row's own constant, and the gate route is unchanged.
//!
//! **The kernel probe ran BEFORE the producer was written** (q7): `a * b =
//! Nat.mul a b` closes by `rfl` against the real checker, and the same-shaped
//! `a * b = Nat.add a b` is REFUSED. So the identification side B rests on is
//! the kernel's decision, not a spelling assumption — the discipline the three
//! spelling-gap defects (`Expr::nat_lit`, `Nat.beq`, `Nat.lt`/`Nat.sub`) were
//! each caught for missing.

#![allow(clippy::doc_markdown)]

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_origin::emit::{CleanOriginShape, plan_clean_origin_body};
use trust_clean_origin::{EmitRefusal, FaithfulnessMethod, admit_lowering};
use trust_types::admissible_body::{RecBodyExpr, WfRecBody, recognize_wf_nat_rec};
use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

// ═══════════════════════════════════════════════════════════════════════════
// harness
// ═══════════════════════════════════════════════════════════════════════════

/// Elaborate + kernel-check one island source. `Err` carries the ISLAND's own
/// diagnostics, joined.
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

/// One row: island verdict, then (if it elaborated) the CALL-lane verdict.
fn row(tag: &str, name: &str, source: &str) {
    match island(source) {
        Err(why) => eprintln!("ROW {tag:<10} | ISLAND REJECTS | {}", first_line(&why)),
        Ok(env) => {
            let call = match plan_clean_origin_body(&env, name) {
                Ok(plan) => format!("PLANS {:?}", plan.shape()),
                Err(refusal) => format!("CALL REFUSES | {}", first_line(&refusal.note())),
            };
            eprintln!("ROW {tag:<10} | ISLAND OK      | {call}");
        }
    }
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(240).collect()
}

/// A bounded structural rendering of a kernel term — enough to read a
/// `WellFounded.fix` spine's motive and binder shape.
fn render(expr: &Expr, depth: usize) -> String {
    if depth == 0 {
        return "…".to_owned();
    }
    match expr.kind() {
        ExprKind::MData(_, inner) => render(inner, depth),
        ExprKind::BVar(i) => format!("#{i}"),
        ExprKind::FVar(_) => "fvar".to_owned(),
        ExprKind::Sort(_) => "Sort".to_owned(),
        ExprKind::Lit(l) => format!("lit({l:?})"),
        ExprKind::Const(n, _) => n.to_string(),
        ExprKind::Lam(_, ty, body) => {
            format!("(fun : {} => {})", render(ty, depth - 1), render(body, depth - 1))
        }
        ExprKind::Pi(_, ty, body) => {
            format!("({} -> {})", render(ty, depth - 1), render(body, depth - 1))
        }
        ExprKind::App(..) => {
            // MEASURED, not assumed: `get_app_args_iter` walks the spine from
            // the OUTERMOST application inward, so it yields the LAST argument
            // first. Printing it unreversed renders `WellFounded.fix α C rel
            // hwf F x` as `… F hwf rel C α`, which is exactly the kind of
            // reading error this file exists to avoid making about someone
            // else's code.
            let head = expr.get_app_fn();
            let mut args: Vec<String> =
                expr.get_app_args_iter().map(|a| render(a, depth - 1)).collect();
            args.reverse();
            format!("({} {})", render(head, depth - 1), args.join(" "))
        }
        other => format!("<{other:?}>"),
    }
}

/// Print the elaborated definition value's spine, if it elaborated.
fn spine(tag: &str, name: &str, source: &str, depth: usize) {
    match island(source) {
        Err(why) => eprintln!("SPINE {tag} | ISLAND REJECTS | {}", first_line(&why)),
        Ok(env) => match env.get_const(&Name::from_string(name)).and_then(|c| c.value.clone()) {
            None => eprintln!("SPINE {tag} | no value"),
            Some(v) => eprintln!("SPINE {tag} | {}", render(&v, depth)),
        },
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q1) the RATIFIED example — two parameters, a one-parameter measure
// ═══════════════════════════════════════════════════════════════════════════

const GCD_MOD: &str = "def gcd (a b : Nat) : Nat := \
                       if h : 0 < b then gcd b (a % b) else a\n\
                       termination_by b";

#[test]
fn probe_q1_ratified_gcd() {
    row("q1 gcd%", "gcd", GCD_MOD);
    spine("q1 gcd%", "gcd", GCD_MOD, 9);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q2) SUBTRACTIVE gcd — every measure spelling that could work
// ═══════════════════════════════════════════════════════════════════════════

#[test]
fn probe_q2_subtractive_gcd_measures() {
    // The textbook two-branch subtractive Euclid. Only `a + b` decreases in
    // both branches.
    let two_branch = |measure: &str| {
        format!(
            "def gcdSub (a b : Nat) : Nat := \
             if h : 0 < b then (if a >= b then gcdSub (a - b) b else gcdSub a (b - a)) else a\n\
             termination_by {measure}"
        )
    };
    for m in ["a + b", "(a + b)", "b", "a"] {
        row(&format!("q2 2br {m}"), "gcdSub", &two_branch(m));
    }

    // Single-descent spellings: the swap is folded into the call.
    let swap = "def gcdSwap (a b : Nat) : Nat := \
                if h : 0 < b then gcdSwap b (a - b) else a\n\
                termination_by b";
    row("q2 swap b", "gcdSwap", swap);

    let swap_a = "def gcdSwapA (a b : Nat) : Nat := \
                  if h : 0 < b then gcdSwapA b (a - b) else a\n\
                  termination_by a";
    row("q2 swap a", "gcdSwapA", swap_a);

    // Equal-guard form.
    let eq = "def gcdEq (a b : Nat) : Nat := \
              if h : 0 < b then (if b <= a then gcdEq (a - b) b else gcdEq a (b - a)) else a\n\
              termination_by a + b";
    row("q2 eq", "gcdEq", eq);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q3) two-parameter, ONE-parameter measure, subtraction argument
// ═══════════════════════════════════════════════════════════════════════════

/// Multiplication by repeated addition — genuinely recursive, genuinely
/// useful, whose decreasing argument is a SUBTRACTION and whose second
/// parameter is threaded unchanged.
const MUL_ADD: &str = "def mulAdd (a b : Nat) : Nat := \
                       if h : 0 < a then b + mulAdd (a - 1) b else 0\n\
                       termination_by a";

/// Same, descending on the SECOND parameter.
const MUL_ADD2: &str = "def mulAdd2 (a b : Nat) : Nat := \
                        if h : 0 < b then a + mulAdd2 a (b - 1) else 0\n\
                        termination_by b";

/// The second parameter is genuinely USED and genuinely CHANGED.
const SUM_TO: &str = "def sumTo (a b : Nat) : Nat := \
                      if h : 0 < a then sumTo (a - 1) (b + a) else b\n\
                      termination_by a";

#[test]
fn probe_q3_two_parameter_threaded() {
    row("q3 mulAdd", "mulAdd", MUL_ADD);
    row("q3 mulAdd2", "mulAdd2", MUL_ADD2);
    row("q3 sumTo", "sumTo", SUM_TO);
    spine("q3 mulAdd", "mulAdd", MUL_ADD, 10);
    spine("q3 mulAdd2", "mulAdd2", MUL_ADD2, 10);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q4) the single-parameter baseline, for contrast
// ═══════════════════════════════════════════════════════════════════════════

const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

#[test]
fn probe_q4_single_parameter_baseline() {
    row("q4 cds", "countdownSum", COUNTDOWN_SUM);
    spine("q4 cds", "countdownSum", COUNTDOWN_SUM, 10);
}

// ═══════════════════════════════════════════════════════════════════════════
// (q5) p8's own fixture, re-measured
// ═══════════════════════════════════════════════════════════════════════════

// ═══════════════════════════════════════════════════════════════════════════
// (q6/q7) the SMALLEST candidate extension: `*` in the value vocabulary
// ═══════════════════════════════════════════════════════════════════════════

/// FACTORIAL. Single parameter, `Nat`, guard `0 < n`, self-call at `n - 1`,
/// zero arm `1` — every constituent of the emittable R2 fragment EXCEPT the
/// `*` in its nonzero arm.
const FACT: &str = "def fact (n : Nat) : Nat := \
                    if h : 0 < n then n * fact (n - 1) else 1\n\
                    termination_by n";

/// **THE HEADLINE.** Factorial PLANS, against the real elaborated side A, and
/// its plan is pinned field by field — because the emitter reads those fields.
///
/// Before the `nat.mul` row this exact source refused with *"its nonzero
/// branch computes (`HMul.hMul`) outside this fragment's vocabulary"*. That
/// refusal was true and is now paid off; nothing else about the well-founded
/// fragment moved for it (q10 pins that the boundary still holds elsewhere).
#[test]
fn probe_q6_factorial_plans() {
    let env = island(FACT).expect("factorial must elaborate and kernel-check");
    assert!(env.get_const(&Name::from_string("Nat.mul")).is_some(), "`Nat.mul` must exist");
    let plan = plan_clean_origin_body(&env, "fact")
        .expect("FACTORIAL must plan against the REAL elaborated side A");
    assert_eq!(plan.shape(), &factorial_shape(), "zero arm `1`, nonzero arm `n * rec`");
    assert_eq!(plan.signature().arity(), 1);
    assert_eq!(format!("{:?}", plan.return_ty()), "BignumNat");
    eprintln!(
        "ROW q6 fact | ISLAND OK | PLANS WellFoundedNatRec {{ zero = 1, \
         nonzero = Decreasing * Rec, rec_arg = Pred }}"
    );
}

/// The planned trio for `fact`, in the vocabulary both sides use.
fn factorial_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::NatConst(1),
        nonzero_value: RecBodyExpr::Mul(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred],
        measure_index: 0,
        lowering: trust_clean_origin::WfLowering::OnParameter,
    }
}

/// **THE KERNEL PROBE, run BEFORE any producer is written.** Side B renders
/// raw `Nat.mul`; the elaborator emits the surface `HMul.hMul … instHMulNat`.
/// A `Mul` row is only sound if the kernel identifies the two — the same fact
/// `instHAddNat`/`instHSubNat` already supply for `+`/`-`.
#[test]
fn probe_q7_kernel_identifies_the_two_multiplication_spellings() {
    let ok = island(
        "theorem mulSpelling (a b : Nat) : a * b = Nat.mul a b := rfl\n\
         theorem addSpelling (a b : Nat) : a + b = Nat.add a b := rfl",
    );
    eprintln!("ROW q7 mul defeq | {}", if ok.is_ok() { "KERNEL ADMITS" } else { "REFUSED" });
    assert!(ok.is_ok(), "`a * b` must be defeq to `Nat.mul a b`: {:?}", ok.err());

    // MUTATION CONTROL at the same layer — otherwise the admit above is a
    // rubber stamp rather than a decision.
    let bad = island("theorem mulWrong (a b : Nat) : a * b = Nat.add a b := rfl");
    eprintln!("ROW q7 mutation  | {}", if bad.is_err() { "REFUSED (good)" } else { "ADMITTED!!" });
    assert!(bad.is_err(), "`a * b = Nat.add a b` must be REFUSED");
}

/// The full refusal texts, so the v7/D3 question ("does it carry the fix?")
/// is answered from the compiler's own output rather than from prose.
#[test]
fn probe_q8_refusal_texts() {
    for (name, source) in [("gcd", GCD_MOD), ("mulAdd", MUL_ADD), ("fact", FACT)] {
        let env = island(source).expect("elaborates");
        if let Err(refusal) = plan_clean_origin_body(&env, name) {
            eprintln!("\n──── NOTE for `{name}` ────\n{}\n", refusal.note());
        }
    }
}

#[test]
fn probe_q5_p8_fixture_reason() {
    // `r2_session_probes` p8 asserts this is rejected and attributes the
    // rejection to "multi-parameter well-founded recursion is refused in
    // clean's elaborator". q1 says otherwise; this row records WHY it is
    // rejected.
    row(
        "q5 gcdish",
        "gcdish",
        "def gcdish (a : Nat) (b : Nat) : Nat := \
         if h : 0 < b then gcdish b (a - 1) else a\n\
         termination_by b",
    );
    // The same shape with a derivable decrease.
    row(
        "q5 fixed",
        "gcdish2",
        "def gcdish2 (a : Nat) (b : Nat) : Nat := \
         if h : 0 < b then gcdish2 a (b - 1) else a\n\
         termination_by b",
    );
}

// ═══════════════════════════════════════════════════════════════════════════
// (q9) THE FULL ROUTE, with its mutation battery — `control_8` at `nat.mul`
// ═══════════════════════════════════════════════════════════════════════════
//
// Side A is the REAL elaborated `fact` (not a hand-built mirror), side B is
// the emitted-MIR contract built exactly as `ArmLowerer` lowers
// `zero_value = NatConst(1)`, `nonzero_value = Mul(Decreasing, Rec)`,
// `rec_arg = Pred` — which is `countdownSum`'s traced body with `from_u64(0)`
// become `from_u64(1)` in the zero arm and `add` become `mul` at the root:
//
// ```text
// _0,_1,_4,_5,_8,_9,_12: Nat   _2,_6,_7,_10,_11: &Nat   _3: bool  (_4,_12 dead)
// bb0: _2 = &_1;  is_zero(move _2) -> _3, bb1
// bb1: switchInt(move _3) [(0, bb3)] otherwise bb2
// bb2: from_u64(const 1u64) -> _0, bb7                        // zero arm
// bb3: from_u64(const 1u64) -> _5, bb4                        // nonzero arm…
// bb4: _6 = &_1; _7 = &_5; sub(move _6, move _7) -> _8, bb5
// bb5: fact(move _8) -> _9, bb6
// bb6: _10 = &_1; _11 = &_9; mul(move _10, move _11) -> _0, bb7
// bb7: return
// ```

const FACT_SELF_PATH: &str = "clean_origin_wf_rec::fact";
const BIGNUM_SUB: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::sub";
const BIGNUM_ADD: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::add";
const BIGNUM_MUL: &str = "trust_bignum::arith::<impl trust_bignum::Nat>::mul";

fn nat_adt() -> Ty {
    Ty::adt("trust_bignum::Nat", Vec::new())
}

fn nat_adt_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: nat_adt(), name: None }
}

fn nat_adt_ref_local(index: usize) -> LocalDecl {
    LocalDecl { index, ty: Ty::Ref { mutable: false, inner: Box::new(nat_adt()) }, name: None }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn call(callee: &str, args: Vec<Operand>, dest: Place, target: BlockId) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(target),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
    }
}

fn emitted_factorial() -> VerifiableFunction {
    let locals = vec![
        nat_adt_local(0),
        nat_adt_local(1),
        nat_adt_ref_local(2),
        LocalDecl { index: 3, ty: Ty::Bool, name: None },
        nat_adt_local(4),
        nat_adt_local(5),
        nat_adt_ref_local(6),
        nat_adt_ref_local(7),
        nat_adt_local(8),
        nat_adt_local(9),
        nat_adt_ref_local(10),
        nat_adt_ref_local(11),
        nat_adt_local(12),
    ];
    let blocks = vec![
        BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(
                Place::local(2),
                Rvalue::Ref { mutable: false, place: Place::local(1) },
            )],
            terminator: call(
                "trust_bignum::Nat::is_zero",
                vec![Operand::Move(Place::local(2))],
                Place::local(3),
                BlockId(1),
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
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                Place::local(0),
                BlockId(7),
            ),
        },
        BasicBlock {
            id: BlockId(3),
            stmts: Vec::new(),
            terminator: call(
                "trust_bignum::Nat::from_u64",
                vec![Operand::Constant(ConstValue::Uint(1, 64))],
                Place::local(5),
                BlockId(4),
            ),
        },
        BasicBlock {
            id: BlockId(4),
            stmts: vec![
                assign(Place::local(6), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(7), Rvalue::Ref { mutable: false, place: Place::local(5) }),
            ],
            terminator: call(
                BIGNUM_SUB,
                vec![Operand::Move(Place::local(6)), Operand::Move(Place::local(7))],
                Place::local(8),
                BlockId(5),
            ),
        },
        BasicBlock {
            id: BlockId(5),
            stmts: Vec::new(),
            terminator: call(
                FACT_SELF_PATH,
                vec![Operand::Move(Place::local(8))],
                Place::local(9),
                BlockId(6),
            ),
        },
        BasicBlock {
            id: BlockId(6),
            stmts: vec![
                assign(Place::local(10), Rvalue::Ref { mutable: false, place: Place::local(1) }),
                assign(Place::local(11), Rvalue::Ref { mutable: false, place: Place::local(9) }),
            ],
            terminator: call(
                BIGNUM_MUL,
                vec![Operand::Move(Place::local(10)), Operand::Move(Place::local(11))],
                Place::local(0),
                BlockId(7),
            ),
        },
        BasicBlock { id: BlockId(7), stmts: Vec::new(), terminator: Terminator::Return },
    ];
    VerifiableFunction {
        name: "fact".into(),
        def_path: FACT_SELF_PATH.into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks,
            arg_count: 1,
            return_ty: nat_adt(),
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
    }
}

fn factorial_recognised() -> WfRecBody {
    WfRecBody {
        zero_value: RecBodyExpr::NatConst(1),
        nonzero_value: RecBodyExpr::Mul(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred],
        measure_index: 0,
    }
}

/// **THE ADMIT.** The emitted body reads back as the planned trio, and the
/// whole route ends at the F-layer kernel gate with side A the REAL
/// elaborator's — so the `HMul.hMul … instHMulNat` the island emits is
/// identified with side B's raw `Nat.mul` by the kernel, on a STUCK `dite`,
/// which is the only place that identification counts.
#[test]
fn probe_q9_factorial_admits_end_to_end() {
    let extracted = emitted_factorial();
    assert_eq!(
        recognize_wf_nat_rec(&extracted),
        Some(factorial_recognised()),
        "the emitted-and-extracted body must read back as the planned recursion"
    );

    let env = island(FACT).expect("fact elaborates");
    let plan = plan_clean_origin_body(&env, "fact").expect("fact plans");
    assert_eq!(plan.shape(), &factorial_shape());
    let faithful =
        admit_lowering(&env, &plan, &extracted).expect("the emission must pass the F-layer gate");
    assert_eq!(faithful.name(), "fact");
    assert_eq!(faithful.admitted_at(), &Ty::BignumNat);
    assert_eq!(faithful.method(), FaithfulnessMethod::WellFoundedFunctionalDefeq);
    eprintln!("ROW q9 fact route | FAITHFUL by WellFoundedFunctionalDefeq");
}

/// **THE MUTATIONS.** An ADMIT with no refused sibling is not a measurement.
/// Every row differs from the admitted emission in exactly ONE construct.
#[test]
fn probe_q9b_factorial_mutations_refuse() {
    let env = island(FACT).expect("fact elaborates");
    let plan = plan_clean_origin_body(&env, "fact").expect("fact plans");

    // (a) THE OPERATION ITSELF. The emitted root computes `+` where side A
    //     says `*`. This is the mutation the whole row exists to catch, and it
    //     is caught STRUCTURALLY — the recognizer reads `Add`, the plan says
    //     `Mul`, and the shapes are compared by direct equality.
    let mut wrong_op = emitted_factorial();
    if let Terminator::Call { func: callee, .. } = &mut wrong_op.body.blocks[6].terminator {
        *callee = BIGNUM_ADD.into();
    }
    let refusal = admit_lowering(&env, &plan, &wrong_op)
        .expect_err("`add` where the definition says `mul` must never emit");
    assert!(
        matches!(refusal, EmitRefusal::LoweringShapeMismatch { .. }),
        "expected the structural catch, got {refusal:?}"
    );
    assert!(refusal.is_compiler_defect(), "a wrong emission is a compiler defect");

    // (b) THE SAME MUTATION AT THE KERNEL, so the structural catch is never
    //     the only thing standing there. Hand the gate a side B built from the
    //     WRONG reading through the REAL frozen producer: the kernel must
    //     refuse `Nat.add` against side A's `HMul.hMul`.
    let wrong_reading = WfRecBody {
        nonzero_value: RecBodyExpr::Add(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        ..factorial_recognised()
    };
    let reflected = trust_clean_origin::reflect_wf::reflect_wf_functional(&env, "fact", &wrong_reading, trust_clean_origin::WfLowering::OnParameter)
        .expect("the frozen producer renders whatever reading it is given");
    let gate = trust_clean_origin::gate::check_faithful_wf_functional(
        &env,
        "fact",
        &reflected,
        plan.result_carrier(),
    );
    assert!(
        gate.is_err(),
        "the KERNEL must separate `Nat.add x rec` from `HMul.hMul … x rec`; if it does not, \
         the structural catch above is the only thing between `n!` and `n + (n-1)!`"
    );
    eprintln!("ROW q9b add-for-mul | REFUSED structurally AND at the kernel");

    // (c) OPERAND ORDER, at the kernel. `mul` is commutative in VALUE, so this
    //     row measures whether the gate is deciding on the TERM (it is — defeq
    //     on a stuck `dite` is intensional) rather than on arithmetic.
    let swapped = WfRecBody {
        nonzero_value: RecBodyExpr::Mul(
            Box::new(RecBodyExpr::Rec),
            Box::new(RecBodyExpr::Decreasing),
        ),
        ..factorial_recognised()
    };
    let reflected =
        trust_clean_origin::reflect_wf::reflect_wf_functional(&env, "fact", &swapped, trust_clean_origin::WfLowering::OnParameter)
            .expect("renders");
    let swapped_gate = trust_clean_origin::gate::check_faithful_wf_functional(
        &env,
        "fact",
        &reflected,
        plan.result_carrier(),
    );
    assert!(
        swapped_gate.is_err(),
        "MEASURED 2026-08-25: the gate REFUSES `Nat.mul rec x` against side A's \
         `Nat.mul x rec`. `Nat.mul`'s commutativity is a THEOREM in this kernel, not a \
         definitional identity, so defeq on the stuck `dite` separates the two orders — \
         which is what makes the operand order of the emitted call load-bearing rather \
         than incidental."
    );
    eprintln!("ROW q9c swapped operands | REFUSED (operand order is decided, not incidental)");

    // (d) FORGED CALLEES at the new row. A table that accepted "anything
    //     ending in `::mul`" would be caught here.
    for forged in [
        "my_crate::arith::<impl my_crate::Nat>::mul",
        "evil_bignum::Nat::mul",
        "trust_bignum::arith::<impl trust_bignum::Nat>::checked_mul",
    ] {
        let mut mutant = emitted_factorial();
        if let Terminator::Call { func: callee, .. } = &mut mutant.body.blocks[6].terminator {
            *callee = forged.into();
        }
        assert!(
            matches!(
                admit_lowering(&env, &plan, &mutant),
                Err(EmitRefusal::LoweringUnrecognised { .. })
            ),
            "`{forged}` must not authenticate as the runtime's `mul`"
        );
    }
    eprintln!("ROW q9d forged callees | 3 near-misses REFUSED");
}

// ═══════════════════════════════════════════════════════════════════════════
// (q10) the boundary that did NOT move
// ═══════════════════════════════════════════════════════════════════════════

/// Adding `*` must not have opened the vocabulary generally. `/` — the next
/// operation over, and the one whose Rust realization PANICS where Clean's is
/// total — must still refuse, and must still name itself (v7/D3).
#[test]
fn probe_q10_division_still_refuses() {
    let source = "def divDown (n : Nat) : Nat := \
                  if h : 0 < n then n / divDown (n - 1) else 1\n\
                  termination_by n";
    match island(source) {
        Err(why) => eprintln!("ROW q10 `/` | ISLAND REJECTS | {}", first_line(&why)),
        Ok(env) => {
            let note = plan_clean_origin_body(&env, "divDown")
                .map(|p| format!("{:?}", p.shape()))
                .expect_err("`/` must stay outside the emittable fragment")
                .note();
            assert!(
                note.contains("HDiv.hDiv") || note.contains("Nat.div"),
                "the catch-all must NAME the construct it refused (v7/D3): {note}"
            );
            eprintln!("ROW q10 `/` | ISLAND OK | CALL REFUSES | {}", first_line(&note));
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
// (q11) the VALUES the run-pass fixture asserts — pinned at the KERNEL first
// ═══════════════════════════════════════════════════════════════════════════

/// `tests/ui/trust/clean_origin_wf_rec_mul.rs` asserts that the EMITTED binary
/// computes these. This probe is what makes them probe-pinned rather than
/// invented: each is a closed `rfl` at the real kernel, so the fixture's
/// expected values and the declaration's meaning cannot drift apart.
///
/// The refuting control is not optional — without it, `rfl` closing on every
/// row would be evidence of nothing.
#[test]
fn probe_q11_factorial_values_at_the_kernel() {
    let sources = format!(
        "{FACT}\n\
         theorem fact_0 : fact 0 = 1 := rfl\n\
         theorem fact_1 : fact 1 = 1 := rfl\n\
         theorem fact_3 : fact 3 = 6 := rfl\n\
         theorem fact_5 : fact 5 = 120 := rfl\n\
         theorem fact_8 : fact 8 = 40320 := rfl"
    );
    island(&sources).expect("every factorial value must COMPUTE by kernel reduction");

    let bad = island(&format!("{FACT}\ntheorem fact_bad : fact 5 = 121 := rfl"));
    assert!(bad.is_err(), "`fact 5 = 121` must be REFUSED, or the rows above are a rubber stamp");
    eprintln!("ROW q11 values | 0!,1!,3!,5!,8! COMPUTE at the kernel; `fact 5 = 121` REFUSED");
}
