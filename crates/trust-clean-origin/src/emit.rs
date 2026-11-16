// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! I5 decision 2, **applied**: the Clean-origin body plan and the round trip
//! that feeds [`crate::gate::check_faithful`] its side B.
//!
//! # What this module is for
//!
//! [`crate::gate`] is the *decision*: given side A (the Clean `def`'s body) and
//! side B (`R(lowered)`), does the kernel identify them? It has no opinion about
//! where side B comes from, deliberately — that keeps the decision auditable in
//! isolation.
//!
//! This module supplies the two halves around it, and it is the **only** way a
//! [`crate::gate::Faithful`] can be obtained for an *emitted* body:
//!
//! * [`plan_clean_origin_body`] reads a Clean `def` out of the kernel
//!   environment and decides whether the compiler knows how to emit it at all,
//!   returning a [`CleanOriginPlan`] — the total-carrier signature plus the
//!   shape. **A plan is not permission to emit.** It is permission to *attempt*
//!   an emission that will then be checked.
//! * [`admit_lowering`] takes the body the compiler actually produced, already
//!   extracted back out of MIR, routes it through the **pre-existing E6
//!   Rust→Clean path**, and puts the resulting term to the gate.
//!
//! # THE ROUTE, AND WHY IT IS NOT CO-AUTHORED
//!
//! ```text
//! mir::Body  --trust_mir_extract::extract_function-->  VerifiableFunction
//!            --trust_types::recognize_admissible_body-->  AdmissibleBody
//!            --trust_spec_elab::admit_projection_function-->  kernel Expr   (side B)
//!            --crate::gate::check_faithful------------->  Faithful | GateRefusal
//! ```
//!
//! Every step of that chain already existed, and every one of them was written
//! for the OPPOSITE direction — E6 kernel-import, which reflects a Rust `fn`
//! into Clean so a contract can name it. None of it was written to make a
//! Clean-origin body pass. That is the whole reason the comparison means
//! something: side A comes from the Clean parser and elaborator, side B comes
//! from the MIR the backend will actually codegen, and the two producers do not
//! know about each other.
//!
//! The corollary is a standing prohibition, the same one that freezes
//! `crates/trust-clean/src/reflect.rs`: **if a Clean-origin body fails this
//! gate, the fix is never to edit `recognize_admissible_body` or
//! `admit_*_function`.** Those are side B's producers. Editing them to make
//! side B agree with side A converts the gate into a round trip.
//!
//! # Why the round trip goes through MIR rather than short-circuiting
//!
//! The obvious "optimisation" is to skip the emission and compare the plan
//! against side A directly — the plan was derived from side A, so it would
//! always agree. That is exactly the failure mode: it would check that the
//! compiler read the Clean term correctly and say nothing about what it
//! EMITTED. The gate's subject is the emitted body, so the emitted body is what
//! must be re-read. `tests/control_3_clean_origin_emitter_mutation.rs` mutates
//! the emitted body — not the plan — and requires a refusal.
//!
//! # The fragment, stated as a measurement
//!
//! Today: **`Projection`** (a direct parameter, `fun x0 … x_{n-1} => x_i`),
//! **`InductiveProjection`** (a structurally recursive/fold-defined function
//! proved extensionally equal to a parameter by a closed axiom-free recursor
//! proof), **`WrappingBinOp`** (a single wrapping `+`/`-`/`*` over parameters
//! and in-range numerals), **`Composed`** (a nested tree of those same ops,
//! `2..=COMPOSED_MAX_OPS` nodes), **`Select`** (the parameter-select `ite`,
//! R2/C5a) and **`SelectLiteral`** (the param-vs-const compare
//! `if a ⊲ 10 then a else b` for `<`, `<=` or propositional `=`, R2/C9 —
//! numeral strictly on the comparison's right). Ordinary projection and
//! inductive projection support every exact
//! carrier, including the unbounded `trust_bignum::Nat`; the arithmetic and
//! select shapes retain their documented restriction that EVERY signature
//! position sits at one unsigned machine width. All are what
//! the kernel demonstrably admits: the probe corpus
//! (`tests/e6-fragment-probe/`) runs this same comparison in the opposite
//! direction and records `Projection` as discharging (d01–d05, d08, d09) and
//! the composed chain discharging end-to-end (f21), and
//! `tests/fragment_widening_probes.rs` measured the single-op arithmetic
//! ADMITs in both side-A spellings — including numeral operands (probes
//! a4–a6, 2026-08-19) — and the nested `(a + b) * a` ADMIT (probe_f) before
//! the respective emitter arms existed. The C10/C11 recursion probes also pin
//! the raw defeq boundary and the structural-induction closure before the
//! compiler arm is selected. **Every** `ConstantUint` probe
//! remains `defeq-rejected` or `unproved` on the compiler lane (f04,
//! f06–f09): the shape that looks simplest is still one the pipeline refuses
//! — R1 did NOT flip that pin, nor any other nullary/root-literal boundary.
//!
//! R2 (2026-08-22) adds **`WellFoundedNatRec`** — single-parameter
//! well-founded `Nat` recursion at the bignum carrier, guarded by
//! `if h : 0 < n`, with exactly ONE self-call at `n - 1` and branch values
//! over the parameter / `Nat` numerals / `+`. Its measured ground is
//! `tests/r2_wf_equation_probes.rs` (w0–w9 — w1 pins the fix spine's
//! spelling, w5–w7 derive the F-layer judgment, w7/d4 records the escape) and
//! `tests/r2_axiom_closure_probes.rs` (c0–c9 — the escape reproduced at c1 and
//! closed at c2). Its gate is [`crate::gate::check_faithful_wf_functional`],
//! never `check_faithful_equations` (a fix spine has no minor premises) and
//! never the whole-term lane (side B would have to mint an accessibility
//! witness MIR does not contain). Its measured boundaries are stated in the
//! refusals: a decrease by more than one stays out (the emitted predecessor is
//! `Nat::sub(&n, &1)`), a multi-parameter fix stays out (R3, and blocked in
//! `first-party/clean` besides — **BOTH HALVES OF THAT CLAUSE WERE MEASURED
//! FALSE AND R3a RETIRED IT, 2026-08-26; see the note below**), and a WF
//! verdict cannot leave its crate (no
//! wire tag — see [`crate::admission::mint_encoded_digest_for_export`]).
//!
//! **R3a (2026-08-26) WIDENS `WellFoundedNatRec` FROM ARITY 1 TO ARITY N**,
//! with the measure still a SINGLE parameter decreasing by exactly one. Both
//! halves of R2's "a multi-parameter fix stays out (R3, and blocked in
//! `first-party/clean` besides)" were measured false at the same pin: what
//! `first-party/clean` refuses is a measure naming more than one parameter
//! (a lexicographic or packed measure), not a recursion naming more than one
//! parameter, and a two-parameter recursion with a one-parameter measure
//! elaborates and kernel-checks today (`tests/r7_arity_widening_probes.rs`
//! q1). The arity limit was THIS crate's, so the widening needed no pin move
//! and no `compiler/**` edit — the compiler-side materializer was already
//! generic in `template.arg_count` and `TemplateTy::Param { index }`.
//!
//! What that costs in checking power: NOTHING, and the accounting is worth
//! stating because "more shapes admit" reads like less checking. The extra
//! self-call arguments are ordinary VALUE arguments. They are decided by the
//! type check of side B at side A's own functional type (gate step 7, w7/d1)
//! and by the kernel defeq of the two functionals (step 8, argument-sensitive
//! per w7/d3). The decrease proof is still BORROWED from side A's
//! kernel-checked declaration, side B still writes only the sentinel, and the
//! axiom-closure audit still runs over the term the kernel is handed. Nothing
//! in the widening lets side B author evidence. Its mutation battery is
//! `tests/control_16_wf_arity_emitter_mutation.rs`, whose three new rows are
//! the ones arity created: a swapped SELF-CALL operand pair, a zero test on
//! the wrong parameter, and a wrong threaded-parameter index.
//!
//! **R3c (2026-08-27) TEACHES THE READERS `first-party/clean`'s PHASE-3
//! (SUM-MEASURE) LOWERING, ALONGSIDE PHASE 2 AND NOT INSTEAD OF IT.** A
//! `termination_by` measure that mentions SEVERAL parameters is now lowered by
//! the pin (`wf_recursion::sum_measure`) as a course-of-values recursion on the
//! measure's VALUE, and that term is a shape none of this crate's readers could
//! parse: an `n`-DEPENDENT Pi motive where they demand a constant `Nat` arrow
//! tower, a spine seeded `(Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))` where they
//! expect only the parameters, one EXTRA hypothesis binder in the functional,
//! and an `arity + 3`-argument `rec` — FIVE at arity 2 — whose decrease proof is
//! LAST rather than second. [`WfLowering`] names the two, and every layout
//! number downstream is derived from it plus the arity.
//!
//! What landed, and what did not:
//!
//! * [`read_wf_sum_measure_anatomy`] READS the shape, component by component,
//!   fail-closed. [`recognise_wf_nat_rec`] classifies by ARITHMETIC (`N + 5`
//!   against `N + 7` at the same peel depth) and routes to it, so a phase-3
//!   body now gets a refusal that names the lowering instead of one that
//!   reports a malformed spine that is not there.
//! * [`crate::gate::check_faithful_wf_functional`] parses a phase-3 side A for
//!   ITSELF and borrows its decrease slots at the sum-measure layout — measured
//!   end to end in `tests/phase3_spine_reader_probes.rs` q4, with the
//!   wrong-slot, wrong-arity and wrong-telescope side Bs refused at c2.
//! * NOTHING EMITS phase 3 yet, and the refusal says so with its two reasons:
//!   the guard sits on a SOURCE parameter rather than on the fix's own
//!   recursion variable, and `reflect_wf::reflect_wf_functional` — the side-B
//!   PRODUCER — renders only the phase-2 telescope. Those are producer changes,
//!   not reader ones.
//!
//! Phase 2 is byte-identical, and that is a test rather than a claim:
//! `phase3_spine_reader_probes` p2 pins an existing phase-2 body's plan against
//! a literal and every phase-2 layout number against the constants R2/R3a
//! shipped.
//!
//! **R3d (2026-08-27) CLOSES THE THIRD BULLET: PHASE 3 IS EMITTED.** The
//! two-argument `gcd` the pin ratified —
//! `def gcdB (a b : Nat) : Nat := if h : 0 < b then gcdB ((a-b)+(b-a))
//! (a-(a-b)) else a` with `termination_by a + 2*b` — plans, materializes, reads
//! back, reflects, passes the F-layer gate and RUNS from Rust with no fuel
//! wrapper (`tests/ui/trust/clean_origin_wf_rec_gcd_direct.rs`,
//! `gcd_phase3_probes` p5). The bullet's two reasons turned out to be one:
//!
//! * *"the guard sits on a SOURCE parameter"* was TRUE and not a blocker. The
//!   emitted zero test borrows a PARAMETER'S LOCAL either way, which is exactly
//!   what the materializer already emits; what was missing is a reader that
//!   DISCOVERS which parameter ([`recognise_wf_sum_measure_rec`]) instead of
//!   reading it off the spine's major premise. [`WfLayout`] carries the
//!   lowering now, and `measure_index` means the GUARDED parameter at both.
//! * *"the side-B producer renders only the phase-2 telescope"* was the real
//!   one, and it needed one thing this lane had never had: side B cannot author
//!   the MEASURE. It occupies the `rec` binder's type, the `hm` binder's type
//!   and each self-call's major premise, and MIR contains no measure at all.
//!   Those three positions are now written as
//!   [`crate::gate::MEASURE_SLOT_SENTINEL`] and BORROWED beside the decrease
//!   proof — the same accounting, at three more positions, all of them
//!   termination plumbing rather than program.
//!
//! [`CleanOriginShape::WellFoundedNatRec`] gained a `lowering` FIELD rather
//! than a sibling variant, because the emitted MIR is byte-identical between
//! the two: one zero test, two arm regions, one self-call with one operand per
//! parameter. Two variants for one MIR contract is the "one body, two plans"
//! hazard this crate refuses everywhere else.
//!
//! R1 (2026-08-21) adds **`StructuralNatRec`** — single-parameter structural
//! `Nat` recursion in equation form at the bignum carrier, one recursive use
//! per step, case values over the parameter / `Nat` numerals / `+`. Its
//! measured ground is `tests/r1_equation_probes.rs` (e1–e5, s2–s8: the s2
//! vacuity pin is WHY its gate is the abstract-ih judgment,
//! [`crate::gate::check_faithful_equations`], never whole-term defeq and
//! never the constant-citing per-equation spelling), and its measured
//! boundaries are stated in the refusals: the u64-carrier recursor stays out
//! (e2 — open u64 equations are not definitional), `WellFounded.fix` stays
//! out (R2's seam), fib waits on the pair carrier (e4 measured its `.cov`
//! equations green; `control_7` pins both refusals).
//!
//! Per ruling v7/D2 that is a statement of where we are, never a design. The
//! way to widen it is to make the two sides agree at the kernel — extending the
//! COMPILER — never to relax the gate.

use std::time::{Duration, Instant};

use clean_kernel::name::NameInner;
use clean_kernel::{
    ConstantKind, DeclarationVerification, Environment, Expr, ExprKind, Level, Literal, Name,
};
use trust_clean_carrier::{
    Carrier, CarrierRefused, CarrierSignature, CleanType, carrier_signature_for,
};
use trust_spec_elab::{Domain, MachineUIntWidth};
use trust_types::admissible_body::{
    AdmissibleBody, ArithBinOp, ArithExpr, ArithOperand, BeqOperand, BoolBinOp, BoolValueBody,
    RawBinOpKind, RecBodyExpr, SelectCmp, StructuralRecBody, WfRecBody, recognize_admissible_body,
    recognize_bool_value, recognize_raw_binop, recognize_structural_rec, recognize_wf_nat_rec,
    recognize_wf_sum_measure_rec,
};
use trust_types::{Ty, VerifiableFunction};

use crate::gate::{
    Faithful, FaithfulnessMethod, GateRefusal, check_faithful_equations_for_name,
    check_faithful_for_name, check_faithful_for_name_with_deadline,
    check_faithful_wf_functional_for_name,
};
use crate::table;

/// Declaration-wide rails for recursive projection discovery. A wider
/// signature remains a valid Clean definition, but it is outside this emitted
/// fragment rather than receiving work proportional to user-controlled arity.
const INDUCTIVE_PROJECTION_MAX_ARITY: usize = 8;
const INDUCTIVE_PROJECTION_MAX_CANDIDATES: usize = 8;
const INDUCTIVE_PROJECTION_TOTAL_TIMEOUT: Duration = Duration::from_secs(2);

/// Maximum operators in a composed Boolean body. This bounds emission work;
/// the independently authored E6 reader retains its own limits.
pub const BOOL_EXPRESSION_MAX_OPS: usize = 32;
const BOOL_EXPRESSION_MAX_DEPTH: usize = 64;

/// A pure, total Boolean expression read from the original Clean declaration.
/// This is emission data, never the reflected subject of the faithfulness gate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BoolExpr {
    /// A zero-based source parameter.
    Param(usize),
    /// A Boolean literal inside an expression (not a new constant-body lane).
    Literal(bool),
    /// Boolean negation.
    Not(Box<Self>),
    /// Strict conjunction; the operands are pure and total.
    And(Box<Self>, Box<Self>),
    /// Strict disjunction; the operands are pure and total.
    Or(Box<Self>, Box<Self>),
}

impl BoolExpr {
    fn check_bounds(&self, arity: usize, depth: usize, ops: &mut usize) -> bool {
        if depth > BOOL_EXPRESSION_MAX_DEPTH {
            return false;
        }
        match self {
            Self::Param(index) => *index < arity,
            Self::Literal(_) => true,
            Self::Not(child) => {
                *ops += 1;
                *ops <= BOOL_EXPRESSION_MAX_OPS && child.check_bounds(arity, depth + 1, ops)
            }
            Self::And(left, right) | Self::Or(left, right) => {
                *ops += 1;
                *ops <= BOOL_EXPRESSION_MAX_OPS
                    && left.check_bounds(arity, depth + 1, ops)
                    && right.check_bounds(arity, depth + 1, ops)
            }
        }
    }
}

/// Maximum decisions in one Rust-callable unsigned conditional tree.
pub const UINT_CONDITIONAL_MAX_DECISIONS: usize = 32;

/// Pure unsigned conditional dataflow. All operands use the plan signature's
/// one exact machine width; source parameter positions are outermost-first.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UIntConditional {
    /// A bare parameter or in-range unsigned numeral.
    Operand(ArithOperand),
    /// A propositional comparison followed by two independently checked arms.
    If {
        /// Comparison selected by the original proposition.
        cmp: SelectCmp,
        /// Source parameter on the comparison's left.
        left: usize,
        /// Parameter or numeral on the comparison's right.
        right: ArithOperand,
        /// Value when the comparison is true.
        then_branch: Box<UIntConditional>,
        /// Value when the comparison is false.
        else_branch: Box<UIntConditional>,
    },
}

/// The body shapes the compiler knows how to originate from a Clean `def`.
///
/// Deliberately a closed enum. A widening is a new variant plus its own
/// emitter arm plus its own round-trip arm — never a fall-through.
///
/// # Deliberately NOT `#[non_exhaustive]`
///
/// Every other public type in this crate is, because their consumers should
/// fail closed on a variant they do not know. This one is the opposite: its
/// consumer is `rustc_mir_transform`'s emitter, and a variant the emitter does
/// not know must be a COMPILE ERROR there, not a runtime fall-through.
/// `#[non_exhaustive]` would force that emitter to carry a `_ =>` arm, and a
/// `_ =>` arm on the enum that decides what MIR gets emitted is exactly the
/// place a future shape would silently acquire the wrong body.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CleanOriginShape {
    /// `fun x0 … x_{n-1} => x_i` — return the `projected`-th **source**
    /// parameter verbatim. The MIR is one block: `_0 = move _{projected+1};
    /// return`.
    Projection {
        /// The 0-based *source* parameter position returned. Not the de Bruijn
        /// index: under `n` binders, source parameter `i` is `BVar(n-1-i)`, and
        /// getting that inversion backwards is precisely the one-construct
        /// mistranslation this lane can make.
        projected: usize,
    },
    /// A recursive/fold-defined Clean body proven extensionally equal to a
    /// source-parameter projection by a closed, axiom-free structural-
    /// induction proof. The emitted MIR is deliberately the same one-block
    /// projection as [`Self::Projection`]; the distinct variant prevents an
    /// inductive verdict from being mistaken for syntactic/defeq recognition.
    /// [`admit_lowering`] re-reads that MIR and re-runs the induction gate, so
    /// the plan-time proof is never the permission that escapes.
    InductiveProjection {
        /// The 0-based source parameter returned.
        projected: usize,
    },
    /// `fun x0 … x_{n-1} => <numeral>` at an unsigned machine width, for **any
    /// `n` including zero** (§6f landing 2) — a `def` whose whole peeled body is
    /// an in-range carrier numeral, in either measured spelling
    /// (`{C}.ofNat v`, or `OfNat.ofNat {C} v (instOfNat{C} v)`). The MIR is one
    /// block: `_0 = const v_u{w}; return`.
    ///
    /// **Width is deliberately not a field**, exactly as for
    /// [`Self::WrappingBinOp`]: it comes from the plan's [`CarrierSignature`],
    /// so there is no second place a width can disagree.
    ///
    /// **Arity is deliberately not a field either**, and that is this shape's
    /// one soundness-relevant fact. `AdmissibleBody::ConstantUint` ERASES the
    /// arity — `fragment_widening_probes::probe_e3` measured that a unary body
    /// reads back as the same value a nullary one does — so the arity is bound
    /// on side B and nowhere else: [`admit_lowering`] requires
    /// `extracted.body.arg_count == plan.signature.arity()` before any
    /// reflection runs, and the reflection's own lambda count is that same
    /// `arg_count`. Carrying the arity here as well would create the second
    /// place probe_e3's defect lived in.
    ///
    /// Kernel ground: `landing2_selection_probes` l2_p1 (the two producers mint
    /// the same term at zero parameters, so the routing repair probe_e3
    /// diagnosed is a routing change and not a semantic one), l2_p2/l2_p3 (ADMIT
    /// at arity 0, 1 and 2 in both numeral spellings), l2_p2b (width skew
    /// refused in both directions) and l2_p3b (the arity erasure refused in both
    /// directions).
    ConstantUint {
        /// The returned numeral, re-range-checked against the result carrier's
        /// width on the sealed plan.
        value: u128,
    },
    /// A single wrapping binary op over two operands, each a source parameter
    /// or an in-range numeral, at ONE unsigned machine width shared by every
    /// signature position — used or not, because the reflected side B
    /// (`admit_expr_function`) is single-domain over ALL parameters. The MIR:
    /// `bb0: _0 = Call(u{w}::wrapping_{op}, [l, r]) -> bb1: Return`.
    ///
    /// `ArithBinOp`/`ArithOperand` are REUSED from
    /// `trust_types::admissible_body`, not redefined — a vocabulary reuse, not
    /// a producer edit: the values here come from the Clean term, the values
    /// on the recognizer side come from the emitted MIR, and the structural
    /// comparison in [`admit_lowering`] is then direct equality. Width is
    /// deliberately NOT a field — it is derived from the plan's
    /// [`CarrierSignature`], so there is no second place a width can disagree.
    WrappingBinOp {
        /// The operation (`wrapping_add`/`wrapping_sub`/`wrapping_mul`).
        op: ArithBinOp,
        /// Left operand: 0-based source parameter or in-range literal.
        left: ArithOperand,
        /// Right operand: 0-based source parameter or in-range literal.
        right: ArithOperand,
    },
    /// A NESTED composition of wrapping `+`/`-`/`*` — at least two op nodes —
    /// over source parameters and in-range numerals, every signature position
    /// at ONE unsigned machine width (`fun a b => (a + b) * a`). The MIR is
    /// the linear call chain `recognize_call_chain` was written for: one
    /// authenticated `u{w}::wrapping_{op}` `Call` per tree node in POST-ORDER
    /// through fresh temporaries, the root writing `_0`, then `Return`.
    ///
    /// The vocabulary is `trust_types::admissible_body::ArithExpr`, REUSED
    /// for the same reason `WrappingBinOp` reuses `ArithBinOp`/`ArithOperand`
    /// — a vocabulary reuse, not a producer edit: the tree here comes from
    /// the Clean term, the recognizer's from the emitted MIR, and the
    /// structural comparison in [`admit_lowering`] is direct equality. Its
    /// leaves are `Param | Const` and its nodes are binops, so a dangling
    /// intermediate reference is unrepresentable; the invariants the type
    /// cannot carry — node count in `2..=`[`COMPOSED_MAX_OPS`], leaf bounds —
    /// are re-checked on the sealed plan by [`plan_clean_origin_body`]. Width
    /// is derived from the plan's [`CarrierSignature`], exactly as for
    /// `WrappingBinOp`.
    Composed {
        /// The composed expression tree, in the shape the recognizer reports
        /// it. Emission flattens it by post-order traversal.
        expr: ArithExpr,
    },
    /// `fun x0 … x_{n-1} => if xl ⊲ xr then xt else xe` (R2/C5a) — the
    /// parameter-select `ite`, at ONE unsigned machine width across every
    /// signature position (the reflected side B, `admit_select_function`, is
    /// single-domain). All four positions are SOURCE parameters — constant
    /// arms and computed conditions are outside the fragment (e6 probe f03
    /// pins the former). The MIR is the four-block O0 diamond
    /// `recognize_select` was written for, years before this lane.
    ///
    /// `SelectCmp` is REUSED from `trust_types::admissible_body`, same as the
    /// arithmetic vocabulary: plan/recognition agreement stays direct
    /// equality. Kernel ground: `probe_h_select_admits` — check_faithful
    /// ADMITS the reflected diamond against the island `ite`, refuses swapped
    /// arms, and refuses even the Le-for-Lt instance swap (defeq is
    /// intensional on the stuck `ite`).
    Select {
        /// The comparison (`<`, `<=`, `==`); `!=`/`>`/`>=` are outside both
        /// the recognizer and the elaborator, and fail closed at recognition.
        cmp: SelectCmp,
        /// 0-based source parameter on the comparison's left.
        cmp_left: usize,
        /// 0-based source parameter on the comparison's right.
        cmp_right: usize,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
    /// `fun x0 … x_{n-1} => if xl ⊲ LIT then xt else xe` (R2/C9) — the
    /// param-vs-const compare, at ONE unsigned machine width across every
    /// signature position. The literal is STRICTLY the comparison's RIGHT
    /// operand, in either numeral spelling on side A; a literal on the LEFT
    /// (`if 10 < a`) is outside the fragment and fails closed, mirroring the
    /// reflected side B (`admit_select_literal_function`), whose signature
    /// cannot even spell it. Arms remain bare source parameters in this
    /// narrow shape; constant arms route through [`Self::SelectOperands`].
    ///
    /// The MIR is the same four-block O0 diamond as [`Self::Select`], with
    /// the comparison's right operand an inline scalar constant. Kernel
    /// ground: `probe_i_select_literal_admits` plus
    /// `probe_i5_select_literal_le_and_propositional_eq_real_elaboration_admit`
    /// — check_faithful ADMITS the reflected trees for `<`, `<=` and
    /// propositional `=`, while wrong comparison, instance, operand, literal
    /// and arm mutations refuse.
    SelectLiteral {
        /// The comparison (`<`, `<=`, `==`), as for [`Self::Select`].
        cmp: SelectCmp,
        /// 0-based source parameter on the comparison's left.
        cmp_param: usize,
        /// The numeral the parameter is compared against — the comparison's
        /// right operand, re-range-checked on the sealed plan.
        literal: u128,
        /// Parameter returned when the comparison holds.
        then_param: usize,
        /// Parameter returned otherwise.
        else_param: usize,
    },
    /// `fun x0 … x_{n-1} => if xl ⊲ <rhs> then <then> else <else>` (§6f
    /// LANDING 3) — the GENERAL select, whose comparison right-hand side and
    /// **both arms** are [`ArithOperand`]s: a source parameter or an in-range
    /// numeral. `if a < b then a else 0`, `if a < b then 1 else 0`,
    /// `if a < 10 then a else 0`, `if a < 1 then 7 else a`.
    ///
    /// # Why this is not a new ROW, and why it is a new SHAPE
    ///
    /// The kernel HEAD is unchanged — `ite` at `<` is `ite` at `<` whether its
    /// arms are parameters or numerals — so no [`crate::table`] row, selector
    /// or realization moves, and [`crate::table::ladder_row`] maps this rung
    /// onto the SAME `select.{lt,le,eq}` rows [`Self::Select`] maps onto. What
    /// changed is the ARMS, and an arm is dataflow, which side B owns. It is
    /// nevertheless a distinct SHAPE because the plan is what the emitter
    /// builds from, and a numeral arm is a different instruction from a
    /// parameter copy.
    ///
    /// # It is DISJOINT from [`Self::Select`] / [`Self::SelectLiteral`]
    ///
    /// `recognise_select_ite` mints this variant only when at least one ARM is
    /// a numeral; a bare-parameter select keeps its existing variant, byte for
    /// byte, so every pin on those shapes is untouched. The sealed plan
    /// re-checks that invariant, because a `SelectOperands` with two parameter
    /// arms would be a second spelling of one shape — the exact "two
    /// representations of one thing" hazard the tree refuses everywhere else.
    ///
    /// The MIR is the same four-block O0 diamond as [`Self::Select`], with the
    /// arm assignments and the comparison's right operand each an inline
    /// scalar or a parameter copy. Kernel ground: `landing3_selection_probes`
    /// l3_p2 (ADMIT against the REAL elaboration, with the wrong-value,
    /// swapped-arm, parameter-for-constant and Le-for-Lt mutants refused),
    /// l3_p3 (the same across `<=`, both-arms-constant, a literal comparison
    /// and arity 1) and l3_p4 (the general producer reproduces both frozen
    /// select producers' terms exactly on their overlap).
    SelectOperands {
        /// The comparison (`<`, `<=`, `==`), as for [`Self::Select`].
        cmp: SelectCmp,
        /// 0-based source parameter on the comparison's left. A numeral on the
        /// LEFT is not a fragment decision: it does not ELABORATE
        /// (`landing3_selection_probes::l3_p6`).
        cmp_left: usize,
        /// The comparison's right operand: a parameter or an in-range numeral.
        cmp_right: ArithOperand,
        /// The value when the comparison holds.
        then_arm: ArithOperand,
        /// The value otherwise.
        else_arm: ArithOperand,
    },
    /// A bounded tree of unsigned selects over parameter comparisons and
    /// parameter/numeral leaves. At least two selects keep this disjoint from
    /// the existing single-select shapes. Emission is checked against the
    /// original declaration through the independent E6 emitted-body reader.
    UnsignedConditional {
        /// The exact source-side conditional tree; the signature owns its width.
        expr: UIntConditional,
    },
    /// `fun x0 … x_{n-1} => if xl == <rhs> then <then> else <else>` (§6f
    /// LANDING 6) — the select whose branch condition is written with the
    /// idiomatic `==` rather than the propositional `=`.
    ///
    /// # It is a DIFFERENT SHAPE because it is a different KERNEL TERM
    ///
    /// `==` is not a fourth comparison and not a flag on [`Self::Select`]. It
    /// states the condition as a **`Bool`-level decision lifted back to a
    /// proposition** — measured at every machine width by
    /// `landing5_selection_probes::l5_p1`:
    ///
    /// ```text
    /// ite.{1} {C}
    ///   (Eq.{1} Bool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r)
    ///                Bool.true)
    ///   (instDecidableEqBool (BEq.beq.{0} {C} (…) l r) Bool.true)
    ///   t e
    /// ```
    ///
    /// while `a = b` states it as `Eq {C} l r` at `instDecidableEq{C}`. The two
    /// are **not definitionally equal** — the Clean island refuses even
    /// `theorem … := rfl` between the two `ite`s (`l5_p3`) — so they are two
    /// terms, not two renderings, and a body emitted for one cannot be gated
    /// against the other.
    ///
    /// # THE EMITTED MIR IS DIFFERENT TOO, and that is what landing 6 pays
    ///
    /// Landing 5 landed the producer, measured the kernel, and then REFUSED to
    /// serve the demand, because both spellings realized one MIR — one
    /// `BinOp::Eq`, one `SwitchInt` — and side B, which reads only the emitted
    /// body, could not tell them apart while the kernel could. This shape
    /// emits the TWO-STEP diamond instead: the `Bool` decision, its
    /// `= Bool.true` lift, then the branch
    /// ([`crate::materialize::MirShape::BoolDecisionBranch`]). The emitter
    /// moved to meet the reader; the reader was not widened to accept an
    /// ambiguous body.
    ///
    /// The operand vocabulary is landing 3's, unchanged: the comparison's
    /// right-hand side and both arms are [`ArithOperand`]s. Unlike
    /// [`Self::SelectOperands`] there is NO disjointness invariant against
    /// bare-parameter arms, because there is no narrower sibling shape for the
    /// `==` spelling — one shape, one plan, and nothing to be a second spelling
    /// OF.
    ///
    /// Kernel ground: `landing5_selection_probes` l5_p1 (side A pinned
    /// construct by construct at four widths), l5_p4 (the producer ADMITS
    /// against the REAL elaboration across the whole operand vocabulary, with
    /// nine refused mutations) and `landing6_selection_probes` l6_p2 (the whole
    /// pipeline: plan, emitted two-step diamond, side B's reader, the producer
    /// and the gate) / l6_p3 (the two realizations are not interchangeable in
    /// EITHER direction).
    SelectBeq {
        /// 0-based source parameter on the decision's left. A numeral on the
        /// LEFT does not elaborate (`landing3_selection_probes::l3_p6`).
        cmp_left: usize,
        /// The decision's right operand: a parameter or an in-range numeral.
        cmp_right: ArithOperand,
        /// The value when the decision holds.
        then_arm: ArithOperand,
        /// The value otherwise.
        else_arm: ArithOperand,
    },
    /// **§6f LANDING 8** — [`Self::SelectBeq`]'s tree with the two coordinates
    /// landing 6 fixed now read out of the kernel term:
    ///
    /// ```text
    /// def q (a b : UInt64) : UInt64 := if (a &&& 1) == 0 then a else b
    /// def r (a b : UInt64) : UInt64 := if (a == b) = false then a else b
    /// ```
    ///
    /// # Two widenings, one shape, and why they are not two
    ///
    /// They are the same frame — the `Bool` DECISION, its LIFT to a
    /// proposition, then the branch — with a different operand vocabulary and a
    /// different lift constant. Both are realized by
    /// [`crate::table::MirShape::BoolDecisionBranch`], which no other row
    /// realizes, so `select.beq` still declares `MirAliasing::Unique`
    /// truthfully and the row set does not move (landing 3's finding, applied
    /// to a second position: the table selects VOCABULARY, and an operand and a
    /// polarity are both read back out of the emitted bytes by side B).
    ///
    /// # DISJOINT from [`Self::SelectBeq`], and the invariant is on the SEALED
    /// PLAN
    ///
    /// A `true` scrutinee with two LEAF operands is `SelectBeq` byte for byte,
    /// so every pin landing 6 and `control_13` put on that shape is untouched.
    /// `recognise_beq_general_select_ite` cannot mint it; the sealed plan
    /// re-checks it anyway, so "one body has one plan" is a property of the
    /// plan rather than of one recogniser.
    ///
    /// # THE DIVISOR RULE APPLIES INSIDE AN OPERAND
    ///
    /// A [`BeqOperand::RawBin`] with `Div`/`Rem` admits only a strictly
    /// positive numeral right leaf, for landing 7's measured reason: Clean's
    /// `{C}.div`/`.mod` are TOTAL and Rust's `/`/`%` PANIC. The rule is stated
    /// once, in `recognise_raw_binop_leaf`, and re-checked on the sealed plan.
    ///
    /// Kernel ground: `landing8_selection_probes` l8_p1 (side A pinned
    /// construct by construct at u8/u16/u32/u64 for all four operators, in both
    /// decision positions, with the computed operand appearing VERBATIM in the
    /// proposition and in the instance — no normal form anywhere), l8_p2 (the
    /// four measured scrutinee spellings, their defeq bridges, and the four
    /// disequality trees pairwise non-defeq), l8_p3/l8_p4 (the whole pipeline
    /// through `admit_lowering`) and `control_15` (fourteen refused mutations).
    SelectBeqGeneral {
        /// The constant the `Bool` decision is lifted against: `true` for the
        /// `==` spelling, `false` for `(a == b) = false`.
        ///
        /// **A POLARITY, and the one field in this shape whose mistake is a
        /// wrong binary rather than a refusal.** It is transcribed into the
        /// emitted `Eq(_d, const <scrutinee>)` and read back from there, never
        /// compensated for by swapping the arms or the `SwitchInt` targets —
        /// landing 6 refused that in advance, and l8_p2 measures that the
        /// arm-swapped `==` body is NOT definitionally equal to this one even
        /// though it computes the same function.
        scrutinee: bool,
        /// The decision's LEFT operand.
        cmp_left: BeqOperand,
        /// The decision's RIGHT operand.
        cmp_right: BeqOperand,
        /// The value when the lifted proposition holds.
        then_arm: ArithOperand,
        /// The value otherwise.
        else_arm: ArithOperand,
    },
    /// `fun x0 … x_{n-1} => xl <op> xr` for `<op>` one of the raw-binop rows'
    /// operators — `&&&`, `|||`, `/`, `%` (§6f LANDING 7) and `^^^`, `>>>`
    /// (clean `bf31976f48`, 2026-09-23) — at an unsigned machine width: the
    /// operators whose realization is a BARE `Rvalue::BinaryOp` rather than a
    /// call to a marker-authenticated `core::num` primitive. The authority on
    /// the set is `table::raw_binop_rows`; this list is a reader's summary.
    ///
    /// # Why it is not a fourth [`ArithBinOp`] on [`Self::WrappingBinOp`]
    ///
    /// Two reasons, and both are structural rather than stylistic:
    ///
    /// * `ArithBinOp` is `AdmissibleBody::Arithmetic`'s operand, and
    ///   `AdmissibleBody` is the vocabulary of the **gate-free E6
    ///   kernel-import direction** — `trust_certify::clean_island::
    ///   admit_function_into` matches it exhaustively — so a variant there
    ///   widens what may be imported as a defining equation with no side A and
    ///   no kernel gate. This lane must widen the CALL direction alone.
    /// * every `ArithBinOp` maps to a [`PrimitiveCallee`] through
    ///   `CalleeSelector::at_width`, a closed match over exactly three wrapping
    ///   identities. `u{N}`'s `&`, `|`, `^`, `/`, `%` and `>>` are on the
    ///   `BitAnd`, `BitOr`, `BitXor`, `Div`, `Rem` and `Shr` trait impls in
    ///   `core::ops` (`bitxor_impl!`, `shr_impl_all!` for `^` and `>>`), not
    ///   in `core::num`, so a fourth variant would demand a callee that does
    ///   not exist. (`core::num` does carry `wrapping_div`, `wrapping_rem` and
    ///   `wrapping_shr`, but they are methods the operators do not call, and
    ///   `RustcTotalPrimitiveMethod::classify` authenticates only
    ///   `wrapping_{add,sub,mul}` — so none of them is a callee either.)
    ///
    /// # THE DIVISOR RULE — the one soundness constraint in this shape
    ///
    /// Clean's `UInt{N}.div` and `.mod` are **TOTAL**: measured at the kernel
    /// (`landing7_selection_probes::l7_p6`), GROUND `7 / 0` reduces to `0` and
    /// `7 % 0` to `7`, where Rust's `/` and `%` PANIC. So for
    /// [`RawBinOpKind::Div`]/[`RawBinOpKind::Rem`] this shape admits ONLY a
    /// `right` that is a strictly positive [`ArithOperand::Const`] — a
    /// statically nonzero divisor, where the two semantics agree on every
    /// input. A variable divisor and a literal zero are both REFUSED on side
    /// A with a v7/D3 note, and refused independently on side B by the frozen
    /// producer, which will not mint `p0 / p1` or `p0 / 0` at all.
    ///
    /// **`/` and `%` are NOT symmetric at an OPEN dividend, and the refusals
    /// differ because of it.** `a / 0` IS definitionally the constant `0` at an
    /// open `a` — `Nat.div` recurses on the DIVISOR — so `a / 0`'s refusal can
    /// and does offer "write the value directly". `a % 0` is NOT definitionally
    /// the identity at an open `a`: `Nat.mod` goes through the fuel-driven
    /// `Nat.modCore`, which recurses on the DIVIDEND, so the term is STUCK.
    /// `l7_p6` asserts both directions and `l7_p8` asserts that the constant
    /// rewrite is offered for `a / 0` and withheld for `a % 0`; a uniform
    /// "recurse on the divisor" reading of this paragraph (which it carried
    /// until 2026-08-25) would justify offering it for both, and the kernel
    /// does not agree. `control_15::half_6` pins the `%` half from the
    /// consumer side.
    ///
    /// `&&&` and `|||` have no such case: `Nat.land`/`Nat.lor` of two values
    /// below `2^N` is below `2^N`, so the round-trip is exact and the MIR
    /// `BitAnd`/`BitOr` computes the same function everywhere.
    ///
    /// Kernel ground: `landing7_selection_probes` l7_p1 (side A pinned
    /// construct by construct at u8/u16/u32/u64 from the REAL elaborator),
    /// l7_p2/l7_p3 (the whole pipeline — plan, emitted body, side B's reader,
    /// the FROZEN producer and the gate), l7_p4 (every mutation refused) and
    /// l7_p6/l7_p8 (the total-vs-panicking boundary, from both sides).
    RawBinOp {
        /// The operator.
        op: RawBinOpKind,
        /// Left operand: 0-based source parameter or in-range numeral.
        left: ArithOperand,
        /// Right operand: 0-based source parameter or in-range numeral. For
        /// `Div`/`Rem` it is a strictly positive numeral, re-checked on the
        /// sealed plan — see THE DIVISOR RULE above.
        right: ArithOperand,
    },
    /// **W6 (Rust-calls-Clean, comparison to `Bool`)** — a `def` whose whole
    /// body is a comparison of two source parameters returned as `Bool`:
    /// `def lt (a b : UInt64) : Bool := a < b`, whose kernel term is
    /// `decide (a < b)` (`<`/`<=`) or `BEq.beq {C} … a b` (`==`). The result
    /// carrier is `Bool`; the MIR is a one-block bare
    /// [`crate::table::MirShape::ComparisonValue`], `_0 = <cmp>(l, r); return`.
    ///
    /// # It is DISJOINT from every select shape
    ///
    /// A select's result carrier is `u{w}` and its body is an `ite`; this
    /// shape's result carrier is `Bool` and its head is `decide`/`BEq.beq`, so
    /// `recognise_select_ite` and the `==` recognisers all decline it (they
    /// require a `UInt` result). It is reflected through the SAME shared
    /// `recognize_admissible_body` chain the projection/constant/arithmetic
    /// shapes use — side B reads it back as
    /// [`trust_types::admissible_body::AdmissibleBody::ComparisonBool`], which
    /// the E6 kernel-import direction ALREADY reads, so routing the CALL lane
    /// through the shared chain exposes nothing new to E6.
    ///
    /// # Operands are PARAMETERS only
    ///
    /// A numeral RIGHT operand elaborates with a Nat-reduced Decidable instance
    /// (`instDecidableNatLt (a.toNat…) 10`), which is NOT definitionally equal
    /// to the carrier-instance term `admit_comparison_function` mints — measured
    /// 2026-09-13, `a < 10 : Bool` is refused fail-closed by the gate. So the
    /// recogniser admits only bare-parameter operands; a literal-operand
    /// comparison-to-`Bool` is a named residual pending a Nat-reduced-instance
    /// producer. `!=` (`Bool.not (BEq.beq …)`) is likewise a residual: it has
    /// no `SelectCmp` and its top-level `Bool.not` is the boolean-connective
    /// lane's, not this one's.
    DecideComparison {
        /// The comparison (`<`, `<=`, `==`).
        cmp: SelectCmp,
        /// 0-based source parameter on the comparison's left.
        cmp_left: usize,
        /// 0-based source parameter on the comparison's right.
        cmp_right: usize,
    },
    /// **W6 (Rust-calls-Clean, boolean negation)** — `def f (b : Bool) : Bool
    /// := not b`, whose kernel term is `Bool.not b`. The result and the operand
    /// carry `Bool`; the MIR is a one-block `_0 = UnaryOp(Not, param); return`
    /// ([`crate::table::MirShape::BoolNotValue`]). Reflected through the
    /// AUTHORED `admit_bool_value_function` via the SEPARATE entry point
    /// `recognize_bool_value` — never the shared `recognize_admissible_body`
    /// chain, so the gate-free E6 import direction cannot reach it.
    BoolNot {
        /// 0-based source parameter negated.
        param: usize,
    },
    /// **W6 (Rust-calls-Clean, boolean connective)** — `def f (a b : Bool) :
    /// Bool := a && b` / `a || b`, whose kernel terms are `and a b` / `or a b`
    /// (def-eq to `Bool.and`/`Bool.or`). Both operands are `Bool` parameters;
    /// the MIR is a one-block `_0 = <BitAnd|BitOr>(l, r); return` at the `bool`
    /// carrier ([`crate::table::MirShape::BoolConnValue`]). Same reflection lane
    /// as [`Self::BoolNot`].
    ///
    /// DISJOINT from the machine-UInt raw-binop shapes: those return a `UInt`
    /// and extract a width; this returns `Bool` and has none. The emitted MIR
    /// is a strict `&`/`|` on `bool`, which computes exactly the total
    /// `Bool.and`/`Bool.or` — short-circuit is observationally identical for
    /// pure `bool` operands.
    BoolConnective {
        /// The connective (`&&`/`||`).
        op: BoolBinOp,
        /// 0-based source parameter on the left.
        left: usize,
        /// 0-based source parameter on the right.
        right: usize,
    },
    /// A bounded tree of pure Boolean operators. Primitive bodies keep their
    /// existing shapes. The emitted body is checked through the pre-existing
    /// general E6 importer, not a reflection reconstructed from this tree.
    BoolExpression {
        /// The original declaration's expression, for emission only.
        expr: BoolExpr,
    },
    /// Structural single-step `Nat` recursion at the bignum carrier (R1,
    /// §6e AS AMENDED): side A is the island's own recursor spine
    /// `fun n => @Nat.rec.{1} (fun _ => Nat) b_A s_A n` (the measured
    /// equation-form output, `recursion_boundary_probes` r3), and the emitted
    /// body is the zero-test/predecessor/self-call contract
    /// `recognize_structural_rec` was extended for. The faithfulness gate for
    /// this shape is [`crate::gate::check_faithful_equations`] — per-minor-
    /// premise defeq with the recursive result held ABSTRACT, plus the
    /// kernel-checked recursive-argument identity, plus equation-set
    /// completeness against the kernel's own minor-premise count — never
    /// whole-term defeq, which is unavailable for fixpoints (§6e), and never
    /// the constant-citing per-equation spelling, which is VACUOUS (probe
    /// s2).
    ///
    /// `RecBodyExpr` is REUSED from `trust_types::admissible_body` (the
    /// `WrappingBinOp` precedent): plan/recognizer agreement stays direct
    /// equality. The vocabulary values here come from the Clean term; the
    /// recognizer's come from the emitted MIR.
    StructuralNatRec {
        /// The zero-case value. Never contains `Rec`/`Pred`.
        base: RecBodyExpr,
        /// The succ-case value. Contains exactly one `Rec`.
        step: RecBodyExpr,
        /// The self-call argument — `Pred` for the whole class; carried (and
        /// re-checked on the sealed plan) rather than implied, so the
        /// emitter, the recognizer and the kernel identity check all name
        /// the same fact.
        rec_arg: RecBodyExpr,
    },
    /// Single-parameter WELL-FOUNDED `Nat` recursion at the bignum carrier
    /// (R2, §6e MEASUREMENT NOTE + ESCAPE CLOSED): side A is the island's own
    /// WF lowering — a `@WellFounded.fix.{1,1} α C r hwf F x` spine whose
    /// functional guards a self-call on `0 < x`
    /// (`recursion_boundary_probes` the `countdownSum` row, spelling pinned by
    /// `r2_wf_equation_probes` w1) — and the emitted body is the SAME
    /// zero-test/predecessor/self-call MIR contract R1 emits.
    ///
    /// The faithfulness gate for this shape is
    /// [`crate::gate::check_faithful_wf_functional`] — the F-LAYER judgment:
    /// side A's spine parsed by the gate itself, side A's declaration closure
    /// audited empty, side A's decrease proofs BORROWED into side B's slots,
    /// side B kernel-checked at side A's own functional type, its post-borrow
    /// closure audited, and then defeq of the two functionals. Never
    /// whole-term defeq against the fix (w1: side B would have to mint an
    /// accessibility witness MIR does not contain), and never an equation
    /// route (w2/w4 measured its exact boundary; the F layer crosses none of
    /// it).
    ///
    /// **R1's three components do not carry over, and that is measured, not
    /// assumed** (w7): the recursive-argument identity DISSOLVES into typing,
    /// because a WF slot has type `rec : (y : α) → r y x → C y` and a
    /// non-decreasing call cannot be given side A's proof; and equation-set
    /// completeness dissolves because a functional has no case family — its
    /// case split lives inside the term the defeq already covers.
    ///
    /// `RecBodyExpr` is REUSED from `trust_types::admissible_body`, the same
    /// vocabulary reuse as every shape above: the values here come from the
    /// Clean term, the recognizer's come from the emitted MIR, and the
    /// structural comparison in [`admit_lowering`] is direct equality. The
    /// FIELD NAMES are R2's denotation and deliberately not R1's — a
    /// functional has no case substitution, so the arms are named by the zero
    /// test that selects them.
    WellFoundedNatRec {
        /// The value when the parameter IS zero — side A's `dite` ELSE
        /// branch. Never contains `Rec`/`Pred`.
        zero_value: RecBodyExpr,
        /// The value when the parameter is NONZERO — side A's `dite` THEN
        /// branch. Contains exactly one `Rec`.
        nonzero_value: RecBodyExpr,
        /// The self-call arguments, by 0-based SOURCE parameter position. The
        /// MEASURE position is `Pred` for the whole class; carried (and
        /// re-checked on the sealed plan) rather than implied, so the emitter,
        /// the recognizer and the kernel all name the same fact. The other
        /// positions are ordinary values — R3a's whole content.
        rec_args: Vec<RecBodyExpr>,
        /// Which 0-based source parameter the emitted body's ZERO TEST decides.
        ///
        /// At [`WfLowering::OnParameter`] that is also the parameter side A's
        /// `WellFounded.fix` passes as its major premise — the measure — which
        /// is why the field is named for it.
        ///
        /// **At [`WfLowering::OnMeasureValue`] (R3d) the two come apart, and
        /// the name is kept for the field's MIR meaning.** Phase 3's recursion
        /// variable is the measure's VALUE and is not a parameter at all; what
        /// the guard sits on is an ordinary source parameter, and that is what
        /// the emitted `Nat::is_zero` decides. Every consumer of this field —
        /// the materializer's `measure_local`, the MIR reader's own reading of
        /// the entry block's borrow, `RecBodyExpr::Decreasing`'s denotation —
        /// means the GUARDED parameter, so the field is the same field; only
        /// the coincidence with the measure is gone.
        measure_index: usize,
        /// Which of `first-party/clean`'s two well-founded lowerings side A is
        /// in — **the reflection's and the gate's layout, never the MIR's**.
        ///
        /// R3d. The emitted body is byte-identical either way (one zero test on
        /// `measure_index`, one self-call with one operand per parameter), which
        /// is why this is a FIELD rather than a second variant: two variants
        /// with one MIR contract is the "one body, two plans" hazard this crate
        /// refuses everywhere else. What it selects is the SIDE-B TELESCOPE
        /// ([`crate::reflect_wf::reflect_wf_functional`]) and the gate's borrow
        /// layout, both of which are functions of the lowering and the arity.
        lowering: WfLowering,
    },
    /// **W5 (Lean-calls-Rust), increment 2** — `fun x0 … x_{n-1} => f (g x0) …`:
    /// a linear chain of applications of RUST CALLEES, the constants the
    /// compiler declared in the Clean environment for the admissible sibling
    /// `fn`s of the island (`trust_certify::clean_island::declare_rust_callees`).
    /// `def twice_inc (x : UInt64) : UInt64 := inc (inc x)` is the acceptance
    /// program (battery row r18).
    ///
    /// Nodes are in POST-ORDER, root last, exactly as [`Self::Composed`]
    /// flattens its tree, and each node's arguments are source parameters,
    /// in-range numerals at the callee's parameter carrier, `Bool` literals, or
    /// EARLIER nodes.
    ///
    /// **A node may be read by SEVERAL later nodes** (2026-09-15): that is the
    /// explicit value temporary — `def dup (x) := let y := dbl x; sub2 y y` is
    /// ONE `dbl` node read twice, emitted as one `Call` whose temporary is
    /// copied at each use (`walk_let_spine`, which marks it
    /// [`RustCallNode::let_binding`]). The control flow stays linear; only the
    /// dataflow is a DAG. The MIR is the linear call chain
    /// `recognize_call_chain` was written for, with one `Call` to the
    /// registered callee `DefId` per node through fresh temporaries typed at
    /// the CALLEE's result carrier, the root writing `_0`, then `Return`
    /// ([`crate::table::MirShape::RustCallChain`]).
    ///
    /// # What the gate decides, and what it does not
    ///
    /// Side B ([`trust_types::admissible_body::recognize_rust_call_chain`], a
    /// SEPARATE entry point) reads the chain back, reflects it as
    /// `fun x => inc (inc x)` over the callee CONSTANTS (never their bodies —
    /// the kernel holds each as a stuck `Opaque`), and [`crate::gate::check_faithful`]
    /// decides definitional equality of two applications of the same stuck
    /// head: a swapped argument, a wrong callee, a missing application or a
    /// literal at the wrong value all refuse
    /// (`control_23_rust_call_emitter_mutation`).
    ///
    /// What the verdict does NOT cover, stated per the design's SOUNDNESS
    /// charges: the Clean term is total and the binary computes it ONLY IF
    /// every callee returns. The callee's panic/termination obligations are
    /// ORDINARY Rust obligations of that `fn`; under verification they are
    /// charged by increment 3, and until then this shape enters no
    /// panic-free registry and mints no caller-side summary
    /// (`trust_verify.rs`'s call model returns `None` for it). The identity
    /// "constant `inc` DENOTES `fn inc`" is compiler-asserted
    /// (`docs/TCB.md`).
    ///
    /// The callee table is part of the plan ([`CleanOriginPlan::callees`]);
    /// the node's `callee` indexes it.
    RustCallChain {
        /// The calls, post-order, root last. Non-empty.
        nodes: Vec<RustCallNode>,
    },
}

/// One admissible Rust callee as a plan carries it (W5).
///
/// `def_path` is the extractor's rendering of the registered callee `DefId`
/// (`trust_mir_extract::func_operand_name` over `Operand::function_handle`),
/// which is the string side B reads back from the emitted `Call` — so the
/// identity check in [`admit_lowering`] compares two renderings of ONE
/// `DefId`, the same discipline `resolve_bignum_method` documents. Only the
/// MIR-time session can supply it; the mint seam, which never reaches side
/// B, passes the empty string, and a plan carrying an empty `def_path` is
/// REFUSED by [`admit_lowering`] rather than matched by name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustCalleeRef {
    /// The Clean constant name (the callee's bare Rust item name).
    pub clean_name: String,
    /// The extractor's rendering of the callee `DefId`; empty at the mint
    /// seam.
    pub def_path: String,
    /// The Rust carrier of every parameter, in order.
    pub params: Vec<Ty>,
    /// The Rust carrier of the result.
    pub result: Ty,
}

/// One call in a [`CleanOriginShape::RustCallChain`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RustCallNode {
    /// Index into [`CleanOriginPlan::callees`].
    pub callee: usize,
    /// The arguments, in call order.
    pub args: Vec<RustCallArg>,
    /// W5 increment 7 — `Some(k)`: this node is the value of the `k`-th
    /// Rust-call `let` on the top-level spine of the `def` body, an explicit
    /// VALUE TEMPORARY evaluated exactly once, in binding order, before the
    /// body, whatever its use count (0, 1 or n reads via
    /// [`RustCallArg::Node`]). `None`: an ordinary post-order operand node,
    /// read exactly once by a later node (or the root, read never).
    ///
    /// The kernel cannot see this distinction — zeta identifies
    /// `let y := f x; g y y` with `g (f x) (f x)` — so the once-evaluation
    /// claim rests on the STRUCTURAL chain `check_rust_call_chain` seals
    /// (`docs/TCB.md`, the let-temp ONCE-EVALUATION row).
    pub let_binding: Option<usize>,
}

/// One argument of a [`RustCallNode`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RustCallArg {
    /// A 0-based source parameter.
    Param(usize),
    /// The result of an EARLIER node, by index.
    Node(usize),
    /// A literal at the callee's parameter carrier.
    Literal(RustCallLiteral),
}

/// A literal argument, in the two carrier families this lane admits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RustCallLiteral {
    /// An in-range numeral at an unsigned machine width (the width is the
    /// callee parameter's, re-checked on the sealed plan).
    UInt(u128),
    /// `true` / `false`.
    Bool(bool),
}

/// The measured cap on wrapping-op NODES in one [`CleanOriginShape::Composed`]
/// tree.
///
/// Per ruling v7/D2 this is a statement of where we are, never a design: it is
/// the largest chain the reflected rendering was actually put to the kernel at
/// (`tests/fragment_widening_probes.rs` probe_f2 ADMITs a chain of exactly this
/// many ops, in both side-A spellings, and pins the plan-time refusal one past
/// it). Raising it is an edit to the probe first — measure the new depth at
/// the kernel — and to this constant second, never the other way round.
pub const COMPOSED_MAX_OPS: usize = 32;

/// A Clean `def` the compiler may attempt to emit, with the total carrier
/// signature it must be emitted at.
///
/// **Constructible only by [`plan_clean_origin_body`].** The seal matters for
/// the same reason [`crate::mint::MintGrant`]'s does: holding a
/// `CleanOriginPlan` is evidence that the declaration is kernel-checked, has a
/// definition body, and has a TOTAL carrier in **every** position — arguments
/// and result. There is no way to spell "the interesting arguments carry".
#[derive(Debug, Clone)]
pub struct CleanOriginPlan {
    name: String,
    declaration: Name,
    signature: CarrierSignature,
    shape: CleanOriginShape,
    /// W5: the Rust callees a [`CleanOriginShape::RustCallChain`] node may
    /// index. Empty for every other shape and for every plan built without
    /// a callee table.
    callees: Vec<RustCalleeRef>,
    /// See [`Self::source_is_direct`]. Decided once, at planning, from the
    /// same environment value every downstream consumer reads.
    source_is_direct: bool,
}

/// A standalone source-side emission plan, not a faithfulness permission.
///
/// Literal bodies may have distinct UInt8/16/32/64 parameter carriers because
/// standalone reflection reconstructs their complete typed telescope. This
/// plan cannot be passed to the legacy, single-domain MIR reflection API.
///
/// ```compile_fail
/// use trust_clean_origin::emit::{CleanOriginPlan, StandaloneCleanOriginPlan};
/// fn cannot_relabel(plan: &StandaloneCleanOriginPlan) {
///     let _: CleanOriginPlan = plan.clone();
/// }
/// ```
#[derive(Debug, Clone)]
pub struct StandaloneCleanOriginPlan {
    inner: StandalonePlanKind,
}

#[derive(Debug, Clone)]
enum StandalonePlanKind {
    Legacy(CleanOriginPlan),
    Literal {
        name: String,
        declaration: Name,
        signature: CarrierSignature,
        shape: CleanOriginShape,
        /// Trust (WS5.20): the source numeral was outside `0..2^w` and `shape`
        /// carries its residue — disclosed by [`StandaloneCleanOriginPlan::
        /// reduces_out_of_range_literal`], never hidden in the value.
        reduced: bool,
    },
}

impl StandaloneCleanOriginPlan {
    /// Exact source identity, independent of its diagnostic rendering.
    #[must_use]
    pub fn declaration(&self) -> &Name {
        match &self.inner {
            StandalonePlanKind::Legacy(plan) => plan.declaration(),
            StandalonePlanKind::Literal { declaration, .. } => declaration,
        }
    }

    #[must_use]
    pub fn name(&self) -> &str {
        match &self.inner {
            StandalonePlanKind::Legacy(plan) => plan.name(),
            StandalonePlanKind::Literal { name, .. } => name,
        }
    }

    #[must_use]
    pub fn signature(&self) -> &CarrierSignature {
        match &self.inner {
            StandalonePlanKind::Legacy(plan) => plan.signature(),
            StandalonePlanKind::Literal { signature, .. } => signature,
        }
    }

    #[must_use]
    pub fn shape(&self) -> &CleanOriginShape {
        match &self.inner {
            StandalonePlanKind::Legacy(plan) => plan.shape(),
            StandalonePlanKind::Literal { shape, .. } => shape,
        }
    }

    /// Trust (WS5.20): whether this is a literal return whose source numeral was
    /// outside `0..2^w` and was planned as its Lean `OfNat` residue — the one
    /// standalone plan whose emitted literal differs from the source spelling
    /// (the gate still kernel-checks the residue against that spelling).
    #[must_use]
    pub fn reduces_out_of_range_literal(&self) -> bool {
        matches!(self.inner, StandalonePlanKind::Literal { reduced: true, .. })
    }

    /// Only a plan actually checked by the legacy planner can be recovered.
    /// A standalone literal never manufactures a legacy MIR plan, even when
    /// its particular signature happens to use one width throughout.
    #[must_use]
    pub fn legacy_plan(&self) -> Option<&CleanOriginPlan> {
        match &self.inner {
            StandalonePlanKind::Legacy(plan) => Some(plan),
            StandalonePlanKind::Literal { .. } => None,
        }
    }
}

impl CleanOriginPlan {
    /// Exact source identity used for all source and proof lookups.
    #[must_use]
    pub fn declaration(&self) -> &Name {
        &self.declaration
    }

    /// The Clean declaration being emitted.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// W5: the Rust callee table a [`CleanOriginShape::RustCallChain`] indexes
    /// — the SAME table the planner was given, carried so the materializer and
    /// the gate resolve a node's callee against what side A was planned over.
    #[must_use]
    pub fn callees(&self) -> &[RustCalleeRef] {
        &self.callees
    }

    /// The total carrier signature: one carrier per argument, one for the
    /// result. Its existence is I4's `CarrierEvidence::Total` for the whole
    /// signature.
    #[must_use]
    pub fn signature(&self) -> &CarrierSignature {
        &self.signature
    }

    /// The recognised body shape.
    #[must_use]
    pub fn shape(&self) -> &CleanOriginShape {
        &self.shape
    }

    /// For a [`CleanOriginShape::WrappingBinOp`] or
    /// [`CleanOriginShape::Composed`] plan: whether the declaration's OWN
    /// kernel value is already that wrapping tree — `UIntW` lambdas over
    /// parameters, in-range literals, `add`/`sub`/`mul` in either spelling and
    /// `UIntW` lets, with no helper call to unfold and no metadata to strip.
    /// For a [`CleanOriginShape::Projection`] or
    /// [`CleanOriginShape::ConstantUint`] plan: whether that value is the same
    /// `UIntW` telescope returning, after substituting its `UIntW` lets,
    /// exactly the plan's parameter or numeral. `false` for every other shape.
    ///
    /// Recognition may see through a transparent Lean helper
    /// (`def f a := square (plusOne a)` plans as a composed tree,
    /// `def g a b := pick a b` as a projection), which is sound for the
    /// carrier gate — it compares against the original declaration by kernel
    /// defeq — but the compiler's kernel-TV companion denotes that original
    /// value syntactically and refuses the helper head. A carrier-gate
    /// consumer that turns a missing companion into a fatal must therefore not
    /// target a plan for which this is `false`.
    #[must_use]
    pub fn source_is_direct(&self) -> bool {
        self.source_is_direct
    }

    /// The Rust carrier types of the parameters, in order — what the emitted
    /// MIR's argument locals must be typed at.
    #[must_use]
    pub fn param_tys(&self) -> Vec<Ty> {
        self.signature.arguments().iter().map(|c| c.rust().clone()).collect()
    }

    /// The Rust carrier type of the result — the emitted MIR's `_0`.
    #[must_use]
    pub fn return_ty(&self) -> &Ty {
        self.signature.result().rust()
    }

    /// The result carrier — the type the faithfulness verdict is admitted at.
    #[must_use]
    pub fn result_carrier(&self) -> &Carrier {
        self.signature.result()
    }

    /// The **caller obligations** this declaration imposes — one per erased
    /// hypothesis binder of its Clean type.
    ///
    /// The caller-side summary lane must forward these to every call site (see
    /// `trust_vcgen::clean_origin_summary`, which will not publish a value fact
    /// unless it can carry them all). Their discharge is an ordinary Rust
    /// obligation, never a `Faithful` token — `fa788aab89` is explicit that the
    /// kernel gate is BLIND to this class of divergence, because it compares
    /// two total Clean terms while the hazard lives between the Clean term and
    /// the emitted MIR instruction.
    ///
    /// **Empty for every plan today, and that is a measured residual, not a
    /// design.** [`plan_clean_origin_body`] reads the declaration's type
    /// through `carrier_signature_for`, the door that refuses a hypothesis
    /// binder outright, so a hypothesis-carrying `def` does not currently
    /// reach a plan at all. Moving the plan lane onto
    /// `carrier_signature_with_hypotheses_for` also requires the body
    /// recognisers to peel the erased proof lambda, which is a separate
    /// increment. Reading this accessor is correct in either state: it reports
    /// what the plan carries.
    ///
    /// That increment must also teach the two compiler lanes that route around
    /// a call site to read this set; today both ask only the Rust contract set
    /// (`trust_mir_extract::def_owes_caller_precondition`). The MIR inliner's
    /// keep-call rule (`rustc_mir_transform`'s
    /// `trust_verify/requires_callee_inlining.rs`) would otherwise inline such a
    /// def, and the value-use gate (`trust_verify/uncharged_callable.rs`) would
    /// admit it as a fn value. Either way the call that charges these is gone.
    #[must_use]
    pub fn preconditions(&self) -> Vec<trust_clean_carrier::CleanOriginPrecondition> {
        self.signature.preconditions()
    }
}

/// Why no Clean-origin body was produced.
///
/// The variants split into two families that must never be confused, because
/// they mean opposite things about who is at fault:
///
/// * [`Self::NotEmittable`] and [`Self::NoTotalCarrier`] are **capability**
///   refusals about side A. The user wrote something outside the fragment; the
///   compiler is honest about it and the v7/D3 note says what to do.
/// * [`Self::LoweringUnrecognised`], [`Self::LoweringShapeMismatch`] and
///   [`Self::ReflectionRejected`] are **correctness** refusals about side B.
///   The compiler was about to emit something that disagrees with what it read.
///   Nothing the user writes changes them, and they are internal-compiler-error
///   shaped.
/// * [`Self::Gate`] preserves the inner [`GateRefusal`] classification:
///   completed disagreement or unchecked side-A provenance is a correctness
///   defect, while a missing Clean body or exhausted bounded decision is a
///   fail-closed capability/resource refusal. See [`Self::is_compiler_defect`].
#[derive(Debug, Clone)]
pub enum EmitRefusal {
    /// Side A is not a shape this lane can originate a body for.
    NotEmittable {
        /// The declaration name.
        name: String,
        /// What was found instead, in the user's terms.
        reason: String,
    },
    /// Side A has no total Rust carrier in some signature position.
    NoTotalCarrier {
        /// The declaration name.
        name: String,
        /// I4's refusal, verbatim — it names the position and the true bound.
        refusal: CarrierRefused,
    },
    /// Side A carries TOTALLY, but side B has no Clean domain that reflects
    /// that carrier back to this Clean type, so the emitted body's agreement
    /// with the declaration could never be re-earned.
    ///
    /// This is a CAPABILITY refusal about the compiler's reflection, not about
    /// what the user wrote, and it is deliberately raised on side A: without
    /// it the mint would grant a `DefId`, resolve, typeck, and then die inside
    /// `clean_origin_mir` with the gate's fail-closed correctness refusal —
    /// the precise fatal that `rustc_resolve::trust_clean_mint::decide`'s
    /// fourth condition exists to convert into an `E0425` with options.
    CarrierDomainNotReflectable {
        /// The declaration name.
        name: String,
        /// The position, in the user's terms (`argument 0`, `the result`).
        position: String,
        /// The Clean type in that position, as the carrier map names it.
        clean: String,
        /// The Rust carrier that position was granted.
        rust: String,
    },
    /// The emitted body did not read back as an admissible shape at all.
    ///
    /// The compiler emitted MIR that its own recognizer does not accept. That
    /// is a defect in the emitter, and it must refuse rather than emit an
    /// unverified body.
    LoweringUnrecognised {
        /// The declaration name.
        name: String,
        /// What the plan said should have been emitted.
        planned: CleanOriginShape,
    },
    /// The emitted body read back as a *different* admissible shape than the
    /// one planned.
    ///
    /// This is the structural half of the mistranslation catch. It is NOT a
    /// substitute for the kernel comparison and never short-circuits it in the
    /// agreeing direction: a shape that matches still goes to the kernel.
    LoweringShapeMismatch {
        /// The declaration name.
        name: String,
        /// What the plan said should have been emitted.
        planned: CleanOriginShape,
        /// What the emitted body actually reads back as.
        recognised: String,
    },
    /// The E6 Rust→Clean reflection refused to mint side B.
    ///
    /// The emitted body was recognised but could not be turned into a kernel
    /// term — an unsupported carrier domain, or the kernel rejecting the
    /// reflected defining equation. Either way there is no side B, so there is
    /// nothing to compare and emission must not proceed.
    ReflectionRejected {
        /// The declaration name.
        name: String,
        /// The producer's own message.
        detail: String,
    },
    /// W5 increment 7: the top-level `let` spine binds a Rust call that the
    /// explicit-value-temporary lane cannot carry to the result.
    ///
    /// Raised by `walk_let_spine` (a let-bound call whose residual body is not
    /// a Rust callee application, a helper or opaque wrapped around a call in
    /// a `let` value, a Rust `let` nested inside another `let`'s value) and by
    /// `check_rust_call_chain`'s seal-time re-checks over a let-bearing chain.
    /// It is returned UNMASKED by the planner: the inductive-projection and
    /// helper-expansion fallbacks never run over it, because each would
    /// replace this note with a generic one and the fix would be lost.
    ///
    /// `defect` separates the user's refusals (`false`: the note carries the
    /// options) from the planner's own consistency tripwires (`true`: the
    /// recognised chain and the environment body disagree about how many
    /// Rust calls the `def` makes — the once-evaluation cross-check).
    LetSpine {
        /// The declaration name.
        name: String,
        /// Why, in the user's terms (or the tripwire's, when `defect`).
        reason: String,
        /// `true` = a planner defect, never something the user wrote.
        defect: bool,
    },
    /// Trust (Clean R80; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1): compiled
    /// code does not run the kernel value this lane would emit. The declaration
    /// carries an `@[implemented_by]` binding, or its value reaches a constant
    /// that does, or the environment's ORDER record is not empty
    /// (`clean_compiler::implemented_by_order`). A refusal about what the user
    /// wrote, never a compiler defect. See `crate::implemented_by`.
    ImplementedBy {
        /// The declaration name.
        name: String,
        /// Why, in the user's terms, with the options.
        reason: String,
    },
    /// Trust (Clean R80 item 5; `docs/DECISION_QUEUE.md` R80-CONSUMERS-1):
    /// compiled code calls an external symbol, not the kernel value this lane
    /// would emit. The declaration carries `@[extern]`, or its value reaches a
    /// constant that does (clean-compiler's `has_compiler_attr` counts both
    /// attributes). A refusal about what the user wrote, never a compiler
    /// defect. See `crate::implemented_by`.
    Extern {
        /// The declaration name.
        name: String,
        /// Why, in the user's terms, with the options.
        reason: String,
    },
    /// The gate refused. See [`GateRefusal`].
    Gate(GateRefusal),
}

impl EmitRefusal {
    /// The declaration this refusal is about.
    #[must_use]
    pub fn name(&self) -> &str {
        match self {
            Self::NotEmittable { name, .. }
            | Self::NoTotalCarrier { name, .. }
            | Self::CarrierDomainNotReflectable { name, .. }
            | Self::LoweringUnrecognised { name, .. }
            | Self::LoweringShapeMismatch { name, .. }
            | Self::ReflectionRejected { name, .. }
            | Self::LetSpine { name, .. }
            | Self::ImplementedBy { name, .. }
            | Self::Extern { name, .. } => name,
            Self::Gate(refusal) => refusal.name(),
        }
    }

    /// Whether this refusal is about the emitted code rather than about what
    /// the user wrote.
    ///
    /// A caller renders the two families differently: a capability refusal is a
    /// diagnostic with options, a correctness refusal is a "please report it".
    /// Telling a user to add an annotation because the compiler mistranslated
    /// its own emission would send them to fix something they did not break.
    #[must_use]
    pub fn is_compiler_defect(&self) -> bool {
        match self {
            // A capability refusal: the carrier is exact and the user's
            // declaration is fine; what is missing is a reflection domain, and
            // the note names the two concrete ways forward.
            Self::NotEmittable { .. }
            | Self::NoTotalCarrier { .. }
            | Self::CarrierDomainNotReflectable { .. }
            // Trust (Clean R80): the binding or the late command is the user's.
            | Self::ImplementedBy { .. }
            | Self::Extern { .. } => false,
            Self::LoweringUnrecognised { .. }
            | Self::LoweringShapeMismatch { .. }
            | Self::ReflectionRejected { .. } => true,
            // W5 increment 7: the user's `let`-spine refusals carry options;
            // the seal's cross-check tripwire is the planner's own.
            Self::LetSpine { defect, .. } => *defect,
            Self::Gate(refusal) => match refusal {
                GateRefusal::Disagreement { .. }
                | GateRefusal::SideANotKernelChecked { .. }
                // The per-defining-equation lane's refusals are all about the
                // emitted code or the pipeline's own routing, never about what
                // the user wrote.
                | GateRefusal::EquationDisagreement { .. }
                | GateRefusal::RecursionStructureDisagreement { .. }
                | GateRefusal::NotStructuralRecursor { .. }
                | GateRefusal::EquationSetMismatch { .. }
                // R2: routing and borrow refusals are the pipeline's own.
                | GateRefusal::NotWellFoundedRecursor { .. }
                | GateRefusal::DecreaseSlotBorrowRefused { .. }
                | GateRefusal::FunctionalDisagreement { .. } => true,
                GateRefusal::ResourceExhausted { .. }
                | GateRefusal::NoCleanBody { .. }
                // NOT a compiler defect: the declaration rests on assumptions
                // the AUTHOR stated, and the refusal's note names what to
                // discharge. Reporting it as "please report this" would send
                // the user to file a bug about their own `axiom`.
                | GateRefusal::AssumptionBearingRecursion { .. } => false,
            },
        }
    }

    /// The operator-facing explanation, ruling v7/D3: **why**, and **what to
    /// do**, with options.
    #[must_use]
    pub fn note(&self) -> String {
        match self {
            Self::NotEmittable { name, reason } => {
                // The raw-binop clause is DERIVED from `raw_binop_rows` (via
                // `raw_binop_vocabulary`), not written out: this paragraph
                // omitted the whole family through landing 7 and the two rows
                // after it. The rest of the paragraph is hand-kept prose.
                let (raw_operators, raw_rules) = raw_binop_vocabulary();
                format!(
                    "`{name}` is kernel-checked, but its body is not a shape this compiler can \
                 emit Rust code for yet: {reason}\n\
                 The callable fragment currently includes: a PARAMETER PROJECTION at \
                 exact carriers (`fun x y => x`), plus a bounded INDUCTIVE-PROJECTION \
                 lane for recursive definitions whose equality to such a projection is \
                 proved locally; a CONSTANT body at an unsigned machine width \
                 (`def six : UInt64 := 6`), at any arity including zero, so a numeral \
                 behind binders the body ignores is emittable too; WRAPPING \
                 `+`/`-`/`*` ARITHMETIC — a single op or a \
                 nested composition of up to {COMPOSED_MAX_OPS} ops — over parameters \
                 and in-range numerals with every signature position at ONE unsigned \
                 machine width (`fun x y => x + y`, `fun x => x - 1`, \
                 `fun x y => (x + y) * x`); ONE RAW BINARY OPERATOR — one of \
                 {raw_operators} — over two parameters or in-range numerals at that same \
                 one width{raw_rules}; a SELECT `if l ⊲ r then t else e` \
                 (`<`/`<=`/`==`) whose arms are bare parameters and whose comparison is \
                 parameter-vs-parameter or parameter-vs-numeral with the numeral strictly \
                 on the right, at that same one width; a bounded unsigned conditional tree \
                 with 2..=32 decisions and parameter/numeral leaves; a SINGLE-PARAMETER STRUCTURAL \
                 `Nat` RECURSION in equation form (`def f : Nat -> Nat | 0 => b \
                 | n + 1 => …f n…`, one recursive use, values built from the parameter, \
                 `Nat` numerals, `+` and `*`) at the bignum carrier; or a WELL-FOUNDED \
                 `Nat` RECURSION over ANY NUMBER of parameters with a ONE-PARAMETER \
                 measure (`termination_by a`, guarded by `if h : 0 < a`, exactly ONE \
                 self-call whose measure argument is `a - 1` and whose other arguments \
                 are ordinary values over `+`, `*` and truncated `-`; a parameter may \
                 be repeated freely, but one passed to the self-call BY ITSELF is used \
                 nowhere else in that branch), at that \
                 same carrier and value vocabulary. This is a measured \
                 boundary of the compiler, \
                 not a rule about what you may write.\n\
                 options:\n\
                 - restate `{name}` inside that fragment and call it, keeping the general \
                   definition alongside for proof position;\n\
                 - if the body nests wrapping `+`/`-`/`*` at one unsigned machine width, \
                   it is emittable directly (up to {COMPOSED_MAX_OPS} ops) — no \
                   decomposition needed; past that, or where another operation \
                   intervenes, split it into single-op `def`s (one wrapping `+`/`-`/`*` \
                   each) and compose them at the call site;\n\
                 - cite `{name}` from a contract instead of calling it — proof position \
                   needs no emitted body and has no shape restriction;\n\
                 - write the computation as a Rust `fn` and prove it agrees with `{name}` \
                   in an `ensures` clause, which is the same guarantee reached from the \
                   other side."
                )
            }
            Self::NoTotalCarrier { name, refusal } => format!(
                "`{name}` is kernel-checked, but some position of its type has no TOTAL \
                 Rust carrier, so there is no Rust type that can hold those values without \
                 loss: {refusal:?}.\n\
                 A partial carrier would make the emitted binary disagree with the \
                 declaration on some inputs, and kernel definitional equality does not \
                 catch that — which is why the carrier is a separate obligation.\n\
                 options:\n\
                 - restate the offending position at a fixed-width Clean type \
                   (`UInt8`/`UInt16`/`UInt32`/`UInt64`), which carries exactly;\n\
                 - keep the unbounded type and cite `{name}` from proof position;\n\
                 - introduce a bounded wrapper in Clean with the bound in its type."
            ),
            Self::CarrierDomainNotReflectable { name, position, clean, rust } => {
                // `BitVec 8` -> `UInt8`: the structure whose single field is
                // this exact bit vector, i.e. the type the reflection actually
                // mints. Spelled from the carrier's own rendering so the note
                // never names a width the user did not write.
                let uint = clean
                    .strip_prefix("BitVec ")
                    .map_or_else(|| "UInt{N}".to_owned(), |bits| format!("UInt{bits}"));
                format!(
                    "`{name}` is kernel-checked and {position} carries TOTALLY and exactly \
                 (`{clean}` -> `{rust}`), but this compiler cannot make `{name}` CALLABLE \
                 from Rust, because it has no way to re-earn the emitted body's agreement \
                 with the declaration at `{clean}`.\n\
                 Why, precisely: the faithfulness gate reflects the EMITTED MIR back into \
                 Clean using only the emitted body's own local types — deliberately, so \
                 that an emitter which typed a local wrongly is caught — and the Clean \
                 domain it reads off `{rust}` is `{uint}`, never `{clean}`. `{uint}` and \
                 `{clean}` are DIFFERENT Clean types (`{uint}` is a structure whose one \
                 field is a `{clean}`), so the reflected term is not definitionally equal \
                 to the declaration and the gate refuses. Refusing HERE turns that into a \
                 diagnostic at the call site with options, instead of a fail-closed \
                 correctness refusal at code generation.\n\
                 This is a measured boundary of the compiler, not a rule about what you \
                 may write (ruling v7/D2), and it is NOT a soundness problem: nothing wrong \
                 is emitted, and `{clean}` still carries everywhere a carrier is only \
                 READ — contract clauses, citations, and the declared-carrier lane.\n\
                 options:\n\
                 - restate `{name}` at `UInt8`/`UInt16`/`UInt32`/`UInt64`, which has the \
                   SAME Rust carrier at the same width and is emittable today, and keep the \
                   `{clean}` version alongside for proof position if the bit-level spelling \
                   is what the proof wants;\n\
                 - cite `{name}` from `requires`/`ensures` instead of calling it — proof \
                   position needs no emitted body and no reflection;\n\
                 - write the computation as a Rust `fn` and prove it agrees with `{name}` \
                   in an `ensures` clause, which is the same guarantee reached from the \
                   other side;\n\
                 - or extend the compiler: side B needs a reflection domain whose Clean \
                   type is `{clean}` at the Rust carrier `{rust}`, AND a way to SELECT it \
                   that does not read the declaration. Unsigned `BitVec`-typed domains \
                   already exist in `trust_spec_elab` (`Domain::U128` at `u128`, \
                   `Domain::USize` at `usize`), so the missing half is not signedness: it \
                   is that `ty_to_domain` maps the emitted local's Rust type ALONE — \
                   deliberately, and pinned by `h_i_the_reflector_never_sees_the_plan` — so \
                   nothing may tell it that this `{rust}` stands for `{clean}` rather than \
                   `{uint}`. That is an owner decision with four costed options, written up \
                   in `docs/design/2026-09-14-bitvec-return-direction.md`; it is not a \
                   widening someone should just write."
                )
            }
            Self::LoweringUnrecognised { name, planned } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` was not recognised by \
                 the compiler's own body recognizer, so it could not be checked against the \
                 Clean definition and NOTHING WAS EMITTED.\n\
                 planned shape : {planned:?}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            Self::LoweringShapeMismatch { name, planned, recognised } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` reads back as a \
                 DIFFERENT shape than the one planned, so nothing was emitted.\n\
                 planned    : {planned:?}\n\
                 emitted    : {recognised}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            Self::ReflectionRejected { name, detail } => format!(
                "INTERNAL: the body emitted for Clean-origin `{name}` could not be reflected \
                 back into a Clean term, so there was nothing to compare the definition \
                 against and nothing was emitted: {detail}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            // W5 increment 7. No fragment boilerplate: the reason already
            // names the binder and the residual, and carries the options.
            Self::LetSpine { name, reason, defect: false } => format!(
                "`{name}` is kernel-checked, but its `let`-bound Rust call cannot be emitted \
                 as a value temporary: {reason}"
            ),
            Self::LetSpine { name, reason, defect: true } => format!(
                "INTERNAL: the Rust-call chain planned for Clean-origin `{name}` failed its \
                 own once-evaluation cross-check, so nothing was planned and nothing was \
                 emitted: {reason}\n\
                 This is a compiler-correctness refusal, not a proof obligation. Please \
                 report it."
            ),
            // Trust (Clean R80): no fragment boilerplate; the reason names the
            // binding and carries the options.
            Self::ImplementedBy { name, reason } | Self::Extern { name, reason } => format!(
                "`{name}` is kernel-checked, but Rust cannot call it through the Clean-origin \
                 lane: {reason}"
            ),
            Self::Gate(refusal) => refusal.note(),
        }
    }
}

impl From<GateRefusal> for EmitRefusal {
    fn from(refusal: GateRefusal) -> Self {
        Self::Gate(refusal)
    }
}

/// Decide whether a Clean `def` can have a Rust body originated for it, and at
/// what carrier signature.
///
/// This reads **side A only**. It is not the gate and it is not permission to
/// emit: it says what an emission would have to look like, so that
/// [`admit_lowering`] has something to compare an actual emission against.
///
/// # Errors
///
/// * [`EmitRefusal::NotEmittable`] — no kernel check, no definition body, or a
///   body outside the emittable fragment;
/// * [`EmitRefusal::NoTotalCarrier`] — some signature position does not carry.
///
/// This is the NO-CALLEE entry: a body applying a Rust callee refuses here as
/// outside the fragment. The three compiler sessions that hold a callee table
/// plan through [`plan_clean_origin_body_with_rust_callees`]; every control
/// and consumer that never sees a Rust callee keeps this signature.
pub fn plan_clean_origin_body(
    env: &Environment,
    name: &str,
) -> Result<CleanOriginPlan, EmitRefusal> {
    plan_clean_origin_body_with_rust_callees(env, name, &[])
}

/// Plan an exact structural declaration without parsing a display string.
pub fn plan_clean_origin_body_for_name(
    env: &Environment,
    declaration: &Name,
) -> Result<CleanOriginPlan, EmitRefusal> {
    plan_clean_origin_body_with_rust_callees_for_name(env, declaration, &[])
}

/// Plan standalone literals using the same source numeral reader as the
/// legacy producer. Nonliteral bodies explicitly use the unchanged legacy
/// planner; this is not a fallback after a refused legacy plan.
pub fn plan_standalone_clean_origin_body(
    env: &Environment,
    name: &str,
) -> Result<StandaloneCleanOriginPlan, EmitRefusal> {
    plan_standalone_clean_origin_body_for_name(env, &Name::from_string(name))
}

/// Standalone planning preserves every string and numeric Name constructor.
pub fn plan_standalone_clean_origin_body_for_name(
    env: &Environment,
    declaration: &Name,
) -> Result<StandaloneCleanOriginPlan, EmitRefusal> {
    let display_name = declaration.to_string();
    let name = display_name.as_str();
    let (body, signature) = checked_definition(env, declaration)?;
    // Eta-contracted recursive bodies are not ordinary literal candidates.
    // Let their existing raw-body legacy recognizer decide, as before. An
    // actual numeral-reading error (including range) is never swallowed.
    let literal = match peel_source_parameters(name, &body, signature.arity()) {
        Ok(cursor) => recognise_standalone_constant_body(name, cursor, &signature)?,
        Err(_) => None,
    };
    if let Some((shape, reduced)) = literal {
        let supported =
            |carrier: &Carrier| matches!(carrier.clean(), CleanType::UInt(8 | 16 | 32 | 64));
        if !supported(signature.result())
            || signature.arguments().iter().any(|carrier| !supported(carrier))
            || !signature.hypotheses().is_empty()
            || !signature.preconditions().is_empty()
        {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: "standalone literal returns require exact UInt8/16/32/64 in every signature position and no erased hypotheses".to_owned(),
            });
        }
        return Ok(StandaloneCleanOriginPlan {
            inner: StandalonePlanKind::Literal {
                name: name.to_owned(),
                declaration: declaration.clone(),
                signature,
                shape,
                reduced,
            },
        });
    }
    Ok(StandaloneCleanOriginPlan {
        inner: StandalonePlanKind::Legacy(plan_checked_legacy_body(
            env,
            declaration,
            &body,
            signature,
            &[],
        )?),
    })
}

/// Trust (WS5.20, F-096): the standalone lane's SCALAR vocabulary beyond the
/// shared [`CleanOriginShape`] — bodies only the standalone lane plans, emits
/// and gates, and the MIR lane never sees (no `crate::table` row, no MIR
/// realization, no E6 import direction). Each is re-decided by the standalone
/// gate from the ACTUAL SSA; the planner is never trusted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StandaloneScalarShape {
    /// `l0 ⊲ r0 && l1 ⊲ r1` (or `||`): two decide-comparisons of parameters,
    /// returned as `Bool` (`STANDALONE.p20_bool_connective`).
    ComparisonConnective {
        /// `&&` or `||`.
        op: BoolBinOp,
        /// The left comparison.
        left: StandaloneComparison,
        /// The right comparison.
        right: StandaloneComparison,
    },
    /// A tree of `&&&`/`|||` over parameters and in-range numerals, at one
    /// unsigned machine width (`STANDALONE.p15_bitwise`).
    Bitwise {
        /// The tree, as the recogniser reads it.
        expr: StandaloneBitwiseExpr,
    },
    /// `x / y` over two parameters at one unsigned machine width — TOTAL, as
    /// Lean's `UIntN.div` is (`x / 0 = 0`), so it is emitted with an explicit
    /// zero guard (`STANDALONE.p13_division`).
    TotalDivision {
        /// 0-based source parameter divided.
        dividend: usize,
        /// 0-based source parameter dividing (may be zero at run time).
        divisor: usize,
    },
}

/// Trust (WS5.20): one comparison of two 0-based source parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StandaloneComparison {
    /// `<`, `<=` or `==`.
    pub cmp: SelectCmp,
    /// Left parameter.
    pub left: usize,
    /// Right parameter.
    pub right: usize,
}

/// Trust (WS5.20): the bitwise operators of [`StandaloneScalarShape::Bitwise`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StandaloneBitwiseOp {
    /// `&&&`.
    And,
    /// `|||`.
    Or,
}

/// Trust (WS5.20): a `&&&`/`|||` tree over parameters and in-range numerals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StandaloneBitwiseExpr {
    /// A parameter or an in-range numeral.
    Operand(ArithOperand),
    /// `left op right`.
    Bin {
        /// The operator.
        op: StandaloneBitwiseOp,
        /// Left subtree.
        left: Box<StandaloneBitwiseExpr>,
        /// Right subtree.
        right: Box<StandaloneBitwiseExpr>,
    },
}

/// Trust (WS5.20): the operation budget of a standalone bitwise tree — the
/// same bound the standalone gate enforces independently.
pub const STANDALONE_BITWISE_MAX_OPS: usize = 32;

/// Trust (WS5.20): a standalone-only scalar plan
/// ([`plan_standalone_scalar_body_for_name`]).
#[derive(Debug, Clone)]
pub struct StandaloneScalarPlan {
    name: String,
    declaration: Name,
    signature: CarrierSignature,
    shape: StandaloneScalarShape,
}

impl StandaloneScalarPlan {
    /// Exact source identity.
    #[must_use]
    pub fn declaration(&self) -> &Name {
        &self.declaration
    }

    /// Diagnostic rendering of the declaration.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The checked carrier signature.
    #[must_use]
    pub fn signature(&self) -> &CarrierSignature {
        &self.signature
    }

    /// The standalone-only shape.
    #[must_use]
    pub fn shape(&self) -> &StandaloneScalarShape {
        &self.shape
    }
}

/// Trust (WS5.20): plan a declaration in the standalone SCALAR vocabulary
/// ([`StandaloneScalarShape`]). Callers consult it only after
/// [`plan_standalone_clean_origin_body_for_name`] refused, and report THAT
/// refusal when this one also declines, so no existing refusal text moves.
///
/// # Errors
///
/// [`EmitRefusal::NotEmittable`] when the body is none of the three shapes, the
/// signature is not one exact unsigned machine width (the `Bool` result of a
/// comparison connective aside), or the declaration carries an erased
/// hypothesis or precondition.
pub fn plan_standalone_scalar_body_for_name(
    env: &Environment,
    declaration: &Name,
) -> Result<StandaloneScalarPlan, EmitRefusal> {
    let display_name = declaration.to_string();
    let name = display_name.as_str();
    let (body, signature) = checked_definition(env, declaration)?;
    let refuse = |reason: &str| EmitRefusal::NotEmittable {
        name: name.to_owned(),
        reason: format!("standalone scalar planning: {reason}"),
    };
    if !signature.hypotheses().is_empty() || !signature.preconditions().is_empty() {
        return Err(refuse("erased hypotheses or preconditions are not in this vocabulary"));
    }
    let arity = signature.arity();
    let Some(CleanType::UInt(width)) = signature.arguments().first().map(|a| a.clean()) else {
        return Err(refuse("the first parameter is not an unsigned machine integer"));
    };
    if !matches!(width, 8 | 16 | 32 | 64)
        || signature.arguments().iter().any(|argument| argument.clean() != CleanType::UInt(width))
    {
        return Err(refuse("every parameter must share one exact UInt8/16/32/64 carrier"));
    }
    let carrier_name = CleanType::UInt(width).name();
    let body = if expr_contains_let(&body) { zeta_normalize(&body) } else { body };
    let cursor = peel_source_parameters(name, &body, arity)?;
    let shape = match signature.result().clean() {
        CleanType::Bool => recognise_standalone_comparison_connective(cursor, arity, &carrier_name)
            .ok_or_else(|| refuse("the Bool body is not a connective of two comparisons"))?,
        CleanType::UInt(result) if result == width => {
            if let Some(shape) =
                recognise_standalone_total_division(name, cursor, arity, &carrier_name, width)?
            {
                shape
            } else {
                let expr = recognise_standalone_bitwise_tree(
                    name,
                    cursor,
                    arity,
                    &carrier_name,
                    width,
                    0,
                )?
                .ok_or_else(|| refuse("the body is not a `&&&`/`|||` tree"))?;
                if bitwise_ops(&expr) < 2 {
                    // One operator is the shared RawBinOp shape's; never plan it twice.
                    return Err(refuse("a single `&&&`/`|||` is the shared raw-binop shape"));
                }
                StandaloneScalarShape::Bitwise { expr }
            }
        }
        _ => return Err(refuse("the result carrier is neither Bool nor the parameters' UInt")),
    };
    Ok(StandaloneScalarPlan {
        name: name.to_owned(),
        declaration: declaration.clone(),
        signature,
        shape,
    })
}

/// One decide-comparison of two parameters at the carrier, in the spellings
/// [`recognise_decide_comparison`] measured (`decide (LT.lt …)`, `decide
/// (LE.le …)`, `decide (Eq …)`, `BEq.beq` through `instBEqOfDecidableEq`),
/// generalised to any arity.
fn read_standalone_comparison(
    expr: &Expr,
    arity: usize,
    carrier: &str,
) -> Option<StandaloneComparison> {
    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    let const_is = |expr: &Expr, name: &str, levels: usize| -> bool {
        matches!(strip_mdata(expr).kind(), ExprKind::Const(n, ls)
            if name_display_eq_str(n, name) && ls.len() == levels)
    };
    let (head, args) = uncurry(strip_mdata(expr));
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if name_display_eq_str(head_name, "decide")
        || name_display_eq_str(head_name, "Decidable.decide")
    {
        let [prop, _instance] = args[..] else {
            return None;
        };
        let (prop_head, prop_args) = uncurry(strip_mdata(prop));
        let ExprKind::Const(prop_name, _) = prop_head.kind() else {
            return None;
        };
        return match &prop_args[..] {
            [ty, _, l, r]
                if name_display_eq_str(prop_name, "LT.lt") && const_is(ty, carrier, 0) =>
            {
                Some(StandaloneComparison {
                    cmp: SelectCmp::Lt,
                    left: bvar_param(l)?,
                    right: bvar_param(r)?,
                })
            }
            [ty, _, l, r]
                if name_display_eq_str(prop_name, "LE.le") && const_is(ty, carrier, 0) =>
            {
                Some(StandaloneComparison {
                    cmp: SelectCmp::Le,
                    left: bvar_param(l)?,
                    right: bvar_param(r)?,
                })
            }
            [ty, l, r] if name_display_eq_str(prop_name, "Eq") && const_is(ty, carrier, 0) => {
                Some(StandaloneComparison {
                    cmp: SelectCmp::Eq,
                    left: bvar_param(l)?,
                    right: bvar_param(r)?,
                })
            }
            _ => None,
        };
    }
    if name_display_eq_str(head_name, "BEq.beq") {
        let [ty, instance, l, r] = args[..] else {
            return None;
        };
        if !const_is(ty, carrier, 0) {
            return None;
        }
        let (instance_head, instance_args) = uncurry(strip_mdata(instance));
        let inst_dec_eq_ok = matches!(
            strip_mdata(instance_args.get(1).copied()?).kind(),
            ExprKind::Const(n, ls)
                if ls.is_empty() && name_eq1_concat(n, &["instDecidableEq", carrier])
        );
        if !const_is(instance_head, "instBEqOfDecidableEq", 1)
            || instance_args.len() != 2
            || !const_is(instance_args[0], carrier, 0)
            || !inst_dec_eq_ok
        {
            return None;
        }
        return Some(StandaloneComparison {
            cmp: SelectCmp::Eq,
            left: bvar_param(l)?,
            right: bvar_param(r)?,
        });
    }
    None
}

/// `and c0 c1` / `or c0 c1` (or the `Bool.and`/`Bool.or` spelling) over two
/// decide-comparisons of parameters.
fn recognise_standalone_comparison_connective(
    cursor: &Expr,
    arity: usize,
    carrier: &str,
) -> Option<StandaloneScalarShape> {
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    let op = if name_display_eq_str(head_name, "and") || name_display_eq_str(head_name, "Bool.and")
    {
        BoolBinOp::And
    } else if name_display_eq_str(head_name, "or") || name_display_eq_str(head_name, "Bool.or") {
        BoolBinOp::Or
    } else {
        return None;
    };
    let [left, right] = args[..] else {
        return None;
    };
    Some(StandaloneScalarShape::ComparisonConnective {
        op,
        left: read_standalone_comparison(left, arity, carrier)?,
        right: read_standalone_comparison(right, arity, carrier)?,
    })
}

/// The head of a raw-binop row at the carrier (`HAnd.hAnd {C} {C} {C}
/// inst{HAnd}{C} l r`, …), with its operator and operand subterms.
fn raw_binop_application<'e>(
    expr: &'e Expr,
    carrier: &str,
) -> Option<(RawBinOpKind, &'e Expr, &'e Expr)> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    for (selected, op) in table::raw_binop_rows(table::CarrierClass::MachineUInt) {
        let Some((class, projection)) = table::surface_class(selected) else {
            continue;
        };
        if !name_eq2(head_name, class, projection) {
            continue;
        }
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return None;
        };
        let is_carrier =
            |t: &Expr| matches!(t.kind(), ExprKind::Const(n, _) if name_eq_str(n, carrier));
        let instance_ok = is_prelude_homogeneous_instance(instance, class, carrier);
        if !(is_carrier(t1) && is_carrier(t2) && is_carrier(t3) && instance_ok) {
            return None;
        }
        return Some((op, strip_mdata(lhs), strip_mdata(rhs)));
    }
    None
}

/// `x / y` over two parameters (the divisor a VARIABLE — the case the shared
/// raw-binop shape refuses because Rust's `/` panics at zero).
fn recognise_standalone_total_division(
    name: &str,
    cursor: &Expr,
    arity: usize,
    carrier: &str,
    width: u32,
) -> Result<Option<StandaloneScalarShape>, EmitRefusal> {
    let Some((RawBinOpKind::Div, lhs, rhs)) = raw_binop_application(cursor, carrier) else {
        return Ok(None);
    };
    match (
        recognise_arith_operand(name, lhs, arity, carrier, width)?,
        recognise_arith_operand(name, rhs, arity, carrier, width)?,
    ) {
        (Some(ArithOperand::Param(dividend)), Some(ArithOperand::Param(divisor))) => {
            Ok(Some(StandaloneScalarShape::TotalDivision { dividend, divisor }))
        }
        _ => Ok(None),
    }
}

/// A `&&&`/`|||` tree over parameters and in-range numerals, bounded by
/// [`STANDALONE_BITWISE_MAX_OPS`] (depth and size).
fn recognise_standalone_bitwise_tree(
    name: &str,
    expr: &Expr,
    arity: usize,
    carrier: &str,
    width: u32,
    depth: usize,
) -> Result<Option<StandaloneBitwiseExpr>, EmitRefusal> {
    if depth > STANDALONE_BITWISE_MAX_OPS {
        return Ok(None);
    }
    if let Some(operand) = recognise_arith_operand(name, expr, arity, carrier, width)? {
        return Ok(Some(StandaloneBitwiseExpr::Operand(operand)));
    }
    let Some((kind, lhs, rhs)) = raw_binop_application(expr, carrier) else {
        return Ok(None);
    };
    let op = match kind {
        RawBinOpKind::BitAnd => StandaloneBitwiseOp::And,
        RawBinOpKind::BitOr => StandaloneBitwiseOp::Or,
        _ => return Ok(None),
    };
    let (Some(left), Some(right)) = (
        recognise_standalone_bitwise_tree(name, lhs, arity, carrier, width, depth + 1)?,
        recognise_standalone_bitwise_tree(name, rhs, arity, carrier, width, depth + 1)?,
    ) else {
        return Ok(None);
    };
    let tree = StandaloneBitwiseExpr::Bin { op, left: Box::new(left), right: Box::new(right) };
    if bitwise_ops(&tree) > STANDALONE_BITWISE_MAX_OPS {
        return Ok(None);
    }
    Ok(Some(tree))
}

fn bitwise_ops(expr: &StandaloneBitwiseExpr) -> usize {
    match expr {
        StandaloneBitwiseExpr::Operand(_) => 0,
        StandaloneBitwiseExpr::Bin { left, right, .. } => {
            1 + bitwise_ops(left) + bitwise_ops(right)
        }
    }
}

/// [`plan_clean_origin_body`] with the crate's admissible Rust callee table
/// (W5, Lean-calls-Rust). `callees` are the constants
/// `trust_certify::clean_island::declare_rust_callees` put into `env` — the
/// planner reads a head that names one of them as a
/// [`CleanOriginShape::RustCallChain`] node. The table is copied into the
/// plan so the materializer and the gate index the same rows side A was read
/// over.
///
/// The three sessions that elaborate islands (mint, MIR gate, verify pass)
/// must hand this the SAME table, or their plans disagree about whether a
/// declaration is emittable at all — which the MIR gate reports as a fatal
/// self-disagreement. The table travels through `ResolverGlobalCtxt`; it is
/// never re-derived from HIR.
pub fn plan_clean_origin_body_with_rust_callees(
    env: &Environment,
    name: &str,
    callees: &[RustCalleeRef],
) -> Result<CleanOriginPlan, EmitRefusal> {
    plan_clean_origin_body_with_rust_callees_for_name(env, &Name::from_string(name), callees)
}

/// Plan a structural declaration against the exact native Rust callee table.
pub fn plan_clean_origin_body_with_rust_callees_for_name(
    env: &Environment,
    declaration: &Name,
    callees: &[RustCalleeRef],
) -> Result<CleanOriginPlan, EmitRefusal> {
    let (body, signature) = checked_definition(env, declaration)?;
    plan_checked_legacy_body(env, declaration, &body, signature, callees)
}

fn checked_definition(
    env: &Environment,
    declaration: &Name,
) -> Result<(Expr, CarrierSignature), EmitRefusal> {
    let kernel_name = declaration.clone();
    let display_name = declaration.to_string();
    let name = display_name.as_str();

    // Trust (Clean R80): an environment with an `@[implemented_by]` ORDER
    // record is refused before anything else, every declaration of it, as
    // `clean_compiler::constant_to_decl` refuses it (`crate::implemented_by`).
    crate::implemented_by::refuse_order(env)
        .map_err(|reason| EmitRefusal::ImplementedBy { name: name.to_owned(), reason })?;

    // PROVENANCE FIRST, exactly as the gate does. A structurally-inserted or
    // unchecked declaration is not a kernel verdict, and planning an emission
    // from it would mean the emitted code's reference was never validated.
    // Checking it here as well as in the gate is not redundant: it makes the
    // *plan* — which decides the emitted signature — rest on a kernel verdict
    // too, so a bad declaration cannot even shape the MIR.
    match env.declaration_verification(&kernel_name) {
        Some(DeclarationVerification::FullKernelCheck) => {}
        verification => {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "it did not enter the Clean environment through a full kernel check \
                     (origin: {verification:?})"
                ),
            });
        }
    }

    let Some(constant) = env.get_const(&kernel_name) else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "there is no such declaration in the Clean environment".to_owned(),
        });
    };

    // `Theorem` and `Opaque` are excluded for the reasons `crate::gate` gives:
    // a proof term is proof-irrelevant and an opaque value is deliberately not
    // exposed to reduction, so neither is something emitted code can be
    // faithful to.
    if constant.kind != ConstantKind::Definition {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is a `{:?}`, not a `def`; only a definition exhibits a value for \
                 emitted code to agree with",
                constant.kind
            ),
        });
    }

    let Some(body) = constant.value.as_ref() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "it has no definition body (an axiom or a valueless opaque asserts a \
                     type without exhibiting a value)"
                .to_owned(),
        });
    };

    // Trust (Clean R80): every lane plans from this body and the kernel values
    // it reaches, so an `@[implemented_by]` or `@[extern]` binding on the
    // declaration or anywhere it reaches means compiled code runs something
    // else (`crate::implemented_by`).
    crate::implemented_by::refuse_reached_binding(env, &kernel_name)
        .map_err(|not_run| not_run.refusal(name))?;

    // I4's decision, over the WHOLE signature. `CarrierSignature` cannot exist
    // with a partial position, so a plan implies total carriers everywhere.
    let signature = carrier_signature_for(&constant.type_)
        .map_err(|refusal| EmitRefusal::NoTotalCarrier { name: name.to_owned(), refusal })?;

    Ok((body.clone(), signature))
}

fn plan_checked_legacy_body(
    env: &Environment,
    declaration: &Name,
    body: &Expr,
    signature: CarrierSignature,
    callees: &[RustCalleeRef],
) -> Result<CleanOriginPlan, EmitRefusal> {
    let display_name = declaration.to_string();
    let name = display_name.as_str();
    // A TOTAL CARRIER IS NOT YET PERMISSION TO EMIT: side B must also be able
    // to REFLECT that carrier back to this Clean type.
    //
    // The gate reflects the emitted MIR using only the emitted body's own local
    // types (`param_domains_of` -> `ty_to_domain`), which is what lets it catch
    // an emitter that typed a local wrongly. That map's image does not contain
    // `BitVec N` at an unsigned carrier: `u64` reads back as `UInt64`, and
    // `UInt64` is a STRUCTURE whose single field is a `BitVec 64`, not the
    // `BitVec 64` itself. So a `BitVec`-typed declaration would plan, mint a
    // `DefId`, resolve, typeck, and then be refused fail-closed inside
    // `clean_origin_mir` — the exact fatal that
    // `rustc_resolve::trust_clean_mint::decide`'s fourth condition exists to
    // convert into an `E0425` carrying options.
    //
    // Measured 2026-09-13 on this tree: without this check,
    // `clean { def bvid (x : BitVec 64) : BitVec 64 := x }` plus a Rust caller
    // compiles to `error: internal: refusing to emit code for Clean declaration
    // `bvid` — the emitted body could not be established to agree with the
    // declaration`. With it, the same program gets the call-site refusal that
    // names the carrier as GRANTED and the reflection as the missing half.
    //
    // This is deliberately keyed on the CLEAN type rather than on the Rust one:
    // `UInt64` and `BitVec 64` share the carrier `u64`, and it is the Clean side
    // that decides whether a reflection can be minted for it.
    for (position, carrier) in signature
        .arguments()
        .iter()
        .enumerate()
        .map(|(i, c)| (format!("argument {i}"), c))
        .chain(core::iter::once(("the result".to_owned(), signature.result())))
    {
        if matches!(carrier.clean(), trust_clean_carrier::CleanType::BitVec(_)) {
            return Err(EmitRefusal::CarrierDomainNotReflectable {
                name: name.to_owned(),
                position,
                clean: carrier.clean().name(),
                rust: carrier.witness().rust_carrier().to_owned(),
            });
        }
    }

    // R2 FIRST, and on the RAW body. The well-founded spine has a spelling
    // `recognise_clean_shape` cannot reach: the island emits it
    // ETA-CONTRACTED — `@WellFounded.fix.{1,1} α C r hwf F`, five arguments
    // and NO outer lambda — and `recognise_clean_shape` opens by peeling
    // `arity` lambdas, so an eta-contracted body fails that peel before any
    // recognizer runs. `recognise_wf_nat_rec` accepts BOTH spellings (the
    // eta-expanded six-argument one w1 pins, and the contracted one) and is
    // therefore given the body before it is peeled.
    //
    // `Ok(None)` = not a `WellFounded.fix` spine at all, so the ordinary
    // recognition chain decides; `Err` = it IS one and falls outside the R2
    // fragment for a specific reason, which is kept in force unless the
    // inductive-projection lane can prove the whole function equal to a
    // parameter (the same fallback order the non-recursive chain uses).
    let shape = match recognise_wf_nat_rec(name, body, &signature).and_then(|found| match found {
        // R3b: the FRAGMENT boundary is decided HERE, inside the same
        // `Result` the recognizer returns, so that "it is a
        // `WellFounded.fix` and it is outside R2's fragment" reaches the
        // inductive-projection fallback below by the identical door that
        // "this reader cannot read it" already used. Before R3b the two
        // were indistinguishable in practice because `read_wf_value`
        // refused first on everything the fragment checks cover; widening
        // it to general `-` separated them, and `cdsConstMinuend` — a body
        // that DENOTES the identity and is proved so by induction —
        // stopped planning. The fallback's contract is about the FUNCTION,
        // never about which layer noticed.
        Some(shape) => check_wf_fragment(name, &shape, &signature).map(|()| Some(shape)),
        None => Ok(None),
    }) {
        Ok(Some(shape)) => shape,
        Ok(None) => match recognise_clean_shape(env, name, body, &signature, callees) {
            Ok(shape) => shape,
            // W5 increment 7: a `let`-spine refusal is returned UNMASKED.
            // The two fallbacks below cannot help it — the inductive-
            // projection lane refuses any body with a Rust call in it, and
            // the helper expansion's `Let` arm refuses a non-identity Rust
            // `let` with a generic note — and letting either run would
            // replace the note that names the binder and the fix.
            Err(original @ EmitRefusal::LetSpine { .. }) => return Err(original),
            Err(original) => {
                if let Some(shape) =
                    recognise_inductive_projection(env, declaration, &signature, callees)
                {
                    shape
                } else {
                    // Trust: follow checked Lean helper definitions on side A only.
                    // The gate still reads the original declaration and frozen R;
                    // expansion neither changes source identity nor mints evidence.
                    let expanded =
                        crate::named_calls::expand_named_calls(env, declaration, body, callees)
                            .map_err(|reason| EmitRefusal::NotEmittable {
                                name: name.to_owned(),
                                reason,
                            })?;
                    if let Some(expanded) = expanded {
                        let shape =
                            recognise_clean_shape(env, name, &expanded, &signature, callees)?;
                        if matches!(
                            shape,
                            CleanOriginShape::StructuralNatRec { .. }
                                | CleanOriginShape::WellFoundedNatRec { .. }
                        ) {
                            return Err(EmitRefusal::NotEmittable {
                                name: name.to_owned(),
                                reason: "a named recursive callee needs an independently gated linked-call realization; whole-term expansion does not supply the per-equation gate's original source spine".to_owned(),
                            });
                        }
                        shape
                    } else {
                        return Err(original);
                    }
                }
            }
        },
        Err(original) => {
            match recognise_inductive_projection(env, declaration, &signature, callees) {
                Some(shape) => shape,
                None => return Err(original),
            }
        }
    };

    match &shape {
        // Belt and braces on the one invariant the emitted MIR depends on: the
        // projected parameter's carrier must be the result carrier, or `_0 =
        // move _{i+1}` is not even type-correct. The kernel already
        // established this when it accepted the definition, so a failure here
        // means the carrier decision and the kernel disagree — refuse rather
        // than emit. (Projection deliberately KEEPS its mixed-width
        // capability across the other positions — `control_3::half_5c` pins
        // it — which is why this check is per-shape rather than hoisted.)
        CleanOriginShape::Projection { projected }
        | CleanOriginShape::InductiveProjection { projected } => {
            if signature.arguments()[*projected].rust() != signature.result().rust() {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "the projected parameter carries at `{:?}` but the result carries at \
                         `{:?}`; the compiler will not emit a body whose carrier decision \
                         disagrees with the kernel's typing",
                        signature.arguments()[*projected].rust(),
                        signature.result().rust()
                    ),
                });
            }
        }
        // §6f landing 2: the constant body. Every invariant the emitter and the
        // reflection depend on is RE-CHECKED on the sealed plan, exactly like
        // the arithmetic bounds — `check_arith_signature` because the reflected
        // side B (`admit_expr_function`) is single-domain over ALL parameters,
        // used or not, and the range because `ArithOperand::Const` cannot carry
        // a width.
        //
        // The ARITY is deliberately not checked here: at this point there is no
        // emitted body to check it against, and re-deriving it from side A
        // would put it in a second place. It is bound in `admit_lowering`,
        // against the emitted body's own parameter list.
        CleanOriginShape::ConstantUint { value } => {
            let width = check_arith_signature(name, "a constant body", &signature)?;
            if *value > max_uint_value(width) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: numeral_out_of_range_reason(*value, width),
                });
            }
        }
        CleanOriginShape::WrappingBinOp { op: _, left, right } => {
            let width = check_arith_signature(name, "a single wrapping op", &signature)?;
            // Operand bounds, RE-CHECKED here even though recognition
            // already enforced them — the plan is the sealed decision the
            // emitter trusts, so the invariants hold on the plan itself.
            for operand in [left, right] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
        }
        CleanOriginShape::Composed { expr } => {
            let width = check_arith_signature(name, "a composed wrapping tree", &signature)?;
            // Tree invariants, RE-CHECKED on the sealed plan for the same
            // reason as the single-op arm: every leaf in bounds, and the node
            // count inside the measured fragment — `ArithExpr` itself cannot
            // carry either bound.
            let ops = check_composed_tree(name, expr, &signature, width)?;
            if !(2..=COMPOSED_MAX_OPS).contains(&ops) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: composed_ops_out_of_range_reason(ops),
                });
            }
        }
        CleanOriginShape::UnsignedConditional { expr } => {
            let width = check_arith_signature(name, "an unsigned conditional tree", &signature)?;
            let decisions = check_unsigned_conditional(name, expr, &signature, width, 0)?;
            if !(2..=UINT_CONDITIONAL_MAX_DECISIONS).contains(&decisions) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "unsigned conditional tree must contain 2..=32 decisions".into(),
                });
            }
        }
        // W5 (Lean-calls-Rust): every carrier agreement the emitted chain
        // depends on, RE-CHECKED on the sealed plan — the plan is the decision
        // the emitter trusts. The kernel already typed the application when it
        // accepted the definition, so a failure here means the callee table
        // and the kernel disagree: refuse rather than emit.
        CleanOriginShape::RustCallChain { nodes } => {
            check_rust_call_chain(name, nodes, &signature, callees, Some((env, declaration)))?;
        }
        // R2/C5a: the same single-domain constraint as the arithmetic shapes,
        // for the same reason — `admit_select_function` is single-domain over
        // ALL parameters, used or not — plus parameter bounds re-checked on
        // the sealed plan. (The width check reuses the arithmetic helper: a
        // select has no arithmetic, but its positions must still all carry at
        // one unsigned machine width for the reflection to be typeable.)
        CleanOriginShape::Select { cmp: _, cmp_left, cmp_right, then_param, else_param } => {
            check_arith_signature(name, "a parameter select", &signature)?;
            for index in [cmp_left, cmp_right, then_param, else_param] {
                if *index >= signature.arity() {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its select names parameter {index} but the signature has \
                             only {} parameter(s)",
                            signature.arity()
                        ),
                    });
                }
            }
        }
        // R2/C9: the same single-domain constraint and parameter bounds as
        // the parameter select, plus the LITERAL range re-checked on the
        // sealed plan — recognition deliberately defers the range so this
        // refusal names the exact boundary (the same shared-reason rule as
        // the arithmetic numerals).
        CleanOriginShape::SelectLiteral { cmp: _, cmp_param, literal, then_param, else_param } => {
            let width = check_arith_signature(name, "a parameter-vs-literal select", &signature)?;
            for index in [cmp_param, then_param, else_param] {
                if *index >= signature.arity() {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its select names parameter {index} but the signature has \
                             only {} parameter(s)",
                            signature.arity()
                        ),
                    });
                }
            }
            if *literal > max_uint_value(width) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: numeral_out_of_range_reason(*literal, width),
                });
            }
        }
        // §6f LANDING 3: the general select. Same single-domain constraint and
        // parameter bounds as the two narrower select shapes — the reflected
        // side B (`admit_select_operands_function`) is single-domain over ALL
        // parameters, used or not — plus the range of EVERY numeral position
        // re-checked on the sealed plan, because `ArithOperand::Const` cannot
        // carry a width. `check_arith_leaf` is reused rather than re-spelled:
        // an operand is an operand, and a second bounds rule here would be a
        // second place a bound could be wrong.
        CleanOriginShape::SelectOperands { cmp: _, cmp_left, cmp_right, then_arm, else_arm } => {
            let width = check_arith_signature(name, "a general select", &signature)?;
            if *cmp_left >= signature.arity() {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its select names parameter {cmp_left} but the signature has only {} \
                         parameter(s)",
                        signature.arity()
                    ),
                });
            }
            for operand in [cmp_right, then_arm, else_arm] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
            // THE DISJOINTNESS INVARIANT. A `SelectOperands` whose arms are
            // both parameters is a second spelling of `Select`/`SelectLiteral`,
            // and two spellings of one shape is the hazard this crate refuses
            // everywhere else: the emitter would build one body and a control
            // would pin the other. `recognise_select_ite` cannot produce it;
            // this re-check is what makes that a property of the SEALED PLAN
            // rather than of one recognizer.
            if matches!((then_arm, else_arm), (ArithOperand::Param(_), ArithOperand::Param(_))) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its select has two bare-parameter arms, which is the \
                             `Select`/`SelectLiteral` shape rather than the general one; the \
                             general shape exists for a NUMERAL arm and carrying it here as \
                             well would give one body two plans"
                        .to_owned(),
                });
            }
        }
        // §6f LANDING 6: the `==` select. The same single-domain constraint and
        // operand bounds as the general select — the reflected side B
        // (`admit_select_beq_function`) is single-domain over ALL parameters,
        // used or not, and `ArithOperand::Const` cannot carry a width — and
        // `check_arith_leaf` is reused rather than re-spelled for the reason
        // landing 3 gave: an operand is an operand, and a second bounds rule
        // here would be a second place a bound could be wrong.
        //
        // There is deliberately NO disjointness invariant here. The general
        // select needs one because two bare-parameter arms would make it a
        // second spelling of `Select`/`SelectLiteral`; the `==` spelling has no
        // narrower sibling at all, so every operand vocabulary is this shape
        // and nothing can be planned two ways.
        CleanOriginShape::SelectBeq { cmp_left, cmp_right, then_arm, else_arm } => {
            let width = check_arith_signature(name, "an `==` select", &signature)?;
            if *cmp_left >= signature.arity() {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its select names parameter {cmp_left} but the signature has only {} \
                         parameter(s)",
                        signature.arity()
                    ),
                });
            }
            for operand in [cmp_right, then_arm, else_arm] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
        }
        // §6f LANDING 8: the general `==` select. Same single-domain constraint
        // and leaf bounds as every other machine shape, plus TWO invariants
        // this shape owns:
        //
        //  * THE DIVISOR RULE inside a computed operand — the same rule, for
        //    the same measured reason, as the whole-body raw binop: Clean's
        //    `{C}.div`/`.mod` are TOTAL and Rust's `/`/`%` PANIC. Re-checked
        //    here because THIS is the decision the emitter trusts, exactly as
        //    landing 7 re-checks it for the whole-body shape.
        //  * THE DISJOINTNESS INVARIANT — a `true` lift over two leaf operands
        //    is `SelectBeq` byte for byte, and two plans for one body is the
        //    hazard the general select's own invariant exists for.
        CleanOriginShape::SelectBeqGeneral {
            scrutinee,
            cmp_left,
            cmp_right,
            then_arm,
            else_arm,
        } => {
            let width = check_arith_signature(name, "a general `==` select", &signature)?;
            let mut computed = false;
            for operand in [cmp_left, cmp_right] {
                match operand {
                    BeqOperand::Param(_) | BeqOperand::Const(_) => {
                        check_arith_leaf(name, &beq_leaf(*operand), &signature, width)?;
                    }
                    BeqOperand::RawBin { op, left, right } => {
                        computed = true;
                        for leaf in [left, right] {
                            check_arith_leaf(name, leaf, &signature, width)?;
                        }
                        if op.panics_at_zero_right_operand()
                            && !matches!(right, ArithOperand::Const(divisor) if *divisor > 0)
                        {
                            return Err(EmitRefusal::NotEmittable {
                                name: name.to_owned(),
                                reason: sealed_plan_divisor_reason(*op),
                            });
                        }
                        if op.right_operand_is_a_shift_amount()
                            && !shift_amount_has_a_side_b(*right, width)
                        {
                            return Err(EmitRefusal::NotEmittable {
                                name: name.to_owned(),
                                reason: sealed_plan_shift_amount_reason(),
                            });
                        }
                    }
                }
            }
            for operand in [then_arm, else_arm] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
            if *scrutinee && !computed {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its `==` select lifts against `Bool.true` over two leaf operands, \
                             which is the `SelectBeq` shape rather than the general one; the \
                             general shape exists for a COMPUTED operand or a `= false` lift, \
                             and carrying it here as well would give one body two plans"
                        .to_owned(),
                });
            }
        }
        // §6f LANDING 7: the raw-binop body. Same single-domain constraint and
        // numeral bounds as every other machine shape — the reflected side B
        // is the FROZEN `admit_expr_function`, which is single-domain over ALL
        // parameters, used or not.
        //
        // AND THE DIVISOR RULE, re-checked here because THIS is the decision
        // the emitter trusts. `recognise_raw_binop_expr` already refuses an
        // unsafe divisor with a v7/D3 note; restating it on the sealed plan is
        // what makes "a `Div`/`Rem` plan carries a strictly positive numeral"
        // a property of the PLAN rather than of one recognizer, which is the
        // same accounting the general select's disjointness invariant gets and
        // matters more here because the failure mode is a wrong binary rather
        // than a duplicate plan.
        CleanOriginShape::RawBinOp { op, left, right } => {
            let width = check_arith_signature(name, "a raw binary operator", &signature)?;
            for operand in [left, right] {
                check_arith_leaf(name, operand, &signature, width)?;
            }
            if op.panics_at_zero_right_operand()
                && !matches!(right, ArithOperand::Const(divisor) if *divisor > 0)
            {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: sealed_plan_divisor_reason(*op),
                });
            }
            if op.right_operand_is_a_shift_amount() && !shift_amount_has_a_side_b(*right, width) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: sealed_plan_shift_amount_reason(),
                });
            }
        }
        // W6 (Rust-calls-Clean): the comparison-to-`Bool` invariants, RE-CHECKED
        // on the sealed plan. The RESULT must be `Bool`, both ARGUMENTS one
        // unsigned machine width (the reflected `admit_comparison_function` is
        // single-domain), and both parameter indices in range. The kernel
        // already typed the comparison when it accepted the definition, so a
        // failure here means the carrier decision and the kernel disagree.
        CleanOriginShape::DecideComparison { cmp: _, cmp_left, cmp_right } => {
            if !matches!(signature.result().clean(), trust_clean_carrier::CleanType::Bool) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its body is a comparison returned as a value but its result \
                             carrier is not `Bool`"
                        .to_owned(),
                });
            }
            // Unlike the arithmetic shapes, the result carrier is `Bool`, not
            // the operand width — so `check_arith_signature` (which compares
            // every position to the RESULT) cannot be used. Every ARGUMENT must
            // instead share one unsigned machine width, because the reflected
            // `admit_comparison_function` is single-domain over all parameters.
            let Some(first) = signature.arguments().first() else {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "a comparison to `Bool` has no operands".to_owned(),
                });
            };
            if !matches!(first.rust(), Ty::Int { width: 8 | 16 | 32 | 64, signed: false }) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its comparison operands carry at `{:?}`, which is not an unsigned \
                         machine width (u8/u16/u32/u64)",
                        first.rust()
                    ),
                });
            }
            if let Some((position, argument)) = signature
                .arguments()
                .iter()
                .enumerate()
                .find(|(_, argument)| argument.rust() != first.rust())
            {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "it is a comparison to `Bool`, but parameter {position} carries at \
                         `{:?}` while parameter 0 carries at `{:?}`; every operand must share \
                         one unsigned machine width, because the reflected lowering it is \
                         checked against is single-domain over all parameters",
                        argument.rust(),
                        first.rust()
                    ),
                });
            }
            for index in [cmp_left, cmp_right] {
                if *index >= signature.arity() {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its comparison names parameter {index} but the signature has \
                             only {} parameter(s)",
                            signature.arity()
                        ),
                    });
                }
            }
        }
        // W6 (Rust-calls-Clean): the boolean-value invariants, RE-CHECKED on the
        // sealed plan. Result and every parameter must be `Bool` (the reflected
        // `admit_bool_value_function` is single-domain over `Bool`), and every
        // named parameter in range.
        CleanOriginShape::BoolNot { .. }
        | CleanOriginShape::BoolConnective { .. }
        | CleanOriginShape::BoolExpression { .. } => {
            let all_bool =
                matches!(signature.result().clean(), trust_clean_carrier::CleanType::Bool)
                    && signature
                        .arguments()
                        .iter()
                        .all(|c| matches!(c.clean(), trust_clean_carrier::CleanType::Bool));
            if !all_bool {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its body is a boolean connective/negation but some position does \
                             not carry `Bool`"
                        .to_owned(),
                });
            }
            let indices: Vec<usize> = match &shape {
                CleanOriginShape::BoolNot { param } => vec![*param],
                CleanOriginShape::BoolConnective { left, right, .. } => vec![*left, *right],
                CleanOriginShape::BoolExpression { expr } => {
                    let mut ops = 0;
                    if !expr.check_bounds(signature.arity(), 0, &mut ops) || ops == 0 {
                        return Err(EmitRefusal::NotEmittable {
                            name: name.to_owned(),
                            reason: "its Boolean expression exceeds the operation/depth bounds, \
                                     names an invalid parameter, or has no operator"
                                .to_owned(),
                        });
                    }
                    Vec::new()
                }
                _ => unreachable!("outer match arm restricts to Boolean shapes"),
            };
            for index in indices {
                if index >= signature.arity() {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its boolean connective names parameter {index} but the signature \
                             has only {} parameter(s)",
                            signature.arity()
                        ),
                    });
                }
            }
        }
        // R1 (§6e as amended): the structural-recursion invariants are
        // RE-CHECKED on the sealed plan, exactly like the arithmetic bounds —
        // the plan is the decision the emitter trusts.
        CleanOriginShape::StructuralNatRec { base, step, rec_arg } => {
            check_structural_nat_signature(name, &signature)?;
            if base.contains(&RecBodyExpr::Rec) || base.contains(&RecBodyExpr::Pred) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its zero case mentions the recursive result or the \
                             predecessor, which have no zero-case reading"
                        .to_owned(),
                });
            }
            if step.count(&RecBodyExpr::Rec) != 1 {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its succ case uses the recursive result {} time(s); the \
                         emittable structural fragment is exactly one recursive use \
                         per step (two-back recurrences like fib compile through the \
                         `.cov` pair-threading, whose pair carrier is not in this \
                         toolchain yet)",
                        step.count(&RecBodyExpr::Rec)
                    ),
                });
            }
            if *rec_arg != RecBodyExpr::Pred {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "its recursion argument is not the structural predecessor \
                             of the parameter"
                        .to_owned(),
                });
            }
            // Move discipline of the emitted body: the parameter is a
            // non-Copy bignum and the emitter has no clone, so each arm may
            // consume it at most once.
            for (arm, value) in [("zero", base), ("succ", step)] {
                if value.count(&RecBodyExpr::Decreasing) > 1 {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its {arm} case uses the parameter more than once; the \
                             emitted body moves the (non-Copy) bignum parameter and \
                             this fragment has no duplication — bind the repeated \
                             value once in Clean, or keep `{name}` for proof position"
                        ),
                    });
                }
                let nodes = value.arith_nodes();
                if nodes > COMPOSED_MAX_OPS {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its {arm} case composes {nodes} `+`/`*` node(s) against a \
                             measured fragment of at most {COMPOSED_MAX_OPS} per case"
                        ),
                    });
                }
            }
            // The termination-evidence seam (design §3): only a
            // `Nat.rec`-headed value of a FullKernelCheck declaration passes.
            require_kernel_termination_evidence(env, declaration, TerminationEvidence::Structural)?;
        }
        // R2 (§6e MEASUREMENT NOTE + ESCAPE CLOSED): the same re-checks on the
        // sealed plan, at R2's own denotation. Everything the emitter and the
        // reflection depend on is re-asserted here, because the plan is the
        // decision the emitter trusts.
        CleanOriginShape::WellFoundedNatRec { .. } => {
            // §6e ESCAPE CLOSED — the re-check on the SEALED plan. Same
            // decision as the one taken at recognition (R3b moved a COPY of it
            // there so a fragment refusal can still reach the
            // inductive-projection fallback); repeated here because the plan,
            // not the recognizer's return value, is what the emitter trusts.
            check_wf_fragment(name, &shape, &signature)?;
            // The termination-evidence seam, at R2's evidence form: a
            // `WellFounded.fix`-headed value of a FullKernelCheck declaration.
            // Totality is then the KERNEL's own — the fix spine's `rec` slot
            // demands a decrease proof at every call (w7/d1) — never an engine
            // obligation, so the v6/D2 boundary is untouched. The other half
            // of that evidence, the audited-empty axiom closure without which
            // the typing rule is switchable off by one assumed decrease
            // (probe c1), is the GATE's hard precondition and is deliberately
            // not duplicated here: a plan is not permission to emit.
            require_kernel_termination_evidence(
                env,
                declaration,
                TerminationEvidence::WellFounded,
            )?;
        }
    }

    // The wrapping-arithmetic shapes and the two leaf shapes have a direct
    // source reading; the value is the environment's, exactly what the
    // compiler's kernel-TV companion denotes (never the expanded body
    // recognition may have used).
    let source_is_direct = {
        use crate::direct_source::{DirectLeaf, reads_directly, reads_leaf_directly};
        let value = env.get_const(declaration).and_then(|constant| constant.value.as_ref());
        let arity = signature.arity();
        match (&shape, signature.result().clean(), value) {
            (
                CleanOriginShape::WrappingBinOp { .. } | CleanOriginShape::Composed { .. },
                CleanType::UInt(width),
                Some(value),
            ) => reads_directly(value, arity, width),
            (CleanOriginShape::Projection { projected }, CleanType::UInt(width), Some(value)) => {
                reads_leaf_directly(value, arity, width, DirectLeaf::Param(*projected))
            }
            (CleanOriginShape::ConstantUint { value: k }, CleanType::UInt(width), Some(value)) => {
                reads_leaf_directly(value, arity, width, DirectLeaf::Literal(*k))
            }
            _ => false,
        }
    };

    Ok(CleanOriginPlan {
        name: name.to_owned(),
        declaration: declaration.clone(),
        signature,
        shape,
        callees: callees.to_vec(),
        source_is_direct,
    })
}

/// **The R2 FRAGMENT boundary, as one pure decision.**
///
/// Extracted from `plan_clean_origin_body`'s `WellFoundedNatRec` arm by R3b so
/// that it can be asked TWICE, at two different moments, for two different
/// reasons:
///
/// 1. at RECOGNITION, where a refusal is still eligible for the
///    inductive-projection fallback — the same door "not a `WellFounded.fix`
///    spine at all" and "a spine this reader cannot read" already went through;
/// 2. again on the SEALED PLAN, which is §6e's ESCAPE-CLOSED re-check: the plan
///    is the decision the emitter trusts, so everything the emitter and the
///    reflection depend on is re-asserted against it.
///
/// Running it twice is deliberate and free — it is pure, it reads no
/// environment, and it decides on the shape alone. What is NOT in here is the
/// termination-evidence seam (`require_kernel_termination_evidence`): that one
/// needs `env`, it is not a fragment question, and a body that fails it must
/// NOT be rescued by any fallback.
///
/// # Why the split exists at all (measured, 2026-08-27)
///
/// Before R3b these checks could only ever fire after the fallback had been
/// skipped, because `read_wf_value` refused first on everything they cover.
/// Widening that reader to general `-` moved two bodies across the line — a
/// decrease by two, and a CONSTANT minuend — from "unreadable" to "read, then
/// refused", and `control_11_a_constant_minuend_that_reduces_to_zero_plans_as_
/// the_identity` caught it immediately: `cdsConstMinuend` DENOTES the identity,
/// the inductive-projection lane proves it, and it must keep planning. A
/// capability that survives only because a reader is too narrow is a capability
/// resting on an accident.
fn check_wf_fragment(
    name: &str,
    shape: &CleanOriginShape,
    signature: &CarrierSignature,
) -> Result<(), EmitRefusal> {
    let CleanOriginShape::WellFoundedNatRec {
        zero_value,
        nonzero_value,
        rec_args,
        measure_index,
        lowering,
    } = shape
    else {
        return Ok(());
    };
    check_wf_nat_signature(name, signature)?;
    if rec_args.len() != signature.arity() || *measure_index >= rec_args.len() {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(&format!(
                "its self-call carries {} argument(s) with the measure at parameter \
                 {measure_index}, against a signature of {} parameter(s) — the emitted \
                 self-call passes one operand per parameter, so a body whose recursion \
                 and signature disagree has no emission",
                rec_args.len(),
                signature.arity()
            )),
        });
    }
    if zero_value.contains(&RecBodyExpr::Rec) || zero_value.contains(&RecBodyExpr::Pred) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(
                "its zero branch mentions the recursive result or the predecessor, \
                 which the emitted zero-test contract confines to the nonzero arm",
            ),
        });
    }
    if nonzero_value.count(&RecBodyExpr::Rec) != 1 {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(&format!(
                "its nonzero branch uses the recursive slot {} time(s); the \
                 emittable well-founded fragment is exactly one self-call per body \
                 (the gate's borrow pairs side B's call sites with side A's one at \
                 a time, so a second call has no measured pairing)",
                nonzero_value.count(&RecBodyExpr::Rec)
            )),
        });
    }
    // THE DECREASING-ARGUMENT BELT — PHASE 2 ONLY, and the asymmetry is the
    // whole of what R3d relaxes.
    //
    // At `OnParameter` the recursion variable IS the guarded parameter, and the
    // only decrease side A can carry is the one the emitted `Nat::sub(&n, &1)`
    // predecessor computes; anything else is a body with no emission, so the
    // belt is a real fragment boundary.
    //
    // At `OnMeasureValue` the recursion variable is the MEASURE'S VALUE. The
    // self-call's arguments are ordinary values with no termination weight at
    // all — what decreases is `m[a⃗] < m[p⃗]`, and side A carries a
    // kernel-checked proof of exactly that in the slot the gate BORROWS. A
    // `Pred` rule here would refuse `gcd`'s own `|a-b|` and `min a b` while
    // establishing nothing the kernel has not already established, because the
    // decrease it would be testing is not the one the recursion runs on.
    // Refusing on it would be this crate deciding a termination question the
    // kernel decided.
    if *lowering == WfLowering::OnParameter && rec_args[*measure_index] != RecBodyExpr::Pred {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(
                "its self-call's DECREASING argument is not `n - 1`; the emittable \
                 well-founded fragment decreases by exactly one, because that is the \
                 argument the emitted `Nat::sub(&n, &1)` predecessor computes. The \
                 other parameters may be threaded or recomputed freely",
            ),
        });
    }
    // Move discipline of the emitted body. R1's rule, generalised PER
    // PARAMETER (R3a) and made MOVE-AWARE (R3b).
    //
    // Until R3b this was a use COUNT: any parameter named twice in a
    // branch was refused. That over-refused, and it is the only thing
    // that stood between the emitter and subtractive Euclid — whose
    // step map names `a` four times and `b` three. The measurement that
    // says so is `gcd_route_probes` m3/m4: the materializer emits
    // `_9 = &_2; _10 = &_2; NatAdd(move _9, move _10)` for a repeated
    // parameter — two SHARED BORROWS, no clone and no move — the MIR
    // reader reads that body back identically, and the gate admits it
    // against the real elaborated side A (`acc3d`, both threaded
    // parameters named twice, FAITHFUL; its swapped-argument mutation
    // REFUSED, so the admit is a decision).
    //
    // So the hazard was never repetition. It is exactly ONE thing: the
    // emitter's only MOVE of a parameter's own local is a BARE
    // parameter node sitting directly at a self-call ARGUMENT position
    // (`ArmLowerer::lower`'s `Rec` arm wraps each lowered argument in
    // `TemplateOperand::Move`, and a bare parameter lowers to the
    // parameter's local itself rather than to a temp). Every other
    // occurrence lowers through `borrow`.
    //
    // `scale a b = if 0 < a then b + scale (a-1) b else 0` remains the
    // adversarial control, and m5 measured the MIR it would emit:
    //
    //     bb5: SELF(move _9, move _2) -> _10
    //     bb6: _11 = &_2; _12 = &_10; NatAdd(move _11, move _12)
    //
    // a borrow of a local the self-call already moved. The MIR reader
    // ACCEPTS that body, so this rule is the only guard — which is why
    // R3b refines it rather than removing it, and why the control lands
    // in the same change.
    //
    // This is a WELL-FORMEDNESS seam, not a proof seam: a wrong answer
    // here is MIR that fails rustc's own borrowck loudly, never a false
    // verdict. The gate downstream is unmoved either way.
    for (arm, value) in [("zero", zero_value), ("nonzero", nonzero_value)] {
        let holds_call = value.contains(&RecBodyExpr::Rec);
        // The bare node that denotes parameter `index` — the one
        // spelling that is a MOVE at an argument position. The measure
        // has its own spelling, exactly as everywhere else in this
        // lane; `Pred` is NOT it (it borrows the measure and returns a
        // temp), which is why the ubiquitous `f (n-1) …` is unaffected.
        let bare = |index: usize| {
            if index == *measure_index {
                RecBodyExpr::Decreasing
            } else {
                RecBodyExpr::Param(index)
            }
        };
        for index in 0..signature.arity() {
            let mut uses = value.parameter_uses(index, *measure_index);
            let mut moved = false;
            if holds_call {
                uses += rec_args
                    .iter()
                    .map(|argument| argument.parameter_uses(index, *measure_index))
                    .sum::<usize>();
                moved = rec_args.iter().any(|argument| *argument == bare(index));
            }
            if moved && uses > 1 {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: wf_boundary_reason(&format!(
                        "its {arm} branch passes parameter {index} to the self-call \
                         BY ITSELF and also uses it elsewhere in that branch ({uses} \
                         uses in total, counting the self-call's own arguments, which \
                         that branch computes); the emitted body MOVES a parameter \
                         passed on its own — every other use is a shared borrow — so \
                         the emission would borrow a local the call has already moved. \
                         Three ways out: pass a computed value instead of the bare \
                         parameter (`{n} + 0` is enough to make it a temp), move the \
                         other use inside the self-call's arguments, or keep the \
                         definition for proof position",
                        n = if index == *measure_index { "n" } else { "p" }
                    )),
                });
            }
        }
        let nodes = value.arith_nodes()
            + if holds_call {
                rec_args.iter().map(RecBodyExpr::arith_nodes).sum::<usize>()
            } else {
                0
            };
        if nodes > COMPOSED_MAX_OPS {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: wf_boundary_reason(&format!(
                    "its {arm} branch composes {nodes} `+`/`*`/`-` node(s) against a \
                     measured fragment of at most {COMPOSED_MAX_OPS} per branch"
                )),
            });
        }
    }
    Ok(())
}

/// Try the one recursive emission shape: a kernel-proved projection.
///
/// Candidate discovery is intentionally small and deterministic. It accepts
/// at most eight parameters/candidates, clones the environment once, and
/// shares one two-second deadline across every proof attempt. For every
/// same-carrier parameter, mint the canonical projection through the frozen
/// side-B producer and ask the faithfulness gate to prove the whole function
/// equal by induction. Only an actual `StructuralInduction` verdict that
/// completes within the shared deadline selects this shape; an alternative
/// defeq spelling belongs in ordinary recognition, not here. Any rail or
/// failed proof leaves the original capability refusal in force.
fn recognise_inductive_projection(
    env: &Environment,
    declaration: &Name,
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
) -> Option<CleanOriginShape> {
    // Trust: pure equality/induction cannot license eliminating Rust calls.
    // The projection body contains none, so its source must contain none too.
    let body = env.get_const(declaration)?.value.as_ref()?;
    crate::named_calls::check_rust_call_free(env, body, callees).ok()?;
    let display_name = declaration.to_string();
    let name = display_name.as_str();
    let deadline = Instant::now() + INDUCTIVE_PROJECTION_TOTAL_TIMEOUT;
    if signature.arity() == 0 || signature.arity() > INDUCTIVE_PROJECTION_MAX_ARITY {
        return None;
    }
    let domains: Vec<Domain> = signature
        .arguments()
        .iter()
        .map(|carrier| ty_to_domain(carrier.rust()))
        .collect::<Option<_>>()?;

    let candidates: Vec<usize> = signature
        .arguments()
        .iter()
        .enumerate()
        .filter_map(|(projected, argument)| {
            (argument.rust() == signature.result().rust()).then_some(projected)
        })
        .take(INDUCTIVE_PROJECTION_MAX_CANDIDATES + 1)
        .collect();
    if candidates.len() > INDUCTIVE_PROJECTION_MAX_CANDIDATES {
        return None;
    }

    let mut scratch = env.clone();
    if Instant::now() >= deadline {
        return None;
    }
    for projected in candidates {
        if Instant::now() >= deadline {
            return None;
        }
        let reflected_name = format!("{name}_trust_clean_origin_inductive_projection_{projected}");
        let admitted = trust_spec_elab::admit_projection_function(
            &mut scratch,
            &reflected_name,
            &domains,
            projected,
        );
        if Instant::now() >= deadline {
            return None;
        }
        if admitted.is_err() {
            continue;
        }
        let side_b = scratch
            .get_const(&Name::from_string(&reflected_name))
            .and_then(|constant| constant.value.clone());
        if Instant::now() >= deadline {
            return None;
        }
        let Some(side_b) = side_b else { continue };
        let faithful = match check_faithful_for_name_with_deadline(
            env,
            declaration,
            &side_b,
            signature.result(),
            deadline,
        ) {
            Ok(faithful) => faithful,
            Err(_) if Instant::now() >= deadline => return None,
            Err(_) => continue,
        };
        if Instant::now() < deadline && faithful.method() == FaithfulnessMethod::StructuralInduction
        {
            return Some(CleanOriginShape::InductiveProjection { projected });
        }
    }
    None
}

/// The plan-time signature check for the structural-recursion shape: exactly
/// one parameter, and EVERY position — parameter and result — at Clean `Nat`
/// (the bignum carrier). The reflected side B is stated at `Nat`, so any
/// other position cannot be identified with any mintable reflection; and the
/// e2 measurement (open equations at the u64 carrier are NOT definitional —
/// `Nat.mod` sticks) is why there is no u64 structural lane to fall back to.
fn check_structural_nat_signature(
    name: &str,
    signature: &CarrierSignature,
) -> Result<(), EmitRefusal> {
    if signature.arity() != 1 {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is a structural recursion over {} parameters; the emittable \
                 structural fragment is single-parameter (widen by naming the extra \
                 parameters in a wrapper `def` and keeping the recursion unary, or \
                 cite `{name}` from proof position)",
                signature.arity()
            ),
        });
    }
    let all_nat = signature.result().clean() == CleanType::Nat
        && signature.arguments().iter().all(|argument| argument.clean() == CleanType::Nat);
    if !all_nat {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "it is a structural recursion whose signature is not `Nat -> Nat`; \
                     the structural lane is stated at the bignum carrier only"
                .to_owned(),
        });
    }
    Ok(())
}

/// The plan-time signature check for the WELL-FOUNDED shape: at least one
/// parameter, and EVERY position at Clean `Nat` (the bignum carrier).
///
/// A separate function from [`check_structural_nat_signature`], with separate
/// wording, deliberately: the two lanes' refusals name different fixes, and a
/// shared message that fit neither would be the v7/D3 defect. The CARRIER
/// condition is the same, and it is the same for the same reason — the
/// reflected side B is stated at `Nat` (its `Nat.sub`, `Nat.add` and `Nat.lt`
/// nodes are `Nat`'s), so no other position can be identified with any mintable
/// reflection.
///
/// # R3a (2026-08-26): the ARITY condition is gone from this lane
///
/// It used to demand exactly one parameter, on the recorded grounds that
/// "multi-parameter well-founded recursion is R3, blocked additionally in
/// `first-party/clean`". The second half of that was measured FALSE at this
/// same pin (`r6_nat_mul_probes` q1, `r7_arity_widening_probes` q1): what
/// `first-party/clean` refuses is a measure naming more than one parameter, not
/// a recursion naming more than one parameter. A two-parameter recursion with a
/// ONE-parameter measure elaborates and kernel-checks today, so the arity limit
/// was this crate's alone — and per v7/D2 a measured fragment boundary is a
/// statement of where we are, never a design.
///
/// What did NOT move: the measure is still a single parameter, decreasing by
/// exactly one, and the recognizer still reads it out of the emitted zero test.
/// A lexicographic or packed measure is still refused, by the elaborator.
fn check_wf_nat_signature(name: &str, signature: &CarrierSignature) -> Result<(), EmitRefusal> {
    if signature.arity() == 0 {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(
                "it is a well-founded recursion over no parameters at all, so there is nothing \
                 for the measure to be",
            ),
        });
    }
    let all_nat = signature.result().clean() == CleanType::Nat
        && signature.arguments().iter().all(|argument| argument.clean() == CleanType::Nat);
    if !all_nat {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: wf_boundary_reason(
                "its signature is not `Nat -> Nat`; the well-founded lane is stated at the \
                 bignum carrier only, because the reflected functional's arithmetic is \
                 `Nat`'s",
            ),
        });
    }
    Ok(())
}

/// Which kernel termination-evidence form a recursive plan requires.
///
/// The seam §6e names, now with BOTH of its arms constructed — R1 landed
/// `Structural` and R2 landed `WellFounded`. They are deliberately separate
/// values rather than "any recursor-ish head": the evidence a recursive
/// emission rests on differs in kind between them (iota over `RecursorRule`s
/// for one, the `rec : (y : α) → r y x → C y` slot's typing rule for the
/// other), and a shape must not silently acquire the other's.
#[derive(Clone, Copy, PartialEq, Eq)]
enum TerminationEvidence {
    /// `Nat.rec`-headed — the kernel's own iota + strict positivity.
    Structural,
    /// `WellFounded.fix`-headed — the kernel's own typing rule at the
    /// decrease slot (`r2_wf_equation_probes` w7/d1).
    WellFounded,
}

/// **Kernel termination evidence for a recursive emission** — the named seam
/// the §6e ruling requires.
///
/// ONLY the required head, on a `FullKernelCheck` declaration, passes.
/// Totality is then the KERNEL's own — iota over `RecursorRule`s plus strict
/// positivity for the structural form (`recursion_boundary_probes` §1b), the
/// decrease slot's typing rule for the well-founded one (w7/d1) — never an
/// engine obligation, so the v6/D2 boundary is untouched. Deliberately
/// re-reads the declaration rather than trusting the recogniser that shaped
/// the plan: the evidence decision is its own seam.
///
/// **What this seam does NOT establish, and must not be read as establishing:**
/// for the well-founded form the typing rule is only as strong as the axiom
/// closure of the proof terms in the decrease slots — with one assumed
/// decrease a diverging functional kernel-checks and the declaration ADMITS
/// (probe c1, reproduced adversely). That other half is
/// `gate::check_faithful_wf_functional`'s hard precondition. A plan is not
/// permission to emit.
fn require_kernel_termination_evidence(
    env: &Environment,
    declaration: &Name,
    required: TerminationEvidence,
) -> Result<(), EmitRefusal> {
    let kernel_name = declaration.clone();
    let display_name = declaration.to_string();
    let name = display_name.as_str();
    if env.declaration_verification(&kernel_name) != Some(DeclarationVerification::FullKernelCheck)
    {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its termination evidence must be the kernel's own, and this \
                     declaration did not enter the environment through a full kernel \
                     check"
                .to_owned(),
        });
    }
    let value = env
        .get_const(&kernel_name)
        .and_then(|constant| constant.value.clone())
        .ok_or_else(|| EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "it has no definition body to read termination evidence from".to_owned(),
        })?;
    // Peel EVERY leading lambda. R3a: an arity-N declaration abstracts N
    // parameters before its recursor/fixpoint spine, so peeling at most one
    // left the head a `Lam` at arity 2 and this seam reported "not a recursor
    // or fixpoint application" about a term that is one.
    let mut cursor = strip_mdata(&value);
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = strip_mdata(inner);
    }
    let head = spine_head(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its value is not a recursor or fixpoint application, so no \
                     kernel termination evidence applies to it"
                .to_owned(),
        });
    };
    match required {
        TerminationEvidence::Structural => {
            if name_eq2(head_name, "Nat", "rec") {
                return Ok(());
            }
            if name_eq2(head_name, "WellFounded", "fix") {
                // The shapes disagree about the same declaration: refuse
                // rather than let a structural plan ride WF evidence.
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: wf_boundary_reason(
                        "a structural plan was shaped for it, but its value is a \
                         `WellFounded.fix` spine — the two termination-evidence forms are \
                         not interchangeable",
                    ),
                });
            }
            Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: "its value is not a recursor application, so the kernel's \
                         structural termination evidence does not apply to it"
                    .to_owned(),
            })
        }
        TerminationEvidence::WellFounded => {
            if name_eq2(head_name, "WellFounded", "fix") {
                return Ok(());
            }
            Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: wf_boundary_reason(
                    "a well-founded plan was shaped for it, but its value is not a \
                     `WellFounded.fix` spine",
                ),
            })
        }
    }
}

/// The one v7/D3 refusal text for a `WellFounded.fix`-headed value that falls
/// OUTSIDE the R2 fragment, shared by the recogniser, the plan-time re-checks
/// and the termination-evidence seam so the spellings cannot drift.
///
/// **RE-WORDED 2026-08-22, when R2 landed.** The pre-R2 text said the lane
/// "needs kernel-checked equation lemmas for the fix form first (R2's
/// prerequisite)" and that "today only direct structural recursion … is
/// emittable". Both halves are now wrong, and the first was already
/// MEASURED-wrong before R2: `r2_wf_equation_probes` w2 measured that the
/// per-constructor equations of a WF `Nat` def are already `rfl`-definitional
/// at an open argument, and w4 measured that the one candidate unfolding lemma
/// (`WellFounded.fixFEq` at this instantiation) closes by bare `rfl` — so the
/// equation route was never the prerequisite. R2's gate is the F-LAYER
/// comparison and states no equation at all. Probe w8 pinned the old text as
/// data with the instruction to re-word it in the change that lands R2; this
/// is that change, and the phrase is kept in the new text — negated — so the
/// correction is visible to a reader who searches for the old claim.
///
/// **RE-VERIFIED 2026-08-22 (the spelling-gap landing), and this is the part a
/// future reader should not take on trust.** The text below advertises
/// `if h : 0 < n … f (n - 1) … else …` with `termination_by n` as the
/// emittable spelling. Until that landing that sentence was FALSE: the exact
/// program it names was refused by
/// [`recognise_wf_nat_rec`], because the recognizer read `Nat.lt` / `Nat.decLt`
/// / `Nat.sub` where the elaborator emits `LT.lt` / `instDecidableNatLt` /
/// `HSub.hSub`. A refusal that hands back the user's own text as the fix is a
/// v7/D3 defect and it went unnoticed because nothing measured this text
/// against the elaborator. `r2_session_probes::probe_p1_canonical_fixture_plans`
/// now does exactly that — it elaborates this sentence's own program and
/// asserts it plans — so the advertisement and the capability cannot drift
/// apart again silently.
fn wf_boundary_reason(detail: &str) -> String {
    format!(
        "it is a WELL-FOUNDED recursion (`WellFounded.fix`) outside the emittable \
         fragment: {detail}. (kernel-checked equation lemmas are NOT R2's prerequisite — \
         measured `r2_wf_equation_probes` w2/w4: the defining equations are already \
         definitional here and the candidate unfolding lemma closes by `rfl`; the gate \
         compares the FUNCTIONAL and states no equation.) The emittable well-founded \
         fragment is ANY NUMBER of `Nat` parameters at the bignum carrier, at EITHER of \
         `first-party/clean`'s two lowerings. With a ONE-PARAMETER measure \
         (`termination_by n`): the measure is guarded by `if h : 0 < n`, there is exactly \
         ONE self-call, and its measure argument is `n - 1`. With a measure over SEVERAL \
         parameters (`termination_by a + 2*b`, lowered as a course-of-values recursion on \
         the measure's VALUE): the guard is `if h : 0 < p` on any ONE parameter, there is \
         exactly ONE self-call, and its arguments are unrestricted — the decrease is \
         stated about the MEASURE and its proof is borrowed from your own declaration. In \
         both, the remaining self-call arguments and both branch values are built from \
         the parameters, `Nat` numerals, `+`, `*` and truncated `-`, and a parameter \
         passed to the self-call BY ITSELF is used nowhere else in that branch. This is a \
         measured boundary of the compiler, not a rule about what you may write.\n\
         options:\n\
         - restate the definition inside that fragment (`if h : 0 < a then … f (a - 1) b′ \
           … else …`, `termination_by a`) and call it, keeping the general definition \
           alongside for proof position;\n\
         - repeating a parameter is FINE — the emitted body borrows it — but a parameter \
           handed to the self-call on its own is MOVED, so give that call a computed \
           argument instead (`p + 0` is enough), or move the other use inside the call's \
           arguments;\n\
         - a measure that names SEVERAL parameters (as a subtractive `gcd`'s `a + 2*b` \
           does) is EMITTED since R3d, so it is no longer a reason on its own. Two things \
           can still refuse it, and they are different: the decrease cascade must \
           discharge the measure obligation at every call site — that is \
           `first-party/clean`'s refusal, raised before this one — and the guard must be \
           a literal `0 < p` on one of the definition's own parameters, which is what the \
           emitted zero test realises;\n\
         - restate it structurally instead (match on `0` / `n + 1` and recurse on `n`), \
           which the structural lane emits;\n\
         - cite it from a contract instead of calling it — proof position needs no \
           emitted body and has no shape restriction;\n\
         - write the computation as a Rust `fn` and prove it agrees in an `ensures` \
           clause, which is the same guarantee reached from the other side."
    )
}

/// The plan-time signature checks shared by the two arithmetic shapes.
///
/// 1. UNIFORM WIDTH, EVERY POSITION — including unused parameters.
///    Load-bearing, not pedantry: the reflected side B
///    (`admit_expr_function`) is single-domain over ALL n parameters, so a
///    mixed-width side A can never be identified with any mintable side B.
///    Refusing at PLAN time keeps the refusal in the user-actionable
///    capability family instead of surfacing later as an internal error.
/// 2. The result must be an unsigned machine integer. `Bool` has a carrier
///    but no arithmetic domain.
///
/// Returns the one width everything carries at. `shape_desc` names the shape
/// in the user's terms (`"a single wrapping op"` / `"a composed wrapping
/// tree"`) so the refusal stays specific.
fn check_arith_signature(
    name: &str,
    shape_desc: &str,
    signature: &CarrierSignature,
) -> Result<u32, EmitRefusal> {
    if let Some((position, argument)) = signature
        .arguments()
        .iter()
        .enumerate()
        .find(|(_, argument)| argument.rust() != signature.result().rust())
    {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc}, but parameter {position} carries at \
                 `{:?}` while the result carries at `{:?}`; a wrapping-arithmetic body is \
                 emittable only when EVERY signature position — used or not — \
                 shares one unsigned machine width, because the reflected lowering \
                 it must be checked against is single-domain over all parameters",
                argument.rust(),
                signature.result().rust()
            ),
        });
    }
    let Ty::Int { width, signed: false } = *signature.result().rust() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc}, but its result carries at `{:?}`, \
                 which has no wrapping arithmetic; the op fragment exists only at \
                 the unsigned machine widths (u8/u16/u32/u64)",
                signature.result().rust()
            ),
        });
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it is {shape_desc} at width {width}, which is not an \
                 unsigned machine width (u8/u16/u32/u64)"
            ),
        });
    }
    Ok(width)
}

/// One arithmetic leaf's plan-time bounds: a parameter index inside the
/// signature's arity, or a numeral inside the carrier width.
fn check_arith_leaf(
    name: &str,
    operand: &ArithOperand,
    signature: &CarrierSignature,
    width: u32,
) -> Result<(), EmitRefusal> {
    match operand {
        ArithOperand::Param(i) if *i >= signature.arity() => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its operand names parameter {i} but the signature has \
                 only {} parameter(s)",
                signature.arity()
            ),
        }),
        ArithOperand::Const(v) if *v > max_uint_value(width) => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: numeral_out_of_range_reason(*v, width),
        }),
        _ => Ok(()),
    }
}

/// **§6f landing 8** — the LEAF a non-computed [`BeqOperand`] denotes, so the
/// sealed plan's bounds check is [`check_arith_leaf`] and not a second rule.
///
/// A `RawBin` operand is deliberately mapped to a leaf that always passes:
/// its own two leaves are checked directly by the caller, and pretending a node
/// is a leaf here would silently skip one of them.
fn beq_leaf(operand: BeqOperand) -> ArithOperand {
    match operand {
        BeqOperand::Param(index) => ArithOperand::Param(index),
        BeqOperand::Const(value) => ArithOperand::Const(value),
        BeqOperand::RawBin { .. } => ArithOperand::Const(0),
    }
}

/// Walk a composed tree checking every leaf with [`check_arith_leaf`], and
/// return the number of binop NODES. Recursion depth is bounded by the node
/// count, which the caller then bounds by [`COMPOSED_MAX_OPS`] — and which
/// recognition already refused to exceed, so a deeper plan cannot exist.
fn check_composed_tree(
    name: &str,
    expr: &ArithExpr,
    signature: &CarrierSignature,
    width: u32,
) -> Result<usize, EmitRefusal> {
    match expr {
        ArithExpr::Operand(leaf) => {
            check_arith_leaf(name, leaf, signature, width)?;
            Ok(0)
        }
        ArithExpr::Bin { op: _, left, right } => {
            let left = check_composed_tree(name, left, signature, width)?;
            let right = check_composed_tree(name, right, signature, width)?;
            Ok(1 + left + right)
        }
    }
}

/// The one refusal reason for a composed tree outside `2..=COMPOSED_MAX_OPS`
/// nodes, shared by recognition and the plan-time re-check so the two
/// spellings cannot drift (the same rule as [`numeral_out_of_range_reason`]).
/// **§6f landing 7** — the sealed-plan restatement of the divisor rule.
///
/// Deliberately a DIFFERENT text from [`unsafe_divisor_reason`], which the
/// recogniser reports: this one is unreachable from anything a user writes
/// (the recogniser refuses first), so it names the internal invariant rather
/// than offering the user options they have already been given.
fn sealed_plan_divisor_reason(op: RawBinOpKind) -> String {
    let spelling = if op == RawBinOpKind::Div { "/" } else { "%" };
    format!(
        "its `{spelling}` reached the sealed plan with a divisor that is not a strictly \
         positive numeral. Clean's `{{C}}.div`/`.mod` are TOTAL while Rust's `{spelling}` \
         PANICS at zero, so emitting a body for this plan would compute a different function \
         from the declaration. `recognise_raw_binop_expr` is required to have refused it \
         already with the user-facing options, so reaching here means the recogniser and the \
         plan check have drifted apart; NOTHING is planned and nothing is emitted"
    )
}

/// The sealed-plan restatement of the shift-amount rule — the counterpart of
/// [`sealed_plan_divisor_reason`], unreachable from anything a user writes for
/// the same reason.
fn sealed_plan_shift_amount_reason() -> String {
    "its right shift (MIR `Shr`) reached the sealed plan with an amount that is not a \
     numeral strictly below the carrier's width. No such plan has a side B — the frozen \
     producer mints a shift only at such a literal — so nothing could be put to the kernel \
     for it. `recognise_raw_binop_expr` is required to have refused it already with the \
     user-facing options, so reaching here means the recogniser and the plan check have \
     drifted apart; NOTHING is planned and nothing is emitted"
        .to_owned()
}

fn composed_ops_out_of_range_reason(ops: usize) -> String {
    format!(
        "its body reached {ops} composed wrapping operation(s) against a measured \
         fragment of 2..={COMPOSED_MAX_OPS} `+`/`-`/`*` nodes per body \
         (fragment_widening_probes probe_f2 is the measurement); split the definition \
         into smaller `def`s of at most {COMPOSED_MAX_OPS} ops each and compose them at \
         the call site"
    )
}

/// Peel exactly the source-order parameter telescope without evaluating away
/// binders or computational content. Literal and legacy readers share this step.
fn peel_source_parameters<'a>(
    name: &str,
    body: &'a Expr,
    arity: usize,
) -> Result<&'a Expr, EmitRefusal> {
    let mut cursor = strip_mdata(body);
    for _ in 0..arity {
        let ExprKind::Lam(_, _, inner) = cursor.kind() else {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "its type has {arity} argument(s) but its body does not abstract that \
                     many; the emittable shapes — a parameter projection, or a single \
                     wrapping `+`/`-`/`*` — are recognised only under a fully-abstracted \
                     body"
                ),
            });
        };
        cursor = strip_mdata(inner);
    }
    Ok(cursor)
}

/// Does `e` contain a `let` binding ANYWHERE inside the emittable-fragment
/// spine? Used to keep every let-free body on its exact pre-existing path:
/// [`zeta_normalize`] rebuilds a term (new `Arc`s) even when it changes
/// nothing, so it is invoked only when this returns `true`.
///
/// The exotic mode extensions (cubical / ZFC / SProp) are treated as leaves:
/// they never appear in a UInt/`Nat` carrier body, and if one somehow held a
/// `let`, missing it here only makes the recogniser refuse the body — never
/// emit a wrong one.
fn expr_contains_let(e: &Expr) -> bool {
    match e.kind() {
        ExprKind::Let(..) => true,
        ExprKind::App(f, a) => expr_contains_let(f) || expr_contains_let(a),
        ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
            expr_contains_let(ty) || expr_contains_let(b)
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => expr_contains_let(inner),
        _ => false,
    }
}

/// Replace every `let y := v; b` with `b[y := v]`, bottom-up — the kernel's own
/// zeta reduction (`tc::whnf`: `Let(_, _, val, body, _) => body.instantiate(val)`).
///
/// The result is `let`-free (every binder is discharged into the body via the
/// de-Bruijn-correct, capture-avoiding [`Expr::instantiate`]), so a nested or
/// shadowing `let`, a `let` whose bound value is itself a `let`, and a `let`
/// in operand position all reduce uniformly. On a `let`-free subterm the walk
/// reproduces the term up to re-allocation, which is why the caller gates it
/// behind [`expr_contains_let`].
///
/// The kernel gate independently checks return-value equality against the
/// original declaration. It does not check Rust call effects or panic:
/// [`recognise_clean_shape`] must separately check substitution effects before
/// invoking this walk. `MData` (transparent to type-checking and to def-eq) is dropped
/// during the walk, exactly as [`strip_mdata`] drops it at the cursor.
fn zeta_normalize(e: &Expr) -> Expr {
    match e.kind() {
        ExprKind::Let(_, _, val, body, _) => {
            let val = zeta_normalize(val);
            zeta_normalize(body).instantiate(&val)
        }
        ExprKind::App(f, a) => Expr::app(zeta_normalize(f), zeta_normalize(a)),
        ExprKind::Lam(bd, ty, b) => Expr::lam(bd.clone(), zeta_normalize(ty), zeta_normalize(b)),
        ExprKind::Pi(bd, ty, b) => Expr::pi(bd.clone(), zeta_normalize(ty), zeta_normalize(b)),
        ExprKind::Proj(name, idx, inner) => {
            Expr::proj_arc(name.clone(), *idx, std::sync::Arc::new(zeta_normalize(inner)))
        }
        // `MData` is transparent; drop it rather than re-import `MDataMap`.
        ExprKind::MData(_, inner) => zeta_normalize(inner),
        _ => e.clone(),
    }
}

/// **W5 increment 7 — the explicit value temporary for a `let`-bound Rust
/// call.** Walk the top-level `let` spine of the peeled body OUTERMOST-FIRST
/// and mint one [`RustCallNode`] per `let` whose value is a Rust callee
/// application, marked [`RustCallNode::let_binding`] `Some(k)`, in scope for
/// every later `let` value and for the residual body through
/// [`RustCallScope`]. The residual body MUST itself be a callee application
/// (the root) — or the LAST temporary itself, by name or through pure
/// aliases (`let y := f x; let z := y; z`), which is the identity `let`
/// after the aliases resolve and makes that node the root (review finding
/// N2, step (iv) below); anything else is a [`EmitRefusal::LetSpine`] naming
/// the binder and the options.
///
/// The semantics this emits is TRUST'S definition, not Lean fidelity: every
/// such `let` is evaluated exactly once, in binding order, before the body,
/// whether the binder is read 0, 1 or n times; a dead binding whose callee
/// panics PANICS (a `let`-bound call is never dropped); arguments evaluate
/// left-to-right (post-order). Lean's compiler DCEs dead lets and promises
/// no order for pure code, and the kernel identifies the once-body with the
/// duplicated and the dropped one (zeta) — so the once/order claim is the
/// STRUCTURAL chain sealed by [`check_rust_call_chain`] and pinned by
/// `control_27`, disclosed in `docs/TCB.md`.
///
/// What is zeta'd IN PLACE, exactly as today's path does it
/// ([`zeta_normalize`]'s rule, `inner.instantiate(val)`): an IDENTITY `let`
/// (`let y := f x; y` stays ONE node — the body's root) and a PURE `let`
/// (`check_rust_call_free`-clean: it contains no call, so substituting it
/// changes no evaluation). A `let` nested inside a value or inside the
/// residual gets today's `check_let_substitutions` + `zeta_normalize`, so a
/// Rust `let` in operand position is refused with the HOIST option and an
/// identity one is admitted, exactly as on the zero-binding path.
///
/// `Ok(None)` = no Rust-call `let` on the spine: the caller runs today's path
/// on the ORIGINAL body, byte-for-byte (every pre-existing `let` fixture is
/// provably unaffected: `control_24`, `named_lean_calls`, `clean_origin_let`).
/// This is the ONE walk; every planner caller (the mint seam, the MIR gate,
/// the verify pass) reaches it through [`recognise_clean_shape`] — do not
/// fork it per caller, or their plans disagree and the MIR gate reports a
/// fatal self-disagreement.
fn walk_let_spine(
    env: &Environment,
    name: &str,
    body: &Expr,
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    // No callee table, no Rust `let`: the no-callee entry keeps its exact
    // pre-existing path, refusal texts included.
    if callees.is_empty() {
        return Ok(None);
    }
    let arity = signature.arity();
    // A body that does not abstract its telescope is today's path's refusal,
    // with today's reason; this walk has nothing to add.
    let Ok(peeled) = peel_source_parameters(name, body, arity) else {
        return Ok(None);
    };
    let mut cursor: Expr = peeled.clone();
    let mut nodes: Vec<RustCallNode> = Vec::new();
    // `temps[k]` = the node computing the `k`-th Rust-call `let`; `binders`
    // its source names, for the notes.
    let mut temps: Vec<usize> = Vec::new();
    let mut binders: Vec<String> = Vec::new();
    let let_refusal =
        |reason: String| EmitRefusal::LetSpine { name: name.to_owned(), reason, defect: false };
    loop {
        let ExprKind::Let(binder, _ty, val, inner, _) = strip_mdata(&cursor).kind() else {
            break;
        };
        let val: &Expr = val;
        // (i) a `let` nested inside this VALUE: today's rule, in place. A
        // Rust `let` nested there has one honest fix — hoist it to the spine.
        let normalized_val;
        let val: &Expr = if expr_contains_let(val) {
            crate::named_calls::check_let_substitutions(env, val, callees).map_err(|reason| {
                let_refusal(format!(
                    "the value bound by `let {binder}` contains a `let` of its own that binds \
                     a Rust call, and a `let` nested inside a value is not on the spine this \
                     compiler evaluates once: {reason}\n\
                     options:\n\
                     - hoist the inner `let` up to the top of the `def` body, BEFORE \
                       `let {binder}` (`let z := f x; let {binder} := g z z; …`), where each \
                       becomes a value temporary evaluated exactly once in binding order;\n\
                     - or perform that computation in a Rust `fn` and bind ITS call instead"
                ))
            })?;
            normalized_val = zeta_normalize(val);
            &normalized_val
        } else {
            val
        };
        let identity = matches!(strip_mdata(inner).kind(), ExprKind::BVar(0));
        // (ii) a RUST `let`: one node, marked with its binding ordinal, in
        // scope for everything after it. (An identity Rust `let` is instead
        // zeta'd below and becomes the root: one node, today's behaviour.)
        if !identity && callee_index_of(val, callees).is_some() {
            let scope = RustCallScope { arity, temps: &temps };
            // A `NotEmittable` raised INSIDE the spine is re-tagged `LetSpine`
            // so the planner returns it verbatim: left as `NotEmittable`, the
            // expansion fallback would replace this accurate note with
            // `check_let_substitutions`'s "`let`-bind the call at the TOP"
            // advice — which the user has already followed.
            let root = read_rust_call_node(name, val, scope, signature, callees, &mut nodes, 0)
                .map_err(|refusal| match refusal {
                    EmitRefusal::NotEmittable { reason, .. } => let_refusal(reason),
                    other => other,
                })?;
            nodes[root].let_binding = Some(temps.len());
            temps.push(root);
            binders.push(binder.to_string());
            cursor = inner.as_ref().clone();
            continue;
        }
        // (iii) an IDENTITY or PURE `let`: zeta in place, depth unchanged.
        if identity {
            cursor = inner.instantiate(val);
            continue;
        }
        match crate::named_calls::check_rust_call_free(env, val, callees) {
            Ok(()) => {
                cursor = inner.instantiate(val);
                continue;
            }
            // A Lean helper, an opaque, an unchecked theorem or an unknown
            // constant wrapped around a Rust call: neither a callee
            // application (no temporary can be minted for it) nor pure (it
            // cannot be substituted). `check_rust_call_free`'s own note
            // names which, and its options.
            Err(reason) => {
                return Err(let_refusal(format!(
                    "the value bound by `let {binder}` is neither a direct application of a \
                     Rust callee (which this compiler would evaluate once as a value \
                     temporary) nor free of Rust calls (which it could substitute): \
                     {reason}\n\
                     options:\n\
                     - `let`-bind the Rust call ITSELF at the top of the `def` body \
                       (`let t := f x; …`) and pass `t` straight to Rust callees — a Lean \
                       helper applied to a temporary has no emitted form yet;\n\
                     - or perform the Lean-side computation in a Rust `fn` and call that"
                )));
            }
        }
    }
    if temps.is_empty() {
        return Ok(None);
    }
    // The RESIDUAL body: today's rule for any `let` left inside it (an
    // identity `let` in operand position is admitted, a Rust `let` there is
    // refused with the hoist option), then it must be a callee application.
    let normalized_rest;
    let rest: &Expr = if expr_contains_let(&cursor) {
        crate::named_calls::check_let_substitutions(env, &cursor, callees).map_err(|reason| {
            let_refusal(format!(
                "after its `let`-bound Rust call(s) {}, the body contains a `let` in operand \
                 position that binds a Rust call: {reason}\n\
                 options:\n\
                 - hoist that `let` up to the top of the `def` body, where it becomes a value \
                   temporary evaluated exactly once in binding order;\n\
                 - or perform that computation in a Rust `fn` and call it",
                spell_binders(&binders)
            ))
        })?;
        normalized_rest = zeta_normalize(&cursor);
        &normalized_rest
    } else {
        &cursor
    };
    let rest = strip_mdata(rest);
    let scope = RustCallScope { arity, temps: &temps };
    // (iv) THE RESULT IS THE LAST TEMPORARY, by name or through an alias
    // chain (review finding N2, 2026-09-16): `let y := f x; let z := y; z`.
    // The alias `let z := y` is pure and was zeta'd in (iii), so the residual
    // is the binder `y` itself — and `let y := f x; …; y` is the IDENTITY
    // `let` this walk already zetas in (ii)/(iii) when nothing separates the
    // binder from the result (`tailLet`, `identityMid`). This is that rule
    // applied after the alias chain resolved, not a new shape: the node is
    // un-marked and becomes the root; nothing is minted and nothing dropped.
    //
    // SOUNDNESS. The source denotes: every binding on the spine evaluated
    // once, in order (`y`'s last among them), then `y`'s value returned. The
    // chain `[nodes[..t] unchanged, nodes[t] un-marked]` emits the same
    // `Call`s in the same order — the marker is the only edit, and no
    // consumer reads it (materializer, side-B reader, admission and
    // reflection are all marker-agnostic; only this walk and the seal are
    // not) — and node `t`'s `Call` now writes `_0` where the temporary
    // reading would write `_t` and forward it with `_0 = copy _t`. That copy
    // is the whole difference, and it is exactly what the identity `let`
    // elides today. Against the seal: the root is not `let`-bound; `t`
    // carried the HIGHEST ordinal, so the ordinals that remain are still
    // `0..k` consecutive in node order; `t` is read never (no node follows
    // it) and its own reads of earlier nodes are untouched; `t` was the last
    // node minted (the residual minted none), so post-order holds and is
    // tripwired below; the node count is unchanged, so the source
    // cross-check (which runs whenever an EARLIER binding keeps its marker)
    // holds iff it held for the same spine under a call body. With a single
    // binding the chain is one ordinary root — byte-identical to the
    // identity `let`'s plan, cross-check gating included.
    //
    // Why an EARLIER temporary stays refused: `let y := f x; let z := g y; y`
    // must still evaluate `z` (a bound call is never dropped — that IS the
    // once-evaluation claim), and a chain has one place for its result, the
    // root's `Call`; returning `y` would need `_0 = copy _y` AFTER `z`'s
    // call, a statement the materializer does not emit and side B's chain
    // reader does not read. `let_spine_residual_refusal` names the bindings
    // after `y` and the reorder/drop options (v7/D3).
    if let &ExprKind::BVar(index) = rest.kind() {
        if let Some(RustCallArg::Node(node)) = scope.resolve(index as usize) {
            if temps.last() == Some(&node) {
                if node + 1 != nodes.len() {
                    return Err(EmitRefusal::LetSpine {
                        name: name.to_owned(),
                        reason: format!(
                            "its result is its last `let`-bound Rust call (node {node}), but \
                             that node is not the last of {} minted; this is a planner \
                             defect, not something you wrote",
                            nodes.len()
                        ),
                        defect: true,
                    });
                }
                nodes[node].let_binding = None;
                return Ok(Some(CleanOriginShape::RustCallChain { nodes }));
            }
        }
    }
    if callee_index_of(rest, callees).is_none() {
        return Err(let_spine_residual_refusal(name, rest, scope, &binders));
    }
    // Same re-tagging as the binding values above: the residual's own
    // `NotEmittable` (e.g. "argument 1 ... computes (idU x)") must survive to
    // the user instead of the fallback's `let`-bind advice.
    let root = read_rust_call_node(name, rest, scope, signature, callees, &mut nodes, 0).map_err(
        |refusal| match refusal {
            EmitRefusal::NotEmittable { reason, .. } => let_refusal(reason),
            other => other,
        },
    )?;
    // The same post-order discipline `recognise_rust_call_chain` asserts:
    // the root is the LAST node, because `_0`'s writer depends on it.
    if root + 1 != nodes.len() {
        return Err(EmitRefusal::LetSpine {
            name: name.to_owned(),
            reason: "its Rust-call chain did not read back in post-order after the `let` \
                     spine; this is a planner defect, not something you wrote"
                .to_owned(),
            defect: true,
        });
    }
    Ok(Some(CleanOriginShape::RustCallChain { nodes }))
}

/// `` `a`, `b` `` for the notes.
fn spell_binders(binders: &[String]) -> String {
    binders.iter().map(|binder| format!("`{binder}`")).collect::<Vec<_>>().join(", ")
}

/// The residual body of a `let` spine is not a Rust callee application: name
/// what it is instead, in the user's terms, and the ways forward (v7/D3).
fn let_spine_residual_refusal(
    name: &str,
    rest: &Expr,
    scope: RustCallScope<'_>,
    binders: &[String],
) -> EmitRefusal {
    let bound = spell_binders(binders);
    let what = match rest.kind() {
        &ExprKind::BVar(index) => match scope.resolve(index as usize) {
            Some(RustCallArg::Node(_)) => {
                // `BVar(j)` under `len` let binders is binding `len-1-j`.
                let ordinal = scope.temps.len() - 1 - index as usize;
                let later = &binders[ordinal + 1..];
                if later.is_empty() {
                    // The LAST temporary is admitted by the walk before this
                    // refusal is reached (N2); never render an empty binder
                    // list into the sentence if that ever regresses.
                    format!(
                        "its result is the temporary `{}` bound by its last `let`, which the \
                         walk should have admitted as the identity case; this is a planner \
                         defect, not something you wrote",
                        binders[ordinal]
                    )
                } else {
                    format!(
                        "its result is the temporary `{}` bound by an EARLIER `let`, so the \
                         Rust call(s) bound after it by {} are never used by the result",
                        binders[ordinal],
                        spell_binders(later)
                    )
                }
            }
            Some(RustCallArg::Param(i)) => format!(
                "its result is parameter {i} itself, so the Rust call(s) bound by {bound} are \
                 never used by the result"
            ),
            _ => format!(
                "its result is a loose bound variable (de Bruijn {index} under {} binders)",
                scope.binders()
            ),
        },
        _ if is_literal_head(rest) => format!(
            "its result is a literal, so the Rust call(s) bound by {bound} are never used by \
             the result"
        ),
        _ => format!(
            "its result is {} (`{}`), which is not an application of a Rust callee; a `let`-\
             bound Rust call can be consumed only by another Rust call",
            render_head(rest.kind()),
            render_spine_head(rest)
        ),
    };
    EmitRefusal::LetSpine {
        name: name.to_owned(),
        reason: format!(
            "{what}. A `let`-bound Rust call is evaluated exactly once as a value temporary \
             and is never dropped, so its value must reach the result through a Rust call.\n\
             options:\n\
             - return the last-bound value itself (`let y := f x; y`), which needs no \
               temporary and emits one call;\n\
             - reorder the `let`s so the binding the result returns is the LAST one;\n\
             - consume the temporaries in a Rust call (`let y := f x; g y y`), the shape the \
               value temporary exists for — Lean-side arithmetic, comparison or a helper \
               applied to a temporary has no emitted form yet, so move that computation into \
               a Rust `fn` and call it;\n\
             - drop a binding the result never uses, or keep it and return a Rust call that \
               reads it (a dead binding IS evaluated: the compiler never drops a `let`-bound \
               call);\n\
             - or cite `{name}` from proof position instead of calling it, which needs no \
               emitted body"
        ),
        defect: false,
    }
}

/// A numeral or `Bool` literal head, in every spelling the operand readers
/// accept, or a raw kernel literal.
fn is_literal_head(expr: &Expr) -> bool {
    let head = spine_head(expr);
    match head.kind() {
        ExprKind::Lit(_) => true,
        ExprKind::Const(head_name, _) => {
            name_ends_with_of_nat(head_name)
                || name_display_eq_str(head_name, "Bool.true")
                || name_display_eq_str(head_name, "Bool.false")
        }
        _ => false,
    }
}

/// The number of Rust-callee-headed application spines in VALUE position of
/// `expr` — the count the kernel-stored body makes, read independently of
/// the spine walk, for [`check_rust_call_chain`]'s once-evaluation
/// cross-check. Binder TYPES and `Pi`s are not value positions and are not
/// counted (a callee application in a type is erased and the walk mints no
/// node for it); everything the admitted fragment can hold is covered:
/// applications, lambdas, `let` values and bodies, projections, metadata.
///
/// `None` = the body exceeded the explicit-stack budget, which the caller
/// refuses fail-closed rather than guessing a count.
fn count_callee_spines(expr: &Expr, callees: &[RustCalleeRef]) -> Option<usize> {
    const BUDGET: usize = 65_536;
    let mut stack: Vec<&Expr> = vec![expr];
    let mut count = 0usize;
    let mut budget = BUDGET;
    while let Some(expr) = stack.pop() {
        budget = budget.checked_sub(1)?;
        let (head, args) = uncurry(expr);
        stack.extend(args);
        match head.kind() {
            ExprKind::Const(..) => {
                if callee_index_of(head, callees).is_some() {
                    count += 1;
                }
            }
            ExprKind::Lam(_, _ty, body) => stack.push(body),
            ExprKind::Let(_, _ty, val, body, _) => {
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) => stack.push(inner),
            _ => {}
        }
    }
    Some(count)
}

/// Re-check a [`CleanOriginShape::RustCallChain`] node list against the
/// declaration it claims to realize — the exact seal `plan_…` applies to a
/// chain before it becomes a plan, exposed so a control can put a HAND-BUILT
/// chain to it (`control_27` half_9: a shared node without its `let` marker,
/// ordinals out of binding order, a body-only node placed before a
/// `let`-bound one, a forward reference, the node cap, the unfold rail, and
/// a node count the environment body contradicts).
///
/// It mints nothing: `Ok(())` is not a plan and not a permission.
///
/// # Errors
///
/// The seal's refusals ([`EmitRefusal::NotEmittable`] for the carrier and
/// reference rules, [`EmitRefusal::LetSpine`] for the let-temp rules), or
/// the declaration's own planning refusal when it is not a kernel-checked
/// `def` with a total carrier signature.
pub fn check_rust_call_chain_for(
    env: &Environment,
    name: &str,
    nodes: &[RustCallNode],
    callees: &[RustCalleeRef],
) -> Result<(), EmitRefusal> {
    let declaration = Name::from_string(name);
    let (_body, signature) = checked_definition(env, &declaration)?;
    check_rust_call_chain(name, nodes, &signature, callees, Some((env, &declaration)))
}

/// Recognize the whole peeled body, refusing an incomplete source telescope.
fn recognise_clean_shape(
    env: &Environment,
    name: &str,
    body: &Expr,
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
) -> Result<CleanOriginShape, EmitRefusal> {
    let arity = signature.arity();

    // ── LET-BINDINGS (2026-09-13, W5 widening; increment 7, 2026-09-16) ────
    //
    // `let y := v; b` is definitionally `b[y := v]`: the kernel's own zeta step
    // is `whnf`'s `Let(_, _, val, body, _) => Continue(body.instantiate(val))`.
    // Two lanes share that rule:
    //
    // 1. A `let` whose value is a RUST CALL, on the top-level spine, is an
    //    explicit VALUE TEMPORARY ([`walk_let_spine`]): one shared
    //    `RustCallChain` node evaluated exactly once whatever its use count.
    //    The kernel cannot see once-evaluation — zeta identifies the once-body
    //    with the duplicated and the dropped one — so that claim is the
    //    structural chain `check_rust_call_chain` seals (`docs/TCB.md`).
    //
    // 2. Every other `let` (pure, or the exact identity) is reduced away with
    //    exactly the zeta rule, bottom-up ([`zeta_normalize`]), and the
    //    let-free body flows into the SAME shape recognisers, materializer,
    //    side-B readers and gate as its let-free equivalent — nothing
    //    downstream learns the `let` existed. Pure duplication
    //    (`let y := x+1; y*y` -> `(x+1)*(x+1)`) reaches the kernel gate, which
    //    compares the proposed shape with the UNTOUCHED declaration.
    //
    // Both are invoked ONLY when [`expr_contains_let`] holds, so every
    // existing control/probe over let-free bodies is byte-for-byte
    // unaffected; and lane 1 returns `Ok(None)` when no Rust-call `let` is on
    // the spine, so every pre-existing `let` fixture stays on lane 2. What
    // neither lane may do is substitute a Rust call: `check_let_substitutions`
    // refuses that with the hoist option, because the kernel's mathematical
    // callee model captures neither effects nor panic.
    let normalized;
    let body: &Expr = if expr_contains_let(body) {
        if let Some(shape) = walk_let_spine(env, name, body, signature, callees)? {
            return Ok(shape);
        }
        crate::named_calls::check_let_substitutions(env, body, callees)
            .map_err(|reason| EmitRefusal::NotEmittable { name: name.to_owned(), reason })?;
        normalized = zeta_normalize(body);
        &normalized
    } else {
        body
    };

    // §6f LANDING 2. Landing 1 refused EVERY nullary body here, with a reason
    // that named its own diagnosis: *"probe_e3 locates that defect in the
    // arity-erasing nullary-mint routing, not in kernel definitional
    // equality"*. Landing 2 measured the repair (l2_p1: the two producers mint
    // the same term at zero parameters) and the boundary moved to where the
    // measurement actually is — a nullary body is refused when it is not a
    // NUMERAL, not because it is nullary. The peel loop below is already a
    // no-op at arity 0, so the constant recognition needs no special case; only
    // the blanket early return had to go.
    let cursor = peel_source_parameters(name, body, arity)?;

    match cursor.kind() {
        &ExprKind::BVar(index) => {
            let index = index as usize;
            if index >= arity {
                // A loose bound variable under the binders we peeled. The
                // kernel would not have accepted this, so reaching it means the
                // environment disagrees with itself; refuse.
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: format!(
                        "its body is a loose bound variable (de Bruijn {index} under {arity} \
                         binders)"
                    ),
                });
            }
            // Under `n` binders, de Bruijn `k` is SOURCE parameter `n-1-k`.
            // This inversion is the one-construct mistake this lane can make;
            // `admit_projection_function` performs the inverse when it mints
            // side B, and the gate is what catches a disagreement.
            Ok(CleanOriginShape::Projection { projected: arity - 1 - index })
        }
        other => {
            // §6f landing 2: the CONSTANT body, first because it is a LEAF and
            // its side-A heads (`{C}.ofNat`, `OfNat.ofNat`) are disjoint from
            // every op spine head — so this is not a tiebreak and the order
            // changes nothing that follows it. `recognise_wrapping_expr` used
            // to return `Ok(None)` for exactly this shape ("a bare leaf body
            // (`fun a => 6`) … keeping the ConstantUint boundary exactly where
            // it was"); that boundary is what this landing moved.
            if let Some(shape) = recognise_constant_body(name, cursor, signature)? {
                return Ok(shape);
            }
            // W5 (Lean-calls-Rust): a head naming a compiler-declared RUST
            // CALLEE. Placed BEFORE the nullary boundary and before every op
            // spine, and disjoint from all of them by construction rather
            // than by order: a callee is admitted only under a bare name the
            // environment did not already hold (`declare_rust_callees`
            // refuses `DuplicateName`), so no prelude head — `ite`,
            // `HAdd.hAdd`, `Nat.rec`, `{C}.ofNat` — can also be a callee.
            if let Some(shape) = recognise_rust_call_chain(name, cursor, arity, signature, callees)?
            {
                return Ok(shape);
            }
            // …and the NULLARY boundary stops here, deliberately. Landing 2
            // measured ONE nullary shape and admitted exactly that one. Every
            // reading below is stated over parameters, and letting a nullary
            // body fall into them would silently admit shapes nothing measured
            // (a nullary `UInt64.add 1 2` reads as a `WrappingBinOp` over two
            // `Const` leaves and would have emitted, unmeasured, as a side
            // effect of deleting an early return). A widening is an increment
            // with a probe, never a fall-through.
            if arity == 0 {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: nullary_non_constant_reason(),
                });
            }
            if let Some(shape) = recognise_wrapping_expr(name, cursor, arity, signature)? {
                return Ok(shape);
            }
            // §6f LANDING 7 — the RAW-BINOP spines (`&&&`, `|||`, `/`, `%`,
            // and since 2026-09-23 `^^^`, `>>>`; the set is `raw_binop_rows`).
            //
            // BESIDE `recognise_wrapping_expr`, never inside it, and the
            // placement is the discipline rather than an accident: the two
            // families realize DIFFERENT MIR (a marker-authenticated `Call`
            // chain versus a bare `Rvalue::BinaryOp`), so widening the
            // wrapping descent to also return these shapes would put one
            // descent in front of two emitter arms — the drift
            // `TemplateRefusal::RealizationDisagrees` exists to catch, made
            // unreachable instead by keeping the descents apart.
            //
            // The six heads (`HAnd.hAnd`, `HOr.hOr`, `HDiv.hDiv`,
            // `HMod.hMod`, `HXor.hXor`, `HShiftRight.hShiftRight`) are
            // DISJOINT from `HAdd`/`HSub`/`HMul` and from every leaf head, so
            // the order here is not a tiebreak either.
            if let Some(shape) = recognise_raw_binop_expr(name, cursor, arity, signature)? {
                return Ok(shape);
            }
            // W6 (Rust-calls-Clean): a comparison of two parameters returned as
            // `Bool` (`decide (a < b)` / `BEq.beq … a b`). Disjoint from every
            // shape below by RESULT TYPE — those all require a `UInt` result and
            // decline a `Bool` one — and by HEAD (`decide`/`BEq.beq` vs `ite`).
            if let Some(shape) = recognise_decide_comparison(cursor, arity, signature) {
                return Ok(shape);
            }
            // W6 (Rust-calls-Clean): a boolean negation/connective over `Bool`
            // parameters (`Bool.not b`, `and a b`, `or a b`). Disjoint by HEAD
            // and by RESULT TYPE (`Bool`) from every shape below.
            if let Some(shape) = recognise_bool_value(cursor, arity, signature) {
                return Ok(shape);
            }
            if let Some(shape) = recognise_bool_expression(cursor, arity, signature) {
                return Ok(shape);
            }
            // R2/C5a: the parameter-select ite.
            if let Some(shape) = recognise_select_ite(cursor, arity, signature) {
                return Ok(shape);
            }
            if let Some(shape) = recognise_unsigned_conditional(cursor, arity, signature) {
                return Ok(shape);
            }
            // R1 (§6e as amended): structural single-step Nat recursion.
            if let Some(shape) = recognise_structural_nat_rec(name, cursor, arity, signature)? {
                return Ok(shape);
            }
            // §6f LANDING 6 — the `==` CONDITION SPELLING, now a SHAPE.
            //
            // Placed AFTER every pre-existing recognizer, exactly where landing
            // 5 put its refusal, so it still cannot take a body that used to
            // plan: the recognizers above return early, and the tree this reads
            // is one every one of them already declined (its proposition is
            // stated at `Bool`, not at the carrier). It is likewise DISJOINT by
            // head from the two boundary arms below, which are
            // `WellFounded.fix`/`Nat.rec` spines.
            if let Some(shape) = recognise_beq_select_ite(cursor, arity, signature) {
                return Ok(shape);
            }
            // §6f LANDING 8 — the GENERAL `==` select: a computed decision
            // operand, and the `= false` lift.
            //
            // Placed immediately AFTER the narrow one, which is the only order
            // that keeps the two disjoint by construction rather than by
            // tiebreak: the narrow recogniser takes every `true`-lifted
            // leaf-operand tree and returns early, so what reaches here is
            // exactly what it declined. The general recogniser then re-states
            // that disjointness itself and the sealed plan re-checks it a third
            // time, because "one body, one plan" must be a property of the plan.
            if let Some(shape) = recognise_beq_general_select_ite(name, cursor, arity, signature)? {
                return Ok(shape);
            }
            // …and the REFUSAL is what remains: `!=`, whose blocker moved but
            // did not clear, and an `==` whose OPERANDS are outside the
            // fragment. Both plan NOTHING and emit NOTHING; this is a v7/D3
            // refusal (*"a refusal must carry the fix, with options"*) and
            // `beq_boundary_reason` states exactly what is and is not claimed.
            if let Some(reading) = recognise_bool_decision_ite(cursor, signature) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: beq_boundary_reason(reading.spelling, signature),
                });
            }
            // The two recursion-adjacent boundaries, each with its own
            // measured v7/D3 refusal instead of the generic fragment text:
            // a WellFounded.fix value OUTSIDE R2's fragment, and the
            // u64-carrier recursor-over-toNat shape (probe e2's boundary: OPEN
            // equations at the u64 carrier are not definitional, so no
            // per-equation gate exists there).
            //
            // R2 (2026-08-22) runs BEFORE this function, on the unpeeled body
            // (`plan_clean_origin_body`), because the island's spine is
            // eta-contracted and would not survive the lambda peel above. What
            // reaches here is therefore a `WellFounded.fix` body that R2's own
            // recogniser already declined AND whose arity peel succeeded — a
            // multi-parameter fix, or a spine R2 read as out-of-fragment for a
            // reason its own refusal already named. Keeping this arm is the
            // fail-closed backstop, not a duplicate route.
            if spine_head_is(cursor, "WellFounded.fix") {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: wf_boundary_reason(
                        "its `WellFounded.fix` spine is not the one-parameter-measure shape \
                         this lane reads",
                    ),
                });
            }
            if is_u64_wrapped_nat_recursor(cursor) {
                return Err(EmitRefusal::NotEmittable {
                    name: name.to_owned(),
                    reason: "it is a recursion computed at `Nat` and wrapped back to a \
                             machine width (`UInt64.ofNat (Nat.rec … (UInt64.toNat _))`). \
                             The per-defining-equation gate cannot be stated at the u64 \
                             carrier: the OPEN equations there are NOT definitional — \
                             `UInt64.toNat (UInt64.ofNat (Nat.succ n))` sticks on `Nat.mod` \
                             at an open `n` (measured: r1_equation_probes e2) — so only \
                             CLOSED u64 instances compute, and a closed-only gate is not a \
                             faithfulness gate. options: restate the recursion at \
                             `Nat -> Nat` (the bignum carrier is exact and emittable) and \
                             convert at the call site; or keep this definition for proof \
                             position, where no emitted body is needed"
                        .to_owned(),
                });
            }
            // §6f landing 1 / ruling v7/D3: the generic fragment prose is kept
            // verbatim (a dozen probes and controls pin substrings of it) and
            // the ROW is CITED BY NAME after it. `head_label` names the kernel
            // head exactly when it is a constant, which is the coordinate a row
            // is keyed on — so the refusal states the work item, not just the
            // disappointment. WHICH citation is the table's answer, not an
            // assumption: `whole_body_refusal` asks `rows_selecting_head`, and
            // a head a whole-body row DOES select (`HOr.hOr` under a nested
            // `(a &&& b) ||| a`, `ite` with a computed arm) is refused on its
            // SHAPE, naming the row; "no selection row" is said only when no
            // row selects the head (`l7_p17` measures all three cases). This
            // site used to say "no selection row" unconditionally, which was
            // false for exactly the bodies whose head is served.
            //
            // Each row is asked at ITS OWN position (`anchored_carriers`), not
            // at one carrier assumed for the body: a row's class is a claim
            // about the result, the compared width, or its `Bool` operands,
            // depending on the row (`table::CarrierAnchor`). The no-row text is
            // named at the result's class, exactly as before rows were asked.
            //
            // The one clause of the fragment prose that is NOT verbatim is the
            // raw-binop family's: its operators and operand rules are read from
            // `raw_binop_rows` by `raw_binop_vocabulary` (the list this text
            // used to omit entirely), and `l7_p16` pins it against an
            // independent list.
            let (raw_operators, raw_rules) = raw_binop_vocabulary();
            Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: format!(
                    "its body computes (`{}`) outside the emittable fragment: it is \
                     neither a bare parameter projection, nor a single wrapping \
                     `+`/`-`/`*`, nor a nested composition of wrapping `+`/`-`/`*`, \
                     nor ONE raw binary operator — one of {raw_operators} — with no \
                     nested operand{raw_rules}, \
                     nor a select (`if x < y then x else y` over bare parameters, or \
                     `if x < 10 then x else y` with an in-range numeral strictly on \
                     the comparison's RIGHT), over parameters and in-range numerals \
                     at one unsigned machine width, nor a bounded unsigned conditional tree, \
                     nor a single-parameter structural \
                     `Nat` recursion.\n{}",
                    render_head(other),
                    table::whole_body_refusal(
                        &head_label(cursor),
                        anchored_carriers(env, cursor, signature),
                    ),
                ),
            })
        }
    }
}

/// **W5 (Lean-calls-Rust) — the RUST-CALL CHAIN, side A.** Read a fully-peeled
/// body whose head is a compiler-declared Rust callee as a
/// [`CleanOriginShape::RustCallChain`].
///
/// `Ok(None)` = the head is not a callee constant at all, so the caller goes
/// on to the op spines and the boundary refusals. `Err` = the head IS a
/// callee but the application falls outside what this lane emits — a wrong
/// arity (the kernel would have refused it, so reaching it is a self-
/// disagreement), an argument outside the operand vocabulary (a computed
/// value that is not itself a callee application), or a chain past the
/// measured node cap.
///
/// The operand vocabulary: a SOURCE PARAMETER (a bound variable), a NUMERAL
/// at the callee's parameter carrier (either measured spelling, via the same
/// [`numeral_leaf`] every arithmetic leaf goes through), a `Bool` literal, or
/// a NESTED callee application. Carrier agreement is recorded here and
/// RE-CHECKED on the sealed plan by [`check_rust_call_chain`].
fn recognise_rust_call_chain(
    name: &str,
    body: &Expr,
    arity: usize,
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    if callees.is_empty() || callee_index_of(body, callees).is_none() {
        return Ok(None);
    }
    let mut nodes = Vec::new();
    // No `let`-bound temporaries in scope: a `let`-bearing body reaches this
    // reader only through `walk_let_spine`, which passes its own scope.
    let scope = RustCallScope { arity, temps: &[] };
    let root = read_rust_call_node(name, body, scope, signature, callees, &mut nodes, 0)?;
    // The root must be the LAST node (post-order); `read_rust_call_node`
    // pushes a node after its arguments, so this holds by construction and is
    // asserted anyway because `_0`'s writer depends on it.
    if root + 1 != nodes.len() {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its Rust-call chain did not read back in post-order; this is a planner \
                     defect, not something you wrote"
                .to_owned(),
        });
    }
    Ok(Some(CleanOriginShape::RustCallChain { nodes }))
}

/// The index into `callees` of the constant at the head of `expr`'s spine,
/// if it names a declared Rust callee.
fn callee_index_of(expr: &Expr, callees: &[RustCalleeRef]) -> Option<usize> {
    let head = spine_head(expr);
    let ExprKind::Const(head_name, _levels) = head.kind() else {
        return None;
    };
    callees.iter().position(|callee| name_display_eq_str(head_name, &callee.clean_name))
}

/// The scope a Rust-call operand is read in (W5 increment 7): the `arity`
/// source parameters under the peeled telescope, plus the `let`-bound VALUE
/// TEMPORARIES the spine walk has pushed so far — `temps[k]` is the index of
/// the node computing the `k`-th Rust-call `let`, outermost first.
///
/// Under `temps.len()` `let` binders inside `arity` lambda binders, de Bruijn
/// `j` names temporary `temps[len-1-j]` when `j < len` (innermost `let` is
/// `BVar(0)`), and source parameter `arity-1-(j-len)` otherwise. The plain
/// lane passes an empty `temps`, which makes the second arm exactly the
/// pre-existing `arity-1-j` inversion.
#[derive(Clone, Copy)]
struct RustCallScope<'a> {
    arity: usize,
    temps: &'a [usize],
}

impl RustCallScope<'_> {
    /// Resolve de Bruijn `index`; `None` = loose under every binder in scope.
    fn resolve(self, index: usize) -> Option<RustCallArg> {
        let bound_lets = self.temps.len();
        if index < bound_lets {
            return Some(RustCallArg::Node(self.temps[bound_lets - 1 - index]));
        }
        let under_lambdas = index - bound_lets;
        (under_lambdas < self.arity).then(|| RustCallArg::Param(self.arity - 1 - under_lambdas))
    }

    /// Every binder an operand can be read under.
    fn binders(self) -> usize {
        self.arity + self.temps.len()
    }
}

/// Read one callee application (and, recursively, its nested applications)
/// into `nodes` in post-order; returns the index of the node pushed for
/// `expr`.
///
/// Recursion depth is bounded by the node count, which is bounded by
/// [`COMPOSED_MAX_OPS`] — checked as nodes are pushed, so an adversarially
/// deep term refuses instead of exhausting the stack.
fn read_rust_call_node(
    name: &str,
    expr: &Expr,
    scope: RustCallScope<'_>,
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
    nodes: &mut Vec<RustCallNode>,
    depth: usize,
) -> Result<usize, EmitRefusal> {
    // THE DESCENT RAIL. Nodes are pushed AFTER their arguments are read, so
    // the node cap alone bounds nothing about the descent; the depth is
    // bounded here, before the recursion, so an adversarially nested term
    // refuses instead of overflowing the stack.
    if depth > COMPOSED_MAX_OPS {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its Rust-call chain nests deeper than {COMPOSED_MAX_OPS} calls, which is past \
                 the measured chain depth. options: split the chain across sibling `def`s and \
                 compose them at the call site"
            ),
        });
    }
    let Some(callee_index) = callee_index_of(expr, callees) else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its Rust-call chain reached a non-callee head; this is a planner defect"
                .to_owned(),
        });
    };
    let callee = &callees[callee_index];
    let (_head, args) = uncurry(expr);
    if args.len() != callee.params.len() {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "it applies Rust callee `{}` to {} argument(s), but `fn {}` takes {}; a \
                 partial application has no Rust body to emit. options: apply `{}` to all \
                 of its parameters; or restate the definition without the partial \
                 application",
                callee.clean_name,
                args.len(),
                callee.clean_name,
                callee.params.len(),
                callee.clean_name,
            ),
        });
    }
    // ARGUMENTS ARE READ IN SOURCE ORDER, and each one's calls are pushed
    // before the next one's, so the emitted chain evaluates them left to
    // right exactly as written — the property the `let` spine walk above
    // relies on, and the reason a nested callee application in operand
    // position is not a reordering.
    let mut read_args = Vec::with_capacity(args.len());
    for (position, (arg, param_ty)) in args.iter().zip(&callee.params).enumerate() {
        let arg = strip_mdata(arg);
        let read = match arg.kind() {
            &ExprKind::BVar(index) => {
                let index = index as usize;
                // A `let`-bound temporary (innermost `let` first), else a
                // SOURCE parameter under the `n` lambda binders (`n-1-k`),
                // else loose — see `RustCallScope::resolve`.
                let Some(operand) = scope.resolve(index) else {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "its body is a loose bound variable (de Bruijn {index} under {} \
                             binders)",
                            scope.binders()
                        ),
                    });
                };
                operand
            }
            _ if callee_index_of(arg, callees).is_some() => {
                let node =
                    read_rust_call_node(name, arg, scope, signature, callees, nodes, depth + 1)?;
                RustCallArg::Node(node)
            }
            _ => match rust_call_literal(name, arg, param_ty)? {
                Some(literal) => RustCallArg::Literal(literal),
                None => {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: format!(
                            "argument {position} of its call to Rust callee `{}` computes \
                             ({}) — a Clean-origin call may pass only a parameter, an \
                             in-range numeral, a `Bool` literal, or the result of another \
                             Rust callee. options: bind the computation in a sibling Rust \
                             `fn` and call that; or restate the argument as one of those \
                             operands",
                            callee.clean_name,
                            render_spine_head(arg),
                        ),
                    });
                }
            },
        };
        read_args.push(read);
    }
    if nodes.len() >= COMPOSED_MAX_OPS {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its Rust-call chain has more than {COMPOSED_MAX_OPS} calls, which is past the \
                 measured chain depth. options: split the chain across sibling `def`s and \
                 compose them at the call site"
            ),
        });
    }
    // An ordinary operand node; `walk_let_spine` marks the `let`-bound ones
    // AFTER the read, on the root it returns.
    nodes.push(RustCallNode { callee: callee_index, args: read_args, let_binding: None });
    Ok(nodes.len() - 1)
}

/// A literal argument at the callee's parameter carrier: `Bool.true` /
/// `Bool.false` for a `bool` parameter, or a carrier numeral in either
/// measured spelling for an unsigned machine parameter. `Ok(None)` = not a
/// literal at that carrier (the caller refuses with the operand vocabulary);
/// `Err` = a numeral that does not fit the parameter's width.
fn rust_call_literal(
    name: &str,
    arg: &Expr,
    param_ty: &Ty,
) -> Result<Option<RustCallLiteral>, EmitRefusal> {
    match param_ty {
        Ty::Bool => {
            let ExprKind::Const(head_name, _) = strip_mdata(arg).kind() else {
                return Ok(None);
            };
            if name_display_eq_str(head_name, "Bool.true") {
                Ok(Some(RustCallLiteral::Bool(true)))
            } else if name_display_eq_str(head_name, "Bool.false") {
                Ok(Some(RustCallLiteral::Bool(false)))
            } else {
                Ok(None)
            }
        }
        Ty::Int { width, signed: false } if matches!(width, 8 | 16 | 32 | 64) => {
            let Some(carrier_name) = uint_carrier_name(*width) else {
                return Ok(None);
            };
            let Some(reading) = numeral_leaf(arg, carrier_name) else {
                return Ok(None);
            };
            match in_range_numeral(name, reading, *width)? {
                ArithOperand::Const(value) => Ok(Some(RustCallLiteral::UInt(value))),
                ArithOperand::Param(_) => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

/// The sealed-plan invariants of a [`CleanOriginShape::RustCallChain`]:
/// every callee index in the table, every node referenced only by a LATER
/// node (post-order), every argument at the carrier the callee's parameter
/// takes, and the root's result at the declaration's result carrier. Each is
/// re-checked here because the plan is the decision the emitter trusts.
///
/// **W5 increment 7 — the chain is a DAG, and this seal is where the
/// once-evaluation claim is made structural.** An ordinary node is read
/// exactly once (the root never); a node marked [`RustCallNode::let_binding`]
/// may be read 0..n times, and the marked nodes carry consecutive ordinals
/// in node order (binding order = evaluation order); and an ORDINARY node
/// below the last marked node must be part of some binding's value —
/// transitively read by a marked node of greater index — or it is a body
/// call evaluated before a binding, which a strict `let` spine never does
/// (review finding N3; the walk cannot mint that order, so this rule is the
/// seal's own defence in depth). Two rails then bound
/// what side B must do with a shared node: the reflected rendering inlines a
/// temporary per use, so its unfolded size is capped at the kernel envelope
/// this lane is measured at (`named_calls::MAX_NODES`); and, when any
/// binding is present, the node count is CROSS-CHECKED against an
/// independent syntactic count of callee applications in the KERNEL-STORED
/// body (`source`) — the term the gate reads — so a walk that minted two
/// nodes for one `let`, or none for a dead one, is refused as a planner
/// defect before the kernel (which would agree with either) is consulted.
/// Exact on the admitted fragment: pure values contain no callee, an
/// identity `let` contributes exactly its one application, helpers and
/// `ite` are refused, and a bare callee constant is refused by the arity
/// check. It is gated on a binding being present because the helper-
/// expansion path legitimately inlines callee applications out of helper
/// bodies, and no let-bound node can come from that path.
fn check_rust_call_chain(
    name: &str,
    nodes: &[RustCallNode],
    signature: &CarrierSignature,
    callees: &[RustCalleeRef],
    source: Option<(&Environment, &Name)>,
) -> Result<(), EmitRefusal> {
    let refuse = |reason: String| EmitRefusal::NotEmittable { name: name.to_owned(), reason };
    if nodes.is_empty() || nodes.len() > COMPOSED_MAX_OPS {
        return Err(refuse(format!(
            "its Rust-call chain has {} node(s), outside the measured 1..={COMPOSED_MAX_OPS}",
            nodes.len()
        )));
    }
    let mut referenced = vec![0usize; nodes.len()];
    for (index, node) in nodes.iter().enumerate() {
        let Some(callee) = callees.get(node.callee) else {
            return Err(refuse(format!(
                "its Rust-call chain names callee #{} but the table has {} entr(y/ies)",
                node.callee,
                callees.len()
            )));
        };
        if node.args.len() != callee.params.len() {
            return Err(refuse(format!(
                "its call to Rust callee `{}` passes {} argument(s) for {} parameter(s)",
                callee.clean_name,
                node.args.len(),
                callee.params.len()
            )));
        }
        for (position, (arg, param_ty)) in node.args.iter().zip(&callee.params).enumerate() {
            let actual: &Ty = match arg {
                RustCallArg::Param(i) => {
                    let Some(carrier) = signature.arguments().get(*i) else {
                        return Err(refuse(format!(
                            "its operand names parameter {i} but the signature has only {} \
                             parameter(s)",
                            signature.arity()
                        )));
                    };
                    carrier.rust()
                }
                RustCallArg::Node(k) => {
                    if *k >= index {
                        return Err(refuse(format!(
                            "its Rust-call chain node {index} reads node {k}, which is not an \
                             EARLIER node; the chain is not in post-order"
                        )));
                    }
                    referenced[*k] += 1;
                    &callees[nodes[*k].callee].result
                }
                RustCallArg::Literal(RustCallLiteral::UInt(value)) => {
                    let Ty::Int { width, signed: false } = param_ty else {
                        return Err(refuse(format!(
                            "argument {position} of its call to `{}` is a numeral, but that \
                             parameter carries at `{param_ty:?}`",
                            callee.clean_name
                        )));
                    };
                    if !matches!(width, 8 | 16 | 32 | 64) || *value > max_uint_value(*width) {
                        return Err(refuse(numeral_out_of_range_reason(*value, *width)));
                    }
                    continue;
                }
                RustCallArg::Literal(RustCallLiteral::Bool(_)) => {
                    if *param_ty != Ty::Bool {
                        return Err(refuse(format!(
                            "argument {position} of its call to `{}` is a `Bool` literal, but \
                             that parameter carries at `{param_ty:?}`",
                            callee.clean_name
                        )));
                    }
                    continue;
                }
            };
            if actual != param_ty {
                return Err(refuse(format!(
                    "argument {position} of its call to Rust callee `{}` carries at `{actual:?}` \
                     but `fn {}` takes `{param_ty:?}` there; the compiler will not emit a body \
                     whose carrier decision disagrees with the kernel's typing",
                    callee.clean_name, callee.clean_name
                )));
            }
        }
    }
    let root = nodes.len() - 1;
    // ── the reference rule over the DAG (W5 increment 7) ───────────────────
    let tripwire =
        |reason: String| EmitRefusal::LetSpine { name: name.to_owned(), reason, defect: true };
    let mut bound_lets = 0usize;
    for (index, node) in nodes.iter().enumerate() {
        let count = referenced[index];
        match node.let_binding {
            Some(ordinal) => {
                if index == root {
                    return Err(tripwire(format!(
                        "the root node is marked as the value of `let` #{ordinal}; the root \
                         is the body's own call and is never `let`-bound"
                    )));
                }
                if ordinal != bound_lets {
                    return Err(tripwire(format!(
                        "node {index} is marked as `let` #{ordinal} but the next binding in \
                         evaluation order is #{bound_lets}; `let`-bound temporaries must \
                         appear in binding order with consecutive ordinals"
                    )));
                }
                bound_lets += 1;
                // A value temporary is read 0..n times; every read is a copy
                // of the ONE local its ONE `Call` wrote.
            }
            None => {
                let expected = usize::from(index != root);
                if count != expected {
                    return Err(refuse(format!(
                        "its Rust-call chain node {index} is read {count} time(s); a chain \
                         reads every ordinary non-root node exactly once and the root never \
                         (only a `let`-bound value temporary may be read 0 or many times)"
                    )));
                }
            }
        }
    }
    // ── binding order over BODY nodes (review finding N3, 2026-09-16) ─────
    //
    // The ordinal rule above pins `let`-vs-`let` order only. A strict `let`
    // spine evaluates every binding BEFORE the body, so an ordinary node
    // (`let_binding: None`) that sits below the last `let`-bound node is
    // admissible only as part of some binding's VALUE: transitively read,
    // through ordinary nodes, by a `let`-bound node of greater index (`let y
    // := inc (dbl x)`: `dbl` is read by `inc`). Otherwise it is a body call
    // evaluated before a binding — `[h x, dbl x (let #0), sub2 N0 N1]` for
    // `let y := dbl x; sub2 (h x) y` — the same calls in a different order,
    // and every other rule here passes it (`h` read once, ordinal 0, root
    // read never, node count 3 == 3) while the kernel would agree with
    // either. The walk cannot mint that order (every binding is read before
    // the residual), so this is the seal's own defence in depth; a chain
    // that trips it is a planner defect, never something the user wrote.
    //
    // A `let`-bound operand stops the descent: it is its own binding's value,
    // and by the reference rule every node in THAT value has a smaller index
    // than it, so it covers them itself.
    if let Some(last_let) = nodes.iter().rposition(|node| node.let_binding.is_some()) {
        let mut in_a_value = vec![false; nodes.len()];
        for node in nodes.iter().filter(|node| node.let_binding.is_some()) {
            let mut pending: Vec<usize> = node
                .args
                .iter()
                .filter_map(|arg| match arg {
                    RustCallArg::Node(k) => Some(*k),
                    _ => None,
                })
                .collect();
            while let Some(k) = pending.pop() {
                if nodes[k].let_binding.is_some() || in_a_value[k] {
                    continue;
                }
                in_a_value[k] = true;
                pending.extend(nodes[k].args.iter().filter_map(|arg| match arg {
                    RustCallArg::Node(j) => Some(*j),
                    _ => None,
                }));
            }
        }
        if let Some(index) =
            (0..last_let).find(|&index| nodes[index].let_binding.is_none() && !in_a_value[index])
        {
            let ordinal = nodes[last_let].let_binding.unwrap_or_default();
            return Err(tripwire(format!(
                "node {index} is an ordinary body call placed before node {last_let}, the \
                 value of `let` #{ordinal}, and is not part of any binding's value; a strict \
                 `let` spine evaluates every binding before the body, so the chain is not in \
                 binding order"
            )));
        }
    }
    // ── the unfold rail ────────────────────────────────────────────────────
    //
    // Side B (`reflect_rust_call::render_node`) renders a shared node once
    // PER USE, so the term the kernel decides over is the chain unfolded to
    // a tree; its size is `1 + Σ unfold[args]` at each node. `control_27`
    // half_13 measures the kernel at this cap.
    //
    // Why a SEPARATE rail is needed at all, and what it costs (measured
    // 2026-09-16, debug build, `render_node` memoized so reflection itself is
    // linear): while every non-root node was read exactly once, the chain WAS
    // the term side B reflects, and `nodes.len() <= COMPOSED_MAX_OPS` bounded
    // it. Sharing severs the two — a chain of `n` nodes each reading its
    // predecessor twice is `n` calls and `2^n - 1` applications, so at
    // `n = 32` it passes the node-count rail, the depth rail and every check
    // above and then costs the compiler its memory instead of producing a
    // refusal. The whole of side B (recognize, reflect, kernel-check the
    // minted definition, `is_def_eq` against the `let` chain) is LINEAR in
    // this weight at ~0.5 µs per unfolded application: weight 2^12 = 4,095 in
    // 3 ms, 2^14 in 8 ms, 2^16 in 33 ms, 2^18 in 123 ms, 2^20 in 500 ms;
    // 2^32 was out of memory before any such cap existed. The operative cap
    // here is the kernel envelope this lane is measured at
    // (`named_calls::MAX_NODES`, 4,096), which is well inside that curve.
    //
    // Saturating on purpose: the weight of a 64-node doubling chain does not
    // fit a `usize`, and a wrapped sum reading as small would ADMIT the very
    // chain this refuses. The order invariant above (a node reads only
    // EARLIER nodes) is what makes a single forward pass exact.
    let mut unfold = vec![0usize; nodes.len()];
    for (index, node) in nodes.iter().enumerate() {
        let mut size = 1usize;
        for arg in &node.args {
            if let RustCallArg::Node(k) = arg {
                size = size.saturating_add(unfold[*k]);
            }
        }
        unfold[index] = size;
    }
    let unfold_cap = crate::named_calls::MAX_NODES;
    if unfold[root] > unfold_cap {
        return Err(EmitRefusal::LetSpine {
            name: name.to_owned(),
            reason: format!(
                "its reflected side B unfolds every shared `let` temporary once per use, \
                 into {} applications, past the {unfold_cap}-node kernel envelope this lane \
                 is measured at (control_27 half_13).\n\
                 options:\n\
                 - split the chain across sibling `def`s and compose them at the call \
                   site;\n\
                 - or re-read the temporaries fewer times per `def`",
                unfold[root]
            ),
            defect: false,
        });
    }
    // ── the once-evaluation cross-check against the KERNEL-STORED body ─────
    if bound_lets > 0 {
        let Some((env, declaration)) = source else {
            return Err(tripwire(
                "a `let`-bearing chain was sealed without its source declaration, so its \
                 node count cannot be cross-checked against the kernel-stored body"
                    .to_owned(),
            ));
        };
        let Some(stored) = env.get_const(declaration).and_then(|constant| constant.value.as_ref())
        else {
            return Err(tripwire(
                "a `let`-bearing chain was sealed for a declaration whose kernel-stored body \
                 cannot be read back"
                    .to_owned(),
            ));
        };
        let Some(occurrences) = count_callee_spines(stored, callees) else {
            return Err(EmitRefusal::LetSpine {
                name: name.to_owned(),
                reason: "its kernel-stored body is too large for the once-evaluation \
                         cross-check's explicit-stack budget. options: split the definition \
                         into smaller `def`s and compose them at the call site"
                    .to_owned(),
                defect: false,
            });
        };
        if occurrences != nodes.len() {
            return Err(tripwire(format!(
                "the plan mints {} Rust-call node(s) but the kernel-stored body of `{name}` \
                 applies a Rust callee {occurrences} time(s); the spine walk and the \
                 declaration disagree about how many calls the emitted body must make, and \
                 the kernel would agree with EITHER (zeta identifies them)",
                nodes.len()
            )));
        }
    }
    let root_result = &callees[nodes[root].callee].result;
    if root_result != signature.result().rust() {
        return Err(refuse(format!(
            "its Rust-call chain's root callee `{}` returns `{root_result:?}` but the \
             declaration's result carries at `{:?}`",
            callees[nodes[root].callee].clean_name,
            signature.result().rust()
        )));
    }
    Ok(())
}

/// **§6f landing 2 — the CONSTANT body.** `fun x0 … x_{n-1} => <numeral>` at an
/// unsigned machine width, for any `n` INCLUDING ZERO: the whole peeled body is
/// an in-range carrier numeral in either measured spelling.
///
/// It reuses [`numeral_leaf`] and [`in_range_numeral`] — the exact readings the
/// arithmetic OPERAND leaves already go through — rather than restating them,
/// because the numeral is one vocabulary item in two positions, which is
/// precisely why the table gave it one row with two side-A routes rather than
/// two rows (`table`'s landing-2 note).
///
/// `Ok(None)` = not a numeral body, so the caller goes on to the op spines and
/// the boundary refusals. `Err` = it IS a numeral but does not fit the result
/// carrier's width, so the refusal names that exact boundary instead of
/// reporting the generic "outside the fragment".
///
/// The ARITY is not an input, and that is the point: `AdmissibleBody::
/// ConstantUint` erases it (probe_e3), so binding it here as well would create
/// the second place the erasure could be papered over. It is bound once, on
/// side B, in [`admit_lowering`].
fn recognise_constant_body(
    name: &str,
    cursor: &Expr,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    // The constant fragment exists at the unsigned machine widths only. `Nat`
    // is a MEASURED absence, not an oversight: side A kernel-checks and
    // `Domain::Nat` mints side B, but side B's READER has no whole-body bignum
    // constant arm, and giving it one widens the E6 kernel-import direction
    // (`landing2_selection_probes::l2_p4`, and the demand ledger's entry).
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let Some(reading) = numeral_leaf(cursor, &signature.result().clean().name()) else {
        return Ok(None);
    };
    match in_range_numeral(name, reading, width)? {
        ArithOperand::Const(value) => Ok(Some(CleanOriginShape::ConstantUint { value })),
        // `in_range_numeral` maps a `NatReading` and cannot report a parameter;
        // refusing rather than `unreachable!()` keeps a future edit to it from
        // becoming a panic in the emitter's own plan path.
        ArithOperand::Param(index) => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "INTERNAL: reading its constant body as a numeral produced parameter \
                 {index}. The numeral reader and the constant recognition have drifted \
                 apart; nothing may be emitted on that. Please report it."
            ),
        }),
    }
}

/// Trust (WS5.20, `STANDALONE.p18_literal_out_of_range`): the STANDALONE lane's
/// constant-body reading. Identical to [`recognise_constant_body`] except that
/// a numeral outside `0..2^width` is reduced modulo `2^width` — which is what
/// Lean's `OfNat` instance for `UInt{width}` computes (`(300 : UInt8)` IS 44) —
/// instead of refused.
///
/// That is NOT a silent reduction: the standalone gate reflects the EMITTED
/// in-range literal (`UInt{width}.ofNat r`) and the Clean kernel must decide it
/// definitionally equal to the untouched source numeral at the exact carrier,
/// so a wrong residue is refused there. The MIR lane keeps
/// [`recognise_constant_body`]'s refusal unchanged (it has no such kernel check
/// over the emitted literal). A numeral that does not fit `u64` (the numeral
/// reader's own bound) stays refused.
fn recognise_standalone_constant_body(
    name: &str,
    cursor: &Expr,
    signature: &CarrierSignature,
) -> Result<Option<(CleanOriginShape, bool)>, EmitRefusal> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let Some(reading) = numeral_leaf(cursor, &signature.result().clean().name()) else {
        return Ok(None);
    };
    match reading {
        NatReading::Fits(value) => {
            let residue = value % (1u128 << width);
            Ok(Some((CleanOriginShape::ConstantUint { value: residue }, residue != value)))
        }
        NatReading::Oversized => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its numeral does not fit u64, the numeral reader's bound, so this lane does \
                 not compute its residue modulo 2^{width}; restate the literal in range \
                 0..2^{width}"
            ),
        }),
    }
}

/// The v7/D3 refusal for a NULLARY body that is not a numeral — landing 1's
/// nullary text, narrowed to what landing 2 left refused.
fn nullary_non_constant_reason() -> String {
    format!(
        "it is a nullary `def` whose body is not a numeral. §6f landing 2 measured and \
         admitted exactly one nullary shape — a constant at an unsigned machine width \
         (`def six : UInt64 := 6`), whose kernel verdict is \
         `landing2_selection_probes::l2_p2` — and every other reading this lane has is \
         stated over PARAMETERS: a projection needs a parameter to project, and the \
         wrapping-op, select and recursion readings need operands under binders. Admitting \
         a nullary body into those readings without measuring it first is how an emitter \
         acquires a shape nobody checked.\n\
         options:\n\
         - if the value is a numeral, write it as one (`def six : UInt64 := 6`) — that \
           shape is emittable at u8/u16/u32/u64;\n\
         - if it is a closed computation, give it the parameters it computes over and call \
           it with them, which puts it inside the measured arithmetic fragment (up to \
           {COMPOSED_MAX_OPS} wrapping `+`/`-`/`*` nodes);\n\
         - cite it from a contract instead of calling it — proof position needs no emitted \
           body and has no shape restriction;\n\
         - or add the row: a nullary shape needs a kernel measurement first \
           (fast-lane-first), then its MIR realization, then its reflection — see \
           `docs/design/2026-08-04-two-language-compiler-architecture.md` §6f."
    )
}

/// Whether the peeled body is an application headed by the named constant.
fn spine_head_is(cursor: &Expr, constant: &str) -> bool {
    let head = spine_head(cursor);
    matches!(head.kind(), ExprKind::Const(n, _) if name_eq_str(n, constant))
}

/// The r5 shape: `UInt64.ofNat (Nat.rec … (UInt64.toNat (bvar _)))` — a
/// recursion computed at `Nat` under a machine-width wrapper. Detected only
/// to NAME the e2 boundary in the refusal; recognition itself stays refused.
fn is_u64_wrapped_nat_recursor(cursor: &Expr) -> bool {
    let (head, args) = uncurry(cursor);
    let of_nat = matches!(head.kind(), ExprKind::Const(n, _)
        if name_ends_with_of_nat(n));
    if !of_nat || args.len() != 1 {
        return false;
    }
    spine_head_is(args[0], "Nat.rec")
}

/// Recognise the structural single-step `Nat` recursion (side A): the exact
/// island equation-form output measured by `recursion_boundary_probes` r3 —
///
/// ```text
/// @Nat.rec.{1} (fun _ => Nat) b_A s_A (bvar 0)      (under ONE lambda)
/// ```
///
/// `Ok(None)` when the body is not a `Nat.rec` spine at all (the caller goes
/// on to the named boundary detections and the generic refusal);
/// `Err(NotEmittable)` when it IS one but falls outside the fragment for a
/// specific, user-fixable reason (multi-parameter, non-Nat signature, an
/// unmappable case value) — so the refusal names the exact boundary.
///
/// The case values are read into the CLOSED `RecBodyExpr` vocabulary by
/// [`read_case_value`]. Side A's step binders map `bvar ih → Rec`,
/// `bvar k → Pred`, `Nat.succ (bvar k) → Decreasing` — the emitted body
/// computes `k` as `pred(n)`, and `n` is `succ k` under the case
/// substitution. `rec_arg` is `Pred` by construction of the class; the plan
/// re-checks it and the KERNEL re-decides it at the gate (probe s4).
fn recognise_structural_nat_rec(
    name: &str,
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Ok(None);
    };
    if !name_eq2(head_name, "Nat", "rec") {
        return Ok(None);
    }
    // From here on the body IS a recursor spine: every failure names its
    // boundary rather than falling through to the generic text.
    if head_levels.as_slice() != [Level::succ(Level::zero())] {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its recursor eliminates outside `Type 0`, which has no value \
                     carrier"
                .to_owned(),
        });
    }
    check_structural_nat_signature(name, signature)?;
    if arity != 1 {
        // Unreachable after the signature check (arity is re-derived from the
        // same signature), kept for the seam's own honesty.
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "structural recursion is emittable at one parameter only".to_owned(),
        });
    }
    let [motive, b_a, s_a, scrutinee] = args[..] else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its `Nat.rec` application carries {} argument(s) where the \
                 motive/base/step/scrutinee form carries 4 — a partially applied \
                 recursor is outside the fragment",
                args.len()
            ),
        });
    };
    let is_nat_const = is_nat_const_expr;
    let ExprKind::Lam(_, motive_param, motive_body) = strip_mdata(motive).kind() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its recursor motive is not a constant-family lambda".to_owned(),
        });
    };
    if !is_nat_const(motive_param) || !is_nat_const(motive_body) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its recursor motive is not `fun _ => Nat`; dependent motives have \
                     no single value carrier"
                .to_owned(),
        });
    }
    if !matches!(strip_mdata(scrutinee).kind(), &ExprKind::BVar(0)) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its recursor does not scrutinise the parameter itself; recursion \
                     over a computed scrutinee is outside the structural fragment"
                .to_owned(),
        });
    }

    // The zero case: no binders in scope beyond the (unused) outer parameter.
    let base = read_case_value(name, b_a, CaseBinders::Zero)?;
    // The succ case: `fun (k : Nat) (ih : Nat) => …`.
    let step_cursor = strip_mdata(s_a);
    let ExprKind::Lam(_, k_ty, step_inner) = step_cursor.kind() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its succ case is not in binder form".to_owned(),
        });
    };
    let step_inner = strip_mdata(step_inner);
    let ExprKind::Lam(_, ih_ty, step_body) = step_inner.kind() else {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its succ case does not bind the recursive result".to_owned(),
        });
    };
    if !is_nat_const(k_ty) || !is_nat_const(ih_ty) {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: "its succ case binders are not at `Nat`".to_owned(),
        });
    }
    let step = read_case_value(name, step_body, CaseBinders::Succ)?;

    Ok(Some(CleanOriginShape::StructuralNatRec { base, step, rec_arg: RecBodyExpr::Pred }))
}

// ───────────────────────────────────────────────────────────────────────────
// R2 — reading side A's WELL-FOUNDED spine
// ───────────────────────────────────────────────────────────────────────────

/// Recognise a well-founded `Nat` recursion of any arity with a ONE-PARAMETER
/// measure (side A): the
/// island's own WF lowering, in BOTH spellings the record carries.
///
/// # THE SPELLING, AND WHY THIS TAKES THE UNPEELED BODY
///
/// The measured island output is a `WellFounded.fix` spine, and the record
/// disagrees with itself about whether it is eta-expanded:
///
/// ```text
/// ETA-EXPANDED  (r2_wf_equation_probes w1, and gate.rs's own parse):
///   fun (n : Nat) => @WellFounded.fix.{1,1} Nat (fun _ => Nat) r hwf F (bvar 0)
/// ETA-CONTRACTED (the §6e MEASUREMENT NOTE's recorded refutation):
///   @WellFounded.fix.{1,1} Nat (fun _ => Nat) r hwf F
/// ```
///
/// Both are accepted here, and accepting both costs nothing: eta is
/// definitional in this kernel (measured — the contracted body kernel-checks
/// at `Nat -> Nat` and is defeq to the expanded one), and the F-layer
/// comparison reads only `F`, which is argument 4 either way. A parser written
/// against one spelling reads NOTHING when handed the other, which is exactly
/// the defect the MEASUREMENT NOTE records; this function is therefore given
/// the body BEFORE `recognise_clean_shape`'s lambda peel, which the contracted
/// form cannot survive.
///
/// **SETTLED 2026-08-22 (`r2_session_probes` p1): the record's disagreement is
/// resolved in favour of the CONTRACTED form.** Every body the real elaborator
/// produces has ZERO outer lambdas and FIVE spine arguments — measured for
/// `countdownSum` and for every guard and predecessor variant this crate has
/// put through `CleanIslandSession::check_all`. The eta-EXPANDED arm is
/// therefore reachable only from a hand-built term (w1 is one), and is kept
/// only because eta is definitional here and the arm costs nothing.
///
/// # THE OTHER SPELLING GAP, and what it cost
///
/// Getting the spine right was necessary and not sufficient. Three checks
/// BELOW — the guard proposition, its decidability instance and the self-call's
/// predecessor — were written against raw kernel spellings (`Nat.lt`,
/// `Nat.decLt`, `Nat.sub`) that the elaborator does not emit for any source
/// program, so this recognizer refused every well-founded definition a user
/// could write while its own crate suite stayed green. The suite was green
/// about the KERNEL; `r2_wf_equation_probes` builds its side A by hand. Each of
/// the three now reads the surface tree too, with the mediating instance pinned
/// by name (`instLTNat`, `instDecidableNatLt`, `instHSubNat`) — the boundary is
/// unchanged, only its spelling. Write elaborator claims in
/// `tests/r2_session_probes.rs`, whose side A comes from the session the
/// compiler actually drives.
///
/// `r` and `hwf` are read past without inspection, deliberately. They never
/// enter the F comparison, and w1 measured all three witness spellings and the
/// eta-expanded relation mutually defeq — so a structural requirement here
/// would refuse spellings the kernel cannot tell apart, while adding nothing:
/// if side A's guard really did denote something else, the gate's defeq is
/// what refuses.
///
/// `Ok(None)` when the body is not a `WellFounded.fix` spine at all (the
/// caller falls through to the ordinary chain); `Err(NotEmittable)` when it IS
/// one but falls outside the fragment — so the refusal names the exact
/// boundary instead of the generic fragment text.
fn recognise_wf_nat_rec(
    name: &str,
    body: &Expr,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    let refuse = |detail: &str| EmitRefusal::NotEmittable {
        name: name.to_owned(),
        reason: wf_boundary_reason(detail),
    };

    // Peel EVERY lambda, then uncurry. Five arguments under none is the
    // eta-contracted spelling (arity 1); `5 + N` under `N` is the expanded one
    // at arity N, and it is only a spine when the trailing arguments are the
    // parameters we just peeled — see the argument contract below.
    let mut peeled_lambdas = 0usize;
    let mut cursor = strip_mdata(body);
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        peeled_lambdas += 1;
        cursor = strip_mdata(inner);
    }
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Ok(None);
    };
    if !name_eq2(head_name, "WellFounded", "fix") {
        return Ok(None);
    }
    // From here the body IS a fix spine: every failure names its boundary.
    if head_levels.len() != 2 {
        return Err(refuse(&format!(
            "its `WellFounded.fix` carries {} universe parameter(s) where the value-level \
             instantiation carries 2",
            head_levels.len()
        )));
    }
    // THE ARGUMENT CONTRACT. `α C r hwf F` then one argument per parameter:
    // the MAJOR premise (the measure) first, then the threaded parameters in
    // SOURCE order. Under `fun p_0 … p_{N-1} =>`, source parameter `i` is
    // `BVar(N - 1 - i)`, so the measure index is read straight off argument 5
    // and the rest must be exactly the remaining parameters, in order.
    // Measured — `r7` q1: `addAcc` gives `arg[5] = #1, arg[6] = #0` (measure at
    // source 0) and `addAcc2` gives `arg[5] = #0, arg[6] = #1` (measure at
    // source 1).
    let (f_a, arity, measure_index) = if peeled_lambdas == 0 && args.len() == 5 {
        // The eta-contracted spelling, arity 1 — `countdownSum`'s, measured.
        (args[4], 1, 0)
    } else if peeled_lambdas >= 1 && args.len() == 5 + peeled_lambdas {
        let arity = peeled_lambdas;
        let source_of = |argument: &Expr| match strip_mdata(argument).kind() {
            &ExprKind::BVar(index) => usize::try_from(index)
                .ok()
                .filter(|index| *index < arity)
                .map(|index| arity - 1 - index),
            _ => None,
        };
        let Some(measure_index) = source_of(args[5]) else {
            return Err(refuse(
                "its fix is applied to something other than the definition's own parameter, so \
                 the recursion is over a computed argument",
            ));
        };
        let expected: Vec<usize> = (0..arity).filter(|index| *index != measure_index).collect();
        let threaded: Option<Vec<usize>> = args[6..].iter().map(|a| source_of(a)).collect();
        if threaded.as_deref() != Some(expected.as_slice()) {
            return Err(refuse(&format!(
                "its fix passes its remaining arguments in an order this lane does not read: the \
                 emittable well-founded fragment threads the non-measure parameters through the \
                 recursion in SOURCE order (parameter(s) {expected:?} after the measure, \
                 parameter {measure_index}), because that is the order the emitted body's \
                 self-call passes its operands in. Restate the definition so the recursion \
                 carries its parameters unpermuted, or keep it for proof position"
            )));
        }
        (args[4], arity, measure_index)
    } else if peeled_lambdas >= 1
        && args.len() == WfLowering::OnMeasureValue.spine_arguments(peeled_lambdas)
    {
        // PHASE 3 — the SUM-MEASURE lowering.
        //
        // R3c READ it and refused; **R3d (2026-08-27) PLANS it.** The
        // arithmetic is what separates the two lowerings (`N + 5` vs `N + 7` at
        // the same peel depth, never equal), so the classification is a
        // decision, and the phase-3 reader either recognises every component or
        // says which one refused.
        //
        // Its refusals are `Err`, not `Ok(None)`: the same door phase 2's
        // fragment refusals already use, so the inductive-projection fallback
        // still gets its turn on a function that happens to DENOTE a
        // projection.
        return recognise_wf_sum_measure_rec(name, body, signature).map(Some);
    } else {
        return Err(refuse(&format!(
            "its `WellFounded.fix` spine carries {} argument(s) under {peeled_lambdas} binder(s), \
             where the eta-expanded form at arity N carries 5 + N under N, the eta-contracted \
             form carries 5 under 0, and the sum-measure form carries 7 + N under N",
            args.len()
        )));
    };
    let f_a = strip_mdata(f_a);
    // The functional must be CLOSED, in both spellings and for the same
    // reason the gate gives: the F-layer comparison is a judgment about `F`
    // alone, so an `F` that mentions the definition's own parameter is not
    // something it is defined over. Checking it here as well as at the gate
    // keeps the plan from shaping MIR for a declaration the gate will refuse.
    if f_a.has_loose_bvars_quick() {
        return Err(refuse(
            "its functional mentions a variable bound outside itself, which the F-layer \
             comparison is not defined over",
        ));
    }

    // The signature is checked BEFORE the functional is read, so a non-`Nat`
    // declaration gets the signature refusal rather than a confusing
    // binder-shape one. It must also AGREE with the spine: a declaration whose
    // type says one arity and whose body recurses at another is not something
    // this lane has a reading for.
    check_wf_nat_signature(name, signature)?;
    if signature.arity() != arity {
        return Err(refuse(&format!(
            "its signature takes {} parameter(s) while its `WellFounded.fix` spine recurses over \
             {arity}",
            signature.arity()
        )));
    }

    // α = Nat, C = fun _ => Nat -> … -> Nat. Both are read, because both shape
    // the CARRIER the emitted body computes at — unlike `r`/`hwf`, which do not.
    if !is_nat_const_expr(args[0]) {
        return Err(refuse("its fix eliminates over a type other than `Nat`"));
    }
    let ExprKind::Lam(_, motive_param, motive_body) = strip_mdata(args[1]).kind() else {
        return Err(refuse("its fix motive is not a constant-family lambda"));
    };
    if !is_nat_const_expr(motive_param) || !is_nat_arrow_tower(motive_body, arity - 1) {
        return Err(refuse(&format!(
            "its fix motive is not `fun _ => {}`; a motive that DEPENDS on the recursion's own \
             argument has no single value carrier, and one at a type other than `Nat` has no \
             bignum realization",
            nat_arrow_tower_label(arity - 1)
        )));
    }

    // F = fun (x : Nat) (rec : (y : Nat) → r y x → Nat^(N-1) → Nat)
    //        (threaded : Nat)^(N-1) => dite … .
    let ExprKind::Lam(_, x_ty, after_x) = f_a.kind() else {
        return Err(refuse("its functional is not a lambda over the recursion's argument"));
    };
    if !is_nat_const_expr(x_ty) {
        return Err(refuse("its functional's argument binder is not at `Nat`"));
    }
    let ExprKind::Lam(_, _rec_ty, after_rec) = strip_mdata(after_x).kind() else {
        return Err(refuse("its functional does not bind a recursive slot"));
    };
    // One binder per THREADED parameter, each at `Nat`. Exactly that many: the
    // whole de Bruijn layout below is computed from `arity`, so a telescope
    // that disagreed with the spine would be read at the wrong indices.
    let mut functional_body = strip_mdata(after_rec);
    for threaded in 0..arity - 1 {
        let ExprKind::Lam(_, ty, inner) = functional_body.kind() else {
            return Err(refuse(&format!(
                "its functional binds {} threaded parameter(s) where its `WellFounded.fix` spine \
                 threads {}",
                threaded,
                arity - 1
            )));
        };
        if !is_nat_const_expr(ty) {
            return Err(refuse("one of its functional's threaded binders is not at `Nat`"));
        }
        functional_body = strip_mdata(inner);
    }

    // The guard. MEASURED (`r2_session_probes` p1), the elaborator's own:
    //   @dite.{1} Nat (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 _) x)
    //                 (instDecidableNatLt 0 x) then else
    // and side B's raw rendering `@dite.{1} Nat (Nat.lt 0 x) (Nat.decLt 0 x)`.
    // Both are read; see `is_zero_lt_param` and the instance note below.
    // THE LAYOUT every index below is computed from. At the functional BODY the
    // measure is `bvar arity` (arity 1 → `bvar 1`, R2's constant); under a
    // branch binder it is one further out. `r7` q1 measured `bvar 2` at arity 2.
    let layout = WfLayout { arity, measure_index, lowering: WfLowering::OnParameter };
    let (dite_head, dite_args) = uncurry(functional_body);
    let ExprKind::Const(dite_name, _) = dite_head.kind() else {
        return Err(refuse("its functional's body is not a decidable case split"));
    };
    if !name_eq1(dite_name, "dite") || dite_args.len() != 5 {
        return Err(refuse(
            "its functional's body is not the `dite (0 < n)` guard this lane emits a \
             bignum zero test for — a well-founded body guarded some other way has no \
             emitted contract here",
        ));
    }
    if !is_nat_const_expr(dite_args[0]) {
        return Err(refuse("its guard's result type is not `Nat`"));
    }
    // `0 < x` with `x = bvar 1` under [x, rec], in either measured spelling
    // (see [`is_zero_lt_param`] — the surface `LT.lt`/`instLTNat` tree is what
    // the elaborator emits; the raw `Nat.lt` one is what side B renders).
    if !is_zero_lt_param(dite_args[1], layout.measure_at_body()) {
        return Err(refuse(&format!(
            "{}. The emitted body's zero test decides exactly `0 < n` on the recursion's \
             own measure parameter, and no other guard has a measured emission",
            wf_guard_hint(dite_args[1], layout.measure_at_body())
        )));
    }
    // The decidability instance is read by NAME, the `recognise_arith_tree`
    // precedent: a different instance may denote a different decision
    // procedure, and the emitted `Nat::is_zero` realises this one. TWO names
    // are prelude names for that one procedure — SPELLING-GAP FIX, measured
    // 2026-08-22 (`r2_session_probes` p1/p3): this position is filled by
    // INSTANCE RESOLUTION, which no source text controls, and resolution always
    // mints `instDecidableNatLt`, never the `Nat.decLt` this reader demanded.
    // Pinning both is not "any instance": `instDecidableNatLt` is a REDUCIBLE
    // `Declaration::Definition` whose value is literally `Expr::const_
    // ("Nat.decLt")` (`first-party/clean` `env/order_lemmas_succ.rs:561`), so
    // the two names denote ONE decision procedure — the one
    // `trust_bignum::Nat::is_zero` realises. Any third name still refuses.
    let (dec_head, dec_args) = uncurry(strip_mdata(dite_args[2]));
    let dec_name_ok = matches!(dec_head.kind(), ExprKind::Const(n, levels)
        if levels.is_empty()
            && (name_eq2(n, "Nat", "decLt")
                || name_eq1(n, "instDecidableNatLt")));
    let dec_ok = dec_name_ok
        && dec_args.len() == 2
        && read_wf_numeral(strip_mdata(dec_args[0])) == Some(NatReading::Fits(0))
        && matches!(strip_mdata(dec_args[1]).kind(),
            &ExprKind::BVar(index) if index == layout.measure_at_body());
    if !dec_ok {
        return Err(refuse(&format!(
            // `render_spine_head` returns its own backticks (or unbackticked
            // prose for a non-constant head), so this slot must NOT add a
            // second pair — measured 2026-08-22, it used to print
            // ``Nat.decLe``. The sibling catch-all at the end of
            // `read_wf_value` gets this right; this site did not.
            "its guard's decidability instance is {}, not the prelude's `0 < n` decision \
             (`instDecidableNatLt 0 n`, equivalently `Nat.decLt 0 n`) applied to the \
             recursion's own parameter; only that instance is in the measured emittable \
             fragment, because the emitted `trust_bignum::Nat::is_zero` realises exactly \
             its decision",
            render_spine_head(dite_args[2])
        )));
    }

    // The two branches, each a lambda over its (unread) hypothesis.
    let ExprKind::Lam(_, _, then_body) = strip_mdata(dite_args[3]).kind() else {
        return Err(refuse("its guard's positive branch is not in binder form"));
    };
    let ExprKind::Lam(_, _, else_body) = strip_mdata(dite_args[4]).kind() else {
        return Err(refuse("its guard's negative branch is not in binder form"));
    };

    // THE NONZERO BRANCH, and with it the self-call arguments.
    let mut rec_args: Option<Vec<RecBodyExpr>> = None;
    let nonzero_value = read_wf_value(name, then_body, WfSite::Nonzero, layout, &mut rec_args)?;
    let Some(rec_args) = rec_args else {
        return Err(refuse(
            "its functional never uses its recursive slot, so there is no recursion for \
             this lane to gate — a non-recursive body belongs to the whole-term lane",
        ));
    };
    // THE ZERO BRANCH.
    let mut no_rec: Option<Vec<RecBodyExpr>> = None;
    let zero_value = read_wf_value(name, else_body, WfSite::Zero, layout, &mut no_rec)?;

    Ok(Some(CleanOriginShape::WellFoundedNatRec {
        zero_value,
        nonzero_value,
        rec_args,
        measure_index,
        lowering: WfLowering::OnParameter,
    }))
}

/// **R3d — the PHASE-3 planner arm.** Recognise a well-founded `Nat` recursion
/// in `first-party/clean`'s SUM-MEASURE lowering: the measure names several
/// parameters, so the fix runs on the measure's VALUE and the parameters ride
/// in the motive.
///
/// # Why this is a separate function from [`recognise_wf_nat_rec`]'s phase-2 path
///
/// They agree about the `dite` and about the branch VALUES — the same
/// [`read_wf_value`] reads both, at a [`WfLayout`] that carries the lowering —
/// and they disagree about everything around it: the spine, the motive, the
/// telescope, where the guard may sit, and which self-call arguments are
/// values. Merging them would mean one function whose every step branches on
/// the lowering, which is the shape a reader silently reads one lowering at the
/// other's layout in.
///
/// # THE ONE THING PHASE 3 CHANGES ABOUT THE GUARD
///
/// Phase 2's guard is on the recursion variable, which IS a parameter, so the
/// reader knows which parameter to expect before it looks. Phase 3's recursion
/// variable is the measure's VALUE and is not a parameter at all, so the
/// guarded parameter is DISCOVERED: the reader asks
/// [`is_zero_lt_param`] — the same spelling reader, raw and surface — once per
/// parameter and takes the one that answers. Exactly one can, because the
/// candidates are distinct de Bruijn indices; if none does, the guard is
/// refused with [`wf_guard_hint`]'s own diagnosis plus the phase-3 half of the
/// fix.
///
/// Everything the anatomy reader checks — the motive, the seed and its proof,
/// the telescope, the `rec` slot's type, the hypothesis binder, and that every
/// use of the slot is a full `arity + 3`-argument call whose major premise is
/// the measure at the enclosing parameters — has already been decided by
/// [`read_wf_sum_measure_anatomy`] before this function reads a value. That is
/// deliberate: this arm's own reading is confined to what the EMITTED body must
/// realise (a zero test on one parameter, two branch values and one self-call's
/// source arguments), and the plumbing is decided by the reader that was
/// written for it.
fn recognise_wf_sum_measure_rec(
    name: &str,
    body: &Expr,
    signature: &CarrierSignature,
) -> Result<CleanOriginShape, EmitRefusal> {
    let refuse = |detail: &str| EmitRefusal::NotEmittable {
        name: name.to_owned(),
        reason: wf_boundary_reason(detail),
    };
    let anatomy = read_wf_sum_measure_anatomy(body).map_err(|detail| {
        refuse(&format!(
            "it is headed by a `WellFounded.fix` carrying the SUM-MEASURE lowering's argument \
             count, but {detail}"
        ))
    })?;
    let arity = anatomy.arity();
    let lowering = WfLowering::OnMeasureValue;

    // The signature is checked BEFORE the functional is read, the same order
    // phase 2 uses and for the same reason: a non-`Nat` declaration gets the
    // signature refusal rather than a confusing binder-shape one.
    check_wf_nat_signature(name, signature)?;
    if signature.arity() != arity {
        return Err(refuse(&format!(
            "its signature takes {} parameter(s) while its sum-measure `WellFounded.fix` spine \
             recurses over {arity}",
            signature.arity()
        )));
    }

    // ONE self-call, and it must sit directly under the guard's own hypothesis
    // binder. Both are re-decided by `read_wf_value` below (which refuses a
    // second call and gives the recursive slot a reading only in the nonzero
    // arm); stating them here first is what lets the refusal name the count the
    // anatomy measured instead of reporting a value it could not read.
    if anatomy.calls().len() != 1 {
        return Err(refuse(&format!(
            "its functional uses the recursive slot {} time(s); the emittable well-founded \
             fragment is exactly one self-call per body (the gate's borrow pairs side B's call \
             sites with side A's one at a time, so a second call has no measured pairing)",
            anatomy.calls().len()
        )));
    }
    if anatomy.calls()[0].depth() != 1 {
        return Err(refuse(&format!(
            "its one self-call sits under {} binder(s) below the functional's body where the \
             emitted body puts it under exactly one — the guard's own hypothesis binder. A call \
             under any other binder is reached by the emitted body along a path this lane has no \
             contract for",
            anatomy.calls()[0].depth()
        )));
    }

    // The functional's telescope was counted by the anatomy reader; peel it
    // again here rather than carrying an index across, so this arm reads the
    // `dite` out of a term it opened itself.
    let mut functional_body = strip_mdata(anatomy.functional());
    for _ in 0..lowering.functional_binders(arity) {
        let ExprKind::Lam(_, _, inner) = functional_body.kind() else {
            return Err(refuse(
                "its functional's telescope is shorter than its own sum-measure spine says, so \
                 the guard would be read at the wrong binder depth",
            ));
        };
        functional_body = strip_mdata(inner);
    }

    // The guard, in the same `dite` contract phase 2 reads.
    let (dite_head, dite_args) = uncurry(functional_body);
    let ExprKind::Const(dite_name, _) = dite_head.kind() else {
        return Err(refuse("its functional's body is not a decidable case split"));
    };
    if !name_eq1(dite_name, "dite") || dite_args.len() != 5 {
        return Err(refuse(
            "its functional's body is not the `dite (0 < p)` guard this lane emits a bignum zero \
             test for — a well-founded body guarded some other way has no emitted contract here",
        ));
    }
    if !is_nat_const_expr(dite_args[0]) {
        return Err(refuse("its guard's result type is not `Nat`"));
    }

    // WHICH PARAMETER THE GUARD SITS ON — discovered, never assumed. Each
    // candidate is a distinct de Bruijn index, so at most one can answer.
    let candidate = |index: usize| WfLayout { arity, measure_index: index, lowering };
    let Some(measure_index) = (0..arity)
        .find(|index| is_zero_lt_param(dite_args[1], candidate(*index).measure_at_body()))
    else {
        return Err(refuse(&format!(
            "{}. On the SUM-MEASURE lowering (WF phase 3) the recursion variable is the \
             MEASURE'S VALUE and is not a parameter at all, so the emitted body's zero test \
             decides `0 < p` on one of the definition's own {arity} parameter(s) — the guard \
             must be a literal `<` against `0` on one of those",
            wf_guard_hint(dite_args[1], candidate(0).measure_at_body())
        )));
    };
    let layout = candidate(measure_index);

    // The decidability instance, by NAME, exactly as phase 2 reads it: a
    // different instance may denote a different decision procedure, and the
    // emitted `trust_bignum::Nat::is_zero` realises this one.
    let (dec_head, dec_args) = uncurry(strip_mdata(dite_args[2]));
    let dec_name_ok = matches!(dec_head.kind(), ExprKind::Const(n, levels)
        if levels.is_empty()
            && (name_eq2(n, "Nat", "decLt")
                || name_eq1(n, "instDecidableNatLt")));
    let dec_ok = dec_name_ok
        && dec_args.len() == 2
        && read_wf_numeral(strip_mdata(dec_args[0])) == Some(NatReading::Fits(0))
        && matches!(strip_mdata(dec_args[1]).kind(),
            &ExprKind::BVar(index) if index == layout.measure_at_body());
    if !dec_ok {
        return Err(refuse(&format!(
            "its guard's decidability instance is {}, not the prelude's `0 < p` decision \
             (`instDecidableNatLt 0 p`, equivalently `Nat.decLt 0 p`) applied to the parameter \
             its own guard tests; only that instance is in the measured emittable fragment, \
             because the emitted `trust_bignum::Nat::is_zero` realises exactly its decision",
            render_spine_head(dite_args[2])
        )));
    }

    let ExprKind::Lam(_, _, then_body) = strip_mdata(dite_args[3]).kind() else {
        return Err(refuse("its guard's positive branch is not in binder form"));
    };
    let ExprKind::Lam(_, _, else_body) = strip_mdata(dite_args[4]).kind() else {
        return Err(refuse("its guard's negative branch is not in binder form"));
    };

    let mut rec_args: Option<Vec<RecBodyExpr>> = None;
    let nonzero_value = read_wf_value(name, then_body, WfSite::Nonzero, layout, &mut rec_args)?;
    let Some(rec_args) = rec_args else {
        return Err(refuse(
            "its functional never uses its recursive slot in the branch the zero test selects \
             for a NONZERO parameter, so there is no recursion for this lane to gate",
        ));
    };
    let mut no_rec: Option<Vec<RecBodyExpr>> = None;
    let zero_value = read_wf_value(name, else_body, WfSite::Zero, layout, &mut no_rec)?;

    Ok(CleanOriginShape::WellFoundedNatRec {
        zero_value,
        nonzero_value,
        rec_args,
        measure_index,
        lowering,
    })
}

/// The de Bruijn layout of ONE well-founded functional, derived from its arity
/// and its measure position.
///
/// The reader's half of `reflect::RecCall` — deliberately its own type in its
/// own crate half, because a reader that imported the producer's layout would
/// be agreeing with side B by construction instead of reading side A. The two
/// are held together by the KERNEL (the gate's defeq), not by a shared struct,
/// and `r7`'s controls are what measure that they agree.
/// **R3d: the layout is a function of the LOWERING as well as the arity.**
///
/// Phase 2's functional binds `x, rec, threaded…`; phase 3's binds
/// `n, rec, p⃗, hm`. Every index below moves, and the two telescopes have
/// different LENGTHS, so a reader that used one set of numbers on the other
/// lowering would read parameters where the hypothesis is. Both spellings are
/// measured — phase 2 by `r7` q1, phase 3 by `gcd_phase3_probes` p2, which
/// reads the elaborated `gcdB` binder by binder.
#[derive(Clone, Copy)]
struct WfLayout {
    arity: usize,
    measure_index: usize,
    lowering: WfLowering,
}

impl WfLayout {
    /// The GUARDED parameter's index at the functional BODY.
    ///
    /// Phase 2: `bvar arity` — under `x, rec, threaded…` the measure is the
    /// outermost binder (`bvar 1` at arity 1, R2's constant).
    /// Phase 3: `bvar (arity - measure_index)` — under `n, rec, p⃗, hm` the
    /// guarded parameter is one of the `p⃗`, and `hm` sits inside them.
    /// Measured on `gcdB`: arity 2, guard on source 1, `bvar 1`.
    fn measure_at_body(self) -> u32 {
        let index = match self.lowering {
            WfLowering::OnParameter => self.arity,
            WfLowering::OnMeasureValue => self.arity.saturating_sub(self.measure_index),
        };
        u32::try_from(index).unwrap_or(u32::MAX)
    }

    /// The guarded parameter's index under a BRANCH binder, one further out.
    fn measure_at_branch(self) -> u32 {
        self.measure_at_body().saturating_add(1)
    }

    /// The recursive slot's index under a branch binder.
    ///
    /// Phase 2: `bvar arity`. Phase 3: `bvar (arity + 2)` — measured on `gcdB`,
    /// whose self-call head is `#4` at arity 2.
    fn rec_at_branch(self) -> u32 {
        let index = match self.lowering {
            WfLowering::OnParameter => self.arity,
            WfLowering::OnMeasureValue => self.arity + 2,
        };
        u32::try_from(index).unwrap_or(u32::MAX)
    }

    /// The course-of-values HYPOTHESIS `hm`'s index under a branch binder.
    ///
    /// Phase 3 only: `hm` is the functional's innermost binder, so it is
    /// `bvar 0` at the body and `bvar 1` under the branch. It has no VALUE
    /// reading — it is a proof — and is listed so the reader can say so by
    /// name instead of reporting an unknown index.
    fn hypothesis_at_branch(self) -> Option<u32> {
        matches!(self.lowering, WfLowering::OnMeasureValue).then_some(1)
    }

    /// How many arguments a self-call carries.
    fn rec_call_arity(self) -> usize {
        self.lowering.rec_call_arity(self.arity)
    }

    /// Where the self-call's SOURCE arguments start.
    ///
    /// Phase 2: `rec <decreasing> <proof> <threaded…>` — the decreasing
    /// argument is alone at 0 and the threaded ones start at 2.
    /// Phase 3: `rec <major> <hm> <p⃗> <proof>` — ALL of them start at 2, in
    /// source order, because phase 3's recursion variable is not a parameter
    /// and none of the arguments is privileged.
    const fn source_argument_start(self) -> usize {
        2
    }

    /// The 0-based SOURCE parameter indices threaded beside the measure, in
    /// source order.
    fn other_indices(self) -> impl Iterator<Item = usize> {
        (0..self.arity).filter(move |index| *index != self.measure_index)
    }

    /// Which SOURCE parameter a de Bruijn index under a branch binder names, or
    /// `None` when it is not a parameter at all.
    fn source_of_branch_bvar(self, index: u32) -> Option<usize> {
        if index == self.measure_at_branch() {
            return Some(self.measure_index);
        }
        let index = usize::try_from(index).ok()?;
        match self.lowering {
            WfLowering::OnParameter => {
                if index == 0 || index >= self.arity {
                    return None;
                }
                // Threaded binders occupy 1 ..= arity-1, innermost = last in
                // source order. `r7` q1 measured `#1` naming the sole threaded
                // parameter of both `addAcc` (source 1) and `addAcc2`
                // (source 0).
                self.other_indices().nth(self.arity - 1 - index)
            }
            // Phase 3 binds every parameter, in source order, at
            // `2 ..= arity + 1` under a branch binder — `bvar 0` is the branch
            // hypothesis and `bvar 1` is `hm`. Measured on `gcdB`: `a` at
            // `#3`, `b` at `#2`.
            WfLowering::OnMeasureValue => {
                (2..=self.arity + 1).contains(&index).then(|| self.arity + 1 - index)
            }
        }
    }
}

/// Whether `expr` is `Nat` behind exactly `arrows` non-dependent `Nat` arrows.
///
/// The motive shape a well-founded recursion of arity N carries: `fun _ => Nat`
/// at arity 1, `fun _ => Nat -> Nat` at arity 2 (`r7` q1 measured exactly that
/// for `addAcc`, `dbl` and `addAcc2`). Non-dependence is not a separate check
/// and does not need to be: a tower of `Nat` constants mentions no variable at
/// all, so a motive that DID depend on the recursion's argument — phase 3's
/// `fun n => Π a b, Nat.lt (a+b) n → Nat` — fails this outright.
fn is_nat_arrow_tower(expr: &Expr, arrows: usize) -> bool {
    let mut cursor = strip_mdata(expr);
    for _ in 0..arrows {
        let ExprKind::Pi(_, domain, codomain) = cursor.kind() else {
            return false;
        };
        if !is_nat_const_expr(domain) {
            return false;
        }
        cursor = strip_mdata(codomain);
    }
    is_nat_const_expr(cursor)
}

/// How [`is_nat_arrow_tower`] spells what it wanted, for a refusal.
fn nat_arrow_tower_label(arrows: usize) -> String {
    let mut label = String::from("Nat");
    for _ in 0..arrows {
        label.insert_str(0, "Nat -> ");
    }
    label
}

/// Whether an expression is the bare constant `Nat`.
fn is_nat_const_expr(expr: &Expr) -> bool {
    matches!(strip_mdata(expr).kind(), ExprKind::Const(n, levels)
        if name_eq1(n, "Nat") && levels.is_empty())
}

// ═══════════════════════════════════════════════════════════════════════════
// PHASE 3 — the SUM-MEASURE lowering, READ (2026-08-27)
// ═══════════════════════════════════════════════════════════════════════════

/// Which of `first-party/clean`'s two well-founded lowerings a
/// `WellFounded.fix`-headed body is in.
///
/// **This is a TAG, not a reading.** `emit` and `gate` each derive it from side
/// A independently and neither consults the other's parse — the discipline
/// `parse_wf_fix_spine`'s doc states, kept literally. What is shared is the
/// name of the answer, so that a refusal in one half and a refusal in the other
/// cannot disagree about which lowering they were looking at.
///
/// The two are told apart by ARITHMETIC, not by a heuristic: at the same peel
/// depth `N` a phase-2 spine carries `N + 5` arguments and a phase-3 spine
/// carries `N + 7`, and `N + 5 = N + 7` has no solution. A body that matches
/// neither count is not classified at all.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WfLowering {
    /// **Phase 1/2** — `termination_by` names ONE parameter and the fix runs on
    /// that PARAMETER. Motive `fun _ => Nat -> … -> Nat` (constant in the
    /// recursion variable); spine `α C r hwf F` plus one argument per
    /// parameter; the functional binds `x`, `rec` and one binder per threaded
    /// parameter; a self-call carries `N + 1` arguments with the decrease proof
    /// at position 1.
    ///
    /// This is everything R2/R3a/R3b shipped, and reading it must not move.
    OnParameter,
    /// **Phase 3** — `termination_by` mentions SEVERAL parameters, so the fix
    /// runs on the measure's VALUE and the parameters ride in the motive
    /// (`first-party/clean`'s `wf_recursion::sum_measure`, landed in the pin
    /// this crate builds against). Motive `fun n => Π p⃗, Nat.lt m n → ret`,
    /// which DEPENDS on the recursion variable; spine seeded
    /// `(Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))`; the functional binds one
    /// EXTRA hypothesis binder `hm : Nat.lt m n` after the parameters; and a
    /// self-call is `rec m hm a⃗ prf`, `N + 3` arguments with the decrease proof
    /// LAST.
    OnMeasureValue,
}

impl WfLowering {
    /// How many arguments this lowering's `WellFounded.fix` spine carries at
    /// declaration arity `arity`.
    ///
    /// Phase 2: `α C r hwf F` + one per parameter. Phase 3: the same five, then
    /// the SEED `Nat.succ m`, then one per parameter, then the seed PROOF
    /// `Nat.le.refl (Nat.succ m)`.
    #[must_use]
    pub const fn spine_arguments(self, arity: usize) -> usize {
        match self {
            Self::OnParameter => arity + 5,
            Self::OnMeasureValue => arity + 7,
        }
    }

    /// How many binders this lowering's FUNCTIONAL opens before its body.
    ///
    /// Phase 2: `x`, `rec`, and one per THREADED parameter — `1 + 1 + (N - 1)`,
    /// i.e. `arity + 1`, because the recursion variable IS one of the
    /// parameters.
    ///
    /// Phase 3: `n`, `rec`, one per parameter (ALL of them — the recursion
    /// variable is the measure's value and is not a parameter at all), and
    /// `hm` — `1 + 1 + N + 1`, i.e. `arity + 3`. That extra binder is the whole
    /// shape difference at the telescope, and getting it wrong is how a reader
    /// silently reads the parameters where the hypothesis is.
    #[must_use]
    pub const fn functional_binders(self, arity: usize) -> usize {
        match self {
            Self::OnParameter => arity + 1,
            Self::OnMeasureValue => arity + 3,
        }
    }

    /// Where the recursive slot sits, as a de Bruijn index, at the functional's
    /// BODY.
    ///
    /// Phase 2's telescope is `x, rec, threaded…`, so `rec` is `arity - 1` (and
    /// 0 at arity 1 — the literal R2 shipped). Phase 3's is
    /// `n, rec, p⃗, hm`, so `rec` is `arity + 1`.
    #[must_use]
    pub fn rec_binder_depth(self, arity: usize) -> u32 {
        let arity = u32::try_from(arity).unwrap_or(u32::MAX);
        match self {
            Self::OnParameter => arity.saturating_sub(1),
            Self::OnMeasureValue => arity.saturating_add(1),
        }
    }

    /// How many arguments ONE self-call carries.
    ///
    /// Phase 2: the decreasing argument, its proof, and one per threaded
    /// parameter. Phase 3: the measure's value, the course-of-values hypothesis
    /// `hm`, one per parameter, and the decrease proof.
    #[must_use]
    pub const fn rec_call_arity(self, arity: usize) -> usize {
        match self {
            Self::OnParameter => arity + 1,
            Self::OnMeasureValue => arity + 3,
        }
    }

    /// Which of those arguments is the DECREASE PROOF — the slot the gate
    /// borrows from side A and side B may never author.
    ///
    /// Phase 2 puts it second (`rec arg prf threaded…`); phase 3 puts it LAST
    /// (`rec m hm a⃗ prf`), because `rec m hm : Π p⃗', Nat.lt m[p⃗'] m → ret`
    /// consumes the parameters before the obligation.
    #[must_use]
    pub const fn decrease_slot_position(self, arity: usize) -> usize {
        match self {
            Self::OnParameter => 1,
            Self::OnMeasureValue => arity + 2,
        }
    }
}

/// One self-call inside a PHASE-3 functional.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WfSumMeasureCall {
    depth: u32,
    major: Expr,
    arguments: Vec<Expr>,
    decrease_proof: Expr,
}

impl WfSumMeasureCall {
    /// Binders entered between the functional's BODY and this call site, so
    /// `rec` is `BVar(arity + 1 + depth)` and `hm` is `BVar(depth)` here.
    #[must_use]
    pub const fn depth(&self) -> u32 {
        self.depth
    }

    /// The MAJOR premise — the measure at the call's own enclosing parameters,
    /// which is what makes `hm` the hypothesis `rec` demands.
    #[must_use]
    pub const fn major(&self) -> &Expr {
        &self.major
    }

    /// The self-call's source arguments, in SOURCE order.
    #[must_use]
    pub fn arguments(&self) -> &[Expr] {
        &self.arguments
    }

    /// The term in the decrease slot. Read and recorded, never authored — the
    /// gate is what borrows it, and this crate never mints one.
    #[must_use]
    pub const fn decrease_proof(&self) -> &Expr {
        &self.decrease_proof
    }
}

/// What this crate reads out of a PHASE-3 `WellFounded.fix` body.
///
/// Every field is a term taken FROM side A; nothing here is constructed on side
/// A's behalf. The reader's whole job is to decide "this is the sum-measure
/// lowering and these are its parts, or it is not and here is why".
#[derive(Clone, Debug)]
pub struct WfSumMeasureAnatomy {
    arity: usize,
    measure: Expr,
    motive: Expr,
    functional: Expr,
    return_ty: Expr,
    calls: Vec<WfSumMeasureCall>,
}

impl WfSumMeasureAnatomy {
    /// The declaration's arity — the number of outer lambdas, cross-checked
    /// against the spine, the motive and the functional telescope.
    #[must_use]
    pub const fn arity(&self) -> usize {
        self.arity
    }

    /// The measure `m`, spelled as it appears in the SEED: source parameter `i`
    /// is `BVar(arity - 1 - i)`. The motive and the `hm` binder must agree with
    /// it on the nose, which is what ties the three together.
    #[must_use]
    pub const fn measure(&self) -> &Expr {
        &self.measure
    }

    /// The motive `C = fun n => Π p⃗, Nat.lt m n → ret`.
    #[must_use]
    pub const fn motive(&self) -> &Expr {
        &self.motive
    }

    /// The functional `F`.
    #[must_use]
    pub const fn functional(&self) -> &Expr {
        &self.functional
    }

    /// The motive's return type, under `n` and the parameters.
    #[must_use]
    pub const fn return_ty(&self) -> &Expr {
        &self.return_ty
    }

    /// Every self-call, in a deterministic pre-order.
    #[must_use]
    pub fn calls(&self) -> &[WfSumMeasureCall] {
        &self.calls
    }
}

/// A bounded traversal envelope for the phase-3 functional walk, the same node
/// budget the gate's own functional walks apply.
///
/// # R3d (2026-08-27): 4,096 was too small to READ the pin's own `gcd`
///
/// Measured at `first-party/clean` `4f7bdab766`: the elaborated body of
///
/// ```text
/// def gcdB (a b : Nat) : Nat :=
///   if h : 0 < b then gcdB ((a-b)+(b-a)) (a-(a-b)) else a
/// termination_by a + 2*b
/// ```
///
/// is **14,425** core nodes, of which the FUNCTIONAL is 14,283 and the single
/// self-call's DECREASE PROOF — the cascade's `Or.rec`-headed term — is
/// **14,013** on its own. Every other component together is under 300. So a
/// 4,096-node envelope refused side A on the ONE part of it side B never
/// authors and the comparison is blind to, and the refusal it produced named
/// the envelope rather than anything about the program.
///
/// The envelope is kept — an unbounded walk over a user-controlled term is work
/// proportional to the input — and moved to a number the measurement supports
/// with room for a deeper cascade. This is a RESOURCE rail, not a fragment
/// boundary: nothing about which bodies are readable changes with it, only how
/// large a decrease proof may ride along. `gcd_phase3_probes` p1 pins the
/// measured size so a future cascade that outgrows this number fails with its
/// own measurement rather than silently.
pub(crate) const SUM_MEASURE_NODE_LIMIT: usize = 262_144;

/// A bounded NESTING-DEPTH envelope for the same walks — the STACK rail, which
/// the node budget above is not and never was.
///
/// # R3e (2026-08-28): raising the node budget removed an accidental stack guard
///
/// The three walks over a user-authored side-A term — `scan_sum_measure_calls`
/// here, `gate::walk_functional` and `gate::rebuild_functional` — are DIRECT
/// Rust recursions. Every level of the term costs a Rust stack frame, and none
/// of them uses `stacker`. Before R3d the 4,096-node budget was, incidentally,
/// also their depth guard: a term cannot be deeper than it has nodes, so no
/// walk could ever recurse past 4,096 frames. R3d moved that number to 262,144
/// for a reason that had nothing to do with stacks (a 14,013-node DECREASE
/// PROOF riding inside a 14,283-node functional), and in doing so it raised the
/// worst-case descent by the same factor of 64.
///
/// That is a real defect, and it is a CRASH rather than a wrong answer:
/// `clean-kernel` guards its own descents with `stack_safe`
/// (`first-party/clean/crates/clean-kernel/src/expr/mod.rs`, a 256 KB red zone
/// and 1 MB growth increments), so a term far deeper than any Rust stack is
/// exactly the kind of term the kernel ACCEPTS and hands on. Measured below,
/// the fattest of the three walks exhausts an 8 MB stack at about **620**
/// levels — six hundred, not forty thousand — and the compiler dies with
/// `SIGSEGV` instead of refusing. A verifying compiler may decline to read a
/// term; it may not segfault on one the kernel admitted.
///
/// # Why a depth rail and not `stacker`
///
/// `stacker` is how `clean-kernel`, `clean-parser`, `clean-elab` and
/// `clean-auto` solve this, and it is the better answer where it applies. It is
/// deliberately not the answer HERE: this crate's dependency list is part of
/// its argument (see the manifest header — the set is closed and each entry is
/// justified there), and growing the stack on demand is a capability decision,
/// not a resource one. A refusal is strictly better than a crash and no worse
/// than the unbounded stack, and it is what v7/D3 asks for: say the bound, say
/// what to do about it.
///
/// # The number is DERIVED, from two measurements
///
/// It is `DESCENT_STACK_BUDGET / WIDEST_MEASURED_FRAME`, so raising it is not a
/// matter of taste — one of the two facts under it has to move first.
///
/// * **What the deepest real term costs.** Measured on the pin's own `gcdB`
///   (`gcd_phase3_probes` p1, which now records depth beside node count): the
///   functional carrying the 14,013-node cascade proof is **53 levels deep**.
///   Nodes and depth are not proportional and that term is the proof of it — a
///   14,283-node term at depth 53. The rail clears it by about 5.8x.
/// * **What one level costs.** Measured 2026-08-28 by stack-pointer delta at
///   `-Copt-level=0`: `gate::walk_functional` **2,752 B/frame**,
///   `gate::rebuild_functional` **13,552 B/frame**. The second is the binding
///   one, and it is why the rail is in the hundreds rather than the thousands:
///   the frame is wide because the rebuild holds a dozen 144-byte `Expr`
///   temporaries per arm and a debug build shares no slots between them. An
///   optimised build's frames are expected to be narrower — that has NOT been
///   measured here and the rail does not rest on it. The rail is chosen
///   against the widest configuration that was measured, because a rail chosen
///   against release would not protect the debug builds this crate is actually
///   tested and staged in.
///
/// **The durable way to raise this rail is to make the frame cheaper**, not to
/// raise the budget: at 13.5 KB a frame, the budget IS the compiler's stack.
/// Splitting `rebuild_functional`'s per-arm temporaries — or routing all three
/// walks through `stacker` and paying the dependency — buys depth honestly.
///
/// Like the node budget this is a RESOURCE rail, not a fragment boundary:
/// nothing about which bodies are READABLE changes with it.
pub(crate) const SUM_MEASURE_DEPTH_LIMIT: usize = DESCENT_STACK_BUDGET / WIDEST_MEASURED_FRAME;

/// How much stack ONE descent of these walks may consume.
///
/// Half of the 8 MB that rustc gives its compilation threads
/// (`rustc_interface`'s `STACK_SIZE`), which is the stack this lane runs on
/// inside `clean_origin_mir`. Half, not all: the walk is called several frames
/// into a MIR pass, and the pass has to survive the refusal it is handed.
pub(crate) const DESCENT_STACK_BUDGET: usize = 4 * 1024 * 1024;

/// The widest frame measured among the three walks, in the build configuration
/// that produces the widest frames.
///
/// `gate::rebuild_functional`, 13,552 B at `-Copt-level=0`, measured by
/// stack-pointer delta between consecutive descents on 2026-08-28. If this
/// number is ever re-measured, re-measure it the same way and in the same
/// configuration — a release figure here would silently multiply the rail.
pub(crate) const WIDEST_MEASURED_FRAME: usize = 13_552;

/// The v7/D3 refusal a walk emits when a term outruns [`SUM_MEASURE_DEPTH_LIMIT`].
///
/// One function so the three walks cannot drift into three different accounts
/// of the same rail, and so the refusal always carries the fix — naming a bound
/// with no next step is the defect v7/D3 names.
///
/// `subject` names whose term ran out of room, in the voice of the walk that
/// asked ("its functional", "the functional", "side B's functional").
pub(crate) fn depth_envelope_refusal(subject: &str) -> String {
    format!(
        "{subject} nests deeper than the {SUM_MEASURE_DEPTH_LIMIT}-level traversal depth this \
         lane walks. The rail is a STACK bound, not a fragment boundary: this walk is a direct \
         recursion, so one level of the term costs one Rust stack frame, and a deeper descent \
         would exhaust the compiler's stack rather than refuse. Options: (1) split the \
         definition — a helper `def` per stage keeps each functional shallow, and the call lane \
         gates each one on its own; (2) if the depth is in a `termination_by` DECREASE PROOF \
         rather than in the program, state a simpler measure: the cascade's proof grows with the \
         measure, and `gcd_phase3_probes` p1 records what the shipped one costs; (3) if this \
         term is genuinely this deep and the lane must read it, the rail is derived — it is \
         `emit::DESCENT_STACK_BUDGET / emit::WIDEST_MEASURED_FRAME`, so raise it by making the \
         walk's frame cheaper (or by routing all three walks through `stacker`, as clean-kernel \
         does), never by moving the number alone: at the measured frame width the budget already \
         IS half the compiler's stack"
    )
}

/// Whether `expr` is the bare constant `name` at no universe arguments.
fn is_bare_const(expr: &Expr, name: &str) -> bool {
    matches!(strip_mdata(expr).kind(), ExprKind::Const(n, levels)
        if name_eq_str(n, name) && levels.is_empty())
}

/// `name ARG` for a bare unary constant, or `None`.
fn read_unary_const_app<'e>(expr: &'e Expr, name: &str) -> Option<&'e Expr> {
    let ExprKind::App(function, argument) = strip_mdata(expr).kind() else {
        return None;
    };
    is_bare_const(function, name).then(|| strip_mdata(argument))
}

/// Whether `expr` is `Nat.lt <measure> (BVar bound)` in the raw spelling the
/// sum-measure lowering builds it in.
///
/// Raw only, deliberately, and unlike the GUARD: the guard is written by a USER
/// and reaches the term through instance resolution, so it has a surface
/// spelling this crate had to learn the hard way (`r2_session_probes` p1). This
/// proposition is built by `sum_measure.rs` itself out of
/// `Expr::const_("Nat.lt")`, so there is exactly one spelling to read and
/// accepting a second would be accepting a term the lowering does not produce.
fn is_raw_nat_lt_at_bound(expr: &Expr, measure: &Expr, bound: u32) -> bool {
    let ExprKind::App(f1, arg1) = strip_mdata(expr).kind() else {
        return false;
    };
    let ExprKind::App(head, arg0) = strip_mdata(f1).kind() else {
        return false;
    };
    is_bare_const(head, "Nat.lt")
        && *strip_mdata(arg0) == *measure
        && matches!(strip_mdata(arg1).kind(), &ExprKind::BVar(index) if index == bound)
}

/// **THE PHASE-3 READER.** Read a `WellFounded.fix` body in the SUM-MEASURE
/// lowering, fail-closed, or say exactly which component refused.
///
/// The shape, from `first-party/clean`'s
/// `crates/clean-elab/src/infer/wf_recursion/sum_measure.rs`:
///
/// ```text
/// C     := fun (n : Nat) => Π (p⃗), Nat.lt m n → ret
/// F     := fun (n : Nat) (rec : (k : Nat) → Nat.lt k n → C k) (p⃗)
///              (hm : Nat.lt m n) => body[ f a⃗ ↦ rec m hm a⃗ prf ]
/// value := fun (p⃗) => @WellFounded.fix.{1,v} Nat C Nat.lt hwf F
///              (Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))
/// ```
///
/// # The four identifications, and why each is CHECKED rather than assumed
///
/// * **an `n`-DEPENDENT Pi motive.** Phase 2's motive is a `Nat` arrow tower
///   and mentions no variable at all, so `is_nat_arrow_tower` rejects this one
///   outright — the phases cannot be read at each other's layout by accident.
///   The measure inside it must be the SAME term the seed carries, which is the
///   cross-check that the motive, the seed and the `hm` binder are about one
///   measure and not three.
/// * **the seed `(Nat.succ m) p⃗ (Nat.le.refl (Nat.succ m))`.** `Nat.lt m
///   (Nat.succ m)` is `Nat.le (Nat.succ m) (Nat.succ m)` by δ, which is why
///   `Nat.le.refl` is the whole seed proof. Both halves are read, and the bound
///   in the proof must be the SAME term as the seed — a `Nat.le.refl` at some
///   other bound is a different (and possibly unprovable) claim wearing the
///   right head.
/// * **the extra hypothesis binder.** `arity + 3` binders, EXACTLY: every de
///   Bruijn index below is computed from that number, so a functional whose
///   telescope disagrees with its own spine must refuse rather than be read at
///   the wrong layout. This is `peel_functional`'s rule at phase 3.
/// * **the `arity + 3`-argument `rec`.** Five at arity 2. `rec m hm` is
///   `Π p⃗', Nat.lt m[p⃗'] m → ret`, so the parameters come next and the
///   obligation LAST — the mirror image of phase 2, where the proof is second.
///
/// # What is and is not checked around `r` and `hwf`
///
/// The RELATION (`r`) is read, because it is the one place the two lowerings
/// differ in a way that is not a count: phase 2 builds an eta-expanded
/// `fun a b => Nat.lt a b` and `sum_measure.rs` cites the bare constant. The
/// WITNESS (`hwf`) is read past without inspection, for the reason phase 2
/// gives: it never enters the F-layer comparison, and w1 measured the three
/// witness spellings mutually defeq — so a structural requirement here would
/// refuse spellings the kernel cannot tell apart while adding nothing.
///
/// The call's MAJOR premise IS compared to the measure lifted into the call
/// site's own context, because that identification is cheap and it is what
/// makes `hm` the hypothesis `rec` demands.
///
/// # Errors
///
/// A human-readable detail naming the component that refused. The caller wraps
/// it in the shared [`wf_boundary_reason`] text so a phase-3 refusal is
/// recognisably the same kind of refusal as a phase-2 one.
pub fn read_wf_sum_measure_anatomy(body: &Expr) -> Result<WfSumMeasureAnatomy, String> {
    // 1. THE OUTER TELESCOPE. `fun (p⃗) => …`, one lambda per parameter.
    let mut param_tys: Vec<&Expr> = Vec::new();
    let mut cursor = strip_mdata(body);
    while let ExprKind::Lam(_, ty, inner) = cursor.kind() {
        param_tys.push(strip_mdata(ty));
        cursor = strip_mdata(inner);
    }
    let arity = param_tys.len();
    if arity == 0 {
        return Err("it abstracts no parameter at all, so the sum-measure lowering's seed has \
                    nothing to be a measure OF"
            .to_owned());
    }
    let lowering = WfLowering::OnMeasureValue;

    // 2. THE SPINE.
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return Err("its body is not an application headed by a constant".to_owned());
    };
    if !name_eq2(head_name, "WellFounded", "fix") {
        return Err(format!("its body is headed by `{head_name}`, not `WellFounded.fix`"));
    }
    if head_levels.len() != 2 {
        return Err(format!(
            "its `WellFounded.fix` carries {} universe parameter(s) where the value-level \
             instantiation carries 2",
            head_levels.len()
        ));
    }
    if args.len() != lowering.spine_arguments(arity) {
        return Err(format!(
            "its spine carries {} argument(s) under {arity} binder(s), where the sum-measure \
             lowering at arity {arity} carries {} (`α C r hwf F`, the seed `Nat.succ m`, one \
             argument per parameter, and the seed proof `Nat.le.refl (Nat.succ m)`)",
            args.len(),
            lowering.spine_arguments(arity)
        ));
    }
    let seed_index = 5;
    let params_index = 6;
    let seed_proof_index = params_index + arity;

    if !is_nat_const_expr(args[0]) {
        return Err("its fix eliminates over a type other than `Nat`; the sum-measure lowering \
                    runs the recursion on the MEASURE's value, which is a `Nat`"
            .to_owned());
    }
    // The relation is the BARE constant. Phase 2 builds an eta-expanded
    // `fun a b => Nat.lt a b`; `sum_measure.rs` cites `Nat.lt` itself, and
    // reading that difference is part of telling the phases apart.
    if !is_bare_const(args[2], "Nat.lt") {
        return Err("its fix's relation is not the bare constant `Nat.lt`, which is the only \
                    relation the sum-measure lowering runs on"
            .to_owned());
    }

    // 3. THE SEED, and its proof. `Nat.lt m (Nat.succ m)` is `Nat.le.refl` by δ,
    //    so both halves name the SAME `Nat.succ m` or the seed proves something
    //    else.
    let Some(measure) = read_unary_const_app(args[seed_index], "Nat.succ") else {
        return Err("its fix is seeded with something other than `Nat.succ <measure>`; the \
                    course-of-values encoding starts one above the measure so that the seed \
                    proof can be `Nat.le.refl`"
            .to_owned());
    };
    let measure = measure.clone();
    for (source_index, argument) in args[params_index..seed_proof_index].iter().enumerate() {
        let want = u32::try_from(arity - 1 - source_index).unwrap_or(u32::MAX);
        if !matches!(strip_mdata(argument).kind(), &ExprKind::BVar(index) if index == want) {
            return Err(format!(
                "its fix passes something other than the definition's own parameter {source_index} \
                 in that position, so the recursion is not over the arguments the emitted body \
                 would hold"
            ));
        }
    }
    let Some(seed_bound) = read_unary_const_app(args[seed_proof_index], "Nat.le.refl") else {
        return Err("its fix's accessibility seed is not `Nat.le.refl <bound>`".to_owned());
    };
    if *strip_mdata(seed_bound) != *strip_mdata(args[seed_index]) {
        return Err("its fix's seed proof is `Nat.le.refl` at a DIFFERENT bound than the seed it \
                    is supposed to justify, so it does not prove `Nat.lt m (Nat.succ m)`"
            .to_owned());
    }

    // 4. THE MOTIVE — `fun n => Π p⃗, Nat.lt m n → ret`, n-DEPENDENT.
    let motive = strip_mdata(args[1]);
    let ExprKind::Lam(_, motive_binder, motive_body) = motive.kind() else {
        return Err("its fix motive is not a lambda over the course-of-values bound".to_owned());
    };
    if !is_nat_const_expr(motive_binder) {
        return Err("its fix motive's bound is not at `Nat`".to_owned());
    }
    let mut motive_cursor = strip_mdata(motive_body);
    for source_index in 0..arity {
        let ExprKind::Pi(_, ty, inner) = motive_cursor.kind() else {
            return Err(format!(
                "its fix motive re-binds {source_index} parameter(s) where the sum-measure \
                 lowering re-binds all {arity} of them before the measure hypothesis"
            ));
        };
        if !is_nat_const_expr(ty) {
            return Err(format!(
                "its fix motive re-binds parameter {source_index} at a type other than `Nat`; \
                 this lane is stated at the bignum carrier only"
            ));
        }
        motive_cursor = strip_mdata(inner);
    }
    let ExprKind::Pi(_, hypothesis, return_ty) = motive_cursor.kind() else {
        return Err("its fix motive does not end in the measure hypothesis `Nat.lt m n → ret`; a \
                    motive with no hypothesis is phase 2's constant family, not this one"
            .to_owned());
    };
    let motive_bound = u32::try_from(arity).unwrap_or(u32::MAX);
    if !is_raw_nat_lt_at_bound(hypothesis, &measure, motive_bound) {
        return Err(
            "its fix motive's hypothesis is not `Nat.lt m n` at the SAME measure its seed \
                    carries; the motive, the seed and the functional's hypothesis binder must \
                    name one measure, or the recursion is not the one the seed starts"
                .to_owned(),
        );
    }
    let return_ty = strip_mdata(return_ty);
    if !is_nat_const_expr(return_ty) {
        return Err("its fix motive returns at a type other than `Nat`; the well-founded lane is \
                    stated at the bignum carrier only, because the reflected functional's \
                    arithmetic is `Nat`'s"
            .to_owned());
    }

    // 5. THE FUNCTIONAL TELESCOPE — `arity + 2` binders, EXACTLY.
    let functional = strip_mdata(args[4]);
    if functional.has_loose_bvars_quick() {
        return Err("its functional mentions a variable bound outside itself, which the F-layer \
                    comparison is not defined over"
            .to_owned());
    }
    let binders = lowering.functional_binders(arity);
    let mut telescope: Vec<&Expr> = Vec::new();
    let mut functional_body = functional;
    for _ in 0..binders {
        let ExprKind::Lam(_, ty, inner) = functional_body.kind() else {
            return Err(format!(
                "its functional binds {} binder(s) where the sum-measure lowering at arity \
                 {arity} binds {binders} (the course-of-values bound, the recursive slot, one \
                 per parameter, and the measure hypothesis)",
                telescope.len()
            ));
        };
        telescope.push(strip_mdata(ty));
        functional_body = strip_mdata(inner);
    }
    if !is_nat_const_expr(telescope[0]) {
        return Err("its functional's course-of-values bound is not at `Nat`".to_owned());
    }
    for (source_index, ty) in telescope[2..2 + arity].iter().enumerate() {
        if !is_nat_const_expr(ty) {
            return Err(format!(
                "its functional re-binds parameter {source_index} at a type other than `Nat`"
            ));
        }
    }
    // `rec : (k : Nat) → Nat.lt k n → C k`. Read structurally rather than by
    // equality against a rebuilt term: binder NAMES take part in `Expr`
    // equality, and this reader must not depend on what the elaborator called
    // its binders. The codomain is the un-reduced redex `C k` the lowering
    // builds; the beta-reduced spelling is accepted too, because the two are
    // the same type and neither is this crate's to prefer.
    {
        let ExprKind::Pi(_, k_ty, after_k) = telescope[1].kind() else {
            return Err("its functional does not bind a recursive slot".to_owned());
        };
        if !is_nat_const_expr(k_ty) {
            return Err(
                "its functional's recursive slot does not take a `Nat` major premise; the \
                        sum-measure lowering recurses on the measure's VALUE"
                    .to_owned(),
            );
        }
        let ExprKind::Pi(_, k_lt_n, codomain) = strip_mdata(after_k).kind() else {
            return Err("its functional's recursive slot does not demand a decrease proof, so it \
                        is not a well-founded slot at all"
                .to_owned());
        };
        let raw_lt = match strip_mdata(k_lt_n).kind() {
            ExprKind::App(f1, arg1) => match strip_mdata(f1).kind() {
                ExprKind::App(lt_head, arg0) => {
                    is_bare_const(lt_head, "Nat.lt")
                        && matches!(strip_mdata(arg0).kind(), ExprKind::BVar(0))
                        && matches!(strip_mdata(arg1).kind(), ExprKind::BVar(1))
                }
                _ => false,
            },
            _ => false,
        };
        if !raw_lt {
            return Err("its functional's recursive slot demands something other than \
                        `Nat.lt k n`"
                .to_owned());
        }
        let codomain = strip_mdata(codomain);
        let redex = matches!(codomain.kind(), ExprKind::App(function, argument)
            if *strip_mdata(function) == *motive
                && matches!(strip_mdata(argument).kind(), ExprKind::BVar(1)));
        let reduced = *codomain == strip_mdata(motive_body).instantiate(&Expr::bvar(1));
        if !(redex || reduced) {
            return Err("its functional's recursive slot returns at something other than the \
                        fix's own motive applied to the major premise"
                .to_owned());
        }
    }
    // `hm : Nat.lt m n`, at the context [n, rec, p⃗] — where `n` is
    // `BVar(arity + 1)` and source parameter `i` is `BVar(arity - 1 - i)`, the
    // SAME spelling the seed uses, which is why the measure compares on the
    // nose.
    let hm_bound = u32::try_from(arity + 1).unwrap_or(u32::MAX);
    if !is_raw_nat_lt_at_bound(telescope[arity + 2], &measure, hm_bound) {
        return Err("its functional's last binder is not the measure hypothesis `Nat.lt m n` at \
                    the measure its seed carries; without it the recursive slot has no argument \
                    to be applied to and this is not the sum-measure lowering"
            .to_owned());
    }

    // 6. THE SELF-CALLS.
    let mut calls = Vec::new();
    let mut visited = 0usize;
    scan_sum_measure_calls(functional_body, arity, &measure, 0, 0, &mut visited, &mut calls)?;

    Ok(WfSumMeasureAnatomy {
        arity,
        measure,
        motive: motive.clone(),
        functional: functional.clone(),
        return_ty: return_ty.clone(),
        calls,
    })
}

/// Walk a phase-3 functional body and record every `rec m hm a⃗ prf` call site.
///
/// `depth` counts binders entered since the functional's BODY, so `rec` is
/// `BVar(arity + 1 + depth)` and `hm` is `BVar(depth)` at the current node.
/// Every use of the recursive slot must be a full `arity + 3`-argument
/// application: a slot the walk cannot see is a slot the gate's borrow cannot
/// fill and the closure audit cannot cover.
///
/// `descent` is NOT `depth`: it counts this walk's own Rust stack frames, which
/// every sub-term costs, while `depth` counts only BINDERS and an application
/// spine adds none. The two rails are independent and both are checked — see
/// [`SUM_MEASURE_DEPTH_LIMIT`] for why a node budget is not a stack guard.
fn scan_sum_measure_calls(
    expr: &Expr,
    arity: usize,
    measure: &Expr,
    depth: u32,
    descent: usize,
    visited: &mut usize,
    calls: &mut Vec<WfSumMeasureCall>,
) -> Result<(), String> {
    *visited = visited.checked_add(1).ok_or("its functional exceeded its traversal envelope")?;
    if *visited > SUM_MEASURE_NODE_LIMIT {
        return Err(format!(
            "its functional exceeded its {SUM_MEASURE_NODE_LIMIT}-node traversal envelope"
        ));
    }
    // Checked BEFORE any recursive call below, so the frame that would have
    // overflowed is the one that refuses.
    let descent = descent.checked_add(1).ok_or_else(|| depth_envelope_refusal("its functional"))?;
    if descent > SUM_MEASURE_DEPTH_LIMIT {
        return Err(depth_envelope_refusal("its functional"));
    }
    let lowering = WfLowering::OnMeasureValue;
    let rec_index = lowering.rec_binder_depth(arity).saturating_add(depth);
    let call_arity = lowering.rec_call_arity(arity);
    let cursor = strip_mdata(expr);
    match cursor.kind() {
        &ExprKind::BVar(index) if index == rec_index => Err(format!(
            "its functional uses the recursive slot somewhere other than as a \
             {call_arity}-argument self-call `rec m hm a⃗ prf`, so a decrease slot could not be \
             located"
        )),
        ExprKind::BVar(_)
        | ExprKind::FVar(_)
        | ExprKind::Sort(_)
        | ExprKind::Const(_, _)
        | ExprKind::Lit(_) => Ok(()),
        ExprKind::App(function, argument) => {
            if matches!(spine_head(cursor).kind(), &ExprKind::BVar(index) if index == rec_index) {
                let (_head, args) = uncurry(cursor);
                if args.len() != call_arity {
                    return Err(format!(
                        "its functional applies the recursive slot to {} argument(s) where the \
                         sum-measure slot at arity {arity} takes {call_arity} (the measure's \
                         value, the course-of-values hypothesis, one per parameter, and the \
                         decrease proof)",
                        args.len()
                    ));
                }
                // `rec m hm …` — the major premise is the measure at THIS call
                // site's parameters, lifted out of the seed's context into the
                // functional's; `hm` is the functional's own hypothesis binder.
                // Both are what make `rec m hm : Π p⃗', Nat.lt m[p⃗'] m → ret`.
                let want_major = measure.lift(depth.saturating_add(1));
                if *strip_mdata(args[0]) != want_major {
                    return Err(
                        "its functional applies the recursive slot to a major premise other than \
                         the measure at the enclosing parameters, so the course-of-values \
                         hypothesis is not the one the slot demands"
                            .to_owned(),
                    );
                }
                if !matches!(strip_mdata(args[1]).kind(), &ExprKind::BVar(index) if index == depth)
                {
                    return Err(
                        "its functional does not pass its own measure hypothesis to the recursive \
                         slot, so the call is not the sum-measure lowering's"
                            .to_owned(),
                    );
                }
                let slot = lowering.decrease_slot_position(arity);
                calls.push(WfSumMeasureCall {
                    depth,
                    major: strip_mdata(args[0]).clone(),
                    arguments: args[2..slot].iter().map(|a| strip_mdata(a).clone()).collect(),
                    decrease_proof: strip_mdata(args[slot]).clone(),
                });
                for argument in args {
                    scan_sum_measure_calls(
                        argument, arity, measure, depth, descent, visited, calls,
                    )?;
                }
                return Ok(());
            }
            scan_sum_measure_calls(function, arity, measure, depth, descent, visited, calls)?;
            scan_sum_measure_calls(argument, arity, measure, depth, descent, visited, calls)
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            scan_sum_measure_calls(ty, arity, measure, depth, descent, visited, calls)?;
            scan_sum_measure_calls(
                body,
                arity,
                measure,
                depth.saturating_add(1),
                descent,
                visited,
                calls,
            )
        }
        ExprKind::Let(_, ty, value, body, _) => {
            scan_sum_measure_calls(ty, arity, measure, depth, descent, visited, calls)?;
            scan_sum_measure_calls(value, arity, measure, depth, descent, visited, calls)?;
            scan_sum_measure_calls(
                body,
                arity,
                measure,
                depth.saturating_add(1),
                descent,
                visited,
                calls,
            )
        }
        ExprKind::Proj(_, _, inner) => {
            scan_sum_measure_calls(inner, arity, measure, depth, descent, visited, calls)
        }
        _ => Err("its functional leaves the core expression fragment this lane is measured over"
            .to_owned()),
    }
}

// R3d RETIRED `sum_measure_not_yet_emittable`, the v7/D3 refusal R3c installed
// for a body this crate could READ but not EMIT. Recorded here rather than
// deleted silently, because its text is what a reader searching for "does not
// yet EMIT it" would find and it named two blockers by module:
//
//   * *"the guard sits on a SOURCE parameter rather than on the fix's own
//     recursion variable"* — TRUE, and it turned out not to be a blocker at
//     all: the emitted body's zero test is a test on a parameter's LOCAL either
//     way, so a guard on a source parameter is exactly what the materializer
//     already emits. What was missing was a reader that DISCOVERED which
//     parameter (`recognise_wf_sum_measure_rec`) rather than assuming the
//     measure's.
//   * *"the side-B producer renders only the phase-2 telescope"* — TRUE, and it
//     was the real one. `reflect_wf::reflect_wf_functional` now renders both,
//     and the measure plumbing it cannot author is borrowed at the gate beside
//     the decrease proof it already could not.

/// Whether an expression is the guard `0 < n` on the recursion's own
/// parameter, in either MEASURED spelling, as it stands under the functional's
/// two binders (`n = bvar 1`).
///
/// # The two spellings, and why the surface one had to be added
///
/// **SPELLING-GAP FIX, measured 2026-08-22 from
/// `CleanIslandSession::check_all` (`r2_session_probes` p1/p2).** The reader
/// was written against the RAW spelling only:
///
/// ```text
/// Nat.lt <0> (bvar 1)                                   -- 2 args
/// ```
///
/// which is what `reflect_wf` renders on side B and what the hand-built
/// `r2_wf_equation_probes` terms use — but it is NOT what the elaborator emits
/// for the fixture's own `if h : 0 < n`. The real guard keeps the surface
/// class projection:
///
/// ```text
/// @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (bvar 1)
/// ```
///
/// four arguments, head `LT.lt`. Reading only the raw form made this lane
/// unreachable from every program a user can write (the
/// `2026-08-22-r2-wf-call-lane-unreachable` audit). Both are read now, and the
/// boundary is exactly as wide as before: the surface form is admitted ONLY
/// through the prelude's own `instLTNat`, because
/// `LT.lt Nat instLTNat a b` whnf-reduces to `Nat.lt a b`
/// (`first-party/clean` `tc/tests2/ordering_projection_value.rs:194`) and a
/// different instance is a different `<`, which the emitted
/// `trust_bignum::Nat::is_zero` does not realise. The `recognise_arith_tree`
/// precedent, applied to an ordering class.
///
/// `n > 0` (`@GT.gt.{0} Nat instLTNat (bvar 1) 0`) is measured and NOT read
/// here: its operands are the other way round, side B renders `Nat.lt` and
/// nothing has measured the gate's defeq on the stuck `dite` through `GT.gt`.
/// It fails closed, and [`wf_guard_hint`] names the one-word fix.
fn is_zero_lt_param(expr: &Expr, measure: u32) -> bool {
    let (head, args) = uncurry(strip_mdata(expr));
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return false;
    };
    let is_zero_then_param = |zero: &Expr, param: &Expr| {
        read_wf_numeral(strip_mdata(zero)) == Some(NatReading::Fits(0))
            && matches!(strip_mdata(param).kind(), &ExprKind::BVar(index) if index == measure)
    };
    // (a) the RAW spelling — side B's rendering, and a source `Nat.lt 0 n`.
    if name_eq2(head_name, "Nat", "lt") && args.len() == 2 {
        return is_zero_then_param(args[0], args[1]);
    }
    // (b) the SURFACE spelling the elaborator actually mints, with the
    //     ordering instance pinned by name.
    if name_eq2(head_name, "LT", "lt") && args.len() == 4 {
        if head_levels.len() != 1 || !head_levels[0].is_zero() {
            return false;
        }
        if !is_nat_const_expr(args[0]) {
            return false;
        }
        let prelude_instance = matches!(strip_mdata(args[1]).kind(), ExprKind::Const(n, levels)
            if name_eq1(n, "instLTNat") && levels.is_empty());
        return prelude_instance && is_zero_then_param(args[2], args[3]);
    }
    false
}

/// The v7/D3 fix hint for a well-founded body whose guard is not `0 < n` on
/// its own parameter — TRUE of the program in front of it.
///
/// The old text told the user to write `if h : 0 < n`, which for the canonical
/// fixture is what they had already written; that was the audit's first
/// diagnostic defect. Each measured near-miss now gets its own sentence.
fn wf_guard_hint(guard: &Expr, measure: u32) -> String {
    let (head, args) = uncurry(strip_mdata(guard));
    let head_name = match head.kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => {
            return format!(
                "its guard is {}, not a comparison on the recursion's own parameter; \
                 restate it as `if h : 0 < n`",
                render_head(other)
            );
        }
    };
    match head_name.as_str() {
        "GT.gt" | "GE.ge" => format!(
            "its guard is spelled `n {} 0`; write the comparison the other way round \
             (`if h : 0 < n`), which is the direction the emitted zero test decides",
            if head_name == "GT.gt" { ">" } else { ">=" }
        ),
        "LT.lt" | "Nat.lt" => {
            // The right shape, the wrong operands: say WHICH.
            let (zero, param) = match (head_name.as_str(), args.len()) {
                ("Nat.lt", 2) => (args[0], args[1]),
                ("LT.lt", 4) => (args[2], args[3]),
                _ => {
                    return "its guard is a `<` this lane does not read; spell it \
                            `if h : 0 < n` on the recursion's own parameter"
                        .to_owned();
                }
            };
            if !matches!(strip_mdata(param).kind(), &ExprKind::BVar(index) if index == measure) {
                return "its guard compares against something other than the parameter the \
                        recursion DESCENDS on, so the emitted zero test would decide a \
                        different proposition than the one the measure decreases in; write \
                        `if h : 0 < n` on the `termination_by` parameter itself"
                    .to_owned();
            }
            if read_wf_numeral(strip_mdata(zero)) != Some(NatReading::Fits(0)) {
                // Distinguish "the bound is not 0" from "the bound is spelled
                // in a way this lane does not read" — claiming the first about
                // the second is a refusal that is false of the program.
                if let Some(spelling) = describe_unread_nat_spelling(strip_mdata(zero)) {
                    return format!("its guard's bound {spelling}");
                }
                return "its guard tests the parameter against a bound other than `0`; the \
                        emitted body's test is a ZERO test, so only `0 < n` has an emission \
                        — restate the definition with a `0 < n` guard and fold the bound \
                        into the branch values"
                    .to_owned();
            }
            "its guard is a `<` at `Nat` through an ordering instance other than the \
             prelude's `instLTNat`; a different instance is a different `<`, which the \
             emitted `trust_bignum::Nat::is_zero` does not realise"
                .to_owned()
        }
        // `Nat.le (Nat.succ 0) n` is `0 < n` DELTA-UNFOLDED. TWO source
        // spellings reach here and the kernel term cannot tell them apart, so
        // the hint must not presuppose either (measured 2026-08-22):
        //
        //   * an explicit `@dite`, in which position the elaborator unfolds
        //     `Nat.lt` however the proposition was spelled — this is the
        //     mechanism, and the audit's "de Bruijn shift" attribution is
        //     wrong; the index is `bvar 1` either way;
        //   * `if h : Nat.le (Nat.succ 0) n` (or `1 <= n`) written out, which
        //     contains no `@dite` at all.
        //
        // The arm used to assert the first unconditionally AND prescribe "the
        // `if h :` form" — telling a user who had already written `if h :`
        // that their program was something it was not. Naming both routes is
        // the only statement true of both; the actionable half (write a
        // literal `<` against `0`) is unchanged and correct for both.
        "Nat.le"
            if args.len() == 2
                && matches!(uncurry(strip_mdata(args[0])), (h, a)
                    if matches!(h.kind(), ExprKind::Const(n, _)
                        if name_eq2(n, "Nat", "succ"))
                        && a.len() == 1
                        && read_wf_numeral(strip_mdata(a[0])) == Some(NatReading::Fits(0))) =>
        {
            "its guard reached the compiler as `Nat.le (Nat.succ 0) n`, which is `0 < n` \
             with `Nat.lt` already unfolded — either because the guard was written in \
             that unfolded form (`Nat.le (Nat.succ 0) n`, `1 <= n`), or because it was \
             written inside an explicit `@dite`, where the elaborator unfolds `Nat.lt` \
             whatever proposition you spell. Write it as a literal `<` against `0` in \
             the `if h :` form — `if h : 0 < n` — which is the one spelling that reaches \
             the compiler as the `<` the emitted zero test is stated against, and needs \
             no explicit instance"
                .to_owned()
        }
        "LE.le" | "Nat.le" => "its guard is a `<=`, not `0 < n`; the emitted body's test is \
                               a ZERO test, so restate the guard as `if h : 0 < n`"
            .to_owned(),
        // Two equality shapes with OPPOSITE branch polarity, so they get two
        // hints. `n == 0` selects the ZERO case in its `then` arm, which the
        // emitted body's arms are the other way round from; `n ≠ 0` already
        // matches the emitted polarity and needs only the guard rewritten.
        "Eq" => "its guard is an equality test rather than the order comparison `0 < n`; an \
                 equality-against-zero guard also selects its arms in the OPPOSITE order \
                 from the emitted zero test, so restate it as `if h : 0 < n` and swap the \
                 two branches"
            .to_owned(),
        "Ne" | "Not" => "its guard is a disequality test (`n ≠ 0`) rather than `0 < n`; the \
                         emitted body's test is stated as an order comparison, so restate \
                         the guard as `if h : 0 < n` — the branches already stand the right \
                         way round"
            .to_owned(),
        other => format!(
            "its guard is headed by `{other}` rather than `0 < n` on the recursion's own \
             parameter; restate it as `if h : 0 < n`"
        ),
    }
}

/// Name a `Nat` numeral spelling this lane recognises AS a numeral but cannot
/// READ, so that a refusal about it does not assert the wrong value.
///
/// [`read_wf_numeral`] returns `None` for two different situations: "this is
/// not a numeral at all" and "this is a numeral in a spelling outside the read
/// set". The two callers that compare a numeral against a REQUIRED value — the
/// guard's bound (`0`) and the decrement (`1`) — turn that single `None` into
/// "some value other than the required one", which is FALSE of a program whose
/// value is right and whose spelling is merely unread.
///
/// Measured 2026-08-22, both from real island sources:
///
/// * `if h : @OfNat.ofNat Nat 0 (instOfNatNat 0) < n` refused with "tests the
///   parameter against a bound other than `0`" — the bound IS `0`. Writing the
///   numeral's instance explicitly makes the elaborator wrap it AGAIN, so the
///   guard arrives as `OfNat.ofNat Nat (OfNat.ofNat Nat 0 _) _`, two `OfNat`
///   deep, and [`read_nat_numeral`] reads exactly one.
/// * `f (n - @OfNat.ofNat Nat 1 (instOfNatNat 1))` refused with "subtracts
///   something other than the literal 1" — it subtracts `1`.
///
/// This is deliberately a DIAGNOSTIC, not a widening: the fragment boundary
/// does not move, the term still refuses, and the reader still reads exactly
/// one `OfNat`. Only the stated reason changes, from a false claim about the
/// value to a true claim about the spelling, with the fix attached (v7/D3).
fn describe_unread_nat_spelling(expr: &Expr) -> Option<&'static str> {
    let cursor = strip_mdata(expr);
    if read_wf_numeral(cursor).is_some() {
        // It WAS read. The caller's complaint is about the value, and the
        // caller's own message is the true one.
        return None;
    }
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if name_eq2(head_name, "OfNat", "ofNat")
        && args.len() == 3
        && matches!(strip_mdata(args[0]).kind(), ExprKind::Const(n, _)
            if name_eq1(n, "Nat"))
        && nat_literal(strip_mdata(args[1])).is_none()
    {
        return Some(
            "is a `Nat` numeral whose literal slot is itself an `OfNat.ofNat` \
             application. That nesting is what the elaborator produces when a numeral is \
             written with its instance given explicitly (`@OfNat.ofNat Nat 0 \
             (instOfNatNat 0)`), and this lane reads a numeral exactly one `OfNat` deep — \
             so the value may well be the required one and the compiler cannot confirm it \
             here. Write the numeral plainly (`0`, `1`) and let the elaborator insert the \
             instance",
        );
    }
    // A `Nat.succ` tower is only THIS class if it is a tower over a numeral
    // that ran past the cap. `Nat.succ n` over a parameter is an ordinary
    // out-of-fragment term and must keep the caller's message.
    if name_eq2(head_name, "Nat", "succ") && args.len() == 1 {
        let mut probe = strip_mdata(args[0]);
        let mut depth: u32 = 1;
        loop {
            let (h, a) = uncurry(probe);
            let is_succ = matches!(h.kind(), ExprKind::Const(n, _)
                if name_eq2(n, "Nat", "succ"));
            if !is_succ || a.len() != 1 {
                return (read_nat_numeral(probe).is_some() && depth > WF_SUCC_TOWER_LIMIT)
                    .then_some(
                        "is a `Nat` numeral built as a `Nat.succ` tower deeper than this \
                         lane unwinds, so its value is not read here rather than known to \
                         be wrong; write the numeral plainly",
                    );
            }
            depth = depth.saturating_add(1);
            probe = strip_mdata(a[0]);
        }
    }
    None
}

/// The deepest `Nat.succ` tower [`read_wf_numeral`] will unwind.
///
/// A statement of where we are, never a design (v7/D2): an elaborator writes
/// large numerals as literals, so a tower past this depth is not a spelling
/// anything produces — and an unbounded peel over a user-controlled term is
/// work proportional to the input. Past the cap the reading fails closed to
/// `None` and the caller renders the fragment refusal.
const WF_SUCC_TOWER_LIMIT: u32 = 1_024;

/// Read a `Nat` numeral on the well-founded lane: the three spellings
/// [`read_nat_numeral`] covers, PLUS a bounded `Nat.succ` tower over one of
/// them.
///
/// # Why the tower is read here and NOT on the structural lane
///
/// This is not an inconsistency between the two lanes; it is the case
/// substitution. In a structural minor premise `Nat.succ X` is overwhelmingly
/// the PARAMETER under its own case substitution (`n := succ k`), so
/// [`read_case_value`] gives it a dedicated reading and a dedicated refusal —
/// reading it as a numeral there would silently convert "the parameter" into
/// "some constant". A well-founded functional has no case substitution and no
/// case binder: its parameter is a plain binder (`bvar 2`), so `Nat.succ` at a
/// value site can only be arithmetic, and the ambiguity that justifies R1's
/// refusal does not exist.
fn read_wf_numeral(expr: &Expr) -> Option<NatReading> {
    let mut cursor = strip_mdata(expr);
    let mut tower: u64 = 0;
    loop {
        if let Some(reading) = read_nat_numeral(cursor) {
            return Some(match reading {
                NatReading::Oversized => NatReading::Oversized,
                NatReading::Fits(value) => match value.checked_add(u128::from(tower)) {
                    Some(total) => NatReading::Fits(total),
                    None => NatReading::Oversized,
                },
            });
        }
        let ExprKind::App(head, arg) = cursor.kind() else {
            return None;
        };
        let is_succ = matches!(strip_mdata(head).kind(), ExprKind::Const(n, _)
            if name_eq2(n, "Nat", "succ"));
        if !is_succ || tower >= u64::from(WF_SUCC_TOWER_LIMIT) {
            return None;
        }
        tower += 1;
        cursor = strip_mdata(arg);
    }
}

/// Which branch of the functional a value is being read from. All de Bruijn
/// indices are relative to the branch body, and BOTH branches share one
/// layout — computed from [`WfLayout`] since R3a, and at arity 1 the literals
/// R2 shipped: `x = bvar (N+1)`, `rec = bvar N`, the j-th threaded parameter
/// `= bvar (N-1-j)`, the branch hypothesis `= bvar 0`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WfSite {
    /// The negative branch — the value when the MEASURE is zero. No
    /// recursive use has a reading here.
    Zero,
    /// The positive branch — the value when the MEASURE is NONZERO. The one
    /// site where the recursive slot may be applied.
    Nonzero,
    /// Inside the self-call's ARGUMENT. Same layout; a nested self-call has no
    /// reading.
    RecArg,
}

impl WfSite {
    fn position(self) -> &'static str {
        match self {
            Self::Zero => "zero branch",
            Self::Nonzero => "nonzero branch",
            Self::RecArg => "self-call argument",
        }
    }
}

/// Read one side-A branch value into the closed [`RecBodyExpr`] vocabulary,
/// fail-closed with a boundary-naming refusal.
///
/// The admitted spellings, at R2's denotation:
///
/// * `bvar 2` — the functional's own parameter ↦ [`RecBodyExpr::Decreasing`];
/// * `rec ARG PRF` — a TWO-argument application of the recursive slot
///   (`bvar 1`) ↦ [`RecBodyExpr::Rec`], with `ARG` read at
///   [`WfSite::RecArg`] into `rec_arg`. The PROOF is read past and discarded
///   deliberately: side B never authors one, the gate BORROWS side A's, and
///   probe w7/d2 measured that two functionals differing only in the slot's
///   proof are defeq — so recording it here would put a term into the plan
///   that contributes nothing the comparison reads;
/// * `Nat.pred X`, `Nat.sub X 1`, or the surface
///   `HSub.hSub Nat Nat Nat instHSubNat X 1` where `X` is the parameter ↦
///   [`RecBodyExpr::Pred`] (w6 (b′) measured the first two defeq; the surface
///   one is what the elaborator ACTUALLY emits for `n - 1` — see
///   [`read_nat_sub`], the spelling gap that made this lane unreachable);
/// * `Nat` numerals in the three measured spellings, and `+` in the two —
///   both through the shared readers the structural lane uses, so the two
///   lanes cannot drift about what a numeral or an addition is.
///
/// The branch HYPOTHESIS (`bvar 0`) has no value reading: it is a proof, and a
/// value computed from a proof is outside every carrier.
fn read_wf_value(
    name: &str,
    expr: &Expr,
    site: WfSite,
    layout: WfLayout,
    rec_args: &mut Option<Vec<RecBodyExpr>>,
) -> Result<RecBodyExpr, EmitRefusal> {
    let cursor = strip_mdata(expr);
    let position = site.position();
    let refuse = |reason: String| EmitRefusal::NotEmittable {
        name: name.to_owned(),
        reason: wf_boundary_reason(&reason),
    };

    if let &ExprKind::BVar(index) = cursor.kind() {
        if index == layout.measure_at_branch() {
            return Ok(RecBodyExpr::Decreasing);
        }
        if index == layout.rec_at_branch() {
            return Err(refuse(format!(
                "its {position} mentions the recursive slot other than as a {}-argument \
                 self-call `f (n - 1) <proof> <threaded…>`, so the emitted body has no call \
                 to make",
                layout.rec_call_arity()
            )));
        }
        // A THREADED parameter. `Param(i)`, never `Param(measure_index)` — the
        // measure has its own spelling above, and one position with two
        // spellings would make `admit_lowering`'s structural comparison pass or
        // fail on a naming accident.
        if let Some(source_index) = layout.source_of_branch_bvar(index) {
            return Ok(RecBodyExpr::Param(source_index));
        }
        if layout.hypothesis_at_branch() == Some(index) {
            return Err(refuse(format!(
                "its {position} computes a value from the course-of-values HYPOTHESIS the \
                 sum-measure lowering threads (`hm : Nat.lt m n`), which is a proof and which \
                 no carrier represents"
            )));
        }
        return match index {
            0 => Err(refuse(format!(
                "its {position} computes a value from the guard's own PROOF, which no \
                 carrier represents"
            ))),
            _ => Err(refuse(format!(
                "its {position} references de Bruijn index {index}, outside this \
                 fragment's vocabulary"
            ))),
        };
    }

    let (head, args) = uncurry(cursor);

    // THE SELF-CALL: `rec ARG PRF THREADED…`, the recursive slot applied to
    // exactly one argument per parameter plus the decrease proof. Recognised on
    // the head being the slot's own binder, which is what makes side B's
    // rendering unable to cite the defined constant.
    if matches!(head.kind(), &ExprKind::BVar(index) if index == layout.rec_at_branch()) {
        if site != WfSite::Nonzero {
            return Err(refuse(format!(
                "its {position} applies the recursive slot, which has a reading only in the \
                 branch the zero test selects for a NONZERO parameter"
            )));
        }
        if args.len() != layout.rec_call_arity() {
            return Err(refuse(format!(
                "its {position} applies the recursive slot to {} argument(s) where the \
                 well-founded slot at arity {} takes {} ({})",
                args.len(),
                layout.arity,
                layout.rec_call_arity(),
                match layout.lowering {
                    WfLowering::OnParameter =>
                        "the decreasing argument, its decrease proof, and one per threaded \
                         parameter",
                    WfLowering::OnMeasureValue =>
                        "the measure's value, the course-of-values hypothesis, one per \
                         parameter, and the decrease proof",
                }
            )));
        }
        if rec_args.is_some() {
            return Err(refuse(format!(
                "its {position} contains more than one self-call; the emittable \
                 well-founded fragment is exactly one per body"
            )));
        }
        // Read into SOURCE order, so the vector the plan carries is indexed the
        // same way the emitted body's operands are.
        //
        // Phase 2 privileges the DECREASING argument — it is alone at position
        // 0, ahead of its proof, and the threaded ones follow. Phase 3
        // privileges none of them: the recursion variable is the measure's
        // VALUE, so all `arity` source arguments sit together at
        // `source_argument_start()`, in source order, between the
        // (major, hm) plumbing and the trailing decrease proof.
        let mut collected = vec![None; layout.arity];
        let mut nested: Option<Vec<RecBodyExpr>> = None;
        let start = layout.source_argument_start();
        match layout.lowering {
            WfLowering::OnParameter => {
                collected[layout.measure_index] =
                    Some(read_wf_value(name, args[0], WfSite::RecArg, layout, &mut nested)?);
                for (source_index, argument) in layout.other_indices().zip(&args[start..]) {
                    collected[source_index] =
                        Some(read_wf_value(name, argument, WfSite::RecArg, layout, &mut nested)?);
                }
            }
            WfLowering::OnMeasureValue => {
                for (source_index, argument) in
                    (0..layout.arity).zip(&args[start..start + layout.arity])
                {
                    collected[source_index] =
                        Some(read_wf_value(name, argument, WfSite::RecArg, layout, &mut nested)?);
                }
            }
        }
        let Some(read) = collected.into_iter().collect::<Option<Vec<_>>>() else {
            return Err(refuse(format!(
                "its {position} leaves one of the recursion's parameters without a self-call \
                 argument"
            )));
        };
        *rec_args = Some(read);
        return Ok(RecBodyExpr::Rec);
    }

    let is_param = |e: &Expr| {
        matches!(strip_mdata(e).kind(),
            &ExprKind::BVar(index) if index == layout.measure_at_branch())
    };
    if let ExprKind::Const(head_name, _) = head.kind() {
        // The predecessor's unary spelling.
        if name_eq2(head_name, "Nat", "pred") && args.len() == 1 && is_param(args[0]) {
            return Ok(RecBodyExpr::Pred);
        }
    }
    // `-`, through the shared reader — the same accounting `read_nat_add`
    // gets, and for the same reason: `-` at `Nat` has a raw spelling and a
    // surface one, and reading only the raw one is what made this lane
    // unreachable.
    //
    // R3b, 2026-08-27 — this used to read the PREDECESSOR and nothing else
    // (`is_param(minuend)` and a literal-1 subtrahend, everything else a
    // refusal). It now reads GENERAL truncated subtraction, which is what makes
    // subtractive Euclid's step map (`|a-b|` and `min a b`) expressible; the
    // predecessor is a CANONICAL SPECIAL CASE of it rather than the only case.
    //
    // Canonicalising is load-bearing, not tidiness. `Pred` and
    // `Sub(Decreasing, NatConst(1))` are the same emitted `Nat::sub(&n, &1)`,
    // so admitting both spellings would give one position two side-A trees and
    // `admit_lowering`'s direct structural equality against side B — which
    // canonicalises IDENTICALLY, in `walk_structural_arm` — would refuse a
    // correct body (or, with the two readers disagreeing about which way to
    // canonicalise, admit on a naming accident). This is the R3a
    // `Param`/`Decreasing` rule at a second position.
    //
    // WHAT STILL REFUSES A DECREASE THAT IS NOT `n - 1`: the plan's
    // `rec_args[measure_index] != Pred` belt, untouched by R3b. A decrease by
    // two, or from a constant minuend, now READS as an ordinary `Sub` and is
    // refused there instead of here — one layer later, with a message that
    // names the decreasing argument and says the other parameters are free.
    // `control_11_a_subtrahend_other_than_one_is_refused` and
    // `control_11_a_minuend_that_is_not_the_parameter_…` pin that handover.
    if let Some((minuend, subtrahend)) = read_nat_sub(name, cursor)? {
        let subtrahend_is_one =
            matches!(read_wf_numeral(strip_mdata(subtrahend)), Some(NatReading::Fits(1)));
        if is_param(minuend) && subtrahend_is_one {
            return Ok(RecBodyExpr::Pred);
        }
        // AN UNREAD SPELLING IS NOT A WRONG VALUE — v7/D3, and the one piece of
        // the old predecessor-only arm that had to survive the widening
        // verbatim. `n - @OfNat.ofNat Nat 1 (instOfNatNat 1)` subtracts exactly
        // `1`; it is refused because the numeral sits one `OfNat` deeper than
        // `read_wf_numeral` unwinds, and a refusal that said "the amount is not
        // 1" would be false OF THE PROGRAM. Diagnosed here, before the
        // descent, because the recursive call would reach the vocabulary
        // catch-all and report `OfNat.ofNat` as an unknown operation — true
        // but useless, and it drops the "your value may well be right" half.
        // `r2_session_probes` p9(c) is the row that holds this.
        //
        // A subtrahend that READS but is not `1` (`n - 2`) is deliberately NOT
        // caught here: it descends into an ordinary `Sub` and is refused by
        // `check_wf_fragment`'s decreasing-argument belt, which is the layer
        // that owns that question now.
        if let Some(spelling) = describe_unread_nat_spelling(strip_mdata(subtrahend)) {
            return Err(refuse(format!("the amount its {position} subtracts {spelling}")));
        }
        return Ok(RecBodyExpr::Sub(
            Box::new(read_wf_value(name, minuend, site, layout, rec_args)?),
            Box::new(read_wf_value(name, subtrahend, site, layout, rec_args)?),
        ));
    }

    // Numerals and `+`. `+` goes through the SHARED reader the structural lane
    // uses, so the two lanes cannot drift about what an addition is; numerals
    // go through the WF reader, which additionally unwinds a bounded `Nat.succ`
    // tower (see [`read_wf_numeral`] for why that is lane-specific and not a
    // divergence).
    if let Some(value) = read_wf_numeral(cursor) {
        return match value {
            NatReading::Fits(v) => match u64::try_from(v) {
                Ok(v) => Ok(RecBodyExpr::NatConst(v)),
                Err(_) => Err(refuse(nat_numeral_too_large_reason())),
            },
            NatReading::Oversized => Err(refuse(nat_numeral_too_large_reason())),
        };
    }
    if let Some((lhs, rhs)) = read_nat_add(name, cursor)? {
        return Ok(RecBodyExpr::Add(
            Box::new(read_wf_value(name, lhs, site, layout, rec_args)?),
            Box::new(read_wf_value(name, rhs, site, layout, rec_args)?),
        ));
    }
    // `*`, through its own shared reader — the `nat.mul` row (§R6). This is
    // what makes `fact` emittable; nothing else about the well-founded
    // fragment moved for it.
    if let Some((lhs, rhs)) = read_nat_mul(name, cursor)? {
        return Ok(RecBodyExpr::Mul(
            Box::new(read_wf_value(name, lhs, site, layout, rec_args)?),
            Box::new(read_wf_value(name, rhs, site, layout, rec_args)?),
        ));
    }
    // `%`, through its own shared reader — the `nat.mod` row (§R8). This is
    // what makes the TEXTBOOK MODULO `gcd` emittable; nothing else about the
    // well-founded fragment moved for it.
    //
    // Operands are read in ORDER and never swapped: `%` is not commutative and
    // the kernel is what decides that (`r8_nat_mod_probes` q1's `order
    // mutation` row).
    if let Some((lhs, rhs)) = read_nat_rem(name, cursor)? {
        return Ok(RecBodyExpr::Rem(
            Box::new(read_wf_value(name, lhs, site, layout, rec_args)?),
            Box::new(read_wf_value(name, rhs, site, layout, rec_args)?),
        ));
    }

    Err(refuse(format!(
        "its {position} computes ({}) outside this fragment's vocabulary (the parameters, \
         `Nat` numerals, `+`, `*`, truncated `-`, `%`, and one self-call)",
        render_spine_head(cursor)
    )))
}

/// Which binders are in scope while reading one case value of a structural
/// recursion (all de Bruijn indices are relative to the case body).
#[derive(Clone, Copy, PartialEq, Eq)]
enum CaseBinders {
    /// The zero case: only the def's own (unused) parameter binder is in
    /// scope, and referencing it would be a loose index the kernel already
    /// refused — so NO bound variable is readable.
    Zero,
    /// The succ case, under `k` (bvar 1) and `ih` (bvar 0). The def's own
    /// parameter binder sits at bvar 2 and is NOT readable: the recursor
    /// binds everything the case may use.
    Succ,
}

/// Read one side-A case value into the closed [`RecBodyExpr`] vocabulary,
/// fail-closed with a boundary-naming refusal. The admitted spellings, each
/// measured (`r1_equation_probes` s7/s8 and the e-rows):
///
/// * binders — `bvar 0` (`ih`) ↦ `Rec`, `bvar 1` (`k`) ↦ `Pred`,
///   `Nat.succ (bvar 1)` ↦ `Decreasing` (succ case only);
/// * `Nat` numerals — a kernel literal, `Nat.zero`, or the island's surface
///   `OfNat.ofNat Nat <lit> <inst>` (s7). The OfNat INSTANCE argument is
///   deliberately read loosely: a wrong-denotation instance yields a plan
///   whose emission the KERNEL gate then refuses against the actual minor
///   premise — the same the-gate-is-the-authority accounting as
///   `ty_to_domain`'s ADT-name note — whereas rejecting non-prelude
///   spellings here would only convert a caught-by-the-gate case into a
///   capability refusal;
/// * addition — `Nat.add a b`, or the surface
///   `HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat a b` with EXACTLY the
///   prelude instance (s8 measures the two spellings kernel-identical; a
///   user instance is refused by name, the `recognise_arith_tree`
///   precedent).
fn read_case_value(
    name: &str,
    expr: &Expr,
    binders: CaseBinders,
) -> Result<RecBodyExpr, EmitRefusal> {
    let cursor = strip_mdata(expr);
    let refuse = |reason: String| EmitRefusal::NotEmittable { name: name.to_owned(), reason };

    if let &ExprKind::BVar(index) = cursor.kind() {
        return match (binders, index) {
            (CaseBinders::Succ, 0) => Ok(RecBodyExpr::Rec),
            (CaseBinders::Succ, 1) => Ok(RecBodyExpr::Pred),
            _ => Err(refuse(format!(
                "a case value references de Bruijn index {index}, which is outside \
                 the structural fragment's case vocabulary"
            ))),
        };
    }

    // `Nat.succ (bvar k)` — the parameter itself, under the case substitution.
    let (head, args) = uncurry(cursor);
    if let ExprKind::Const(head_name, _) = head.kind() {
        if name_eq2(head_name, "Nat", "succ") {
            if binders == CaseBinders::Succ
                && args.len() == 1
                && matches!(strip_mdata(args[0]).kind(), &ExprKind::BVar(1))
            {
                return Ok(RecBodyExpr::Decreasing);
            }
            return Err(refuse(
                "a case value applies `Nat.succ` to something other than the case \
                 binder; successor arithmetic beyond the parameter itself is outside \
                 this fragment (restate it with `+ 1`)"
                    .to_owned(),
            ));
        }
    }

    // Numerals, in the three measured spellings.
    if let Some(value) = read_nat_numeral(cursor) {
        return match value {
            NatReading::Fits(v) => match u64::try_from(v) {
                Ok(v) => Ok(RecBodyExpr::NatConst(v)),
                Err(_) => Err(refuse(nat_numeral_too_large_reason())),
            },
            NatReading::Oversized => Err(refuse(nat_numeral_too_large_reason())),
        };
    }

    // Addition, in the two measured spellings.
    if let Some((lhs, rhs)) = read_nat_add(name, cursor)? {
        return Ok(RecBodyExpr::Add(
            Box::new(read_case_value(name, lhs, binders)?),
            Box::new(read_case_value(name, rhs, binders)?),
        ));
    }
    // Multiplication, likewise (§R6). R1 gains the node with R2 because the
    // MIR dataflow reader they SHARE now produces it: a `Mul` this reader
    // refused would be a structural body the emitter can build and the planner
    // cannot name, which is the drift `recognize_wf_nat_rec`'s delegation note
    // warns a widener about.
    if let Some((lhs, rhs)) = read_nat_mul(name, cursor)? {
        return Ok(RecBodyExpr::Mul(
            Box::new(read_case_value(name, lhs, binders)?),
            Box::new(read_case_value(name, rhs, binders)?),
        ));
    }

    Err(refuse(format!(
        "a case value computes (`{}`) outside the structural fragment's vocabulary \
         (the parameter, `Nat` numerals, `+`, `*`, and one recursive use)",
        render_head(cursor.kind())
    )))
}

/// The one refusal reason for a `Nat` numeral past `u64` in a structural
/// case: the emitted body materialises numerals through
/// `trust_bignum::Nat::from_u64`, so larger literals are a (stated) fragment
/// boundary, not a silent truncation.
fn nat_numeral_too_large_reason() -> String {
    "a case value carries a Nat numeral larger than u64; the emitted body \
     materialises numerals through `trust_bignum::Nat::from_u64`, so larger \
     literals are outside today's fragment — build the value arithmetically, or \
     keep the definition for proof position"
        .to_owned()
}

/// Read a `Nat` numeral in the measured spellings: a kernel literal,
/// `Nat.zero`, or `OfNat.ofNat.{0} Nat <lit> <inst>` (the island's surface
/// spelling; instance read loosely — see [`read_case_value`]).
fn read_nat_numeral(expr: &Expr) -> Option<NatReading> {
    let cursor = strip_mdata(expr);
    if let ExprKind::Lit(Literal::Nat(value)) = cursor.kind() {
        return Some(match value.to_u64() {
            Some(small) => NatReading::Fits(u128::from(small)),
            None => NatReading::Oversized,
        });
    }
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    if name_eq2(head_name, "Nat", "zero") && args.is_empty() {
        return Some(NatReading::Fits(0));
    }
    if name_eq2(head_name, "OfNat", "ofNat") {
        let [ty, literal, _instance] = args[..] else {
            return None;
        };
        if !matches!(strip_mdata(ty).kind(), ExprKind::Const(n, _)
            if name_eq1(n, "Nat"))
        {
            return None;
        }
        return nat_literal(literal);
    }
    None
}

/// Read a `Nat` addition spine: `Nat.add lhs rhs`, or the surface
/// `HAdd.hAdd.{0,0,0} Nat Nat Nat instHAddNat lhs rhs` with exactly the
/// prelude instance (measured kernel-identical to `Nat.add`, probe s8).
/// `Ok(None)` = not an addition; `Err` = an addition through a non-prelude
/// instance (a specific, user-fixable boundary).
fn read_nat_add<'e>(
    name: &str,
    expr: &'e Expr,
) -> Result<Option<(&'e Expr, &'e Expr)>, EmitRefusal> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Ok(None);
    };
    if name_eq2(head_name, "Nat", "add") {
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return Ok(Some((lhs, rhs)));
    }
    if name_eq2(head_name, "HAdd", "hAdd") {
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let is_nat = |t: &Expr| {
            matches!(strip_mdata(t).kind(), ExprKind::Const(n, _)
                if name_eq1(n, "Nat"))
        };
        if !(is_nat(t1) && is_nat(t2) && is_nat(t3)) {
            return Ok(None);
        }
        if !matches!(strip_mdata(instance).kind(), ExprKind::Const(n, levels)
            if name_eq1(n, "instHAddNat") && levels.is_empty())
        {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: "its `+` at `Nat` routes through an instance other than the \
                         prelude's `instHAddNat`; only the prelude instance is in the \
                         measured emittable fragment (spell the op so it elaborates \
                         through the prelude instance, or keep the definition for \
                         proof position)"
                    .to_owned(),
            });
        }
        return Ok(Some((lhs, rhs)));
    }
    Ok(None)
}

/// Read a `Nat` multiplication spine: `Nat.mul lhs rhs`, or the surface
/// `HMul.hMul.{0,0,0} Nat Nat Nat instHMulNat lhs rhs` with exactly the
/// prelude instance. `Ok(None)` = not a multiplication; `Err` = a
/// multiplication through a non-prelude instance.
///
/// The EXACT twin of [`read_nat_add`], deliberately — the same two spellings,
/// the same by-name instance pin, the same `Ok(None)`/`Err` split. The kernel
/// fact it rests on was measured BEFORE this function existed
/// (`r6_nat_mul_probes` q7): `a * b = Nat.mul a b` closes by `rfl` against the
/// real checker, and the same-shaped `a * b = Nat.add a b` is REFUSED — so the
/// identification side B relies on is the kernel's decision, not this reader's
/// assumption. Pinning `instHMulNat` by name is soundness-bearing for the
/// reason `read_nat_add` pins `instHAddNat`: a different instance may denote a
/// different `*`, and the emitted `trust_bignum::Nat::mul` realises one.
fn read_nat_mul<'e>(
    name: &str,
    expr: &'e Expr,
) -> Result<Option<(&'e Expr, &'e Expr)>, EmitRefusal> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Ok(None);
    };
    if name_eq2(head_name, "Nat", "mul") {
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return Ok(Some((lhs, rhs)));
    }
    if name_eq2(head_name, "HMul", "hMul") {
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let is_nat = |t: &Expr| {
            matches!(strip_mdata(t).kind(), ExprKind::Const(n, _)
                if name_eq1(n, "Nat"))
        };
        if !(is_nat(t1) && is_nat(t2) && is_nat(t3)) {
            return Ok(None);
        }
        if !matches!(strip_mdata(instance).kind(), ExprKind::Const(n, levels)
            if name_eq1(n, "instHMulNat") && levels.is_empty())
        {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: "its `*` at `Nat` routes through an instance other than the \
                         prelude's `instHMulNat`; only the prelude instance is in the \
                         measured emittable fragment (spell the op so it elaborates \
                         through the prelude instance, or keep the definition for \
                         proof position)"
                    .to_owned(),
            });
        }
        return Ok(Some((lhs, rhs)));
    }
    Ok(None)
}

/// Read a `Nat` remainder spine: `Nat.mod lhs rhs`, or the surface
/// `HMod.hMod.{0,0,0} Nat Nat Nat instHModNat lhs rhs` with exactly the prelude
/// instance. `Ok(None)` = not a remainder; `Err` = a remainder through a
/// non-prelude instance (a specific, user-fixable boundary).
///
/// The EXACT twin of [`read_nat_sub`], deliberately — the same two spellings,
/// the same by-name instance pin, the same `Ok(None)`/`Err` split. §R8,
/// 2026-08-28.
///
/// # What the surface spelling actually is
///
/// MEASURED, not assumed (`r8_nat_mod_probes` q3): `def m (a b : Nat) := a % b`
/// elaborates to `HMod.hMod Nat Nat Nat instHModNat #1 #0`, and the raw
/// `Nat.mod a b` to `Nat.mod #1 #0`. Reading only the raw spelling would
/// describe a reading no user program can select — the `read_nat_sub` header's
/// spelling-gap bug, which is why this reader was written from a dump rather
/// than by analogy.
///
/// # Why the instance is pinned by name
///
/// [`read_nat_add`]'s reason, and it is soundness-bearing here for a sharper
/// one: a user `HMod Nat` instance is a DIFFERENT `%`, and the emitted
/// `trust_bignum::Nat::rem` realises exactly one function — Lean's total
/// `Nat.mod`. The prelude instance is the one measured to reduce to the
/// `Nat.mod` side B renders (`q1`'s `rfl`), so accepting any other instance
/// would let a term the kernel reads one way be realised the other way.
///
/// # Errors
///
/// [`EmitRefusal::NotEmittable`] for a non-prelude `HMod` instance at `Nat`.
fn read_nat_rem<'e>(
    name: &str,
    expr: &'e Expr,
) -> Result<Option<(&'e Expr, &'e Expr)>, EmitRefusal> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Ok(None);
    };
    if name_eq2(head_name, "Nat", "mod") {
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return Ok(Some((lhs, rhs)));
    }
    if name_eq2(head_name, "HMod", "hMod") {
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        if !(is_nat_const_expr(t1) && is_nat_const_expr(t2) && is_nat_const_expr(t3)) {
            return Ok(None);
        }
        if !matches!(strip_mdata(instance).kind(), ExprKind::Const(n, levels)
            if name_eq1(n, "instHModNat") && levels.is_empty())
        {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: wf_boundary_reason(
                    "its `%` at `Nat` routes through an instance other than the prelude's \
                     `instHModNat`; only the prelude instance is in the measured emittable \
                     fragment, because it is the one that reduces to the `Nat.mod` the \
                     emitted `Nat::rem(&a, &b)` realises (spell the op so it elaborates \
                     through the prelude instance, or keep the definition for proof \
                     position)",
                ),
            });
        }
        return Ok(Some((lhs, rhs)));
    }
    Ok(None)
}

/// Read a `Nat` subtraction spine: `Nat.sub lhs rhs`, or the surface
/// `HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat lhs rhs` with exactly the
/// prelude instance. `Ok(None)` = not a subtraction; `Err` = a subtraction
/// through a non-prelude instance (a specific, user-fixable boundary).
///
/// # SPELLING-GAP FIX, measured 2026-08-22
///
/// This is the twin of [`read_nat_add`], and its absence was the audit's third
/// (and previously unrecorded) blocker: `read_wf_value` read only the RAW
/// `Nat.sub`, while the fixture's own `n - 1` elaborates to
///
/// ```text
/// @HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat (bvar 2)
///   (@OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
/// ```
///
/// so the self-call argument fell through to the catch-all — whose text lists
/// `n - 1` as in-fragment vocabulary while refusing exactly `n - 1`. The tell
/// for why it went unnoticed for so long is instructive: the SAME body's `+`
/// was read correctly, because `read_nat_add` is SHARED with R1's structural
/// lane and was derived from a real measurement (probe s8), whereas the `-`
/// reading was well-founded-lane-local and was never measured against the
/// elaborator at all.
///
/// The prelude instance is pinned by name for `read_nat_add`'s reason:
/// `instHSubNat` is `add_homogeneous_hetero_instance("instHSubNat", "HSub",
/// "HSub.mk", "Nat", "Nat.sub")` (`first-party/clean`
/// `env/algebra_hetero.rs:1298`), so the surface tree reduces to `Nat.sub lhs
/// rhs` — exactly what side B renders. A user `HSub Nat` instance is a
/// different subtraction and refuses.
///
/// # Errors
///
/// [`EmitRefusal::NotEmittable`] for a non-prelude `HSub` instance at `Nat`.
fn read_nat_sub<'e>(
    name: &str,
    expr: &'e Expr,
) -> Result<Option<(&'e Expr, &'e Expr)>, EmitRefusal> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return Ok(None);
    };
    if name_eq2(head_name, "Nat", "sub") {
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return Ok(Some((lhs, rhs)));
    }
    if name_eq2(head_name, "HSub", "hSub") {
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        if !(is_nat_const_expr(t1) && is_nat_const_expr(t2) && is_nat_const_expr(t3)) {
            return Ok(None);
        }
        if !matches!(strip_mdata(instance).kind(), ExprKind::Const(n, levels)
            if name_eq1(n, "instHSubNat") && levels.is_empty())
        {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: wf_boundary_reason(
                    "its `-` at `Nat` routes through an instance other than the prelude's \
                     `instHSubNat`; only the prelude instance is in the measured emittable \
                     fragment, because it is the one that reduces to the `Nat.sub` the \
                     emitted `Nat::sub(&n, &1)` realises (spell the op so it elaborates \
                     through the prelude instance, or keep the definition for proof \
                     position)",
                ),
            });
        }
        return Ok(Some((lhs, rhs)));
    }
    Ok(None)
}

/// The largest value an unsigned integer of `width` bits can hold. `width` is
/// already validated to be a machine width (8/16/32/64) by every caller.
fn max_uint_value(width: u32) -> u128 {
    (1u128 << width) - 1
}

/// The one refusal reason for a numeral outside `0..2^width`, shared by
/// recognition and the plan-time re-check so the two spellings cannot drift.
///
/// Emitting `v mod 2^w` would actually be defeq-faithful — `ofNat` wraps — but
/// the claim is subtle and the honest answer is to refuse: fail-closed costs
/// capability, never soundness.
fn numeral_out_of_range_reason(value: u128, width: u32) -> String {
    format!(
        "its numeral operand `{value}` does not fit the u{width} result carrier; restate \
         the literal in range 0..2^{width} — the compiler will not silently reduce it \
         modulo 2^{width}, because the emitted value must be the one the definition names"
    )
}

/// Recognise the parameter-select `ite` at the signature's result carrier, or
/// `None` (the caller renders the capability refusal).
///
/// The exact tree Clean's `elab_if` mints for `if l ⊲ r then t else e` at a
/// machine carrier — and the exact tree `admit_select_function` builds on
/// side B (the 2026-07-25 Option-B ruling made them identical by
/// construction; `probe_h_select_admits` measures rather than assumes it):
///
/// ```text
/// ite.{1} {C} (LT.lt.{0} {C} instLT{C} l r) (instDecidable{C}Lt l r) t e
///             (LE.le / instLE{C} / instDecidable{C}Le for <=;
///              Eq.{1} {C} l r    / instDecidableEq{C} for ==)
/// ```
///
/// Everything is matched EXACTLY — head levels, the carrier type argument,
/// the comparison's instance constant, and the requirement that the Decidable
/// instance is applied to the SAME two operands the proposition names (a
/// different instance argument is a different denotation, the same rule the
/// numeral spelling enforces on `instOfNat`). Both arms must be bare bound
/// parameters, and the comparison's LEFT operand too; its RIGHT operand is a
/// bare bound parameter ([`CleanOriginShape::Select`]) or — R2/C9 — a numeral
/// in either measured spelling ([`CleanOriginShape::SelectLiteral`];
/// `probe_i_select_literal_admits` and
/// `probe_i5_select_literal_le_and_propositional_eq_real_elaboration_admit`
/// are the kernel ground). Anything else fails
/// closed to `None`: notably e6 f02's `toNat` comparison spelling
/// (kernel-equal, but a DIFFERENT tree — admitting it here would put an
/// unmeasured identification on the emit lane), f03's constant arms, and a
/// literal LEFT operand (`if 10 < a`), which the reflected side B's
/// vocabulary cannot even spell.
/// **W6 (Rust-calls-Clean) — recognise a comparison of two parameters returned
/// as `Bool`.**
///
/// The kernel terms, measured 2026-09-13 at `def f (a b : UInt64) : Bool`:
///
/// ```text
/// a <  b   =>  decide (LT.lt {C} instLT{C} a b) (instDecidable{C}Lt a b)
/// a <= b   =>  decide (LE.le {C} instLE{C} a b) (instDecidable{C}Le a b)
/// a == b   =>  BEq.beq {C} (instBEqOfDecidableEq {C} instDecidableEq{C}) a b
/// ```
///
/// (`==` is `BEq.beq`, NOT `decide (Eq …)`; the explicit `decide (a = b)`
/// spelling is accepted too, since it is definitionally equal.) Both operands
/// must be bare parameters — see [`CleanOriginShape::DecideComparison`] on why a
/// numeral operand and `!=` are residuals. `>`/`>=` are expressed by operand
/// order (`b < a` / `b <= a`).
///
/// SOUNDNESS: this recogniser is never trusted. It produces the plan the
/// emitter builds from, and `crate::gate::check_faithful` re-decides definitional
/// equality of the EMITTED MIR's reflection against the untouched declaration.
/// A misread comparison or a swapped operand emits a body that denotes a
/// different function, whose reflection FAILS def-eq and is refused fail-closed
/// — never a silently wrong binary. `control_25_clean_comparison_emitter_mutation`
/// pins exactly those refusals.
fn recognise_decide_comparison(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    // The result carrier is `Bool` — the whole distinction from a select, and
    // what makes this recogniser disjoint from every `UInt`-result one below.
    if !matches!(signature.result().clean(), CleanType::Bool) {
        return None;
    }
    // Both operands are the two source parameters, at one unsigned machine
    // width (the reflected side B, `admit_comparison_function`, is single-domain
    // over all parameters; re-checked on the sealed plan).
    if arity != 2 {
        return None;
    }
    let CleanType::UInt(width) = signature.arguments().first()?.clean() else {
        return None;
    };
    let carrier_owned;
    let carrier: &str = match uint_carrier_name(width) {
        Some(s) => s,
        None => {
            carrier_owned = format!("UInt{width}");
            &carrier_owned
        }
    };
    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    let const_is = |expr: &Expr, name: &str, levels: usize| -> bool {
        matches!(strip_mdata(expr).kind(), ExprKind::Const(n, ls)
            if name_display_eq_str(n, name) && ls.len() == levels)
    };

    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, _head_levels) = head.kind() else {
        return None;
    };
    if name_display_eq_str(head_name, "decide")
        || name_display_eq_str(head_name, "Decidable.decide")
    {
        // `decide <prop> <inst>` — the `<`/`<=` spelling (and the explicit
        // `decide (a = b)`).
        if args.len() != 2 {
            return None;
        }
        let (prop_head, prop_args) = uncurry(strip_mdata(args[0]));
        let ExprKind::Const(prop_name, _plevels) = prop_head.kind() else {
            return None;
        };
        let (cmp, cmp_left, cmp_right) = if name_display_eq_str(prop_name, "LT.lt")
            || name_display_eq_str(prop_name, "LE.le")
        {
            // `LT.lt {C} instLT{C} l r` — 4 args at the carrier.
            if prop_args.len() != 4 || !const_is(prop_args[0], carrier, 0) {
                return None;
            }
            let cmp =
                if name_display_eq_str(prop_name, "LT.lt") { SelectCmp::Lt } else { SelectCmp::Le };
            (cmp, bvar_param(prop_args[2])?, bvar_param(prop_args[3])?)
        } else if name_display_eq_str(prop_name, "Eq") {
            // `Eq {C} l r` — 3 args at the carrier.
            if prop_args.len() != 3 || !const_is(prop_args[0], carrier, 0) {
                return None;
            }
            (SelectCmp::Eq, bvar_param(prop_args[1])?, bvar_param(prop_args[2])?)
        } else {
            return None;
        };
        return Some(CleanOriginShape::DecideComparison { cmp, cmp_left, cmp_right });
    }
    if name_display_eq_str(head_name, "BEq.beq") {
        // `BEq.beq {C} (instBEqOfDecidableEq {C} instDecidableEq{C}) l r` — the
        // idiomatic `a == b`. The instance is authenticated exactly: a bare
        // `instBEq{C}` is a DIFFERENT decision procedure, and while the gate
        // would refuse a mismatch fail-closed, authenticating here keeps the
        // shape's meaning single.
        if args.len() != 4 || !const_is(args[0], carrier, 0) {
            return None;
        }
        let (inst_head, inst_args) = uncurry(strip_mdata(args[1]));
        let inst_dec_eq_ok = matches!(
            strip_mdata(inst_args.get(1).copied()?).kind(),
            ExprKind::Const(n, ls)
                if ls.is_empty() && name_eq1_concat(n, &["instDecidableEq", carrier])
        );
        if !const_is(inst_head, "instBEqOfDecidableEq", 1)
            || inst_args.len() != 2
            || !const_is(inst_args[0], carrier, 0)
            || !inst_dec_eq_ok
        {
            return None;
        }
        let cmp_left = bvar_param(args[2])?;
        let cmp_right = bvar_param(args[3])?;
        return Some(CleanOriginShape::DecideComparison {
            cmp: SelectCmp::Eq,
            cmp_left,
            cmp_right,
        });
    }
    None
}

/// **W6 (Rust-calls-Clean) — recognise a boolean negation or connective over
/// `Bool` parameters returned as `Bool`.**
///
/// The kernel terms, measured 2026-09-13:
///
/// ```text
/// not b    =>  Bool.not (BVar)
/// a && b   =>  and (BVar) (BVar)      (def-eq to `Bool.and`)
/// a || b   =>  or  (BVar) (BVar)      (def-eq to `Bool.or`)
/// ```
///
/// The result and every parameter carry `Bool`, and every operand is a bare
/// parameter. SOUNDNESS: never trusted — `crate::gate::check_faithful` re-decides
/// definitional equality of the EMITTED body's reflection (minted by
/// `admit_bool_value_function` as `Bool.not`/`Bool.and`/`Bool.or`) against the
/// untouched declaration, so a misread connective or operand is refused
/// fail-closed. `control_26_clean_bool_value_emitter_mutation` pins those
/// refusals.
fn recognise_bool_value(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    if !matches!(signature.result().clean(), CleanType::Bool) {
        return None;
    }
    // Every parameter carries `Bool` (the reflected `admit_bool_value_function`
    // is single-domain over `Bool`; re-checked on the sealed plan).
    if !signature.arguments().iter().all(|c| matches!(c.clean(), CleanType::Bool)) {
        return None;
    }
    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return None;
    };
    if !head_levels.is_empty() {
        return None;
    }
    if name_display_eq_str(head_name, "Bool.not") && args.len() == 1 {
        Some(CleanOriginShape::BoolNot { param: bvar_param(args[0])? })
    } else if name_display_eq_str(head_name, "and") && args.len() == 2 {
        Some(CleanOriginShape::BoolConnective {
            op: BoolBinOp::And,
            left: bvar_param(args[0])?,
            right: bvar_param(args[1])?,
        })
    } else if name_display_eq_str(head_name, "or") && args.len() == 2 {
        Some(CleanOriginShape::BoolConnective {
            op: BoolBinOp::Or,
            left: bvar_param(args[0])?,
            right: bvar_param(args[1])?,
        })
    } else {
        None
    }
}

fn recognise_bool_expression(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    if !matches!(signature.result().clean(), CleanType::Bool)
        || !signature.arguments().iter().all(|c| matches!(c.clean(), CleanType::Bool))
    {
        return None;
    }
    fn read(expr: &Expr, arity: usize, depth: usize, ops: &mut usize) -> Option<BoolExpr> {
        if depth > BOOL_EXPRESSION_MAX_DEPTH {
            return None;
        }
        let expr = strip_mdata(expr);
        if let ExprKind::BVar(index) = expr.kind() {
            return ((*index as usize) < arity)
                .then(|| BoolExpr::Param(arity - 1 - *index as usize));
        }
        let (head, args) = uncurry(expr);
        let ExprKind::Const(name, levels) = head.kind() else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        match args.as_slice() {
            [] if name_display_eq_str(name, "Bool.true") => Some(BoolExpr::Literal(true)),
            [] if name_display_eq_str(name, "Bool.false") => Some(BoolExpr::Literal(false)),
            [child] if name_display_eq_str(name, "Bool.not") => {
                *ops += 1;
                if *ops > BOOL_EXPRESSION_MAX_OPS {
                    return None;
                }
                Some(BoolExpr::Not(Box::new(read(child, arity, depth + 1, ops)?)))
            }
            [left, right]
                if name_display_eq_str(name, "and")
                    || name_display_eq_str(name, "Bool.and")
                    || name_display_eq_str(name, "or")
                    || name_display_eq_str(name, "Bool.or") =>
            {
                *ops += 1;
                if *ops > BOOL_EXPRESSION_MAX_OPS {
                    return None;
                }
                let is_and =
                    name_display_eq_str(name, "and") || name_display_eq_str(name, "Bool.and");
                let left = Box::new(read(left, arity, depth + 1, ops)?);
                let right = Box::new(read(right, arity, depth + 1, ops)?);
                Some(if is_and { BoolExpr::And(left, right) } else { BoolExpr::Or(left, right) })
            }
            _ => None,
        }
    }
    let mut ops = 0;
    let expr = read(cursor, arity, 0, &mut ops)?;
    (ops > 0).then_some(CleanOriginShape::BoolExpression { expr })
}

enum Rhs {
    Param(usize),
    Literal(u128),
}

struct SelectIte<'a> {
    cmp: SelectCmp,
    left: usize,
    right: ArithOperand,
    then_branch: &'a Expr,
    else_branch: &'a Expr,
}

fn read_select_ite<'a>(
    cursor: &'a Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<SelectIte<'a>> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return None;
    };
    let carrier_owned;
    let carrier: &str = match uint_carrier_name(width) {
        Some(s) => s,
        None => {
            carrier_owned = format!("UInt{width}");
            &carrier_owned
        }
    };
    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    let is_carrier_const = |expr: &Expr| -> bool {
        matches!(strip_mdata(expr).kind(), ExprKind::Const(n, levels)
            if name_display_eq_str(n, carrier) && levels.is_empty())
    };

    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, head_levels) = head.kind() else {
        return None;
    };
    if !name_display_eq_str(head_name, "ite")
        || head_levels.len() != 1
        || head_levels[0] != Level::succ(Level::zero())
        || args.len() != 5
        || !is_carrier_const(args[0])
    {
        return None;
    }

    // The proposition: LT.lt/LE.le with the homogeneous instance, or Eq.
    let (prop_head, prop_args) = uncurry(args[1]);
    let ExprKind::Const(prop_name, prop_levels) = prop_head.kind() else {
        return None;
    };
    let (cmp, dec_inst_parts, l_expr, r_expr): (SelectCmp, [&str; 3], &Expr, &Expr) =
        if name_display_eq_str(prop_name, "LT.lt") || name_display_eq_str(prop_name, "LE.le") {
            if prop_levels.len() != 1 || !prop_levels[0].is_zero() || prop_args.len() != 4 {
                return None;
            }
            let (cmp, class) = if name_display_eq_str(prop_name, "LT.lt") {
                (SelectCmp::Lt, "LT")
            } else {
                (SelectCmp::Le, "LE")
            };
            if !is_carrier_const(prop_args[0]) {
                return None;
            }
            let inst_ok = matches!(strip_mdata(prop_args[1]).kind(), ExprKind::Const(n, levels)
                if levels.is_empty() && name_eq1_concat(n, &["inst", class, carrier]));
            if !inst_ok {
                return None;
            }
            let suffix = if cmp == SelectCmp::Lt { "Lt" } else { "Le" };
            (cmp, ["instDecidable", carrier, suffix], prop_args[2], prop_args[3])
        } else if name_display_eq_str(prop_name, "Eq") {
            if prop_levels.len() != 1 || prop_args.len() != 3 || !is_carrier_const(prop_args[0]) {
                return None;
            }
            (SelectCmp::Eq, ["instDecidableEq", carrier, ""], prop_args[1], prop_args[2])
        } else {
            return None;
        };
    let cmp_left = bvar_param(l_expr)?;
    // R2/C9: the comparison's RIGHT operand — a bare parameter (the C5a
    // param-vs-param select, unchanged) or a numeral in either measured
    // spelling. A literal LEFT operand has no arm: `bvar_param(l_expr)`
    // above already failed the tree closed.
    let rhs = if let Some(param) = bvar_param(r_expr) {
        Rhs::Param(param)
    } else {
        match numeral_leaf(r_expr, carrier)? {
            NatReading::Fits(value) => Rhs::Literal(value),
            // A multi-limb literal is out of range for every admitted width;
            // fall through to the generic fragment refusal. (A FITTING but
            // over-width numeral is deliberately let through — the plan-time
            // re-check renders the specific out-of-range reason.)
            NatReading::Oversized => return None,
        }
    };

    // The Decidable instance, applied to the SAME two operands: the same
    // parameter on the left, and on the right the same parameter — or, for
    // the literal select, a numeral of the same VALUE (two spellings of one
    // value share a denotation; a different value is a different denotation
    // and fails closed).
    let (inst_head, inst_args) = uncurry(args[2]);
    let head_is = |name: &str| {
        matches!(inst_head.kind(), ExprKind::Const(n, levels)
            if name_display_eq_str(n, name) && levels.is_empty())
    };
    let head_is_parts = |parts: &[&str]| {
        matches!(inst_head.kind(), ExprKind::Const(n, levels)
            if levels.is_empty() && name_eq1_concat(n, parts))
    };
    if inst_args.len() != 2 {
        return None;
    }
    match &rhs {
        Rhs::Param(cmp_right) => {
            if !head_is_parts(&dec_inst_parts)
                || bvar_param(inst_args[0]) != Some(cmp_left)
                || bvar_param(inst_args[1]) != Some(*cmp_right)
            {
                return None;
            }
        }
        Rhs::Literal(value) => {
            // Measured instance spellings for a literal right operand. The
            // carrier instance is the spelling the current real island path
            // produces for `<`, `<=` and propositional `=` at UInt8/16/32/64
            // (`probe_i5_select_literal_le_and_propositional_eq_real_elaboration_admit`).
            // A historical Clean range reduced `<` to Nat instead; that
            // compatibility spelling remains admitted for `<` only. Both
            // readings are the proposition's OWN comparison on the SAME
            // operands: THIS parameter on the left and a numeral of THIS
            // value on the right, never the two exchanged.
            //
            // 1. REDUCTION TO NAT — every Clean pin before `c91fa93f5`
            //    (R2/C9 SPELLING-GAP FIX, measured 2026-08-21, the fourth
            //    teaching of the measurement rule): instance synthesis
            //    resolved `a < 10` by reduction to `Nat`, minting
            //    `instDecidableNatLt (a.toNat-as-Proj-chain) 10`. Kept: a
            //    Clean pin can move back, and nothing below depends on which
            //    spelling a given pin produces.
            //
            // 2. THE CARRIER INSTANCE — Clean `c91fa93f5` and later
            //    (measured 2026-09-23 at the superproject's Clean pin
            //    `dca882b5f`, at UInt8/16/32/64 alike): that commit made the
            //    carrier's `decLt a b` BE `Nat.decLt a.toNat b.toNat`, and
            //    the same island source now elaborates to
            //    `instDecidable{C}Lt a <LIT>`, whose right operand is the
            //    proposition's `{C}.ofNat LIT` unfolded one δβ step
            //    ([`carrier_instance_numeral`]). Before this arm existed that
            //    tree fell to the generic fragment refusal, and every
            //    driver-level `if a < 10` fixture died at the mint with
            //    E0425 — the same failure the 2026-08-21 fix repaired in the
            //    other direction. The retained Clean 4.30 measurement records
            //    this carrier form for `<`, `<=` and propositional `=` at
            //    every admitted width.
            //
            // SOUNDNESS. Neither reading is trusted. The emitted Rust comparison against an
            // inline scalar is justified ONLY by `crate::gate::check_faithful`: side B — reflected
            // by `admit_select_literal_function` / `admit_select_operands_function` from the
            // EMITTED MIR, never from this plan — must be definitionally equal to the untouched
            // declaration under the kernel. This reading must MATCH what that check compares —
            // `admit_lowering` refuses unless the emitted MIR reads back as
            // this very plan — but widening what this recognizer accepts only
            // changes which bodies are ATTEMPTED: a body whose side B is not
            // defeq to side A is still refused fail-closed at the gate,
            // whatever this arm read. Side B is unchanged. `probe_i3`/`i4`
            // measure the historical `<` identification and `probe_i5`
            // measures the real `<=`/`=` trees, including wrong-comparison,
            // wrong-literal and swapped-arm refusals. Nor can the instance
            // disagree with the proposition it decides: side A was
            // FULL-kernel-checked, so the instance's type is the `ite`'s
            // proposition up to defeq. The operand match below restates that
            // invariant; it is not the thing enforcing it.
            let nat_reduced = cmp == SelectCmp::Lt
                && head_is("instDecidableNatLt")
                && to_nat_projection_param(inst_args[0], carrier, arity) == Some(cmp_left)
                && nat_literal(inst_args[1]) == Some(NatReading::Fits(*value));
            // `dec_inst_parts` is derived from the proposition above, so an
            // Lt/Le/Eq instance can never be read as a different comparison.
            let carrier_instance = head_is_parts(&dec_inst_parts)
                && bvar_param(inst_args[0]) == Some(cmp_left)
                && carrier_instance_numeral(inst_args[1], carrier, width)
                    == Some(NatReading::Fits(*value));
            if !(nat_reduced || carrier_instance) {
                return None;
            }
        }
    }

    Some(SelectIte {
        cmp,
        left: cmp_left,
        right: match rhs {
            Rhs::Param(param) => ArithOperand::Param(param),
            Rhs::Literal(value) => ArithOperand::Const(value),
        },
        then_branch: args[3],
        else_branch: args[4],
    })
}

fn recognise_select_ite(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    let selected = read_select_ite(cursor, arity, signature)?;
    let CleanType::UInt(width) = signature.result().clean() else { return None };
    let carrier = uint_carrier_name(width)?;
    let bvar_param = |expr: &Expr| match strip_mdata(expr).kind() {
        &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
        _ => None,
    };
    let cmp = selected.cmp;
    let cmp_left = selected.left;
    let rhs = match selected.right {
        ArithOperand::Param(param) => Rhs::Param(param),
        ArithOperand::Const(value) => Rhs::Literal(value),
    };
    // §6f LANDING 3: each ARM is a bare bound parameter or a numeral in
    // either measured spelling. The real elaborator mints a constant arm in
    // the CARRIER spelling (`UInt64.ofNat 0`, measured in l3_p2/l3_p3) — the
    // same spelling `Domain::numeral` mints on side B — and `numeral_leaf`
    // accepts the surface spelling too, exactly as it does for the comparison
    // operand. Anything else still fails the tree closed.
    let arm = |expr: &Expr| -> Option<ArithOperand> {
        match bvar_param(expr) {
            Some(param) => Some(ArithOperand::Param(param)),
            None => match numeral_leaf(expr, carrier)? {
                // A multi-limb literal is out of range for every admitted
                // width; fall through to the generic fragment refusal, the
                // same disposition the comparison operand takes.
                NatReading::Oversized => None,
                NatReading::Fits(value) => Some(ArithOperand::Const(value)),
            },
        }
    };
    let then_arm = arm(selected.then_branch)?;
    let else_arm = arm(selected.else_branch)?;

    // The two arm vocabularies are DISJOINT by construction: a select whose
    // arms are both bare parameters keeps its pre-landing-3 variant, byte for
    // byte, so every pin on `Select`/`SelectLiteral` is untouched and there is
    // never a choice of which shape a body is.
    if let (ArithOperand::Param(then_param), ArithOperand::Param(else_param)) = (then_arm, else_arm)
    {
        return Some(match rhs {
            Rhs::Param(cmp_right) => {
                CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param }
            }
            Rhs::Literal(literal) => CleanOriginShape::SelectLiteral {
                cmp,
                cmp_param: cmp_left,
                literal,
                then_param,
                else_param,
            },
        });
    }
    Some(CleanOriginShape::SelectOperands {
        cmp,
        cmp_left,
        cmp_right: match rhs {
            Rhs::Param(cmp_right) => ArithOperand::Param(cmp_right),
            Rhs::Literal(literal) => ArithOperand::Const(literal),
        },
        then_arm,
        else_arm,
    })
}

fn recognise_unsigned_conditional(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    fn read(
        expression: &Expr,
        arity: usize,
        signature: &CarrierSignature,
        depth: usize,
        decisions: &mut usize,
    ) -> Option<UIntConditional> {
        if depth > UINT_CONDITIONAL_MAX_DECISIONS {
            return None;
        }
        if let ExprKind::BVar(index) = strip_mdata(expression).kind() {
            let index = usize::try_from(*index).ok()?;
            return (index < arity)
                .then(|| UIntConditional::Operand(ArithOperand::Param(arity - 1 - index)));
        }
        let CleanType::UInt(width) = signature.result().clean() else { return None };
        if let Some(NatReading::Fits(value)) = numeral_leaf(expression, uint_carrier_name(width)?) {
            return Some(UIntConditional::Operand(ArithOperand::Const(value)));
        }
        let selected = read_select_ite(expression, arity, signature)?;
        *decisions += 1;
        if *decisions > UINT_CONDITIONAL_MAX_DECISIONS {
            return None;
        }
        Some(UIntConditional::If {
            cmp: selected.cmp,
            left: selected.left,
            right: selected.right,
            then_branch: Box::new(read(
                selected.then_branch,
                arity,
                signature,
                depth + 1,
                decisions,
            )?),
            else_branch: Box::new(read(
                selected.else_branch,
                arity,
                signature,
                depth + 1,
                decisions,
            )?),
        })
    }
    let mut decisions = 0;
    let expr = read(cursor, arity, signature, 0, &mut decisions)?;
    (decisions >= 2).then_some(CleanOriginShape::UnsignedConditional { expr })
}

fn check_unsigned_conditional(
    name: &str,
    expression: &UIntConditional,
    signature: &CarrierSignature,
    width: u32,
    depth: usize,
) -> Result<usize, EmitRefusal> {
    if depth > UINT_CONDITIONAL_MAX_DECISIONS {
        return Err(EmitRefusal::NotEmittable {
            name: name.into(),
            reason: "unsigned conditional depth exceeds its bound".into(),
        });
    }
    match expression {
        UIntConditional::Operand(operand) => {
            check_arith_leaf(name, operand, signature, width)?;
            Ok(0)
        }
        UIntConditional::If { left, right, then_branch, else_branch, .. } => {
            check_arith_leaf(name, &ArithOperand::Param(*left), signature, width)?;
            check_arith_leaf(name, right, signature, width)?;
            let then_count =
                check_unsigned_conditional(name, then_branch, signature, width, depth + 1)?;
            let else_count =
                check_unsigned_conditional(name, else_branch, signature, width, depth + 1)?;
            let count = 1 + then_count + else_count;
            if count > UINT_CONDITIONAL_MAX_DECISIONS {
                return Err(EmitRefusal::NotEmittable {
                    name: name.into(),
                    reason: "unsigned conditional decisions exceed their bound".into(),
                });
            }
            Ok(count)
        }
    }
}

/// Which `Bool`-level equality spelling a condition was written with.
///
/// §6f landing 5. Not a comparison and not a shape: a LABEL. In landing 6 the
/// [`BoolDecisionSpelling::Equal`] half acquired a shape
/// ([`CleanOriginShape::SelectBeq`]) and the `NotEqual` half stayed a label for
/// a refusal, which is why this enum is still two variants and not one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoolDecisionSpelling {
    /// `a == b` — `Eq Bool (BEq.beq …) Bool.true`.
    Equal,
    /// `a != b` — the same with a `Bool.not` around the decision.
    NotEqual,
}

/// One READING of a `Bool`-level equality `ite`, as
/// [`recognise_bool_decision_ite`] parses it.
///
/// §6f landing 6 factored this out of that function's return type so the tree
/// is parsed ONCE and read twice: [`recognise_beq_select_ite`] turns the
/// `Equal` half into a shape, and the planner's refusal arm turns whatever is
/// left into a diagnosis. A second parser of one tree is exactly the drift this
/// crate refuses everywhere else.
struct BoolDecisionIte<'a> {
    /// Which surface operator produced it.
    spelling: BoolDecisionSpelling,
    /// **§6f LANDING 8** — the `Bool` constant the decision is lifted against.
    ///
    /// Landing 6 required this to be `Bool.true` and had no field for it. Four
    /// spellings are measured to reach here from real sources (`l8_p2`):
    /// `Bool.true` (what `==` and `= Bool.true` produce), a bare depth-1 `true`
    /// (`= true`), `Bool.false` (`= Bool.false`) and a bare depth-1 `false`
    /// (`= false`). Each pair is definitionally equal, so what is carried here
    /// is the VALUE and not the spelling — but the reader accepts exactly those
    /// four constants and nothing else, because a reader arm for a spelling no
    /// source produces is the R2 defect `control_14`'s spelling grain exists to
    /// catch.
    scrutinee: bool,
    /// Whether the scrutinee was spelled `Bool.true` EXACTLY — the one
    /// spelling the narrow `SelectBeq` lane was written and mutation-
    /// controlled for.
    ///
    /// Carried separately from [`Self::scrutinee`] because the VALUE and the
    /// SPELLING answer different questions: the value decides which SHAPE a
    /// body belongs to; the spelling decides whether a lane's existing
    /// controls actually cover it. Reading only the value let `(a == b) = true`
    /// — a bare depth-1 `true`, per `l8_p2` — reach the pre-existing narrow
    /// row with no demand entry and no mutation control aimed at it.
    scrutinee_is_canonical_true: bool,
    /// The decision's left operand, unparsed.
    left: &'a Expr,
    /// The decision's right operand, unparsed.
    right: &'a Expr,
    /// The `ite`'s then-branch, unparsed.
    then_arm: &'a Expr,
    /// The `ite`'s else-branch, unparsed.
    else_arm: &'a Expr,
}

/// The `Bool` VALUE a measured scrutinee constant denotes, or `None`.
///
/// §6f landing 8. Four spellings, all measured out of a real session
/// (`landing8_selection_probes::l8_p2`) and none of them speculative: a
/// depth-2 `Bool.true`/`Bool.false`, and the bare depth-1 `true`/`false` a
/// user's own `= true` / `= false` token resolves to. The bare spellings are
/// the ones a source actually produces for the explicit lift, and a reader
/// keyed only on `Bool.false` would match no real `(a == b) = false` at all.
fn bool_scrutinee_value(expr: &Expr) -> Option<bool> {
    let ExprKind::Const(name, levels) = strip_mdata(expr).kind() else {
        return None;
    };
    if !levels.is_empty() {
        return None;
    }
    if name_display_eq_str(name, "Bool.true") || name_display_eq_str(name, "true") {
        Some(true)
    } else if name_display_eq_str(name, "Bool.false") || name_display_eq_str(name, "false") {
        Some(false)
    } else {
        None
    }
}

/// **§6f LANDING 5 — recognise the `Bool`-level equality condition, FOR A
/// REFUSAL AND NOTHING ELSE.**
///
/// The exact tree the REAL island elaborator mints for `if a == b then … else
/// …` at a machine carrier, measured at u8/u16/u32/u64 and pinned construct by
/// construct in `tests/landing5_selection_probes.rs::l5_p1`:
///
/// ```text
/// ite.{1} {C}
///   (Eq.{1} Bool (BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r)
///                Bool.true)
///   (instDecidableEqBool <the same decision> Bool.true)
///   t e
/// ```
///
/// and, for `!=`, the same with `Bool.not` wrapping the decision.
///
/// # This function selects no row and returns no shape, deliberately
///
/// `recognise_select_ite` reads the PROPOSITIONAL spelling (`Eq {C} l r`) and
/// is what the `select.eq` row is stated over. This one reads a **second
/// spelling of the same condition** which the emit lane cannot realize:
/// measured, the two `ite`s are NOT definitionally equal (the island rejects
/// even `theorem … := rfl` between them, `l5_p3`), so a body emitted for one
/// cannot be gated against the other; and the MIR that would tell the two
/// apart needs a `bool` CONSTANT operand — a new
/// `crate::materialize::TemplateOperand` primitive, which
/// `rustc_mir_transform::clean_origin_mir::materialize` matches with no
/// wildcard by landing 4's design.
///
/// So what this buys is a DIAGNOSIS, which ruling v7/D3 makes a requirement
/// rather than a nicety: without it a user who writes the idiomatic `==` gets
/// the generic fifteen-row fragment prose and no hint that one character
/// closes it. `l5_p2` measures that the recommended `=` really does travel the
/// whole pipeline, so the advice is not a guess.
///
/// Matched EXACTLY, fail-closed: a tree that is nearly this is not this, and
/// falls through to the generic refusal rather than acquiring advice that
/// might be wrong for it. The operands are deliberately NOT constrained —
/// every operand vocabulary hits the same wall, and a refusal that only fired
/// for bare parameters would leave the constant-arm user with worse advice
/// than the parameter one.
fn recognise_bool_decision_ite<'a>(
    cursor: &'a Expr,
    signature: &CarrierSignature,
) -> Option<BoolDecisionIte<'a>> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return None;
    };
    let carrier_owned;
    let carrier: &str = match uint_carrier_name(width) {
        Some(s) => s,
        None => {
            carrier_owned = format!("UInt{width}");
            &carrier_owned
        }
    };
    let const_is = |expr: &Expr, name: &str, levels: usize| -> bool {
        matches!(strip_mdata(expr).kind(), ExprKind::Const(n, ls)
            if name_display_eq_str(n, name) && ls.len() == levels)
    };

    let (head, args) = uncurry(cursor);
    if !const_is(head, "ite", 1) || args.len() != 5 || !const_is(args[0], carrier, 0) {
        return None;
    }

    // The proposition: `Eq.{1} Bool <decision> <scrutinee>`. The type argument
    // being `Bool` rather than the carrier is the whole distinction — it is
    // what `select.eq`'s selector cannot match.
    //
    // §6f LANDING 8: the SCRUTINEE is read rather than required. Landing 6
    // demanded `Bool.true` here, which made `(a == b) = false` — a body that
    // elaborates, kernel-checks, and denotes a DIFFERENT function — fall
    // through to the generic fifteen-row prose with no mention of equality at
    // all. Reading it is what lets the refusal below name the real boundary and
    // what lets the general shape carry the polarity into the emitted constant.
    let (prop_head, prop_args) = uncurry(args[1]);
    if !const_is(prop_head, "Eq", 1) || prop_args.len() != 3 || !const_is(prop_args[0], "Bool", 0) {
        return None;
    }
    let scrutinee = bool_scrutinee_value(prop_args[2])?;
    let scrutinee_is_canonical_true = const_is(prop_args[2], "Bool.true", 0);

    // The decision, possibly negated. `!=` puts the negation in the DECISION,
    // not in the scrutinee (measured, `l5_p7`), so this is the only place it
    // can be read.
    let (spelling, decision) = {
        let (not_head, not_args) = uncurry(prop_args[1]);
        if const_is(not_head, "Bool.not", 0) && not_args.len() == 1 {
            (BoolDecisionSpelling::NotEqual, not_args[0])
        } else {
            (BoolDecisionSpelling::Equal, prop_args[1])
        }
    };

    // `BEq.beq.{0} {C} (instBEqOfDecidableEq.{0} {C} instDecidableEq{C}) l r`.
    // The instance is authenticated exactly: a bare `instBEq{C}`, or any other
    // `BEq` instance, is a DIFFERENT decision procedure and must not collect
    // advice that assumes it decides equality.
    let (beq_head, beq_args) = uncurry(decision);
    if !const_is(beq_head, "BEq.beq", 1)
        || beq_args.len() != 4
        || !const_is(beq_args[0], carrier, 0)
    {
        return None;
    }
    let (inst_head, inst_args) = uncurry(beq_args[1]);
    let inst_dec_eq_ok = matches!(
        strip_mdata(inst_args.get(1).copied()?).kind(),
        ExprKind::Const(n, ls)
            if ls.is_empty() && name_eq1_concat(n, &["instDecidableEq", carrier])
    );
    if !const_is(inst_head, "instBEqOfDecidableEq", 1)
        || inst_args.len() != 2
        || !const_is(inst_args[0], carrier, 0)
        || !inst_dec_eq_ok
    {
        return None;
    }

    // The `ite`'s own decidability instance: `instDecidableEqBool` applied to
    // the SAME decision term and the SAME scrutinee. Requiring the identity
    // rather than re-parsing is what makes a mismatched pair fall through: two
    // different decisions in the two positions is not this spelling.
    //
    // §6f landing 8: the instance's scrutinee must be the SAME CONSTANT the
    // proposition carries, compared by term identity rather than by value — a
    // proposition lifted against `false` beside an instance deciding `Bool.true`
    // is not a tree any elaborator produces, and admitting it would let one
    // reading stand for two different decisions.
    let (dec_head, dec_args) = uncurry(args[2]);
    if !const_is(dec_head, "instDecidableEqBool", 0)
        || dec_args.len() != 2
        || strip_mdata(dec_args[0]) != strip_mdata(prop_args[1])
        || strip_mdata(dec_args[1]) != strip_mdata(prop_args[2])
    {
        return None;
    }

    Some(BoolDecisionIte {
        spelling,
        scrutinee,
        scrutinee_is_canonical_true,
        left: beq_args[2],
        right: beq_args[3],
        then_arm: args[3],
        else_arm: args[4],
    })
}

/// **§6f LANDING 6 — the `==` select, as a SHAPE.**
///
/// The half of [`recognise_bool_decision_ite`]'s reading that this landing can
/// serve: the `Equal` spelling, over landing 3's operand vocabulary.
///
/// # It reuses the ONE parse, deliberately
///
/// The tree is read by `recognise_bool_decision_ite` and nothing else — a
/// second descent over the same `ite` would be two readers of one contract,
/// the drift this crate refuses everywhere else — and this function only
/// projects that reading into the plan vocabulary. A tree that is the `==`
/// spelling but whose OPERANDS are outside the fragment (a computed operand, a
/// numeral on the left, an out-of-range literal) returns `None` here and falls
/// through to the planner's refusal arm, which still names the spelling: a
/// user gets the boundary they actually hit, not the generic prose.
///
/// `!=` is refused here for the reason its ledger entry states, and refusing it
/// by MATCHING it rather than by failing to parse it is what lets the refusal
/// say `Bool.not` (`landing6_selection_probes::l6_p5`).
fn recognise_beq_select_ite(
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Option<CleanOriginShape> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return None;
    };
    let carrier_owned;
    let carrier: &str = match uint_carrier_name(width) {
        Some(s) => s,
        None => {
            carrier_owned = format!("UInt{width}");
            &carrier_owned
        }
    };
    let reading = recognise_bool_decision_ite(cursor, signature)?;
    if reading.spelling != BoolDecisionSpelling::Equal {
        return None;
    }
    // §6f LANDING 8: the scrutinee used to be REQUIRED to be `Bool.true` by the
    // parse itself; it is now READ, so this shape restates its own half of the
    // boundary. A `false` lift is the general shape's, and `l8_p2` measures
    // that the two `ite`s are not definitionally equal — so admitting one here
    // would plan a body the gate must then refuse.
    //
    // ADVERSARIAL FINDING, landing 8: the VALUE is not enough. Relaxing the
    // shared parse to READ the scrutinee made `bool_scrutinee_value` accept
    // four names, and `l8_p2` measures that `(a == b) = true` puts a BARE
    // depth-1 `true` there — not `Bool.true`. Checking only the value therefore
    // let a source spelling that refused at HEAD flow into this NARROW lane,
    // reaching the pre-existing `select.beq` row, its pre-existing producer and
    // its pre-existing reader: undisclosed, uncounted in the demand ledger, and
    // with no mutation control aimed at it. `control_14` cannot see it either,
    // because its row grain is keyed on the ROW and `select.beq` was already
    // exercised — a new SPELLING reaching an old row is invisible there.
    //
    // So this lane accepts exactly the spelling it was written and controlled
    // for. `= true` and `= Bool.false` and `= false` fall through to the
    // general shape or to a named refusal, which is where a widening can be
    // disclosed, counted and controlled. Restoring the narrow lane rather than
    // retro-fitting three ledger entries is the conservative half of the fix;
    // the demand is recorded for a landing that serves it deliberately.
    if !reading.scrutinee || !reading.scrutinee_is_canonical_true {
        return None;
    }

    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    // ONE operand reader for the decision's right-hand side and both arms —
    // the same rule landing 3's `admit_select_operands_function` is stated
    // over, and the same `numeral_leaf` the propositional select uses, so the
    // carrier and surface numeral spellings are accepted here exactly as they
    // are there.
    let operand = |expr: &Expr| -> Option<ArithOperand> {
        match bvar_param(expr) {
            Some(param) => Some(ArithOperand::Param(param)),
            None => match numeral_leaf(expr, carrier)? {
                // A multi-limb literal is out of range at every admitted width;
                // fall through to the refusal, the same disposition every other
                // select position takes.
                NatReading::Oversized => None,
                NatReading::Fits(value) => Some(ArithOperand::Const(value)),
            },
        }
    };

    Some(CleanOriginShape::SelectBeq {
        // The decision's LEFT operand is a bare parameter. Not caution: a
        // numeral there does not elaborate at all (`l3_p6`).
        cmp_left: bvar_param(reading.left)?,
        cmp_right: operand(reading.right)?,
        then_arm: operand(reading.then_arm)?,
        else_arm: operand(reading.else_arm)?,
    })
}

/// **§6f LANDING 8 — the GENERAL `==` select, as a SHAPE.**
///
/// What [`recognise_beq_select_ite`] declines and the refusal used to swallow:
/// a lift against `false`, and a raw-binop operand in either decision position.
///
/// # It reuses the ONE parse, deliberately
///
/// The tree is read by `recognise_bool_decision_ite` and nothing else — the
/// same rule landing 6 stated when it added the narrow shape. This function
/// projects that reading into a wider plan vocabulary; it does not re-descend.
///
/// # DISJOINT from the narrow shape
///
/// It returns `None` for a `true` lift with two leaf operands: that body is
/// `CleanOriginShape::SelectBeq`, byte for byte, and giving it two plans is the
/// hazard the general select's own disjointness invariant exists for. The
/// sealed plan re-checks it, so the property belongs to the plan rather than to
/// this function.
///
/// # WHAT IT STILL REFUSES, each with a measurement rather than a caution
///
/// * **a computed ARM** (`if a == b then a &&& 1 else b`) — kernel-green
///   (`l8_p6`), but its realization is either a fifth skeleton or a HOIST of
///   the arm's computation into the entry block, which evaluates a branch the
///   declaration does not take. That is a semantic decision with its own
///   controls, not an operand widening;
/// * **a NESTED operand** (`((a &&& b) ||| 1) == 0`) — kernel-green (`l8_p6`),
///   blocked on a deeper statement chain, exactly as landing 7's nested
///   raw-binop tree is;
/// * **a WRAPPING operand** (`(a + 1) == 0`) — kernel-green (`l8_p6`), and the
///   one refusal here whose blocker is a BLOCK BOUNDARY: `+`/`-`/`*` realize a
///   marker-authenticated `Call` TERMINATOR, so a wrapping operand splits the
///   entry block the decision and the lift live in. A fifth skeleton.
///
/// `!=` is still refused for its own recorded reason, one layer further out:
/// its `Bool.not` wraps the DECISION, and `l8_p2` measures that
/// `(a == b) = false` is NOT definitionally equal to it — so this landing does
/// not serve `!=` by accident, and the ledger keeps both entries.
fn recognise_beq_general_select_ite(
    name: &str,
    cursor: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    let Some(carrier) = uint_carrier_name(width) else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let Some(reading) = recognise_bool_decision_ite(cursor, signature) else {
        return Ok(None);
    };
    if reading.spelling != BoolDecisionSpelling::Equal {
        return Ok(None);
    }

    let bvar_param = |expr: &Expr| -> Option<usize> {
        match strip_mdata(expr).kind() {
            &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
            _ => None,
        }
    };
    // ONE reader for both decision positions, over the leaf vocabulary landing
    // 3 stated plus the raw-binop node. `recognise_raw_binop_leaf` is where the
    // DIVISOR RULE lives on side A, and it is the same rule
    // `recognise_raw_binop_expr` applies to a whole body — stated once.
    let mut refusal: Option<EmitRefusal> = None;
    let mut operand = |expr: &Expr| -> Option<BeqOperand> {
        if let Some(param) = bvar_param(expr) {
            return Some(BeqOperand::Param(param));
        }
        if let Some(reading) = numeral_leaf(expr, carrier) {
            return match reading {
                NatReading::Oversized => None,
                NatReading::Fits(value) => Some(BeqOperand::Const(value)),
            };
        }
        match recognise_raw_binop_leaf(name, expr, arity, carrier, width) {
            Ok(found) => found,
            Err(found) => {
                refusal.get_or_insert(found);
                None
            }
        }
    };
    let cmp_left = operand(reading.left);
    let cmp_right = operand(reading.right);
    if let Some(found) = refusal {
        return Err(found);
    }
    let (Some(cmp_left), Some(cmp_right)) = (cmp_left, cmp_right) else {
        return Ok(None);
    };

    // The ARMS stay LEAVES. A computed arm is kernel-green and refused; see
    // this function's own header for why it is a skeleton question rather than
    // an operand one.
    let arm = |expr: &Expr| -> Option<ArithOperand> {
        match bvar_param(expr) {
            Some(param) => Some(ArithOperand::Param(param)),
            None => match numeral_leaf(expr, carrier)? {
                NatReading::Oversized => None,
                NatReading::Fits(value) => Some(ArithOperand::Const(value)),
            },
        }
    };
    let (Some(then_arm), Some(else_arm)) = (arm(reading.then_arm), arm(reading.else_arm)) else {
        return Ok(None);
    };

    // THE DISJOINTNESS INVARIANT, stated here and re-checked on the sealed
    // plan: a `true` lift over two leaves is the narrow shape.
    let has_computed = matches!(cmp_left, BeqOperand::RawBin { .. })
        || matches!(cmp_right, BeqOperand::RawBin { .. });
    if reading.scrutinee && !has_computed {
        return Ok(None);
    }

    Ok(Some(CleanOriginShape::SelectBeqGeneral {
        scrutinee: reading.scrutinee,
        cmp_left,
        cmp_right,
        then_arm,
        else_arm,
    }))
}

/// **§6f LANDING 8 — one RAW-BINOP node in an operand position.**
///
/// The same spine [`recognise_raw_binop_expr`] reads as a whole body, read
/// here as a decision operand. It is a SEPARATE function rather than a call
/// into that one because that one returns a `CleanOriginShape` and re-checks a
/// whole signature; what is shared — and what must be shared, because it is the
/// soundness rule — is the operator vocabulary (read from
/// [`crate::table::raw_binop_rows`], never from a literal here), the prelude
/// instance authentication, the leaf vocabulary
/// ([`recognise_arith_operand`]), the DIVISOR RULE and the SHIFT-AMOUNT RULE.
///
/// `Ok(None)` = not a raw-binop node, so the caller falls through; `Err` = it
/// IS one but is outside the fragment for a specific, user-fixable reason.
fn recognise_raw_binop_leaf(
    name: &str,
    expr: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
) -> Result<Option<BeqOperand>, EmitRefusal> {
    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _levels) = head.kind() else {
        return Ok(None);
    };
    for (selected, op) in table::raw_binop_rows(table::CarrierClass::MachineUInt) {
        let Some((class, projection)) = table::surface_class(selected) else {
            continue;
        };
        if !name_eq2(head_name, class, projection) {
            continue;
        }
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let is_carrier =
            |t: &Expr| matches!(t.kind(), ExprKind::Const(n, _) if name_eq_str(n, carrier_name));
        if !(is_carrier(t1) && is_carrier(t2) && is_carrier(t3)) {
            return Ok(None);
        }
        if !is_prelude_homogeneous_instance(instance, class, carrier_name) {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: non_prelude_instance_reason(class, projection, carrier_name),
            });
        }
        // LEAVES only. A nested spine is kernel-green and has no realization on
        // this lane — one statement per node is a deeper chain, which is
        // landing 7's own nested-tree MISS in a new position.
        let (Some(left), Some(right)) = (
            recognise_arith_operand(name, lhs, arity, carrier_name, width)?,
            recognise_arith_operand(name, rhs, arity, carrier_name, width)?,
        ) else {
            return Ok(None);
        };
        // THE DIVISOR RULE, in an operand position. Same rule, same reason,
        // same refusal text: Clean's `{C}.div`/`.mod` are TOTAL and Rust's
        // `/`/`%` PANIC, so a variable or zero divisor here would emit a
        // statement that traps where the declaration returns a value.
        if op.panics_at_zero_right_operand() {
            match right {
                ArithOperand::Const(divisor) if divisor > 0 => {}
                _ => {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: unsafe_divisor_reason(class, projection, right),
                    });
                }
            }
        }
        // THE SHIFT-AMOUNT RULE, in an operand position — the same rule
        // `recognise_raw_binop_expr` applies to a whole body, stated once in
        // `shift_amount_has_a_side_b`.
        if op.right_operand_is_a_shift_amount() && !shift_amount_has_a_side_b(right, width) {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: shift_amount_reason(class, projection, right, width),
            });
        }
        return Ok(Some(BeqOperand::RawBin { op, left, right }));
    }
    Ok(None)
}

/// The v7/D3 refusal for a `Bool`-level equality condition that this lane still
/// cannot serve (§6f landing 5, NARROWED in landing 6, **CORRECTED in landing
/// 8**).
///
/// **What reaches it changed, and the text changed with it.** Landing 5 refused
/// every `==` body here, because the spelling had no emitted MIR at all.
/// Landing 6 gives `==` its own two-step realization and its own row; landing 8
/// gives the computed operand and the `= false` polarity theirs. So the only
/// `Equal` bodies that reach this function are ones whose operands are outside
/// the raw-binop-plus-leaf vocabulary, and the text names WHICH of the three
/// measured absences it is rather than guessing.
///
/// # THE CORRECTION, and why it is recorded rather than quietly applied
///
/// Landing 6's text said a COMPUTED operand *"resolves its decidability through
/// an elaborator normal form no producer reproduces"*. That sentence is TRUE of
/// `<`/`<=` and **FALSE of `==`**, which is the tree this function is reached
/// on: measured at four widths and four operators (`l8_p1`), the `==` tree
/// carries a computed operand VERBATIM inside `instDecidableEqBool`, with no
/// normal form anywhere in it. A refusal whose stated reason is false of the
/// program in front of it is the `r2_session_probes::probe_p9` defect class,
/// and this one was worse than cosmetic: it pointed the next reader away from
/// the cheapest available landing, which is the landing that deleted it.
///
/// It states three things and claims nothing else:
///
/// 1. **what was found**, in the user's syntax and in the kernel's — because a
///    user who wrote `==` or `!=` and is told about `BEq.beq` can search for it;
/// 2. **the measured boundary**, per ruling v7/D2: this is where the compiler
///    is, not a rule about what may be written, and the work item is named
///    rather than implied;
/// 3. **the options**. For `!=` the one-character `=` fix is honestly absent —
///    there is no emittable spelling of DISEQUALITY through `Bool.not` on this
///    lane — so the negated case gets the two restatements that ARE emitted
///    instead of a fix that would not work.
fn beq_boundary_reason(spelling: BoolDecisionSpelling, signature: &CarrierSignature) -> String {
    let carrier = signature.result().clean().name();
    let (operator, kernel_shape) = match spelling {
        BoolDecisionSpelling::Equal => (
            "`==`",
            format!(
                "`Eq Bool (BEq.beq {carrier} (instBEqOfDecidableEq {carrier} \
                 instDecidableEq{carrier}) a b) Bool.true`"
            ),
        ),
        BoolDecisionSpelling::NotEqual => (
            "`!=`",
            format!(
                "`Eq Bool (Bool.not (BEq.beq {carrier} (instBEqOfDecidableEq {carrier} \
                 instDecidableEq{carrier}) a b)) Bool.true`"
            ),
        ),
    };
    // WHY the refusal, which is different for the two spellings: `==` HAS a row
    // and a realization since landing 6 and a computed-operand vocabulary since
    // landing 8, so reaching this text means an operand is outside a vocabulary
    // this function can NAME; `!=` has none of it. The vocabulary is DERIVED
    // from the rows the operand recogniser reads, never written out here: the
    // hand-written list went stale the day `uint.xor`/`uint.shr` landed.
    let (operators, operand_rules) = raw_binop_vocabulary();
    let diagnosis = match spelling {
        BoolDecisionSpelling::Equal => format!(
            "The `==` spelling itself IS emittable — it selects the `select.beq` row, whose \
             realization transcribes the decision and its `= <bool>` lift as two comparisons \
             so that what the compiler reads back is the tree the kernel checked — so what is \
             outside the fragment here is an OPERAND, not the operator. Each decision operand \
             must be a source parameter, an in-range `{carrier}` numeral, or ONE raw binary \
             operator ({operators}) over two such leaves{operand_rules}; each ARM must be a \
             parameter or an in-range numeral. Three shapes elaborate and kernel-check here and \
             are still refused, each for a realization reason and none for a decidability one: \
             a NESTED operand (`((a &&& b) ||| 1) == 0`) needs a deeper statement chain; a \
             WRAPPING operand (`(a + 1) == 0`) needs a `Call` TERMINATOR, which splits the block \
             the decision and its lift share; and a COMPUTED ARM (`if a == b then a &&& 1 else \
             b`) needs either that same extra block or a hoist that evaluates a branch your \
             declaration does not take."
        ),
        BoolDecisionSpelling::NotEqual => format!(
            "It is not the propositional equality `Eq {carrier} a b` that the `select.eq` row is \
             stated over, and it is not the `Bool`-decision equality the `select.beq` row is \
             stated over either: those two are NOT definitionally equal (the kernel refuses even \
             `rfl` between them), and this is a THIRD tree — the `==` decision with a `Bool.not` \
             wrapped around it. The negation lives in the DECISION, not in the scrutinee, so it \
             is not reachable by flipping the lift's constant: `(a == b) = false` IS emitted \
             since §6f landing 8, and the kernel refuses `rfl` between IT and this tree too \
             (measured, `landing8_selection_probes::l8_p2`) — they are two terms, not two \
             spellings. Admitting this one needs a negation at three layers that have none: the \
             emitted realization vocabulary (`materialize::TemplateRvalue` has no unary rvalue), \
             the reader that reads it back, and the producer that reflects it."
        ),
    };
    let first_option = match spelling {
        BoolDecisionSpelling::Equal => format!(
            "- restate the out-of-fragment position as a parameter, an in-range numeral, or a \
             single one of {operators} over two of those{operand_rules} — `if a == b then a \
             else 0`, `if a == 10 then a else b` and `if (a &&& 1) == 0 then a else b` are all \
             emitted and kernel-gated at u8/u16/u32/u64;"
        ),
        BoolDecisionSpelling::NotEqual => {
            "- restate the disequality as `if (a == b) = false then <then> else <else>`, which \
             IS emitted and kernel-gated at u8/u16/u32/u64 since §6f landing 8 — the arms stay \
             in the order you wrote them, because the polarity is carried by the lift's \
             constant and never by swapping them. Or restate the branch positively — \
             `if a = b then <else-value> else <then-value>` — which elaborates to `Eq` at the \
             carrier and selects the `select.eq` row;"
                .to_owned()
        }
    };
    format!(
        "its branch condition is written with {operator}, which is a `Bool`-level DECISION \
         lifted back to a proposition — {kernel_shape}. {diagnosis} This is a measured boundary \
         of the compiler, not a rule about what you may write (ruling v7/D2); the work item is \
         `docs/design/2026-08-04-two-language-compiler-architecture.md` §6f landing 6 (the row \
         and its realization) as extended by §6f landing 8 (the computed operand and the lift's \
         polarity), whose side-B producers \
         (`trust_spec_elab::admit_select_beq_function` and \
         `admit_select_beq_operands_function`) are already kernel-measured against these exact \
         trees.\n\
         options:\n\
         {first_option}\n\
         - cite the declaration from a contract instead of calling it — proof position needs no \
           emitted body and has no shape restriction;\n\
         - write the computation as a Rust `fn` and prove it agrees with the declaration in an \
           `ensures` clause, which is the same guarantee reached from the other side."
    )
}

/// The raw-binop vocabulary in the user's syntax — the operator list, and the
/// operand rules that restrict it as a parenthetical (empty when no row
/// carries a rule) — DERIVED from [`table::raw_binop_rows`], which is exactly
/// what BOTH raw-binop readers read: [`recognise_raw_binop_expr`] (the whole
/// body) and [`recognise_raw_binop_leaf`] (the `==` decision operand).
///
/// Every refusal text that LISTS the family reads it from here — the `==`
/// boundary ([`beq_boundary_reason`]), the generic fall-through in
/// [`recognise_clean_shape`], and [`EmitRefusal::note`]'s "callable fragment"
/// paragraph — so none of them can name an operator no row serves, or omit
/// one a row does: adding or removing a row moves every text with it. Each
/// rule is read from the operator's own predicate
/// ([`RawBinOpKind::panics_at_zero_right_operand`],
/// [`RawBinOpKind::right_operand_is_a_shift_amount`]), the same predicates
/// both recognisers enforce. `landing7_selection_probes::l7_p15` and `l7_p16`
/// compare each text's list with an independently written one.
fn raw_binop_vocabulary() -> (String, String) {
    let ops: Vec<RawBinOpKind> =
        table::raw_binop_rows(table::CarrierClass::MachineUInt).map(|(_, op)| op).collect();
    let quoted = |filter: &dyn Fn(RawBinOpKind) -> bool, separator: &str| {
        ops.iter()
            .copied()
            .filter(|op| filter(*op))
            .map(|op| format!("`{}`", table::raw_binop_surface_token(op)))
            .collect::<Vec<_>>()
            .join(separator)
    };
    let operators = quoted(&|_| true, ", ");
    let mut rules = Vec::new();
    let divisors = quoted(&RawBinOpKind::panics_at_zero_right_operand, " or ");
    if !divisors.is_empty() {
        rules.push(format!("a {divisors} divisor must be a strictly positive numeral"));
    }
    let shifts = quoted(&RawBinOpKind::right_operand_is_a_shift_amount, " or ");
    if !shifts.is_empty() {
        rules.push(format!("a {shifts} amount must be a numeral below the width"));
    }
    let rules = if rules.is_empty() { String::new() } else { format!(" ({})", rules.join("; ")) };
    (operators, rules)
}

/// The `toNat` PROJECTION CHAIN the real elaborator spells for a `UIntN`
/// parameter when it resolves a literal comparison's decidability by
/// reduction to `Nat`:
///
/// ```text
/// Proj Fin 0 (Proj BitVec 0 (Proj {C} 0 (BVar k)))     -- ((x.toBitVec).toFin).val
/// ```
///
/// Measured 2026-08-21 on the elaborated `if a < 10 then a else b` (the C9
/// driver-level spelling gap): the crate probes hand-built the carrier
/// instance and admitted, but the REAL island elaboration of every Clean pin
/// before `c91fa93f5` never produced it for a literal comparison — this chain
/// under `instDecidableNatLt` is what arrived. (From `c91fa93f5` on, the
/// carrier instance IS what arrives; see [`carrier_instance_numeral`]. Both
/// are read, so the reading does not depend on the pin.) Matched exactly,
/// fail-closed: three projections, all at field 0, in this order, over a
/// bound parameter.
fn to_nat_projection_param(expr: &Expr, carrier: &str, arity: usize) -> Option<usize> {
    let ExprKind::Proj(fin, 0, inner) = strip_mdata(expr).kind() else {
        return None;
    };
    if !name_display_eq_str(fin, "Fin") {
        return None;
    }
    let ExprKind::Proj(bitvec, 0, inner) = strip_mdata(inner).kind() else {
        return None;
    };
    if !name_display_eq_str(bitvec, "BitVec") {
        return None;
    }
    let ExprKind::Proj(c, 0, inner) = strip_mdata(inner).kind() else {
        return None;
    };
    if !name_display_eq_str(c, carrier) {
        return None;
    }
    match strip_mdata(inner).kind() {
        &ExprKind::BVar(index) if (index as usize) < arity => Some(arity - 1 - index as usize),
        _ => None,
    }
}

/// The RIGHT operand of a CARRIER decision instance for a literal comparison
/// (`instDecidable{C}Lt a <operand>`), read as the numeral it spells — or
/// `None`.
///
/// Measured 2026-09-23 at the superproject's Clean pin `dca882b5f`, the first
/// to carry Clean `c91fa93f5`: for `if a < 10 then a else b` the island
/// elaborates the PROPOSITION's right operand as the carrier numeral
/// `UInt64.ofNat 10`, but the INSTANCE's right operand as that same numeral
/// unfolded one δβ step — the value `clean-kernel`'s `init_uint_type` gives
/// `{C}.ofNat`, applied to the literal:
///
/// ```text
/// {C}.ofBitVec (BitVec.ofFin (@OfNat.ofNat.{0} Nat w (instOfNatNat w))
///                            (@Fin.ofNat (2^w - 1) LIT))
/// ```
///
/// identically at UInt8/16/32/64 (`Fin.ofNat {n} a : Fin (n + 1)` is
/// `a % (n + 1)`, so the modulus is `2^w`). The two numeral spellings
/// [`numeral_leaf`] reads are accepted as well, so an instance applied to the
/// proposition's own operand term reads too.
///
/// Read EXACTLY, fail-closed: THIS carrier's `ofBitVec` constructor, THIS
/// carrier's width `w` (the width literal is read through
/// [`read_nat_numeral`]; the kernel already typed side A, which pins it to
/// `w` anyway), the modulus predecessor `2^w - 1` as a bare literal, and the
/// value as a bare `Nat` literal. The reading is the RAW literal — the same
/// convention [`numeral_leaf`] applies to the proposition's operand — and the
/// modular reduction is NEVER performed here: `Fin.ofNat (2^w - 1) (2^w + 10)`,
/// which the kernel reduces to `10`, does not read as `10`, so it fails to
/// match the proposition's `10` and the tree falls to the fragment refusal
/// (fail-closed costs capability, never soundness); a fitting but over-width
/// raw value that does match reaches the plan-time range re-check, which
/// refuses it by name.
fn carrier_instance_numeral(expr: &Expr, carrier: &str, width: u32) -> Option<NatReading> {
    if let Some(reading) = numeral_leaf(expr, carrier) {
        return Some(reading);
    }
    // `2^w - 1`, fail-closed on a width no machine carrier has.
    let modulus_pred = 1u128.checked_shl(width)?.checked_sub(1)?;
    let is_const = |node: &Expr, name: &str| {
        matches!(strip_mdata(node).kind(), ExprKind::Const(n, levels)
            if name_display_eq_str(n, name) && levels.is_empty())
    };
    let (ctor, ctor_args) = uncurry(expr);
    let [bitvec] = ctor_args[..] else {
        return None;
    };
    let ctor_ok = matches!(strip_mdata(ctor).kind(), ExprKind::Const(n, levels)
        if levels.is_empty()
            && (name_eq2(n, carrier, "ofBitVec")
                || matches!(n.inner(), NameInner::Str(p, s)
                    if p.is_anon()
                        && s.strip_prefix(carrier)
                            .and_then(|r| r.strip_prefix('.'))
                            == Some("ofBitVec"))));
    if !ctor_ok {
        return None;
    }
    let (of_fin, of_fin_args) = uncurry(bitvec);
    let [bitvec_width, fin] = of_fin_args[..] else {
        return None;
    };
    if !is_const(of_fin, "BitVec.ofFin")
        || read_nat_numeral(bitvec_width) != Some(NatReading::Fits(u128::from(width)))
    {
        return None;
    }
    let (fin_of_nat, fin_args) = uncurry(fin);
    let [pred, literal] = fin_args[..] else {
        return None;
    };
    if !is_const(fin_of_nat, "Fin.ofNat")
        || nat_literal(pred) != Some(NatReading::Fits(modulus_pred))
    {
        return None;
    }
    nat_literal(literal)
}

/// Uncurry an application spine, stripping metadata between every node:
/// `((f a) b)` becomes `(f, [a, b])`. Head and arguments are all
/// `strip_mdata`'d, for the same reason `strip_mdata` itself exists: an
/// elaborator annotation must not take a definition out of the fragment.
fn uncurry(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut cursor = strip_mdata(expr);
    let mut args = Vec::new();
    while let ExprKind::App(function, argument) = cursor.kind() {
        args.push(strip_mdata(argument));
        cursor = strip_mdata(function);
    }
    args.reverse();
    (cursor, args)
}

#[inline]
fn spine_head(expr: &Expr) -> &Expr {
    let mut cursor = strip_mdata(expr);
    while let ExprKind::App(function, _) = cursor.kind() {
        cursor = strip_mdata(function);
    }
    cursor
}

#[inline]
fn name_eq1(name: &Name, s0: &str) -> bool {
    matches!(name.inner(), NameInner::Str(parent, s) if parent.is_anon() && s.as_ref() == s0)
}

#[inline]
fn name_eq2(name: &Name, s0: &str, s1: &str) -> bool {
    matches!(
        name.inner(),
        NameInner::Str(parent, seg1)
            if seg1.as_ref() == s1
                && matches!(
                    parent.inner(),
                    NameInner::Str(root, seg0) if root.is_anon() && seg0.as_ref() == s0
                )
    )
}

#[inline]
fn name_eq_str(mut name: &Name, expected: &str) -> bool {
    if expected.is_empty() || expected == "[anonymous]" {
        return name.is_anon();
    }
    for part in expected.rsplit('.') {
        if part.is_empty() {
            continue;
        }
        match (name.inner(), part.parse::<u64>()) {
            (NameInner::Num(parent, n), Ok(num)) if *n == num => {
                name = parent;
            }
            (NameInner::Str(parent, s), Err(_)) if s.as_ref() == part => {
                name = parent;
            }
            _ => return false,
        }
    }
    name.is_anon()
}

#[inline]
fn name_display_eq_str(name: &Name, expected: &str) -> bool {
    name_eq_str(name, expected)
        || matches!(name.inner(), NameInner::Str(parent, s) if parent.is_anon() && s.as_ref() == expected)
}

/// The prelude classes whose homogeneous dictionary Clean may also spell
/// through Lean's `@[default_instance]` bridge, with the homogeneous class
/// the bridge takes as its premise.
///
/// Only `>>>` is here. Since clean `d2d5868b7` (2026-11-10, "require genuine
/// homogeneous premises for shift numeral defaults") Clean resolves a NUMERAL
/// shift amount's dictionary the way Lean does: `a >>> 3` elaborates through
/// `instance [ShiftRight α] : HShiftRight α α α` applied to the prelude's own
/// `instShiftRight{C}`, while `a >>> b` keeps the direct `instHShiftRight{C}`
/// (`l7_p11` pins both). `<<<` takes the same bridge, but no raw-binop row
/// serves it (its demand is `Missing` in `table.rs`), so its bridge is not
/// admitted here: a widening is an increment with a probe.
const PRELUDE_DEFAULT_INSTANCE_BRIDGES: [(&str, &str); 1] = [("HShiftRight", "ShiftRight")];

/// Whether `instance` is the prelude's homogeneous `{class}` dictionary at
/// `carrier`, in one of the two spellings the pinned elaborator produces:
///
/// * `inst{class}{carrier}`, the instance Clean registers directly at
///   `{class} C C C`; or
/// * for a class in [`PRELUDE_DEFAULT_INSTANCE_BRIDGES`] only,
///   `@inst{class}.{0} {carrier} inst{premise}{carrier}`: the default bridge
///   applied to the prelude's own homogeneous instance.
///
/// Every other dictionary term is refused, as before: a user instance, a
/// namespaced name, the bridge over a user `ShiftRight` instance, at another
/// carrier or another universe. This is the capability fence, not the proof.
/// Side B is built from the emitted MIR alone, and the kernel still decides
/// definitional equality against side A's own term.
fn is_prelude_homogeneous_instance(instance: &Expr, class: &str, carrier: &str) -> bool {
    if matches!(instance.kind(), ExprKind::Const(n, _) if name_eq1_concat(n, &["inst", class, carrier]))
    {
        return true;
    }
    let Some(&(_, premise)) =
        PRELUDE_DEFAULT_INSTANCE_BRIDGES.iter().find(|(bridged, _)| *bridged == class)
    else {
        return false;
    };
    let (head, args) = uncurry(instance);
    let ExprKind::Const(bridge, levels) = head.kind() else {
        return false;
    };
    let [carrier_arg, dictionary] = args[..] else {
        return false;
    };
    name_eq1_concat(bridge, &["inst", class])
        && levels.len() == 1
        && levels[0].is_zero()
        && matches!(carrier_arg.kind(), ExprKind::Const(n, l) if l.is_empty() && name_eq_str(n, carrier))
        && matches!(dictionary.kind(), ExprKind::Const(n, l)
            if l.is_empty() && name_eq1_concat(n, &["inst", premise, carrier]))
}

/// The v7/D3 refusal for a raw or wrapping operator whose dictionary is not
/// one [`is_prelude_homogeneous_instance`] accepts.
fn non_prelude_instance_reason(class: &str, projection: &str, carrier: &str) -> String {
    let expected = match PRELUDE_DEFAULT_INSTANCE_BRIDGES.iter().find(|(c, _)| *c == class) {
        Some((_, premise)) => format!(
            "`inst{class}{carrier}` (or its default-instance bridge `inst{class}` over the \
             prelude's `inst{premise}{carrier}`)"
        ),
        None => format!("`inst{class}{carrier}`"),
    };
    format!(
        "its `{class}.{projection}` at `{carrier}` routes through an instance other than the \
         prelude's homogeneous {expected}; only the prelude instance is in the measured \
         emittable fragment (a user instance may be kernel-reducible to it, but the compiler \
         will not guess — spell the op so it elaborates through the prelude instance, or keep \
         the definition for proof position)"
    )
}

#[inline]
fn name_eq1_concat(name: &Name, parts: &[&str]) -> bool {
    let NameInner::Str(parent, s) = name.inner() else {
        return false;
    };
    if !parent.is_anon() {
        return false;
    }
    let mut rem = s.as_ref();
    for &part in parts {
        let Some(next) = rem.strip_prefix(part) else {
            return false;
        };
        rem = next;
    }
    rem.is_empty()
}

#[inline]
fn name_ends_with_of_nat(name: &Name) -> bool {
    matches!(
        name.inner(),
        NameInner::Str(parent, s)
            if (!parent.is_anon() && s.as_ref() == "ofNat") || s.ends_with(".ofNat")
    )
}

#[inline]
fn uint_carrier_name(width: u32) -> Option<&'static str> {
    match width {
        8 => Some("UInt8"),
        16 => Some("UInt16"),
        32 => Some("UInt32"),
        64 => Some("UInt64"),
        128 => Some("UInt128"),
        _ => None,
    }
}

/// Attempt to read a fully-peeled body as a wrapping-arithmetic expression at
/// the signature's result carrier: a single binary op ([`CleanOriginShape::WrappingBinOp`])
/// or a nested tree of them ([`CleanOriginShape::Composed`]). Exactly the two
/// spellings the kernel probes measured, at every node
/// (`fragment_widening_probes.rs` a/a2/b/c/d, a4–a6, and probe_f for nesting):
///
/// * **carrier:** `{C}.add|sub|mul lhs rhs`;
/// * **surface:** `H{Add,Sub,Mul}.h{add,sub,mul} {C} {C} {C} instH{…}{C} lhs rhs`
///   with the instance constant EXACTLY the prelude's homogeneous instance.
///
/// Returns `Ok(Some(shape))` on a match; `Ok(None)` when the body is not a
/// wrapping-op spine at all — including a BARE numeral body, which parses as
/// a leaf but is not an op — so the caller falls through to the generic
/// fragment refusal (this is what keeps `fun a => 6` refused, probe_e3's
/// boundary); `Err(refusal)` when a spine WAS matched but is outside the
/// fragment for a specific, user-fixable reason — an out-of-range numeral, a
/// non-prelude instance, or more than [`COMPOSED_MAX_OPS`] nodes — so the
/// refusal can name the exact boundary. A user-defined instance constant is
/// well-typed, kernel-reducible, and would even pass defeq; it is refused
/// HERE so it surfaces as a *capability* refusal rather than tunneling into
/// the internal-error family.
fn recognise_wrapping_expr(
    name: &str,
    body: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    // The wrapping-op fragment exists only at an unsigned machine width; for
    // any other result carrier there is no `{C}.add` family to match.
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let Some(carrier_name) = uint_carrier_name(width) else {
        return Ok(None);
    };

    let mut ops = 0usize;
    let Some(tree) = recognise_arith_tree(name, body, arity, carrier_name, width, &mut ops)? else {
        return Ok(None);
    };
    match tree {
        // A bare leaf body (`fun a => 6`). Not an op: fall through to the
        // generic refusal, keeping the ConstantUint boundary exactly where it
        // was. (A bare BVar body never reaches here — the Projection arm of
        // `recognise_clean_shape` consumed it.)
        ArithExpr::Operand(_) => Ok(None),
        ArithExpr::Bin { op, left, right } => match (*left, *right) {
            // One op over two leaves: the single-op shape, unchanged — its
            // emitter, its structural comparison and its rendering all stay
            // exactly as landed 2026-08-19.
            (ArithExpr::Operand(left), ArithExpr::Operand(right)) => {
                Ok(Some(CleanOriginShape::WrappingBinOp { op, left, right }))
            }
            // Anything nested: the composed tree.
            (left, right) => Ok(Some(CleanOriginShape::Composed {
                expr: ArithExpr::Bin { op, left: Box::new(left), right: Box::new(right) },
            })),
        },
    }
}

/// One node of the recursive wrapping-expression read: a leaf (via the
/// unchanged [`recognise_arith_operand`]) or an op spine in either measured
/// spelling, its operands read by recursion. `ops` counts binop nodes and
/// refuses past [`COMPOSED_MAX_OPS`] — the count bounds the recursion depth,
/// so an adversarially deep Clean term refuses instead of exhausting the
/// stack.
fn recognise_arith_tree(
    name: &str,
    expr: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
    ops: &mut usize,
) -> Result<Option<ArithExpr>, EmitRefusal> {
    // Leaves first: a bound parameter or an in-range numeral. The leaf heads
    // (`BVar`, `{C}.ofNat`, `OfNat.ofNat`) are disjoint from the op heads, so
    // the order here is not a tiebreak.
    if let Some(leaf) = recognise_arith_operand(name, expr, arity, carrier_name, width)? {
        return Ok(Some(ArithExpr::Operand(leaf)));
    }

    let (head, args) = uncurry(expr);
    let ExprKind::Const(head_name, _levels) = head.kind() else {
        return Ok(None);
    };

    // ── carrier spelling: `{C}.op lhs rhs` ──────────────────────────────────
    //
    // §6f landing 1: the op vocabulary is READ FROM THE TABLE. It used to be
    // the literal `[("add", Add), ("sub", Sub), ("mul", Mul)]` right here, and
    // its twin below was the `HAdd`/`HSub`/`HMul` triple — the two inlined
    // tables the ruling's "one table, one descent" is about. The DATAFLOW
    // (uncurrying, the operand recursion, the op budget) stays exactly where it
    // was: the table selects vocabulary, this descent owns structure.
    for (selected, op) in table::arith_operator_rows(table::CarrierClass::MachineUInt) {
        let Some(suffix) = table::carrier_method_suffix(selected) else {
            continue;
        };
        if !name_eq2(head_name, carrier_name, suffix) {
            continue;
        }
        let [lhs, rhs] = args[..] else {
            return Ok(None);
        };
        return recognise_arith_node(name, op, lhs, rhs, arity, carrier_name, width, ops);
    }

    // ── surface spelling: `HAdd.hAdd {C} {C} {C} instHAdd{C} lhs rhs` ───────
    for (selected, op) in table::arith_operator_rows(table::CarrierClass::MachineUInt) {
        let Some((class, projection)) = table::surface_class(selected) else {
            continue;
        };
        if !name_eq2(head_name, class, projection) {
            continue;
        }
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let is_carrier =
            |t: &Expr| matches!(t.kind(), ExprKind::Const(n, _) if name_eq_str(n, carrier_name));
        if !(is_carrier(t1) && is_carrier(t2) && is_carrier(t3)) {
            // A heterogeneous instantiation. Outside both measured spellings;
            // fall through to the generic fragment refusal.
            return Ok(None);
        }
        if !is_prelude_homogeneous_instance(instance, class, carrier_name) {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: non_prelude_instance_reason(class, projection, carrier_name),
            });
        }
        return recognise_arith_node(name, op, lhs, rhs, arity, carrier_name, width, ops);
    }

    Ok(None)
}

/// A matched op spine's node: bump the count against the measured cap, then
/// read both operands by recursion.
#[allow(clippy::too_many_arguments)]
fn recognise_arith_node(
    name: &str,
    op: ArithBinOp,
    lhs: &Expr,
    rhs: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
    ops: &mut usize,
) -> Result<Option<ArithExpr>, EmitRefusal> {
    *ops += 1;
    if *ops > COMPOSED_MAX_OPS {
        return Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: composed_ops_out_of_range_reason(*ops),
        });
    }
    let (Some(left), Some(right)) = (
        recognise_arith_tree(name, lhs, arity, carrier_name, width, ops)?,
        recognise_arith_tree(name, rhs, arity, carrier_name, width, ops)?,
    ) else {
        return Ok(None);
    };
    Ok(Some(ArithExpr::Bin { op, left: Box::new(left), right: Box::new(right) }))
}

/// **§6f LANDING 7 — the RAW-BINOP spine.** `fun x0 … x_{n-1} => xl <op> xr`
/// for `<op>` one of the raw-binop rows' operators at an unsigned machine
/// width — `&&&`, `|||`, `/`, `%` since landing 7, `^^^` and `>>>` since clean
/// `bf31976f48` (the set is read from `table::raw_binop_rows`, never from this
/// comment).
///
/// Side A carries ONE spelling — the homogeneous SURFACE class at the prelude
/// instance:
///
/// ```text
/// H{And,Or,Div,Mod,Xor,ShiftRight}.h{…}.{0,0,0} {C} {C} {C} instH{…}{C} lhs rhs
/// ```
///
/// and that is a MEASUREMENT, not a narrowing. At the clean pin `bad1fd5f8` a
/// real island `a &&& b` produces exactly this and nothing else, at all four
/// widths (`landing7_selection_probes::l7_p1`); the carrier method
/// `UInt{N}.land` is a declared constant now but no source emits it, and side
/// B renders the `toNat`/`ofNat` round trip rather than the carrier method
/// either — so a `CarrierMethod` selector would be a reader arm for a spelling
/// NEITHER side produces, which is the defect class `control_14`'s spelling
/// grain exists to catch.
///
/// # NOT NESTED, and the reason is the realization
///
/// Both operands are LEAVES ([`recognise_arith_operand`]'s vocabulary: a bound
/// parameter or an in-range numeral). A nested tree is measured green at the
/// KERNEL (`l7_p9`: `(a &&& b) ||| a` and `(a + b) &&& a` both ADMIT) and has
/// no emitted realization, because the wrapping family composes as a CALL
/// CHAIN and this family as a single STATEMENT — so a mixed tree is a fifth
/// skeleton, not a deeper recursion. It is a ranked MISS with that measurement
/// attached, deliberately not a fall-through here.
///
/// # THE DIVISOR RULE
///
/// For `/` and `%` the right operand must be a **strictly positive numeral**.
/// Clean's `UInt{N}.div`/`.mod` are TOTAL — GROUND `7 / 0` reduces to `0` and
/// `7 % 0` to `7` (`l7_p6`) — while Rust's `/`/`%` PANIC, so a variable or
/// zero divisor would emit a body that computes a DIFFERENT function from the
/// declaration on exactly the input nothing tests. Both are refused here
/// with a v7/D3 note that names the gap and the options, and refused again
/// independently on side B, where the FROZEN producer will not mint
/// `p0 / p1` or `p0 / 0` at all.
///
/// Returns `Ok(None)` when the body is not one of these four spines, so the
/// caller falls through to the recognizers after it and then to the generic
/// refusal; `Err` when a spine WAS matched but is outside the fragment for a
/// specific, user-fixable reason — a non-prelude instance, an out-of-range
/// numeral, or an unsafe divisor.
fn recognise_raw_binop_expr(
    name: &str,
    body: &Expr,
    arity: usize,
    signature: &CarrierSignature,
) -> Result<Option<CleanOriginShape>, EmitRefusal> {
    // Stated only at an unsigned machine width, exactly as the wrapping spine
    // is: for any other result carrier there is no `H*.h*` instance at the
    // carrier to match.
    let CleanType::UInt(width) = signature.result().clean() else {
        return Ok(None);
    };
    if !matches!(width, 8 | 16 | 32 | 64) {
        return Ok(None);
    }
    let Some(carrier_name) = uint_carrier_name(width) else {
        return Ok(None);
    };

    let (head, args) = uncurry(body);
    let ExprKind::Const(head_name, _levels) = head.kind() else {
        return Ok(None);
    };

    // The operator vocabulary is READ FROM THE TABLE, exactly as the wrapping
    // descent's is since landing 1 — the heads are a `raw_binop_rows`
    // filter, never a literal in this function.
    for (selected, op) in table::raw_binop_rows(table::CarrierClass::MachineUInt) {
        let Some((class, projection)) = table::surface_class(selected) else {
            continue;
        };
        if !name_eq2(head_name, class, projection) {
            continue;
        }
        let [t1, t2, t3, instance, lhs, rhs] = args[..] else {
            return Ok(None);
        };
        let is_carrier =
            |t: &Expr| matches!(t.kind(), ExprKind::Const(n, _) if name_eq_str(n, carrier_name));
        if !(is_carrier(t1) && is_carrier(t2) && is_carrier(t3)) {
            // A heterogeneous instantiation. Outside the measured spelling;
            // fall through to the generic fragment refusal.
            return Ok(None);
        }
        if !is_prelude_homogeneous_instance(instance, class, carrier_name) {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: non_prelude_instance_reason(class, projection, carrier_name),
            });
        }
        let (Some(left), Some(right)) = (
            recognise_arith_operand(name, lhs, arity, carrier_name, width)?,
            recognise_arith_operand(name, rhs, arity, carrier_name, width)?,
        ) else {
            // A nested spine, or an operand outside the leaf vocabulary. Not a
            // shape this row realizes; the generic refusal names the boundary,
            // and `l7_p9` is the measurement behind the MISS entry.
            return Ok(None);
        };
        if op.panics_at_zero_right_operand() {
            match right {
                ArithOperand::Const(divisor) if divisor > 0 => {}
                _ => {
                    return Err(EmitRefusal::NotEmittable {
                        name: name.to_owned(),
                        reason: unsafe_divisor_reason(class, projection, right),
                    });
                }
            }
        }
        // THE SHIFT-AMOUNT RULE. Not a soundness rule — MIR `Shr` and Lean's
        // `{C}.shiftRight` both reduce the amount modulo the width, so no
        // amount is a wrong binary — but a CAPABILITY one: the frozen producer
        // mints side B only for a literal amount strictly below the width, and
        // a plan it cannot reflect is refused here, with the user's options,
        // rather than at the gate with the producer's.
        if op.right_operand_is_a_shift_amount() && !shift_amount_has_a_side_b(right, width) {
            return Err(EmitRefusal::NotEmittable {
                name: name.to_owned(),
                reason: shift_amount_reason(class, projection, right, width),
            });
        }
        return Ok(Some(CleanOriginShape::RawBinOp { op, left, right }));
    }

    Ok(None)
}

/// **Ruling v7/D3, on the one refusal in this file whose subject is SOUNDNESS.**
///
/// Clean's `UInt{N}.div`/`.mod` are TOTAL and Rust's `/`/`%` PANIC. The text
/// says so in the user's terms, states the kernel VALUES rather than alluding
/// to them, and gives options — including the one the measurement makes
/// concrete for `/` and explicitly WITHHOLDS for `%`, because `a % 0` is not
/// definitionally the identity at an open `a` (measured: `l7_p6`).
///
/// # EVERY OPTION IS SPELLED IN THE OPERATOR THAT WAS REFUSED
///
/// The options used to be written as literal `/` text on both the `/` and the
/// `%` path, so a user who wrote `a % b` was told to write `a / 3` and
/// `if b == 0 then … else a / b`. Following that advice literally produces a
/// DIFFERENT function from the one they declared, which makes the refusal a
/// defect under v7/D3 rather than a fix: the ruling is that a refusal carries
/// the fix, and a fix that silently changes the program is not one. `{op}` and
/// `total_at_zero` are threaded through so the suggested guard's `then` arm
/// is the value the declaration ALREADY denotes at a zero divisor — `0` for
/// `/`, the dividend for `%` — and the guard therefore preserves meaning.
/// Pinned by `control_15::half_10`.
fn unsafe_divisor_reason(class: &str, projection: &str, right: ArithOperand) -> String {
    let (found, total_value, replacement) = match right {
        ArithOperand::Const(0) => (
            "a literal ZERO divisor".to_owned(),
            "So this declaration DENOTES a total function of its own",
            true,
        ),
        ArithOperand::Const(value) => {
            (format!("the numeral `{value}`, which this compiler read as out of range"), "", false)
        }
        ArithOperand::Param(index) => (
            format!("parameter {index}, a VARIABLE divisor"),
            "So the declaration is total for every divisor including zero",
            false,
        ),
    };
    let div = class == "HDiv";
    let (op, zero_case) = if div { ("/", "`x / 0 = 0`") } else { ("%", "`x % 0 = x`") };
    // The value the DECLARATION already returns at a zero divisor: `0` for `/`,
    // the dividend for `%`. The guard option below has to name it, because a
    // guard whose `then` arm is anything else is a DIFFERENT function from the
    // one the user wrote — a "fix" that silently changes the program is not a
    // fix (v7/D3).
    let total_at_zero = if div { "0" } else { "a" };
    // `total_value` is empty for an out-of-range numeral, where there is no
    // totality claim to make; the sentence has to close cleanly anyway.
    let totality_sentence = if total_value.is_empty() {
        "The compiler will not silently emit something else for it.".to_owned()
    } else {
        format!("{total_value}, and the compiler will not silently emit something else for it.")
    };
    let mut reason = format!(
        "its `{class}.{projection}` divisor is {found}, and this lane emits `{op}` ONLY at a \
         strictly positive numeral. The reason is a semantic gap, not a parser limit: Clean's \
         `{{C}}.div`/`.mod` are TOTAL — the kernel reduces {zero_case} at an OPEN dividend, \
         because `Nat.div`/`Nat.mod` recurse on the DIVISOR — while Rust's `{op}` PANICS at a \
         zero divisor. A `BinaryOp({op})` emitted for this declaration would therefore compute \
         a DIFFERENT function from the one you wrote, on exactly the input a test that never \
         divides by zero cannot see. {totality_sentence}\n\
         options:\n"
    );
    if replacement && div {
        reason.push_str(
            "         - write the value directly: this declaration is definitionally equal to \
             the constant `0`, which the compiler DOES emit (measured — the `uint.lit` row \
             admits it);\n",
        );
    }
    reason.push_str(&format!(
        "         - use a positive literal divisor instead (`a {op} 3`), which is emitted today \
         at every unsigned machine width;\n\
         \x20        - guard the divisor IN THE DECLARATION \
         (`if b == 0 then {total_at_zero} else a {op} b`) rather than expecting the compiler to \
         insert a guard: a guard the compiler adds is invisible to the kernel, and a guard you \
         write is part of the term the kernel checks. The `then` arm shown is the value your \
         declaration ALREADY returns at a zero divisor ({zero_case}), so this guard preserves \
         its meaning — any other `then` arm declares a different function. That shape is not \
         emittable YET — its `else` arm is a COMPUTED `ite` arm, a separate measured demand — \
         but it is the shape the fix takes;\n\
         \x20        - cite the declaration from a contract instead of calling it: proof \
         position needs no emitted body and has no divisor restriction."
    ));
    reason
}

/// **The shift-amount rule**: a `>>` is planned only at a NUMERAL amount
/// strictly below the carrier's width.
///
/// Stated once, and read by both raw-binop recognisers and both sealed-plan
/// checks. It has the divisor rule's SHAPE and not its REASON. Nothing about
/// the amount can make the emitted body compute a different function: MIR's
/// `BinOp::Shr` takes it as `RHS.rem_euclid(LHS::BITS)` and Lean's
/// `{C}.shiftRight` as `Nat.mod b.toNat N`, the same reduction. What the rule
/// tracks is side B: the frozen `elab_term` mints `x >> k` only for a literal
/// `k` below the width, so any other amount leaves the kernel nothing to
/// compare against (`landing7_selection_probes::l7_p14`).
fn shift_amount_has_a_side_b(amount: ArithOperand, width: u32) -> bool {
    matches!(amount, ArithOperand::Const(k) if k < u128::from(width))
}

/// **Ruling v7/D3, on the shift-amount rule.** Names the boundary as what it
/// is — a missing side B, not a semantic gap — so the user is not told their
/// program is wrong, and offers the fix that preserves meaning: for an
/// out-of-range literal the reduced amount `k % N` IS the declared function,
/// because Lean reduces the amount modulo the width.
///
/// It speaks of the EMITTED operation — MIR's `BinOp::Shr`, which reduces the
/// amount modulo the width and has no overflow case — and says so, because the
/// Rust SOURCE expression `a >> b` is a different operation at an amount of
/// `N` or more (it carries a debug-build overflow check), and a reader who
/// knows only the source operator would otherwise read "agree at every
/// amount" as false.
fn shift_amount_reason(class: &str, projection: &str, amount: ArithOperand, width: u32) -> String {
    let (found, reduced) = match amount {
        ArithOperand::Const(k) => (
            format!("the numeral `{k}`, which is not below the width {width}"),
            Some(k % u128::from(width)),
        ),
        ArithOperand::Param(index) => (format!("parameter {index}, a VARIABLE amount"), None),
    };
    let mut reason = format!(
        "its `{class}.{projection}` amount is {found}, and this lane emits the shift — a bare \
         MIR `Shr` operation — ONLY at a numeral amount strictly below the carrier's width. This \
         is a capability boundary of the compiler, not a problem with your program: Lean's `>>>` \
         at `UInt{width}` shifts by the amount modulo {width}, and so does the emitted MIR `Shr`, \
         which takes its amount as `RHS.rem_euclid({width})`, so the declaration and the emitted \
         operation AGREE at every amount. (That is the MIR operation, not the Rust source \
         expression `a >> b`, which carries a debug-build overflow check at an amount of \
         {width} or more; the emitted body has no such check and needs none.) What is missing \
         is the independent reflection the kernel checks the emitted body against — the frozen \
         producer mints a shift only at a literal amount below the width.\n\
         options:\n"
    );
    if let Some(reduced) = reduced {
        reason.push_str(&format!(
            "         - write the reduced amount (`a >>> {reduced}`): Lean reduces the amount \
             modulo {width}, so it is the SAME function, and it is emitted today;\n"
        ));
    }
    reason.push_str(
        "         - write the computation as a Rust `fn` and prove it agrees with the \
         declaration in an `ensures` clause;\n\
         \x20        - cite the declaration from a contract instead of calling it: proof \
         position needs no emitted body and has no shift-amount restriction.",
    );
    reason
}

/// Read one LEAF of a wrapping-arithmetic expression: a bound parameter, or
/// an in-range numeral in either measured spelling (`{C}.ofNat n`, or
/// `OfNat.ofNat {C} n (instOfNat{C} n)` with the two literals equal).
///
/// `Ok(None)` means "not a leaf this fragment covers" (a free variable, a
/// `let`, …) and the caller — [`recognise_arith_tree`] — goes on to try the
/// op spines, falling through to the generic refusal if nothing matches;
/// `Err` means a numeral WAS matched but does not fit the width.
fn recognise_arith_operand(
    name: &str,
    operand: &Expr,
    arity: usize,
    carrier_name: &str,
    width: u32,
) -> Result<Option<ArithOperand>, EmitRefusal> {
    if let &ExprKind::BVar(index) = operand.kind() {
        let index = index as usize;
        if index >= arity {
            // Loose under the peeled binders; the kernel would not have
            // accepted it. Fail closed through the generic refusal.
            return Ok(None);
        }
        // The same de Bruijn inversion the Projection arm documents — and the
        // mutation controls' favourite target.
        return Ok(Some(ArithOperand::Param(arity - 1 - index)));
    }

    match numeral_leaf(operand, carrier_name) {
        Some(value) => in_range_numeral(name, value, width).map(Some),
        None => Ok(None),
    }
}

/// Read a numeral in either measured spelling — carrier `{C}.ofNat n`, or
/// surface `OfNat.ofNat {C} n (instOfNat{C} n)` with the two literals equal —
/// WITHOUT a range check (each caller applies its own: `in_range_numeral` for
/// the arithmetic leaves; the plan-time re-check for the select literal).
/// `None` means "not a numeral in either spelling" and the caller falls
/// through to its next reading or the generic refusal.
fn numeral_leaf(operand: &Expr, carrier_name: &str) -> Option<NatReading> {
    let (head, args) = uncurry(operand);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };

    // ── carrier numeral: `{C}.ofNat n` ──────────────────────────────────────
    if name_eq2(head_name, carrier_name, "ofNat") {
        let [literal] = args[..] else {
            return None;
        };
        return nat_literal(literal);
    }

    // ── surface numeral: `OfNat.ofNat {C} n (instOfNat{C} n)` ───────────────
    if name_eq2(head_name, "OfNat", "ofNat") {
        let [ty, literal, instance] = args[..] else {
            return None;
        };
        if !matches!(ty.kind(), ExprKind::Const(n, _) if name_eq_str(n, carrier_name)) {
            return None;
        }
        let value = nat_literal(literal)?;
        let (instance_head, instance_args) = uncurry(instance);
        if !matches!(
            instance_head.kind(),
            ExprKind::Const(n, _) if name_eq1_concat(n, &["instOfNat", carrier_name])
        ) {
            return None;
        }
        let [instance_literal] = instance_args[..] else {
            return None;
        };
        if nat_literal(instance_literal) != Some(value) {
            return None;
        }
        return Some(value);
    }

    None
}

/// The value of a kernel `Nat` literal, when it fits `u128`. A multi-limb
/// literal reports `None` from `to_u64` and is treated by the caller as
/// out of range — which it is, for every machine width this lane admits.
fn nat_literal(expr: &Expr) -> Option<NatReading> {
    match expr.kind() {
        ExprKind::Lit(Literal::Nat(value)) => Some(match value.to_u64() {
            Some(small) => NatReading::Fits(u128::from(small)),
            None => NatReading::Oversized,
        }),
        _ => None,
    }
}

/// A `Nat` literal reading: either a value small enough to range-check, or a
/// multi-limb literal that is out of range for every admitted width.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NatReading {
    Fits(u128),
    Oversized,
}

/// Range-check a matched numeral against the carrier width, fail-closed.
fn in_range_numeral(
    name: &str,
    value: NatReading,
    width: u32,
) -> Result<ArithOperand, EmitRefusal> {
    match value {
        NatReading::Fits(value) if value <= max_uint_value(width) => Ok(ArithOperand::Const(value)),
        NatReading::Fits(value) => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: numeral_out_of_range_reason(value, width),
        }),
        NatReading::Oversized => Err(EmitRefusal::NotEmittable {
            name: name.to_owned(),
            reason: format!(
                "its numeral operand does not even fit u64, let alone the u{width} result \
                 carrier; restate the literal in range 0..2^{width} — the compiler will \
                 not silently reduce it modulo 2^{width}"
            ),
        }),
    }
}

/// The kernel HEAD of a term, spelled exactly when it is a constant.
///
/// This is the coordinate a [`table::SelectionRow`] is keyed on, so it is what
/// the whole-body refusal's row citation must carry (§6f landing 1, ruling
/// v7/D3) and what [`table::rows_selecting_head`] is asked about. For a
/// non-constant head it falls back to [`render_head`]'s category, which is
/// still a legible coordinate ("a lambda" has no row either, and no selector
/// is keyed on a category).
fn head_label(cursor: &Expr) -> String {
    let head = spine_head(cursor);
    match head.kind() {
        ExprKind::Const(name, _) => name.to_string(),
        other => render_head(other).to_owned(),
    }
}

/// The [`table::CarrierClass`] of a plan's RESULT carrier — the
/// [`table::CarrierAnchor::Result`] position, and the coordinate a TRUE row
/// miss is named at (`table::no_selection_row`).
///
/// This is the result-only reading this site used before any row was
/// consulted, restored verbatim: the no-row text must stay byte-identical,
/// carrier included. A `Bool` result is `AnyExact` HERE, whatever its
/// arguments; the rows whose class is a claim about another position — the
/// `comparison.*` rows (the compared width) and the `bool.*` rows (their `Bool`
/// operands) — are matched at THAT position by [`anchored_carriers`], row by
/// row, rather than by re-reading this one.
fn carrier_class_of(signature: &CarrierSignature) -> table::CarrierClass {
    carrier_class_of_type(signature.result().clean())
}

/// The [`table::CarrierClass`] a single Clean carrier falls in.
fn carrier_class_of_type(clean: CleanType) -> table::CarrierClass {
    match clean {
        CleanType::UInt(8 | 16 | 32 | 64) => table::CarrierClass::MachineUInt,
        CleanType::Nat => table::CarrierClass::BignumNat,
        _ => table::CarrierClass::AnyExact,
    }
}

/// The carrier class at each [`table::CarrierAnchor`] position of the body
/// whose head is `cursor` — what the whole-body refusal matches each row's own
/// position against (`table::rows_selecting_head`).
fn anchored_carriers(
    env: &Environment,
    cursor: &Expr,
    signature: &CarrierSignature,
) -> table::AnchoredCarriers {
    table::AnchoredCarriers {
        result: carrier_class_of(signature),
        compared_operands: compared_operand_carrier(cursor).map(carrier_class_of_type),
        head_operands: head_operand_carrier(env, cursor).map(carrier_class_of_type),
    }
}

/// The carrier a `Bool`-valued head's comparison is STATED AT — the
/// [`table::CarrierAnchor::ComparedOperands`] position.
///
/// It is the position [`recognise_decide_comparison`] checks against the
/// parameters' width: the type argument of the proposition under `decide`
/// (`LT.lt {C} …`, `Eq {C} …`), or `BEq.beq`'s own `{C}`. It is read here for
/// ANY relation stated at a carrier (`GT.gt {C}` and `GE.ge {C}` are what `a >
/// b` and `a >= b` elaborate to) because the relation is SHAPE — a comparison
/// the rows do not realize in that spelling is still a comparison at `{C}`, and
/// its refusal should say the head is served there. A proposition that is not
/// an application of a relation to a carrier type (`a ≠ b` elaborates to the
/// arrow `a = b → False`; a conjunction's first argument is a proposition)
/// has no such position, and `None` makes the comparison rows select nothing.
fn compared_operand_carrier(cursor: &Expr) -> Option<CleanType> {
    let (head, args) = uncurry(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    let stated_at = if name_display_eq_str(head_name, "decide")
        || name_display_eq_str(head_name, "Decidable.decide")
    {
        let (_relation, relation_args) = uncurry(args.first()?);
        *relation_args.first()?
    } else if name_display_eq_str(head_name, "BEq.beq") {
        *args.first()?
    } else {
        return None;
    };
    trust_clean_carrier::recognize(stated_at).filter(|clean| *clean != CleanType::Sort)
}

/// The carrier the head CONSTANT's explicit operands are declared at — the
/// [`table::CarrierAnchor::HeadOperands`] position — read from the constant's
/// kernel type, not from a list: `Bool.not : Bool → Bool` and `and`/`or :
/// Bool → Bool → Bool` (measured in the island prelude) give `Bool`.
///
/// `None` when the head is not a constant of the environment, has no explicit
/// binder, or its explicit binders do not all sit at ONE modeled carrier —
/// `decide`'s is a `Prop`, `BEq.beq`'s are the bound `α`.
fn head_operand_carrier(env: &Environment, cursor: &Expr) -> Option<CleanType> {
    let head = spine_head(cursor);
    let ExprKind::Const(head_name, _) = head.kind() else {
        return None;
    };
    let mut ty = &env.get_const(head_name)?.type_;
    let mut shared: Option<CleanType> = None;
    while let ExprKind::Pi(binder, domain, body) = strip_mdata(ty).kind() {
        if binder.info == clean_kernel::BinderInfo::Default {
            let clean = trust_clean_carrier::recognize(domain)?;
            if clean == CleanType::Sort || shared.is_some_and(|seen| seen != clean) {
                return None;
            }
            shared = Some(clean);
        }
        ty = body;
    }
    shared
}

/// The head constructor of an expression, for a diagnostic that names what was
/// found without dumping a whole term at the user.
/// Name the CONSTANT at the head of an application spine, for a refusal that
/// has to be true of the program in front of it (v7/D3).
///
/// [`render_head`] answers "what kind of node is this", which for an
/// application is the uninformative "an application" — the shape of every term
/// this fragment refuses. Where the useful fact is *which* constant is applied,
/// this says so, and falls back to `render_head` for a non-constant head.
fn render_spine_head(expr: &Expr) -> String {
    let head = spine_head(expr);
    match head.kind() {
        ExprKind::Const(name, _) => format!("`{name}`"),
        other => render_head(other).to_owned(),
    }
}

fn render_head(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::BVar(_) => "a bound variable",
        ExprKind::FVar(_) => "a free variable",
        ExprKind::Sort(_) => "a sort",
        ExprKind::Const(..) => "a constant",
        ExprKind::App(..) => "an application",
        ExprKind::Lam(..) => "a lambda",
        ExprKind::Pi(..) => "a function type",
        ExprKind::Let(..) => "a `let`",
        ExprKind::Lit(_) => "a literal",
        ExprKind::Proj(..) => "a projection out of a structure",
        ExprKind::MData(..) => "metadata",
        _ => "an expression outside the computational fragment",
    }
}

/// Strip transparent metadata wrappers. `MData` is invisible to type checking,
/// so it must be invisible to shape recognition too — otherwise an elaborator
/// that annotates a term would silently take a definition out of the fragment.
fn strip_mdata(expr: &Expr) -> &Expr {
    let mut cursor = expr;
    while let ExprKind::MData(_, inner) = cursor.kind() {
        cursor = inner;
    }
    cursor
}

/// The name side B is minted under while it is being reflected.
///
/// It is minted into a **clone** of the environment, so this name never enters
/// the crate's real Clean environment and can never be cited, called, or
/// collided with. The suffix is not a namespace separator (`.`) on purpose: a
/// dotted name would create a child of the declaration in the Clean namespace
/// tree, which is exactly the kind of visible side effect a check must not have.
fn reflection_name(name: &str) -> String {
    format!("{name}_trust_clean_origin_reflection")
}

/// **The round trip.** Put the body the compiler actually emitted to the gate.
///
/// `extracted` is the emitted `mir::Body` after
/// `trust_mir_extract::extract_function` — i.e. read back out of MIR, not the
/// plan and not anything this crate produced. It is passed as a
/// `trust_types::VerifiableFunction` rather than a `mir::Body` so that this
/// decision, like every other one in this crate, stays on the fast lane and can
/// be mutation-tested without a compiler.
///
/// The four checks, in order, each fail-closed:
///
/// 1. the emitted body must be recognised by
///    [`recognize_admissible_body`] — the compiler's own recognizer, unmodified;
/// 2. its recognised shape must be the PLANNED shape (a structural catch that
///    never substitutes for the kernel one);
/// 3. it must reflect back into a kernel term via
///    [`trust_spec_elab::admit_projection_function`] (projections),
///    [`trust_spec_elab::admit_expr_function`] (wrapping binops and composed
///    trees, over the recognizer's own rendering — bare for a single op,
///    fully parenthesized for a tree),
///    [`trust_spec_elab::admit_select_function`] (parameter selects) or
///    [`trust_spec_elab::admit_select_literal_function`] (select-vs-literal,
///    R2/C9) — each FULL-KERNEL-CHECKS the reflected defining equation;
/// 4. the kernel must identify that term with side A —
///    [`crate::gate::check_faithful`], **at the carrier type**.
///
/// # Errors
///
/// Any of [`EmitRefusal`]'s side-B variants. There is no degraded mode: a body
/// that does not reach step 4 clean is not emitted.
pub fn admit_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // ── R1: the structural-recursion route (§6e as amended) ────────────────
    //
    // A recursive emission never reaches the `recognize_admissible_body`
    // chain: that chain feeds the E6 kernel-import direction too, and a
    // recursive body must stay invisible there (see
    // `recognize_structural_rec`'s separate-entry-point note). The route is
    // the same four steps in the same order, with the per-defining-equation
    // gate in step 4's seat.
    if let CleanOriginShape::StructuralNatRec { base, step, rec_arg } = &plan.shape {
        return admit_structural_rec_lowering(env, plan, extracted, base, step, rec_arg);
    }
    // ── R2: the well-founded route (§6e MEASUREMENT NOTE + ESCAPE CLOSED) ──
    //
    // Same accounting as R1's arm: a recursive emission never reaches the
    // `recognize_admissible_body` chain, because that chain also feeds the E6
    // kernel-import direction where a recognized body becomes a defining
    // equation with no side A and no kernel gate.
    if let CleanOriginShape::WellFoundedNatRec {
        zero_value,
        nonzero_value,
        rec_args,
        measure_index,
        lowering,
    } = &plan.shape
    {
        return admit_wf_rec_lowering(
            env,
            plan,
            extracted,
            zero_value,
            nonzero_value,
            rec_args,
            *measure_index,
            *lowering,
        );
    }
    // ── §6f LANDING 3: the general select ──────────────────────────────────
    //
    // Same accounting as R1's and R2's arms, and for the SAME reason: a
    // constant-arm emission never reaches the `recognize_admissible_body`
    // chain, because that chain also feeds the E6 kernel-import direction
    // (`trust_certify::clean_island::admit_function_into`) where a recognized
    // body becomes a defining equation with no side A and no kernel gate.
    // Landing 3 measured that the coupling is MECHANICAL — that dispatch
    // matches `AdmissibleBody` exhaustively, so a reader widening spelled as a
    // variant cannot be CALL-only — which is exactly why the capability is
    // reached through `recognize_select_general`, a separate entry point, and
    // why `landing3_selection_probes::l3_p2` pins that the same body still
    // reads back as `None` from the chain.
    if let CleanOriginShape::SelectOperands { cmp, cmp_left, cmp_right, then_arm, else_arm } =
        &plan.shape
    {
        return admit_general_select_lowering(
            env, plan, extracted, *cmp, *cmp_left, *cmp_right, *then_arm, *else_arm,
        );
    }
    // ── §6f LANDING 6: the `==` select ─────────────────────────────────────
    //
    // Same accounting as every arm above, for the SAME reason: the two-step
    // diamond never reaches the `recognize_admissible_body` chain, because that
    // chain also feeds the E6 kernel-import direction
    // (`trust_certify::clean_island::admit_function_into`) where a recognized
    // body becomes a defining equation with no side A and no kernel gate.
    // Landing 3 measured that the coupling is MECHANICAL — that dispatch
    // matches `AdmissibleBody` exhaustively, so a reader widening spelled as a
    // variant cannot be CALL-only — which is why the capability is reached
    // through `recognize_select_beq`, a separate entry point, and why
    // `landing6_selection_probes::l6_p3` pins that the same body still reads
    // back as `None` from the chain AND from `recognize_select_general`.
    if let CleanOriginShape::SelectBeq { cmp_left, cmp_right, then_arm, else_arm } = &plan.shape {
        return admit_beq_select_lowering(
            env, plan, extracted, *cmp_left, *cmp_right, *then_arm, *else_arm,
        );
    }
    // ── §6f LANDING 8: the GENERAL `==` select ─────────────────────────────
    //
    // Same accounting as every arm above, for the SAME reason, and it binds
    // twice here: the reading is produced only by `recognize_select_beq_general`
    // — a separate entry point — AND it carries the RAW-BINOP spelling whose
    // exclusion from `recognize_admissible_body` is the pinned provenance
    // boundary `binop_provenance_pins_never_admit` states. `l8_p5` measures
    // that the emitted bodies still read back as `None` from the chain, from
    // `recognize_select_general`, from `recognize_select_beq` and from
    // `recognize_raw_binop`.
    if let CleanOriginShape::SelectBeqGeneral {
        scrutinee,
        cmp_left,
        cmp_right,
        then_arm,
        else_arm,
    } = &plan.shape
    {
        return admit_beq_general_select_lowering(
            env, plan, extracted, *scrutinee, *cmp_left, *cmp_right, *then_arm, *else_arm,
        );
    }
    // ── §6f LANDING 7: the raw binary operator ─────────────────────────────
    //
    // Same accounting as every arm above, for the SAME reason, and it binds
    // hardest here: the raw-binop spelling's exclusion from
    // `recognize_admissible_body` is a PINNED provenance boundary
    // (`binop_provenance_pins_never_admit`: *"the raw-binop spelling is
    // outside the recognized fragment today"*), and that chain also feeds
    // `trust_certify::clean_island::admit_function_into`, where a recognized
    // body becomes a defining equation with NO side A and NO kernel gate. The
    // capability is therefore reached through `recognize_raw_binop`, a
    // SEPARATE entry point, and `landing7_selection_probes::l7_p5` pins that
    // the same body still reads back as `None` from the chain — so the pin is
    // intact and the E6 import direction's reach did not move.
    if let CleanOriginShape::RawBinOp { op, left, right } = &plan.shape {
        return admit_raw_binop_lowering(env, plan, extracted, *op, *left, *right);
    }
    // ── W5 (Lean-calls-Rust): the Rust-call chain ──────────────────────────
    //
    // Same accounting as every arm above, and it binds hardest of all here:
    // this shape's body is "a chain of calls to USER functions", and a
    // reading of it in `recognize_admissible_body`'s chain would let the
    // gate-free E6 kernel-import direction import `fn f(x) { g(x) }` as the
    // defining equation `f = g` with `g` opaque — a false definitional
    // import. The capability is reached through
    // `recognize_rust_call_chain`, a SEPARATE entry point that also demands
    // an explicit allow-list of callee renderings, and
    // `control_23_rust_call_emitter_mutation::half_7` pins that the same
    // body still reads back as `None` from the chain.
    if let CleanOriginShape::RustCallChain { nodes } = &plan.shape {
        return admit_rust_call_chain_lowering(env, plan, extracted, nodes);
    }
    // ── W6 (Rust-calls-Clean): the boolean negation/connective ─────────────
    //
    // Same accounting as the select/beq/raw-binop arms above: this shape's
    // reading is produced ONLY by the separate entry point
    // `recognize_bool_value`, which is NOT in `recognize_admissible_body`'s
    // chain, so the gate-free E6 kernel-import direction cannot reach it.
    if matches!(
        &plan.shape,
        CleanOriginShape::BoolNot { .. } | CleanOriginShape::BoolConnective { .. }
    ) {
        return admit_bool_value_lowering(env, plan, extracted);
    }
    if matches!(&plan.shape, CleanOriginShape::UnsignedConditional { .. }) {
        return admit_unsigned_conditional_lowering(env, plan, extracted);
    }
    if matches!(&plan.shape, CleanOriginShape::BoolExpression { .. }) {
        return admit_bool_expression_lowering(env, plan, extracted);
    }

    // ── 1. the compiler's own recognizer, on the emitted body ──────────────
    let Some(recognised) = recognize_admissible_body(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    //
    // Arity first, shared by every shape: a call site passes
    // `plan.signature.arity()` arguments to whatever body this is, and an
    // arity disagreement alone must refuse.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "{recognised:?} over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }
    match (&plan.shape, &recognised) {
        (
            CleanOriginShape::Projection { projected }
            | CleanOriginShape::InductiveProjection { projected },
            AdmissibleBody::Projection { param },
        ) if param == projected => {}
        // §6f landing 2: the constant body. The VALUE must agree, and the
        // emitted constant's ENCODED WIDTH must be the emitted body's own
        // return width — a side-B self-consistency check, deliberately not a
        // comparison against the plan's carrier, because the reflection's
        // domain is derived from that same return type and a skew between the
        // two would otherwise reflect a term at a width the emitted scalar is
        // not at. (`recognize_single_block` reads the rvalue, not the type, so
        // it cannot make this check itself without acquiring a rule the E6
        // import direction would inherit.)
        //
        // The ARITY was already bound above, by `arg_count == arity`, which is
        // where probe_e3's erasure is contained — see `CleanOriginShape::
        // ConstantUint`. `landing2_selection_probes::l2_p3b` measures that the
        // KERNEL refuses both wrong pairings independently of this check.
        (
            CleanOriginShape::ConstantUint { value },
            AdmissibleBody::ConstantUint { value: emitted_value, width_bits },
        ) if value == emitted_value
            && matches!(
                extracted.body.return_ty,
                Ty::Int { width, signed: false } if width == *width_bits
            ) => {}
        (
            CleanOriginShape::WrappingBinOp { op, left, right },
            AdmissibleBody::Arithmetic { op: emitted_op, left: emitted_left, right: emitted_right },
        ) if op == emitted_op && left == emitted_left && right == emitted_right => {}
        (CleanOriginShape::Composed { expr }, AdmissibleBody::Composed { expr: emitted_expr })
            if expr == emitted_expr => {}
        (
            CleanOriginShape::Select { cmp, cmp_left, cmp_right, then_param, else_param },
            AdmissibleBody::Select {
                cmp: emitted_cmp,
                cmp_left: emitted_cl,
                cmp_right: emitted_cr,
                then_param: emitted_then,
                else_param: emitted_else,
            },
        ) if cmp == emitted_cmp
            && cmp_left == emitted_cl
            && cmp_right == emitted_cr
            && then_param == emitted_then
            && else_param == emitted_else => {}
        (
            CleanOriginShape::SelectLiteral { cmp, cmp_param, literal, then_param, else_param },
            AdmissibleBody::SelectLiteral {
                cmp: emitted_cmp,
                cmp_param: emitted_cp,
                literal: emitted_lit,
                then_param: emitted_then,
                else_param: emitted_else,
            },
        ) if cmp == emitted_cmp
            && cmp_param == emitted_cp
            && literal == emitted_lit
            && then_param == emitted_then
            && else_param == emitted_else => {}
        // W6 (Rust-calls-Clean): the comparison-to-`Bool` value. Side B reads
        // the one-block `_0 = <cmp>(l, r)` as `ComparisonBool`, whose operands
        // are `CmpOperand::Param` here (this shape admits no numeral operand).
        // The `cmp` and both operands must agree; the gate then re-decides
        // definitional equality of the reflected term against the declaration.
        (
            CleanOriginShape::DecideComparison { cmp, cmp_left, cmp_right },
            AdmissibleBody::ComparisonBool {
                cmp: emitted_cmp,
                left: emitted_left,
                right: emitted_right,
            },
        ) if cmp == emitted_cmp
            && *emitted_left == trust_types::admissible_body::CmpOperand::Param(*cmp_left)
            && *emitted_right == trust_types::admissible_body::CmpOperand::Param(*cmp_right) => {}
        _ => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}"),
            });
        }
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The domains come from the emitted body's OWN local types, never from the
    // plan. That is load-bearing: taking them from the plan would make side B
    // partly a copy of side A, and the gate would stop being able to see an
    // emitter that typed a local wrongly.
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };

    // ── 3a. SELECT THE ROW (§6f landing 1) ─────────────────────────────────
    //
    // The instruction-selection table decides which producer this reading
    // routes to, and the reflector builds that producer's INPUT — never the
    // resulting `Expr`. A reading the table has no row for is a NAMED refusal
    // (v7/D3: `no selection row for <head> at <carrier>`, plus options),
    // reported through the same `LoweringShapeMismatch` variant this arm has
    // always used so no caller's classification moves.
    //
    // The table does not see the plan and `trust_types` cannot see the table:
    // side A's reading and side B's reading remain two authorships, which is
    // the double fault `docs/TCB.md` rests on.
    let (_row, producer_call) = match crate::reflect::producer_call_for(&recognised) {
        Ok(selected) => selected,
        Err(miss) => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}\n{}", miss.note),
            });
        }
    };

    // ── 3b. CALL THE FROZEN PRODUCER ───────────────────────────────────────
    //
    // Minted into a CLONE. The real crate environment must not acquire a
    // constant as a side effect of checking one — a check that mutates the
    // thing it checks cannot be run twice and cannot be reasoned about.
    //
    // Every arm below is an INVOCATION, never a rendering: the `Expr` comes out
    // of `trust_spec_elab`'s own parser and typing, which is what makes side B
    // a program written for the opposite direction rather than a copy of side
    // A. The arithmetic arms additionally re-derive the SINGLE machine domain
    // from the emitted body's own types.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    let minted = match producer_call {
        crate::reflect::ProducerCall::Projection { param } => {
            trust_spec_elab::admit_projection_function(
                &mut scratch,
                &reflected_name,
                &param_domains,
                param,
            )
        }
        crate::reflect::ProducerCall::ExprRendering(rendering) => {
            let domain = shared_machine_domain(name, extracted, &param_domains)?;
            mint_expr_rendering(
                &mut scratch,
                &reflected_name,
                &rendering,
                extracted.body.arg_count,
                &domain,
            )
        }
        // R2/C5a: the select reflection. `admit_select_function` does its own
        // single-domain and Machine-only guards over `param_domains` — which
        // are read off the emitted body's own types above — so a mixed-width
        // or non-machine emission fails closed inside the frozen producer.
        crate::reflect::ProducerCall::Select {
            cmp,
            cmp_left,
            cmp_right,
            then_param,
            else_param,
        } => trust_spec_elab::admit_select_function(
            &mut scratch,
            &reflected_name,
            &param_domains,
            cmp,
            cmp_left,
            cmp_right,
            then_param,
            else_param,
        ),
        // R2/C9: the select-vs-literal reflection, through the NEW producer
        // the phase-1 probes demanded (`admit_select_literal_function` —
        // added BESIDE the frozen four, which are untouched). The producer
        // range-checks the literal fail-closed against the domain the emitted
        // body's OWN types denote.
        crate::reflect::ProducerCall::SelectLiteral {
            cmp,
            cmp_param,
            literal,
            then_param,
            else_param,
        } => trust_spec_elab::admit_select_literal_function(
            &mut scratch,
            &reflected_name,
            &param_domains,
            cmp,
            cmp_param,
            literal,
            then_param,
            else_param,
        ),
        // W6 (Rust-calls-Clean): the comparison-to-`Bool` reflection, through
        // the FROZEN `admit_comparison_function`. It does its own single-domain
        // and Machine/Signed guards over `param_domains` — read off the emitted
        // body's OWN types above — so a mixed-width or non-machine emission
        // fails closed inside the producer. The minted term is
        // `Decidable.decide <prop> <inst>`, def-eq to the island's
        // `decide`/`BEq.beq` (measured 2026-09-13).
        crate::reflect::ProducerCall::Comparison { cmp, cmp_left, cmp_right } => {
            trust_spec_elab::admit_comparison_function(
                &mut scratch,
                &reflected_name,
                &param_domains,
                cmp,
                cmp_left,
                cmp_right,
            )
        }
        // §6f landing 3: unreachable on THIS lane by construction, and the
        // arm is fail-closed rather than a builder. The general select is a
        // reading produced only by `recognize_select_general`, which is not in
        // `recognize_admissible_body`'s chain, so `producer_call_for` — the
        // only thing that feeds this match — can never return it. If it ever
        // does, side B's two entry points have been merged and the E6
        // containment `l3_p2` pins has gone with them.
        crate::reflect::ProducerCall::SelectOperands { .. } => {
            Err("INTERNAL: a general-select producer call reached the `AdmissibleBody` lane. Side \
             B's separate entry points have been merged, which also merges the gate-free E6 \
             kernel-import direction's reach with this one. NOTHING may be emitted on this \
             route. Please report it."
                .to_owned())
        }
        // §6f landing 6: unreachable on THIS lane by construction, and the arm
        // is fail-closed rather than a builder — the same accounting as the
        // general select's arm above. The `==` reading is produced only by
        // `recognize_select_beq`, which is not in `recognize_admissible_body`'s
        // chain, so `producer_call_for` can never return it.
        crate::reflect::ProducerCall::SelectBeq { .. } => {
            Err("INTERNAL: an `==`-select producer call reached the `AdmissibleBody` lane. Side \
             B's separate entry points have been merged, which also merges the gate-free E6 \
             kernel-import direction's reach with this one. NOTHING may be emitted on this \
             route. Please report it."
                .to_owned())
        }
        // §6f landing 8: unreachable on THIS lane by construction, and the arm
        // is fail-closed rather than a builder — the same accounting as the two
        // arms above, and it matters most here, because this reading carries
        // the RAW-BINOP spelling whose exclusion from `recognize_admissible_body`
        // is a PINNED provenance boundary.
        crate::reflect::ProducerCall::SelectBeqGeneral { .. } => {
            Err("INTERNAL: a general `==`-select producer call reached the `AdmissibleBody` \
             lane. Side B's separate entry points have been merged, which also merges the \
             gate-free E6 kernel-import direction's reach with this one — and with it the \
             raw-binop provenance boundary. NOTHING may be emitted on this route. Please \
             report it."
                .to_owned())
        }
    };
    if let Err(detail) = minted {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE. Side A from `env`, side B from the emitted MIR. ───────
    //
    // Admitted at the RESULT carrier: that is the value a call produces, and
    // the plan's `CarrierSignature` is already the statement that every
    // argument position carries too (it cannot exist otherwise).
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// **W5 (Lean-calls-Rust) — the RUST-CALL CHAIN round trip**, the same four
/// fail-closed steps as every other separate-entry-point lane:
///
/// 1. the emitted body must be recognised by
///    [`trust_types::admissible_body::recognize_rust_call_chain`] — trust-types'
///    reading of the linear call chain, given the ALLOW-LIST of callee
///    renderings the plan's table carries, and deliberately outside
///    `recognize_admissible_body`'s chain (see the arm in [`admit_lowering`]);
/// 2. the recognised body must equal the PLANNED chain node for node — the
///    structural catch, never a substitute for the kernel one. Identity is
///    the extractor's rendering of the callee `DefId` against the table's
///    rendering of the registered `DefId`: two renderings of ONE identity,
///    never a bare name;
/// 3. it must reflect through [`crate::reflect_rust_call::reflect_rust_call_chain`]
///    — a Trust-authored side-B producer (`docs/TCB.md`, the Lean-calls-Rust
///    row), built from the RECOGNISED dataflow with its binder types read off
///    the EMITTED body's own locals, and full-kernel-checked in a scratch
///    clone;
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the
///    result carrier. Both sides apply the same stuck `Opaque` heads, so
///    `is_def_eq` is congruence: a swapped argument, a wrong callee, a
///    missing application or a literal at the wrong value refuses
///    (`control_23_rust_call_emitter_mutation`).
fn admit_rust_call_chain_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    nodes: &[RustCallNode],
) -> Result<Faithful, EmitRefusal> {
    use trust_types::admissible_body::{RustCallChainArg, recognize_rust_call_chain};
    let name = plan.name.as_str();

    // Arity first, exactly as every other lane does it.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // The ALLOW-LIST: the extractor's rendering of every registered callee.
    // A plan whose table carries an EMPTY rendering was built at the mint
    // seam, which never reaches side B; refusing it here is what keeps a
    // name-only match unconstructible.
    let mut allowed = std::collections::BTreeSet::new();
    let mut clean_name_of_path = std::collections::BTreeMap::new();
    for callee in &plan.callees {
        if callee.def_path.is_empty() {
            return Err(EmitRefusal::ReflectionRejected {
                name: name.to_owned(),
                detail: format!(
                    "INTERNAL: the plan's Rust callee `{}` carries no `DefId` rendering, so \
                     side B cannot identify the emitted call with it. A plan built at the \
                     mint seam reached the gate. Please report it.",
                    callee.clean_name
                ),
            });
        }
        allowed.insert(callee.def_path.clone());
        clean_name_of_path.insert(callee.def_path.clone(), callee.clean_name.clone());
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = recognize_rust_call_chain(extracted, &allowed) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan, node for node ───────────────
    let mismatch = |detail: String| EmitRefusal::LoweringShapeMismatch {
        name: name.to_owned(),
        planned: plan.shape.clone(),
        recognised: format!("{recognised:?}\n{detail}"),
    };
    if recognised.nodes.len() != nodes.len() {
        return Err(mismatch(format!(
            "{} call(s) emitted for {} planned",
            recognised.nodes.len(),
            nodes.len()
        )));
    }
    for (index, (planned, emitted)) in nodes.iter().zip(&recognised.nodes).enumerate() {
        let callee = &plan.callees[planned.callee];
        if emitted.callee != callee.def_path {
            return Err(mismatch(format!(
                "node {index} calls `{}` where the plan calls `{}` (`{}`)",
                emitted.callee, callee.def_path, callee.clean_name
            )));
        }
        if planned.args.len() != emitted.args.len() {
            return Err(mismatch(format!("node {index} has a different argument count")));
        }
        for (position, (planned_arg, emitted_arg)) in
            planned.args.iter().zip(&emitted.args).enumerate()
        {
            let agrees = match (planned_arg, emitted_arg) {
                (RustCallArg::Param(a), RustCallChainArg::Param(b)) => a == b,
                (RustCallArg::Node(a), RustCallChainArg::Node(b)) => a == b,
                (
                    RustCallArg::Literal(RustCallLiteral::UInt(value)),
                    RustCallChainArg::UInt { value: emitted_value, width_bits },
                ) => {
                    // The emitted scalar must be the planned value AT the
                    // callee parameter's width — the width is the one fact
                    // the kernel typing of the reflected literal will also
                    // decide, and it is checked structurally too so a
                    // width skew is reported as what it is.
                    value == emitted_value
                        && matches!(
                            callee.params.get(position),
                            Some(Ty::Int { width, signed: false }) if width == width_bits
                        )
                }
                (
                    RustCallArg::Literal(RustCallLiteral::Bool(value)),
                    RustCallChainArg::Bool(emitted_value),
                ) => value == emitted_value,
                _ => false,
            };
            if !agrees {
                return Err(mismatch(format!(
                    "node {index} argument {position}: planned {planned_arg:?}, emitted \
                     {emitted_arg:?}"
                )));
            }
        }
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The binder and result types come from the emitted body's OWN locals,
    // never from the plan; the callee constant names come from the table,
    // keyed by the RENDERING side B read — which is the compiler-asserted
    // identity the TCB row discloses.
    let side_b = crate::reflect_rust_call::reflect_rust_call_chain(
        env,
        name,
        &recognised,
        extracted,
        &clean_name_of_path,
    )
    .map_err(|detail| EmitRefusal::ReflectionRejected { name: name.to_owned(), detail })?;

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// The GENERAL SELECT round trip (§6f landing 3) — the same four fail-closed
/// steps as [`admit_lowering`]'s non-recursive lane, with side B's reading
/// taken through the SEPARATE entry point:
///
/// 1. the emitted body must be recognised by
///    [`recognize_select_general`] — trust-types' reading of the four-block
///    diamond, never this crate's, and deliberately outside
///    `recognize_admissible_body`'s chain so the E6 kernel-import direction
///    stays blind to a constant arm;
/// 2. the recognised body must equal the PLANNED vocabulary directly — the
///    structural catch, never a substitute for the kernel one;
/// 3. it must reflect through the FROZEN-adjacent general producer, minted
///    into a scratch clone, with its domains read off the EMITTED body;
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the
///    result carrier.
#[allow(clippy::too_many_arguments)]
fn admit_general_select_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    cmp: SelectCmp,
    cmp_left: usize,
    cmp_right: ArithOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // Arity first, exactly as the shared lane does it: a call site passes
    // `plan.signature.arity()` arguments to whatever body this is.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = trust_types::admissible_body::recognize_select_general(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    if recognised.cmp != cmp
        || recognised.cmp_left != cmp_left
        || recognised.cmp_right != cmp_right
        || recognised.then_arm != then_arm
        || recognised.else_arm != else_arm
    {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The domains come from the emitted body's OWN local types, never from the
    // plan — the same rule the shared lane states: taking them from the plan
    // would make side B partly a copy of side A.
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };

    // 3a. SELECT THE ROW. The general select selects the SAME row a
    // bare-parameter select does; the table does not see the plan.
    let (_row, producer_call) = match crate::reflect::producer_call_for_general_select(&recognised)
    {
        Ok(selected) => selected,
        Err(miss) => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}\n{}", miss.note),
            });
        }
    };
    let crate::reflect::ProducerCall::SelectOperands {
        cmp: elab_cmp,
        cmp_left: elab_left,
        cmp_right: elab_right,
        then_arm: elab_then,
        else_arm: elab_else,
    } = producer_call
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "INTERNAL: the general-select row routed to a producer that is not the \
                     general select route. The table and the reflector have drifted apart and \
                     nothing emitted may rest on it. Please report it."
                .to_owned(),
        });
    };

    // 3b. CALL THE PRODUCER, into a CLONE. `admit_select_operands_function`
    // does its own single-domain and Machine-only guards over `param_domains`
    // — read off the emitted body's own types above — and range-checks every
    // numeral fail-closed before the kernel.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    if let Err(detail) = trust_spec_elab::admit_select_operands_function(
        &mut scratch,
        &reflected_name,
        &param_domains,
        elab_cmp,
        elab_left,
        elab_right,
        elab_then,
        elab_else,
    ) {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// **W6 (Rust-calls-Clean) — the boolean-value round trip.** The same four
/// fail-closed steps as every separate-entry-point lane, for a `Bool`-returning
/// negation or connective over `Bool` parameters:
///
/// 1. the emitted body must be recognised by
///    [`trust_types::admissible_body::recognize_bool_value`] — trust-types'
///    reading of the one-block `UnaryOp(Not)`/`BinaryOp(BitAnd|BitOr)`, and
///    deliberately OUTSIDE `recognize_admissible_body`'s chain so the gate-free
///    E6 kernel-import direction stays blind to it;
/// 2. the recognised body must equal the PLANNED vocabulary directly — the
///    structural catch, never a substitute for the kernel one;
/// 3. it must reflect through `trust_spec_elab::admit_bool_value_function`,
///    minted into a scratch clone with its domains read off the EMITTED body
///    (`Bool.not`/`Bool.and`/`Bool.or`, def-eq to the island's `not`/`and`/`or`);
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the `Bool`
///    result carrier. A misread connective or operand fails HERE, fail-closed.
fn admit_bool_value_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = recognize_bool_value(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    let elab_kind = match (&plan.shape, &recognised) {
        (CleanOriginShape::BoolNot { param }, BoolValueBody::Not { param: emitted })
            if param == emitted =>
        {
            trust_spec_elab::BoolValueKind::Not(*param)
        }
        (
            CleanOriginShape::BoolConnective { op: BoolBinOp::And, left, right },
            BoolValueBody::And { left: el, right: er },
        ) if left == el && right == er => trust_spec_elab::BoolValueKind::And(*left, *right),
        (
            CleanOriginShape::BoolConnective { op: BoolBinOp::Or, left, right },
            BoolValueBody::Or { left: el, right: er },
        ) if left == el && right == er => trust_spec_elab::BoolValueKind::Or(*left, *right),
        _ => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}"),
            });
        }
    };

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    if let Err(detail) = trust_spec_elab::admit_bool_value_function(
        &mut scratch,
        &reflected_name,
        &param_domains,
        elab_kind,
    ) {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// Reflect the ACTUAL emitted body with the existing opposite-direction E6
/// importer. Neither its reader nor its term renderer is authored here. In
/// particular the plan's expression is never passed to the importer. Its
/// The existing gate must establish definitional equality or kernel-check
/// an induction proof against the untouched original declaration, or refuse.
fn admit_unsigned_conditional_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();
    let expected = plan.signature().result().rust();
    // Inspect the actual emission, never a reflection of the source plan.
    // Both reachable and unreachable blocks must use this pure vocabulary.
    let vocabulary_ok = extracted.body.blocks.len() <= 2 * UINT_CONDITIONAL_MAX_DECISIONS + 1
        && extracted.body.locals.iter().all(|local| local.ty == *expected || local.ty == Ty::Bool)
        && (0..=plan.signature().arity()).all(|index| {
            extracted.body.locals.get(index).is_some_and(|local| local.ty == *expected)
        })
        && extracted.body.blocks.iter().all(|block| {
            matches!(block.terminator,
                trust_types::Terminator::Return | trust_types::Terminator::Goto(_)
                    | trust_types::Terminator::SwitchInt { .. })
                && block.stmts.iter().all(|statement| {
                    matches!(statement, trust_types::Statement::Assign { rvalue, .. }
                        if matches!(rvalue, trust_types::Rvalue::Use(_)
                            | trust_types::Rvalue::BinaryOp(
                                trust_types::BinOp::Lt | trust_types::BinOp::Le | trust_types::BinOp::Eq,
                                _, _)))
                })
        });
    if extracted.body.arg_count != plan.signature().arity()
        || extracted.body.return_ty != *expected
        || !vocabulary_ok
    {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.into(), detail: "unsigned conditional emission has a different signature or contains an operation outside its pure bounded vocabulary".into(),
        });
    }
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    match trust_spec_elab::admit_e6_only_body(&mut scratch, extracted, &reflected_name) {
        Some(Ok(_)) => {}
        Some(Err(detail)) => {
            return Err(EmitRefusal::ReflectionRejected { name: name.into(), detail });
        }
        None => {
            return Err(EmitRefusal::LoweringUnrecognised {
                name: name.into(),
                planned: plan.shape.clone(),
            });
        }
    }
    let side_b = scratch
        .get_const(&Name::from_string(&reflected_name))
        .and_then(|constant| constant.value.clone())
        .ok_or_else(|| EmitRefusal::ReflectionRejected {
            name: name.into(),
            detail: "the independent emitted-body reader returned no defining value".into(),
        })?;
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

fn admit_bool_expression_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();
    // Keep this emission slice closed even though the unchanged importer can
    // also read comparisons, XOR and decision trees. This is a vocabulary
    // check, not a second interpretation of operands or temporary dataflow.
    let vocabulary_ok = match extracted.body.blocks.as_slice() {
        [block] => {
            matches!(block.terminator, trust_types::Terminator::Return)
                && block.stmts.len() <= BOOL_EXPRESSION_MAX_OPS + 1
                && block.stmts.iter().all(|stmt| {
                    matches!(stmt, trust_types::Statement::Assign { rvalue, .. }
                        if matches!(rvalue,
                            trust_types::Rvalue::Use(_)
                            | trust_types::Rvalue::UnaryOp(trust_types::UnOp::Not, _)
                            | trust_types::Rvalue::BinaryOp(
                                trust_types::BinOp::BitAnd | trust_types::BinOp::BitOr, _, _)))
                })
        }
        _ => false,
    };
    if extracted.body.arg_count != plan.signature.arity()
        || extracted.body.return_ty != Ty::Bool
        || !vocabulary_ok
        || !param_domains_of(extracted)
            .is_some_and(|domains| domains.iter().all(|domain| *domain == Domain::Bool))
    {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the emitted Boolean expression has a different arity/carrier or is \
                     outside the bounded straight-line Boolean vocabulary"
                .to_owned(),
        });
    }
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    match trust_spec_elab::admit_e6_only_body(&mut scratch, extracted, &reflected_name) {
        Some(Ok(_)) => {}
        Some(Err(detail)) => {
            return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
        }
        None => {
            return Err(EmitRefusal::LoweringUnrecognised {
                name: name.to_owned(),
                planned: plan.shape.clone(),
            });
        }
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the E6 importer accepted no defining value".to_owned(),
        });
    };
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// The `==` SELECT round trip (§6f landing 6) — the same four fail-closed steps
/// as [`admit_lowering`]'s non-recursive lane, with BOTH halves of side B taken
/// through the `==` route:
///
/// 1. the emitted body must be recognised by
///    [`trust_types::admissible_body::recognize_select_beq`] — trust-types'
///    reading of the TWO-STEP diamond, never this crate's, and deliberately
///    outside `recognize_admissible_body`'s chain so the E6 kernel-import
///    direction stays blind to it;
/// 2. the recognised body must equal the PLANNED vocabulary directly — the
///    structural catch, never a substitute for the kernel one;
/// 3. it must reflect through `trust_spec_elab::admit_select_beq_function`,
///    minted into a scratch clone, with its domains read off the EMITTED body;
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the
///    result carrier.
///
/// **Step 4 is where the landing's whole point is cashed.** Because the emitted
/// MIR is the two-step diamond, side B's reading — and therefore the term this
/// lane reflects — is the `BEq.beq … = Bool.true` tree, which is what side A
/// actually is. The propositional `Eq {C} l r` body reads back through the
/// ONE-step reader instead and reflects to a different term, so the kernel
/// refuses each spelling against the other's side A: measured in both
/// directions by `landing6_selection_probes::l6_p3`.
#[allow(clippy::too_many_arguments)]
fn admit_beq_select_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    cmp_left: usize,
    cmp_right: ArithOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // Arity first, exactly as every other lane does it: a call site passes
    // `plan.signature.arity()` arguments to whatever body this is.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = trust_types::admissible_body::recognize_select_beq(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    if recognised.cmp_left != cmp_left
        || recognised.cmp_right != cmp_right
        || recognised.then_arm != then_arm
        || recognised.else_arm != else_arm
    {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The domains come from the emitted body's OWN local types, never from the
    // plan — the same rule every lane states: taking them from the plan would
    // make side B partly a copy of side A.
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };

    // 3a. SELECT THE ROW. The table does not see the plan.
    let (_row, producer_call) = match crate::reflect::producer_call_for_beq_select(&recognised) {
        Ok(selected) => selected,
        Err(miss) => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}\n{}", miss.note),
            });
        }
    };
    let crate::reflect::ProducerCall::SelectBeq {
        cmp_left: elab_left,
        cmp_right: elab_right,
        then_arm: elab_then,
        else_arm: elab_else,
    } = producer_call
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "INTERNAL: the `==`-select row routed to a producer that is not the `==` \
                     route. The table and the reflector have drifted apart and nothing emitted \
                     may rest on it. Please report it."
                .to_owned(),
        });
    };

    // 3b. CALL THE PRODUCER, into a CLONE. `admit_select_beq_function` does its
    // own single-domain and Machine-only guards over `param_domains` — read off
    // the emitted body's own types above — and range-checks every numeral
    // fail-closed before the kernel.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    if let Err(detail) = trust_spec_elab::admit_select_beq_function(
        &mut scratch,
        &reflected_name,
        &param_domains,
        elab_left,
        elab_right,
        elab_then,
        elab_else,
    ) {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// **§6f LANDING 8 — the GENERAL `==` SELECT round trip.** The same four
/// fail-closed steps as [`admit_beq_select_lowering`], with BOTH halves of side
/// B taken through the general route:
///
/// 1. the emitted body must be recognised by
///    [`trust_types::admissible_body::recognize_select_beq_general`] — a
///    SEPARATE entry point, outside `recognize_admissible_body`'s chain, so the
///    gate-free E6 kernel-import direction stays blind to it AND the pinned
///    raw-binop provenance boundary does not move;
/// 2. the recognised body must equal the PLANNED vocabulary directly — every
///    field, INCLUDING the scrutinee. That comparison is where a polarity
///    mistake is caught structurally, before the kernel is asked anything;
/// 3. it must reflect through
///    `trust_spec_elab::admit_select_beq_operands_function`, minted into a
///    scratch clone, with its domains read off the EMITTED body — and with each
///    computed operand elaborated by the FROZEN `elab_term`, which is also
///    where the divisor rule is enforced a THIRD time by a program that knows
///    nothing about this lane;
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the
///    result carrier.
///
/// **Step 4 is where the polarity is finally decided rather than trusted.** The
/// emitted body's `Eq(_d, const false)` is read back as `scrutinee: false`,
/// reflected as `Eq Bool <decision> Bool.false`, and put to the kernel against
/// side A. `l8_p2` measures that this term is not definitionally equal to the
/// `==` one, not to the `==` one with SWAPPED ARMS — which computes the same
/// function — and not to the `Bool.not` (`!=`) one. So a body emitted for one
/// of the four disequality-adjacent trees cannot be gated against another.
#[allow(clippy::too_many_arguments)]
fn admit_beq_general_select_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    scrutinee: bool,
    cmp_left: BeqOperand,
    cmp_right: BeqOperand,
    then_arm: ArithOperand,
    else_arm: ArithOperand,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // Arity first, exactly as every other lane does it.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = trust_types::admissible_body::recognize_select_beq_general(extracted)
    else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan, SCRUTINEE INCLUDED ──────────
    if recognised.scrutinee != scrutinee
        || recognised.cmp_left != cmp_left
        || recognised.cmp_right != cmp_right
        || recognised.then_arm != then_arm
        || recognised.else_arm != else_arm
    {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };

    // 3a. SELECT THE ROW. The table does not see the plan.
    let (_row, producer_call) =
        match crate::reflect::producer_call_for_beq_general_select(&recognised) {
            Ok(selected) => selected,
            Err(miss) => {
                return Err(EmitRefusal::LoweringShapeMismatch {
                    name: name.to_owned(),
                    planned: plan.shape.clone(),
                    recognised: format!("{recognised:?}\n{}", miss.note),
                });
            }
        };
    let crate::reflect::ProducerCall::SelectBeqGeneral {
        scrutinee: elab_scrutinee,
        cmp_left: elab_left,
        cmp_right: elab_right,
        then_arm: elab_then,
        else_arm: elab_else,
    } = producer_call
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "INTERNAL: the general `==`-select row routed to a producer that is not the \
                     general `==` route. The table and the reflector have drifted apart and \
                     nothing emitted may rest on it. Please report it."
                .to_owned(),
        });
    };

    // 3b. CALL THE PRODUCER, into a CLONE.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    if let Err(detail) = trust_spec_elab::admit_select_beq_operands_function(
        &mut scratch,
        &reflected_name,
        &param_domains,
        elab_scrutinee,
        &elab_left,
        &elab_right,
        elab_then,
        elab_else,
    ) {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// **§6f LANDING 7 — the RAW-BINOP round trip.** The same four fail-closed
/// steps as [`admit_lowering`]'s non-recursive lane, with side B's reading
/// taken through the SEPARATE entry point [`recognize_raw_binop`]:
///
/// 1. the emitted body must be recognised by `recognize_raw_binop` —
///    trust-types' reading of the single-statement binop body, never this
///    crate's, and deliberately outside `recognize_admissible_body`'s chain so
///    the pinned raw-binop provenance boundary and the gate-free E6 import
///    direction both stay exactly where they are;
/// 2. the recognised body must equal the PLANNED vocabulary directly — the
///    structural catch, never a substitute for the kernel one;
/// 3. it must reflect through the FROZEN `admit_expr_function`, minted into a
///    scratch clone, with its domain read off the EMITTED body;
/// 4. the kernel must identify the two terms — [`crate::gate::check_faithful`], at the
///    result carrier.
///
/// # THE DIVISOR IS NOT RE-CHECKED HERE, AND THAT IS THE POINT
///
/// A `Div`/`Rem` whose divisor is not a strictly positive numeral is refused
/// twice already — by `recognise_raw_binop_expr` on side A and again on the
/// sealed plan — and would be refused a THIRD time here, by
/// `admit_expr_function` itself, which will not mint `p0 / p1` or `p0 / 0`
/// (*"division/remainder in a spec requires a positive integer literal
/// divisor"*). That third refusal is the valuable one: it comes from a program
/// written years earlier for the OPPOSITE direction, which knows nothing about
/// this lane. Adding a fourth check in this function would add no evidence and
/// would put the boundary somewhere a reader might mistake for the authority.
fn admit_raw_binop_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    op: RawBinOpKind,
    left: ArithOperand,
    right: ArithOperand,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    // Arity first, exactly as every other lane does it: a call site passes
    // `plan.signature.arity()` arguments to whatever body this is.
    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = recognize_raw_binop(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan ──────────────────────────────
    if recognised.op != op || recognised.left != left || recognised.right != right {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body back into Clean ────────────────────────
    //
    // The domain comes from the emitted body's OWN types, never from the plan.
    let Some(param_domains) = param_domains_of(extracted) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "a parameter of the emitted body is not a supported machine carrier".to_owned(),
        });
    };

    // 3a. SELECT THE ROW. The table does not see the plan.
    let (_row, producer_call) = match crate::reflect::producer_call_for_raw_binop(&recognised) {
        Ok(selected) => selected,
        Err(miss) => {
            return Err(EmitRefusal::LoweringShapeMismatch {
                name: name.to_owned(),
                planned: plan.shape.clone(),
                recognised: format!("{recognised:?}\n{}", miss.note),
            });
        }
    };
    let crate::reflect::ProducerCall::ExprRendering(rendering) = producer_call else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "INTERNAL: the raw-binop row routed to a producer that is not the frozen \
                     expression route. The table and the reflector have drifted apart and \
                     nothing emitted may rest on it. Please report it."
                .to_owned(),
        });
    };

    // 3b. CALL THE FROZEN PRODUCER, into a CLONE.
    let mut scratch = env.clone();
    let reflected_name = reflection_name(name);
    let domain = shared_machine_domain(name, extracted, &param_domains)?;
    if let Err(detail) = mint_expr_rendering(
        &mut scratch,
        &reflected_name,
        &rendering,
        extracted.body.arg_count,
        &domain,
    ) {
        return Err(EmitRefusal::ReflectionRejected { name: name.to_owned(), detail });
    }
    let Some(side_b) =
        scratch.get_const(&Name::from_string(&reflected_name)).and_then(|c| c.value.clone())
    else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the reflected defining equation was accepted but carries no value".to_owned(),
        });
    };

    // ── 4. THE GATE ────────────────────────────────────────────────────────
    Ok(check_faithful_for_name(env, plan.declaration(), &side_b, plan.result_carrier())?)
}

/// The structural-recursion round trip (R1, §6e as amended) — the same four
/// fail-closed steps as [`admit_lowering`]'s non-recursive lane, each with
/// its recursion-specific producer:
///
/// 1. the emitted body must be recognised by
///    [`recognize_structural_rec`] — trust-types' reading of the MIR
///    contract, never this crate's;
/// 2. the recognised body must equal the PLANNED vocabulary directly
///    (structural catch; never a substitute for the kernel one);
/// 3. it must reflect into kernel terms via
///    [`crate::reflect_rec::reflect_structural_rec`] — built from the
///    RECOGNIZED dataflow, never the plan, each term full-kernel-checked in
///    a scratch clone, the defined constant cited NOWHERE (the s2 vacuity is
///    unconstructible);
/// 4. the kernel must identify every defining equation and the recursive
///    argument — [`crate::gate::check_faithful_equations`], at the carrier.
fn admit_structural_rec_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    base: &RecBodyExpr,
    step: &RecBodyExpr,
    rec_arg: &RecBodyExpr,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    let Some(recognised) = recognize_structural_rec(extracted) else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan, direct equality ─────────────
    let planned =
        StructuralRecBody { base: base.clone(), step: step.clone(), rec_arg: rec_arg.clone() };
    if recognised != planned {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body's reading into kernel terms ────────────
    let reflected = crate::reflect_rec::reflect_structural_rec(env, name, &recognised)
        .map_err(|detail| EmitRefusal::ReflectionRejected { name: name.to_owned(), detail })?;

    // ── 4. THE GATE — per-defining-equation, at the RESULT carrier ─────────
    Ok(check_faithful_equations_for_name(
        env,
        plan.declaration(),
        &reflected,
        plan.result_carrier(),
    )?)
}

/// The well-founded-recursion round trip (R2) — the same four fail-closed
/// steps as [`admit_lowering`]'s non-recursive lane, each with its
/// WF-specific producer:
///
/// 1. the emitted body must be recognised by
///    [`recognize_wf_nat_rec`] — trust-types' reading of the MIR contract,
///    never this crate's;
/// 2. the recognised body must equal the PLANNED vocabulary directly
///    (structural catch; never a substitute for the kernel one);
/// 3. it must reflect into a functional via
///    [`crate::reflect_wf::reflect_wf_functional`] — built from the RECOGNIZED
///    dataflow, never the plan, with the defined constant unnameable and every
///    decrease slot left as the sentinel for the gate to borrow;
/// 4. the kernel must identify the two functionals, after auditing both sides'
///    axiom closures and type-checking side B at side A's own functional type
///    — [`crate::gate::check_faithful_wf_functional`], at the carrier.
///
/// Step 3 does NOT kernel-check its output, and that is deliberate rather than
/// a gap: the term carries the decrease-slot sentinel, which by construction
/// resolves to nothing, so the only term worth checking is the BORROWED one —
/// and the gate checks exactly that, at side A's type, before it audits or
/// compares (`check_faithful_wf_functional` steps 7 and 7b).
fn admit_wf_rec_lowering(
    env: &Environment,
    plan: &CleanOriginPlan,
    extracted: &VerifiableFunction,
    zero_value: &RecBodyExpr,
    nonzero_value: &RecBodyExpr,
    rec_args: &[RecBodyExpr],
    measure_index: usize,
    lowering: WfLowering,
) -> Result<Faithful, EmitRefusal> {
    let name = plan.name.as_str();

    if extracted.body.arg_count != plan.signature.arity() {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!(
                "a body over {} parameter(s), not {}",
                extracted.body.arg_count,
                plan.signature.arity()
            ),
        });
    }

    // ── 1. trust-types' recognizer, on the emitted body ────────────────────
    //
    // R3d: which ENTRY POINT is chosen by the lowering, and the two differ in
    // exactly one belt — `recognize_wf_nat_rec` requires the self-call's
    // argument at the guarded position to be the emitted predecessor, which is
    // phase 2's termination contract and is not phase 3's (see
    // `check_wf_fragment`'s note). Both read the SAME MIR contract, byte for
    // byte, and both are `trust_types`'s own reading of the emitted body — this
    // lane never tells the MIR reader what to expect.
    let recognised = match lowering {
        WfLowering::OnParameter => recognize_wf_nat_rec(extracted),
        WfLowering::OnMeasureValue => recognize_wf_sum_measure_rec(extracted),
    };
    let Some(recognised) = recognised else {
        return Err(EmitRefusal::LoweringUnrecognised {
            name: name.to_owned(),
            planned: plan.shape.clone(),
        });
    };

    // ── 2. structural agreement with the plan, direct equality ─────────────
    let planned = WfRecBody {
        zero_value: zero_value.clone(),
        nonzero_value: nonzero_value.clone(),
        rec_args: rec_args.to_vec(),
        measure_index,
    };
    if recognised != planned {
        return Err(EmitRefusal::LoweringShapeMismatch {
            name: name.to_owned(),
            planned: plan.shape.clone(),
            recognised: format!("{recognised:?}"),
        });
    }

    // ── 3. reflect the EMITTED body's reading into a kernel functional ─────
    let reflected = crate::reflect_wf::reflect_wf_functional(env, name, &recognised, lowering)
        .map_err(|detail| EmitRefusal::ReflectionRejected { name: name.to_owned(), detail })?;

    // ── 4. THE GATE — the F layer, at the RESULT carrier ───────────────────
    Ok(check_faithful_wf_functional_for_name(
        env,
        plan.declaration(),
        &reflected,
        plan.result_carrier(),
    )?)
}

/// The one machine domain every position of the emitted body denotes.
///
/// The arithmetic reflections are SINGLE-domain: every parameter AND the
/// return of the emitted body must denote one machine domain — read off the
/// emitted body's OWN types, never the plan's, for the reason
/// [`admit_lowering`]'s step 3 states.
fn shared_machine_domain(
    name: &str,
    extracted: &VerifiableFunction,
    param_domains: &[Domain],
) -> Result<Domain, EmitRefusal> {
    let Some(domain @ Domain::Machine(_)) = ty_to_domain(&extracted.body.return_ty) else {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the emitted body's return type is not a supported machine carrier".to_owned(),
        });
    };
    if param_domains.iter().any(|parameter_domain| parameter_domain != &domain) {
        return Err(EmitRefusal::ReflectionRejected {
            name: name.to_owned(),
            detail: "the emitted body's positions do not share one machine domain".to_owned(),
        });
    }
    Ok(domain)
}

/// Mint a rendered arithmetic body over positional `p{i}` names through the
/// frozen [`trust_spec_elab::admit_expr_function`], which FULL-KERNEL-CHECKS
/// the reflected defining equation.
fn mint_expr_rendering(
    scratch: &mut Environment,
    reflected_name: &str,
    rendered: &str,
    arg_count: usize,
    domain: &Domain,
) -> Result<trust_spec_elab::Admission, String> {
    let parameters: Vec<String> = (0..arg_count).map(|i| format!("p{i}")).collect();
    let parameter_refs: Vec<&str> = parameters.iter().map(String::as_str).collect();
    trust_spec_elab::admit_expr_function(scratch, reflected_name, rendered, &parameter_refs, domain)
}

/// The elaboration domain a Rust carrier type denotes, or `None` outside the
/// supported fragment.
///
/// Deliberately a *separate* mapping from `trust_certify`'s private
/// `ty_to_domain`, and deliberately NARROWER: no `PtrSizedInt`. A pointer-sized
/// integer's width is a property of the target, and a Clean-origin body is the
/// one place a width mistake becomes an emitted value rather than a failed
/// proof. `usize` therefore fails closed here even though the E6 reflection
/// direction accepts it — that direction can only decline to prove something.
fn ty_to_domain(ty: &Ty) -> Option<Domain> {
    match ty {
        Ty::Bool => Some(Domain::Bool),
        Ty::Int { width, signed: false } => Some(Domain::Machine(match width {
            8 => MachineUIntWidth::U8,
            16 => MachineUIntWidth::U16,
            32 => MachineUIntWidth::U32,
            64 => MachineUIntWidth::U64,
            _ => return None,
        })),
        // Trust (I6): the bignum carrier, in both spellings this function can
        // meet — the carrier decision's own `Ty::BignumNat`, and the EXTRACTED
        // body's `Adt` naming the runtime type (`trust-mir-extract` renders an
        // ADT by path and knows nothing of the carrier variant).
        //
        // SOUNDNESS NOTE, per the I6 review: the name match here is NOT what
        // makes this sound — nothing stamps or authenticates the ADT at this
        // point. It is sound only because `admit_lowering` re-derives the plan
        // from the kernel declaration, requires structural agreement, and then
        // puts the reflected side B to the kernel gate: a wrong or impostor
        // `Nat` yields a term the kernel refuses to identify with side A. This
        // arm only chooses which DOMAIN the reflection is attempted in.
        Ty::BignumNat => Some(Domain::Nat),
        Ty::Adt { name, .. } if name == "trust_bignum::Nat" => Some(Domain::Nat),
        _ => None,
    }
}

/// The domains of every value parameter of the emitted body, in order.
///
/// Parameters are locals `1..=arg_count` (`_0` is the return place). A missing
/// local or an unsupported type fails the whole reflection closed.
fn param_domains_of(func: &VerifiableFunction) -> Option<Vec<Domain>> {
    (1..=func.body.arg_count)
        .map(|i| func.body.locals.iter().find(|l| l.index == i).and_then(|l| ty_to_domain(&l.ty)))
        .collect()
}

// ───────────────────────────────────────────────────────────────────────────
// R3e — THE READER'S HALF OF THE STACK RAIL, MUTATION-PROVED
// ───────────────────────────────────────────────────────────────────────────

/// [`SUM_MEASURE_DEPTH_LIMIT`] on the phase-3 reader's own walk.
///
/// `gate::bounded_descent_tests` decides the gate's two walks and carries the
/// full account. This module decides the THIRD walk on the same rail and the
/// same bounded stack, and it is not a duplicate: `scan_sum_measure_calls` runs
/// while side A is being READ, before the gate has anything to compare it
/// against, so it is the first of the three a deep term reaches.
#[cfg(test)]
mod bounded_descent_tests {
    use super::*;

    /// The same probe stack `gate::bounded_descent_tests` uses — twice the
    /// budget the rail is derived from.
    const PROBE_STACK: usize = 2 * DESCENT_STACK_BUDGET;

    /// `fun (_ : Nat) => … => Nat`, exactly `levels` lambdas deep, built with a
    /// fold rather than a recursion for the reason the terms exist at all.
    fn lam_chain(levels: usize) -> Expr {
        let leaf = Expr::const_(Name::from_string("Nat"), vec![]);
        (0..levels).fold(leaf.clone(), |inner, _| {
            Expr::lam(clean_kernel::BinderInfo::Default, leaf.clone(), inner)
        })
    }

    /// Read `levels` lambdas with the phase-3 reader's walk, on a thread whose
    /// stack is bounded so a runaway descent aborts instead of passing.
    fn scan(levels: usize) -> Result<Vec<WfSumMeasureCall>, String> {
        let body = lam_chain(levels);
        let measure = Expr::const_(Name::from_string("Nat"), vec![]);
        std::thread::Builder::new()
            .stack_size(PROBE_STACK)
            .spawn(move || {
                let mut visited = 0usize;
                let mut calls = Vec::new();
                scan_sum_measure_calls(&body, 1, &measure, 0, 0, &mut visited, &mut calls)
                    .map(|()| calls)
            })
            .expect("the probe thread must spawn")
            .join()
            .expect("the reader must return a value rather than unwind or overflow the stack")
    }

    /// **(d4) THE READER REFUSES ONE LEVEL PAST THE RAIL, WITH THE FIX.**
    ///
    /// As in `d1`, both halves matter: at the rail the term is still read, one
    /// level past it the refusal names the bound and what moves it.
    #[test]
    fn d4_the_reader_refuses_one_level_past_the_rail() {
        let at_limit = SUM_MEASURE_DEPTH_LIMIT - 1;
        assert!(
            scan(at_limit).is_ok(),
            "a term exactly at the rail must still be read — the rail is a resource bound, not \
             a fragment boundary"
        );

        let message = scan(at_limit + 1).expect_err("one level past the rail must refuse");
        assert!(
            message.contains(&SUM_MEASURE_DEPTH_LIMIT.to_string()),
            "the refusal must NAME the bound it hit; got {message}"
        );
        assert!(
            message.contains("Options:"),
            "v7/D3: a refusal must carry the fix, with options; got {message}"
        );
    }

    /// **(d5) THE CRASH SCALE, at the reader.**
    ///
    /// Without the rail this row does not fail, it SEGFAULTS: the node budget
    /// does not fire until about level 131,000 and the stack is long gone.
    #[test]
    fn d5_a_crash_scale_term_refuses_instead_of_overflowing_the_stack() {
        const CRASH_SCALE: usize = 150_000;
        assert!(
            2 * CRASH_SCALE > SUM_MEASURE_NODE_LIMIT,
            "if the node budget alone caught this term there would be nothing to fix"
        );

        let message = scan(CRASH_SCALE).expect_err("a crash-scale term must refuse, not be read");
        assert!(
            message.contains(&SUM_MEASURE_DEPTH_LIMIT.to_string()),
            "the refusal must be the DEPTH rail's, not the node budget's; got {message}"
        );
    }
}
