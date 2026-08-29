// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **R2 SESSION PROBES — the well-founded CALL lane measured against the REAL
//! elaborator, which is the discipline this lane skipped.**
//!
//! Every side A in this file comes from
//! `trust_certify::clean_island::CleanIslandSession::check_all` — the exact
//! pipeline `clean_origin_mir` drives. Nothing here is hand-built.
//!
//! # Why this file exists
//!
//! `r2_wf_equation_probes.rs` is a true statement about what the KERNEL
//! accepts, and it stays. It is not, and never was, evidence about what the
//! ELABORATOR emits: its side A is a raw kernel term this crate's own tests
//! assemble. The audit
//! `docs/audits/2026-08-22-r2-wf-call-lane-unreachable.md` measured the
//! consequence — the lane's own canonical driver fixture
//! (`tests/ui/trust/clean_origin_wf_rec.rs`) did not compile, failing `E0425:
//! cannot find function countdownSum`, because `recognise_wf_nat_rec` was
//! written against spellings the elaborator does not produce. Three of them:
//!
//! | site | the reader demanded | the elaborator emits |
//! |---|---|---|
//! | the guard proposition | `Nat.lt 0 n` (2 args) | `@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat 0 _) n` (4 args) |
//! | the decidability instance | `Nat.decLt 0 n` | `instDecidableNatLt 0 n` |
//! | the self-call argument | `Nat.sub n 1` / `Nat.pred n` | `@HSub.hSub.{0,0,0} Nat Nat Nat instHSubNat n (@OfNat.ofNat.{0} Nat 1 _)` |
//!
//! The third was never varied by the audit, because the second refused first —
//! and it is the interesting one, because the SAME body's `+` was read
//! correctly all along. `read_nat_add` is SHARED with R1's structural lane and
//! was derived from a real measurement; the `-` reading was well-founded-lane-
//! local and was measured against nothing. That is the shape of this class of
//! defect: the readers with a real-session measurement behind them match, and
//! the ones without do not.
//!
//! This is the THIRD lane caught this way, after landing 3's
//! `Expr::nat_lit(5)` vs `OfNat.ofNat.{0} Nat 5 (instOfNatNat 5)` and landing
//! 5's `Nat.beq` vs `BEq.beq` under `instBEqOfDecidableEq`.
//!
//! # What the fix was, and what it was NOT
//!
//! All three were FRAGMENT-BOUNDARY checks written against the wrong spelling.
//! Each now reads the spelling the elaborator emits **and** the raw one side B
//! renders, with the mediating instance pinned BY NAME in every case
//! (`instLTNat`, `instDecidableNatLt`, `instHSubNat`) — never "any instance".
//! Pinning is soundness-bearing: a different instance may denote a different
//! `<`, a different decision procedure, or a different `-`, and the emitted
//! body realises exactly one of each. The boundary is therefore exactly as
//! wide as it was; only its spelling changed. The three defeq facts that make
//! that true are pinned in `first-party/clean` itself:
//!
//! * `instDecidableNatLt` is a REDUCIBLE `Definition` whose value is literally
//!   `Expr::const_("Nat.decLt")` — `env/order_lemmas_succ.rs:561`;
//! * `LT.lt Nat instLTNat a b` whnf-reduces to `Nat.lt a b` —
//!   `tc/tests2/ordering_projection_value.rs:194`;
//! * `instHSubNat` is `add_homogeneous_hetero_instance(…, "Nat", "Nat.sub")` —
//!   `env/algebra_hetero.rs:1298`.
//!
//! Consequently `reflect_wf.rs` and `reflect.rs` need NO edit, which matters
//! because they are FROZEN: side B goes on rendering `Nat.lt Nat.zero x`,
//! `Nat.decLt Nat.zero x` and `Nat.sub x 1`, and p4 measures the kernel
//! identifying that rendering with the real elaborated side A.
//!
//! Nothing about the SOUNDNESS-BEARING checks moved: `check_wf_nat_signature`
//! (the carrier decision), the closed-functional requirement, the single
//! self-call rule and the two-argument `rec ARG PRF` shape are untouched, and
//! p6/p7/p8 exercise them as refusals.
//!
//! # The measured table
//!
//! | # | island source | verdict |
//! |---|---|---|
//! | p1 | `countdownSum` — the canonical fixture, verbatim | **PLANS**, `WellFoundedNatRec { zero = 0, nonzero = Decreasing + Rec, rec_arg = Pred }` at `Nat -> Nat` |
//! | p2 | `Nat.lt 0 n` written literally in the source | PLANS — the raw guard spelling still reads |
//! | p3 | `Nat.sub n 1` written literally in the source | PLANS — the raw predecessor spelling still reads |
//! | p4 | the canonical fixture through the FULL gate | **FAITHFUL** — frozen side B identified with the real side A |
//! | p5 | `down` (`if n == 0`) | REFUSES, at the guard, with the equality-test hint. The island side is fine; the CALL side is a separate landing |
//! | p5b | `n ≠ 0` | REFUSES with the OTHER polarity's hint — same branch order as the emitted test, different proposition |
//! | p6 | seven single-construct mutations | each REFUSES, each naming its own construct |
//! | p6b | three mutations the ISLAND rejects first | recorded as island-side, so they are not miscounted as CALL-lane evidence |
//! | p6c | five explicit-`@dite` instance spellings | the instance check is a BACKSTOP — no source reaches it as a refusal, and the audit's stated mechanism was wrong |
//! | p7 | `n > 0` | REFUSES with the operand-order hint |
//! | p8 | a two-parameter WF def | rejected ISLAND-side — but for its UNSATISFIABLE MEASURE, not its arity. **Corrected 2026-08-25**: two-parameter WF with a one-parameter measure is supported (R3/R4, both in the pin), `gcd` itself elaborates, and R2's single-parameter rule IS `gcd`'s binding constraint |
//! | p9 | four refusals that were FALSE of the program | REPAIRED — the unfolded guard no longer presupposes an `@dite`; an `OfNat`-nested `0`/`1` is reported as an unread SPELLING, not a wrong VALUE; no source-reachable refusal double-wraps its backticks. **The fragment boundary did not move** — every source in p9 still refuses |

#![allow(clippy::doc_markdown)]

use clean_kernel::Environment;
use trust_clean_origin::emit::{CleanOriginShape, EmitRefusal, plan_clean_origin_body};
use trust_types::admissible_body::RecBodyExpr;

// ═══════════════════════════════════════════════════════════════════════════
// The one side-A source. Every probe goes through it.
// ═══════════════════════════════════════════════════════════════════════════

/// Elaborate and KERNEL-CHECK island sources through the real session, and
/// hand back the environment the planner will read.
///
/// The assertion is deliberate and is half of what this file measures: a
/// refusal that turns out to be an island-side rejection is not a statement
/// about the CALL lane at all, and the audit's own note about `down` was wrong
/// for exactly that reason until it was re-measured.
fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(
        !batch.is_rejected(),
        "the island must elaborate and kernel-check before the CALL lane is a question at \
         all: {batch:?}"
    );
    session.environment().expect("an untainted session has an environment").clone()
}

/// Elaborate ONE definition and plan it.
fn plan_source(source: &str, name: &str) -> Result<CleanOriginShape, EmitRefusal> {
    let env = island(&[source]);
    plan_clean_origin_body(&env, name).map(|plan| plan.shape().clone())
}

/// The refusal text for a source that must NOT plan, with the admit case
/// reported as a failure rather than silently passing.
fn refusal_of(source: &str, name: &str) -> String {
    match plan_source(source, name) {
        Ok(shape) => panic!("`{name}` was expected to refuse, but PLANNED as {shape:?}"),
        Err(refusal) => refusal.note(),
    }
}

/// `n + f (n - 1)` in the nonzero arm, `0` in the zero arm, `Pred` argument —
/// the one shape every admitting probe in this file expects.
fn canonical_shape() -> CleanOriginShape {
    CleanOriginShape::WellFoundedNatRec {
        zero_value: RecBodyExpr::NatConst(0),
        nonzero_value: RecBodyExpr::Add(
            Box::new(RecBodyExpr::Decreasing),
            Box::new(RecBodyExpr::Rec),
        ),
        rec_args: vec![RecBodyExpr::Pred],
        measure_index: 0,
        lowering: trust_clean_origin::WfLowering::OnParameter,
    }
}

/// The canonical fixture, verbatim from `tests/ui/trust/clean_origin_wf_rec.rs`.
const COUNTDOWN_SUM: &str = "def countdownSum (n : Nat) : Nat := \
                             if h : 0 < n then n + countdownSum (n - 1) else 0\n\
                             termination_by n";

// ═══════ (p1) THE CANONICAL FIXTURE PLANS ═══════

/// **The headline.** The exact island text the driver fixture carries plans,
/// and its plan is pinned field by field — because the emitter reads those
/// fields, and a plan that carried a different `rec_arg` or a flipped arm
/// would shape MIR the gate must then refuse.
///
/// Before this landing this island produced
/// *"its guard is not `0 < n` on the recursion's own parameter"* — about a
/// program whose guard is written `if h : 0 < n`. That refusal was the audit's
/// first diagnostic defect (v7/D3): the option it offered was the text already
/// on the screen.
#[test]
fn probe_p1_canonical_fixture_plans() {
    let env = island(&[COUNTDOWN_SUM]);
    let plan = plan_clean_origin_body(&env, "countdownSum")
        .expect("the canonical R2 fixture must plan against the REAL elaborated side A");

    assert_eq!(
        plan.shape(),
        &canonical_shape(),
        "the plan's fields ARE the emitter's contract: zero arm `0`, nonzero arm \
         `n + rec`, self-call argument `n - 1`"
    );
    assert_eq!(plan.name(), "countdownSum");

    // The CARRIER decision, which `check_wf_nat_signature` owns and which
    // `admit_wf_rec_lowering` re-checks the emitted body's arg count against.
    assert_eq!(plan.signature().arity(), 1, "single-parameter, the WF fragment's own boundary");
    assert_eq!(
        format!("{:?}", plan.return_ty()),
        "BignumNat",
        "the well-founded lane is stated at the bignum carrier only"
    );
    assert_eq!(format!("{:?}", plan.param_tys()), "[BignumNat]");

    eprintln!(
        "PROBE-ROW | p1 canonical countdownSum   | PLANS: WellFoundedNatRec {{ zero = 0, \
         nonzero = Decreasing + Rec, rec_arg = Pred }} at Nat -> Nat"
    );
}

// ═══════ (p2/p3) the RAW spellings still read ═══════

/// The raw `Nat.lt` guard — written literally in the source — still plans.
///
/// This is not redundant with p1: it is the control that widening the reader
/// to the surface tree did not REPLACE the raw one. Side B renders `Nat.lt
/// Nat.zero x`, and `reflect_wf.rs` is frozen, so a reader that stopped
/// accepting the raw form would have broken the gate's own comparison.
#[test]
fn probe_p2_raw_nat_lt_guard_still_plans() {
    let shape = plan_source(
        "def rawLt (n : Nat) : Nat := if h : Nat.lt 0 n then n + rawLt (n - 1) else 0\n\
         termination_by n",
        "rawLt",
    )
    .expect("the raw `Nat.lt` guard spelling must still read");
    assert_eq!(shape, canonical_shape());
    eprintln!("PROBE-ROW | p2 `Nat.lt 0 n` guard        | PLANS — the raw spelling still reads");
}

/// The raw `Nat.sub` predecessor — written literally in the source — still
/// plans. Same control, for the third site.
#[test]
fn probe_p3_raw_nat_sub_predecessor_still_plans() {
    let shape = plan_source(
        "def rawSub (n : Nat) : Nat := if h : 0 < n then n + rawSub (Nat.sub n 1) else 0\n\
         termination_by n",
        "rawSub",
    )
    .expect("the raw `Nat.sub` predecessor spelling must still read");
    assert_eq!(shape, canonical_shape());
    eprintln!("PROBE-ROW | p3 `Nat.sub n 1` self-call    | PLANS — the raw spelling still reads");
}

// ═══════ (p4) THE FULL GATE, on the real elaborated side A ═══════

/// The plan is not the verdict, so this probe takes the canonical fixture all
/// the way to `check_faithful_wf_functional` — the same F-layer judgment
/// `clean_origin_mir` reaches — with side B built by the FROZEN
/// `reflect_wf_functional` from the recognized dataflow.
///
/// It answers the question a plan cannot: whether re-deriving the three
/// spellings bought real capability, or only moved the refusal later and made
/// it less legible. It bought capability. The kernel identifies side B's raw
/// `dite (Nat.lt Nat.zero x) (Nat.decLt Nat.zero x) … (Nat.sub x 1) …` with
/// the elaborator's surface `dite (LT.lt Nat instLTNat 0 x)
/// (instDecidableNatLt 0 x) … (HSub.hSub … instHSubNat x 1) …`, which is the
/// three `first-party/clean` reduction facts cashed out by the real checker
/// rather than quoted from a source file.
///
/// The one step this cannot cover is the MIR round trip
/// (`trust_types::recognize_wf_nat_rec` over the emitted body), which needs
/// the compiler. That step compares the emitted body to the PLAN p1 pins, so
/// what is uncovered is the emitter, not the reading.
#[test]
fn probe_p4_canonical_fixture_passes_the_gate() {
    let env = island(&[COUNTDOWN_SUM]);
    let plan = plan_clean_origin_body(&env, "countdownSum").expect("p1");
    let CleanOriginShape::WellFoundedNatRec { zero_value, nonzero_value, rec_args, measure_index, lowering: _ } =
        plan.shape()
    else {
        panic!("p1 pins the shape");
    };

    // Side B, exactly as `admit_wf_rec_lowering` builds it: from the body
    // reading, through the frozen producer, with the defined constant
    // unnameable and every decrease slot left as the sentinel.
    let body = trust_types::admissible_body::WfRecBody {
        zero_value: zero_value.clone(),
        nonzero_value: nonzero_value.clone(),
        rec_args: rec_args.clone(),
        measure_index: *measure_index,
    };
    let reflected =
        trust_clean_origin::reflect_wf::reflect_wf_functional(&env, "countdownSum", &body, trust_clean_origin::WfLowering::OnParameter)
            .expect("the frozen producer must render the planned reading");

    let faithful = trust_clean_origin::gate::check_faithful_wf_functional(
        &env,
        "countdownSum",
        &reflected,
        plan.result_carrier(),
    )
    .expect(
        "THE POINT OF THE LANDING: the kernel must identify the frozen side B rendering \
         with the side A the REAL elaborator produced",
    );
    assert_eq!(
        format!("{:?}", faithful.method()),
        "WellFoundedFunctionalDefeq",
        "the F-layer judgment, not an equation route and not whole-term defeq"
    );

    eprintln!(
        "PROBE-ROW | p4 gate on real side A       | FAITHFUL by WellFoundedFunctionalDefeq \
         — frozen side B identified with the elaborator's surface spelling"
    );
}

// ═══════ (p5) `down` — the Bool-tested shape ═══════

/// `down` ELABORATES and KERNEL-CHECKS, and then REFUSES on the CALL side.
///
/// The two halves are separate questions and this probe pins both, because
/// the record has been wrong about each of them at different times.
///
/// * **The island half is fine, and that is the news.** `probe_w0` in
///   `r2_wf_equation_probes.rs` carried a standing instruction to re-measure
///   `down` on the next stage2 build, because the recorded island-side
///   rejection ("no decreasing proof was found … tried: hypothesis lookup,
///   `Nat.sub_lt`, omega, simp_arith") predated the `Nat.pos_of_ne_zero`
///   landing. Re-measured here, from this tree, through the real session:
///   with `termination_by n` present the Bool-tested `down` elaborates and
///   kernel-checks. The rejection is GONE.
/// * **The CALL half refuses**, and correctly so. Its guard is
///   `Eq Bool (BEq.beq Nat (instBEqOfDecidableEq Nat instDecidableEqNat) n 0)
///   Bool.true` under `instDecidableEqBool` — a different PROPOSITION, not a
///   different spelling of `0 < n` — and its branch POLARITY is inverted (the
///   `then` arm is the zero case). Admitting it is its own landing with its
///   own producer arm and its own mutation controls; it is not reachable by
///   relabelling this reader, and widening the reader to it would plan a body
///   whose emitted zero test selects the wrong arm.
#[test]
fn probe_p5_down_elaborates_but_refuses_at_the_call_lane() {
    let source = "def down (n : Nat) : Nat := if n == 0 then 0 else down (n - 1)\n\
                  termination_by n";
    // Half one: the island. `island` asserts it.
    let env = island(&[source]);
    assert!(
        env.get_const(&clean_kernel::Name::from_string("down")).is_some(),
        "RE-MEASURED 2026-08-22 from this tree: the Bool-tested `down` island elaborates \
         and kernel-checks with `termination_by n` present — the rejection `probe_w0` \
         recorded is gone"
    );

    // Half two: the CALL lane.
    let note = refusal_of(source, "down");
    assert!(
        note.contains("equality test"),
        "the refusal must be TRUE of the program in front of it — an equality-guarded \
         body, not a mis-spelled `0 < n`: {note}"
    );
    assert!(note.contains("if h : 0 < n"), "and it must carry the fix (v7/D3): {note}");
    assert!(
        note.contains("swap the two branches"),
        "and it must say what `down`'s shape actually needs — its `then` arm is the ZERO \
         case, the other way round from the emitted zero test: {note}"
    );

    eprintln!(
        "PROBE-ROW | p5 down (`if n == 0`)        | island: ELABORATES + kernel-checks \
         (re-measured) | CALL: REFUSES at the guard — a different proposition with \
         inverted polarity, its own landing"
    );
}

/// `n ≠ 0` is the equality family's OTHER polarity, and it gets its own hint.
///
/// It is a real near-miss: the elaborator's termination cascade discharges it
/// (via `Nat.pos_of_ne_zero`), so the island admits, and unlike `down` its
/// branches already stand the way the emitted zero test selects them — only
/// the guard proposition is wrong. Telling this user to "swap the branches"
/// would be advice that breaks a correct program, which is why the two shapes
/// do not share a refusal.
#[test]
fn probe_p5b_disequality_guard_gets_the_other_polarity_hint() {
    let note = refusal_of(
        "def neDown (n : Nat) : Nat := if h : n \u{2260} 0 then n + neDown (n - 1) else 0\n\
         termination_by n",
        "neDown",
    );
    assert!(
        note.contains("already stand the right way round"),
        "an `n ≠ 0` guard has the SAME branch polarity as `0 < n`; only the proposition \
         differs: {note}"
    );
    assert!(note.contains("if h : 0 < n"), "and it must carry the fix (v7/D3): {note}");

    eprintln!(
        "PROBE-ROW | p5b `n \u{2260} 0` guard            | REFUSES — same polarity as the \
         emitted test, different proposition; hint does NOT say to swap the arms"
    );
}

// ═══════ (p6) the refused mutations — one construct each ═══════

/// Seven single-construct mutations of the canonical fixture, each refused,
/// each naming the construct that was changed.
///
/// An ADMIT with no refused sibling is not a measurement: it cannot tell a
/// reader that decides from a reader that accepts. Every source here differs
/// from `COUNTDOWN_SUM` in exactly ONE construct, and every one of them
/// elaborates and kernel-checks — so the refusal under test is the CALL lane's,
/// never the island's. Sources that the island itself rejects are recorded in
/// `probe_p6b_mutations_the_island_rejects_first`, because "it refuses" means
/// nothing until you know WHICH side refused.
///
/// **One mutation is missing and its absence is a measurement.** A DEPENDENT
/// MOTIVE (`args[1]` of the fix spine other than `fun _ => Nat`) is not
/// source-reachable: the motive is synthesised from the declared result type,
/// so the only way to move it is to declare a result that is not `Nat` — and
/// that takes `check_wf_nat_signature`'s refusal first, which is exactly
/// mutation (e). The motive check is therefore a fail-closed backstop, like
/// the decidability instance in p6c — and, unlike that one, **no test in this
/// crate exercises it at all today** (grepped 2026-08-22: nothing asserts on
/// "its fix motive is not"). That is a named gap, not a covered case. It
/// belongs to a hand-built battery, because only a hand-built term can put a
/// dependent motive on a `WellFounded.fix` spine; it does not belong in this
/// file, whose whole contract is that side A comes from the real session.
/// Recording it as unreachable is more useful than writing a source that
/// "covers" it by tripping a different check.
#[test]
fn probe_p6_single_construct_mutations_refuse() {
    // (a) THE GUARD OFF THE RECURSION'S OWN PARAMETER. `n + 0` is the
    //     smallest source-level way to move the compared term off the binder
    //     while keeping the decrease derivable, so the island still admits and
    //     the refusal under test is ours.
    let off_param = refusal_of(
        "def offParam (n : Nat) : Nat := \
         if h : 0 < n + 0 then n + offParam (n - 1) else 0\n\
         termination_by n",
        "offParam",
    );
    // R3a re-worded the hint: "the recursion's own parameter" was unambiguous
    // only while the fragment was single-parameter, and a refusal that is
    // ambiguous about WHICH parameter it means is the v7/D3 defect this file
    // exists to catch.
    assert!(
        off_param.contains("something other than the parameter the recursion DESCENDS on"),
        "the emitted zero test decides a proposition about the parameter the recursion \
         descends on; a guard about anything else is a different proposition: {off_param}"
    );

    // (b) THE GUARD AGAINST A BOUND OTHER THAN ZERO. `0 + 0` is a numeral the
    //     numeral reader deliberately does not evaluate — an arithmetic term
    //     is not a literal — so this is the reachable form of "not `0`".
    let bound = refusal_of(
        "def wrongBound (n : Nat) : Nat := \
         if h : 0 + 0 < n then n + wrongBound (n - 1) else 0\n\
         termination_by n",
        "wrongBound",
    );
    assert!(
        bound.contains("bound other than `0`"),
        "the emitted body's test is a ZERO test: {bound}"
    );

    // (c) A SECOND SELF-CALL.
    let twice = refusal_of(
        "def twice (n : Nat) : Nat := \
         if h : 0 < n then twice (n - 1) + twice (n - 1) else 0\n\
         termination_by n",
        "twice",
    );
    assert!(
        twice.contains("more than one self-call"),
        "the single-call rule is what makes the gate's BORROW well-defined — one side-A \
         proof per side-B slot: {twice}"
    );

    // (d) A SELF-CALL AT SOMETHING OTHER THAN `n - 1`.
    let two_down = refusal_of(
        "def twoDown (n : Nat) : Nat := \
         if h : 0 < n then n + twoDown (n - 2) else 0\n\
         termination_by n",
        "twoDown",
    );
    // R3b moved the LAYER that answers this, not the answer. `n - 2` is now
    // READ (as an ordinary `Sub`, since a general truncated `-` is in the
    // vocabulary) and refused by `check_wf_fragment`'s decreasing-argument
    // belt. The boundary is still stated, and still stated in terms of the
    // `Nat::sub(&n, &1)` the emitted body computes.
    assert!(
        two_down.contains("DECREASING argument is not `n - 1`"),
        "the decrease amount is a stated boundary — the emitted body computes \
         `Nat::sub(&n, &1)`: {two_down}"
    );

    // (e) A NON-`Nat` CARRIER, which is `check_wf_nat_signature` — one of the
    //     three SOUNDNESS-ADJACENT checks this landing deliberately did not
    //     touch. It selects bignum MIR over machine-int MIR.
    let carrier = refusal_of(
        "def boolRes (n : Nat) : Bool := if h : 0 < n then boolRes (n - 1) else true\n\
         termination_by n",
        "boolRes",
    );
    assert!(
        carrier.contains("`Nat -> Nat`"),
        "the WF lane is stated at the bignum carrier only, because the reflected \
         functional's arithmetic is `Nat`'s: {carrier}"
    );

    // (f) A GUARD WHOSE DECISION IS A DIFFERENT INSTANCE. `1 <= n` resolves
    //     `Nat.decLe`, not the `0 < n` decision the emitted `Nat::is_zero`
    //     realises. Note WHERE it refuses: at the guard PROPOSITION, which is
    //     upstream of the instance check — see
    //     `probe_p6c_instance_check_is_a_backstop` for why no source reaches
    //     the instance check as a refusal at all.
    let le_guard = refusal_of(
        "def leDown (n : Nat) : Nat := \
         if h : 1 <= n then n + leDown (n - 1) else 0\n\
         termination_by n",
        "leDown",
    );
    assert!(
        le_guard.contains("`<=`"),
        "a `<=` guard is decided by a different procedure than the emitted zero \
         test: {le_guard}"
    );

    // (g) A VALUE OUTSIDE THE VOCABULARY. This is the catch-all, and it NAMES
    //     the constant rather than saying "an application" about every term it
    //     refuses.
    //
    //     **This row used to be `*`, and §R6 (2026-08-25) PAID IT OFF**: `*` is
    //     now the `nat.mul` row and `n * f (n - 1)` — factorial — PLANS
    //     (`r6_nat_mul_probes` q6/q9). The catch-all itself is unchanged and
    //     still needs a subject, so it moved one operation over to `/`, which
    //     is still outside the vocabulary and whose Rust realization PANICS
    //     where Clean's `Nat.div` is total. Recording the move rather than
    //     deleting the row keeps the flip auditable.
    let div = refusal_of(
        "def divDown (n : Nat) : Nat := \
         if h : 0 < n then n / divDown (n - 1) else 1\n\
         termination_by n",
        "divDown",
    );
    assert!(
        div.contains("`HDiv.hDiv`") || div.contains("`Nat.div`"),
        "the catch-all must name the construct it refused (v7/D3): {div}"
    );

    eprintln!(
        "PROBE-ROW | p6 seven mutations           | ALL REFUSE: guard off-parameter, \
         non-zero bound, second self-call, `n - 2`, Bool result, `<=` guard, `/`"
    );
}

/// The mutations the ISLAND rejects before this crate ever sees them — kept as
/// measurements, because a probe that asserted "refuses" on one of these would
/// be measuring `first-party/clean`'s termination cascade and reporting it as
/// evidence about the CALL lane.
///
/// This is not a footnote. It is the same confusion `probe_w0` recorded for
/// `down`, which then stood in the record for months as a CALL-lane fact.
#[test]
fn probe_p6b_mutations_the_island_rejects_first() {
    let rejected = |source: &str| {
        let mut session = trust_certify::clean_island::CleanIslandSession::new();
        assert!(
            session.check_all(&[source]).is_rejected(),
            "expected an ISLAND-side rejection for: {source}"
        );
    };

    // A guard against a literal bound: the decrease cascade cannot get
    // `n - 1 < n` out of `3 < n` (it tries hypothesis lookup, `Nat.sub_lt`,
    // `Nat.mod_lt`, positivity via `Nat.pos_of_ne_zero`, omega, simp_arith).
    rejected(
        "def wrongBound (n : Nat) : Nat := \
         if h : 3 < n then n + wrongBound (n - 1) else 0\n\
         termination_by n",
    );
    // A machine-carrier WF recursion: `0 < n` at `UInt64` is a type mismatch,
    // and routing the measure through `n.toNat` loses the cascade's decrease.
    rejected(
        "def wdown (n : UInt64) : UInt64 := \
         if h : 0 < n.toNat then n + wdown (n - 1) else 0\n\
         termination_by n.toNat",
    );
    // A self-call inside a self-call's argument.
    rejected(
        "def nested (n : Nat) : Nat := \
         if h : 0 < n then n + nested (nested (n - 1)) else 0\n\
         termination_by n",
    );

    eprintln!(
        "PROBE-ROW | p6b island-side rejections   | `3 < n`, a UInt64 measure and a nested \
         self-call never reach this crate — the cascade refuses them first"
    );
}

/// **The decidability-instance check is a BACKSTOP, and this probe is what
/// makes that a measurement rather than an assumption.**
///
/// The `dite` instance position is filled by instance RESOLUTION, which no
/// source text controls: every source spelling that gets past the guard check
/// carries `instDecidableNatLt`. The only way to name the instance yourself is
/// an explicit `@dite` — and in THAT position the elaborator delta-unfolds the
/// proposition to `Nat.le (Nat.succ 0) n` however it was written, so the guard
/// check refuses first, whatever instance you supplied. Measured over five
/// spellings here, including the two that supply the reader's own
/// `Nat.decLt 0 n`.
///
/// This CORRECTS the audit's stated mechanism. It attributed the explicit-`@dite`
/// refusal to explicit lambdas shifting the de Bruijn index off `bvar 1`; the
/// index is `bvar 1` either way, and the real cause is the delta-unfolding.
/// The audit's conclusion — that no source spelling cleared both checks —
/// survives; its reason did not.
///
/// The consequence for the fix is that pinning BOTH `Nat.decLt` and
/// `instDecidableNatLt` costs no capability and removes none: nothing a user
/// can write is refused by that check today, so it exists to fail closed if the
/// elaborator's resolution ever changes. That is the honest description, and
/// it belongs in a probe rather than in a comment nobody re-runs.
#[test]
fn probe_p6c_instance_check_is_a_backstop() {
    for (name, source) in [
        ("i1", "@dite Nat (@LT.lt Nat instLTNat 0 n) (Nat.decLe 1 n)"),
        ("i2", "@dite Nat (@LT.lt Nat instLTNat 0 n) (instDecidableNatLt 0 n)"),
        ("i3", "@dite Nat (Nat.lt 0 n) (Nat.decLe 1 n)"),
        ("i4", "@dite Nat (Nat.lt 0 n) (Nat.decLt 0 n)"),
        ("i5", "@dite Nat (@LT.lt Nat instLTNat 0 n) (Nat.decLt 0 n)"),
    ] {
        let source = format!(
            "def {name} (n : Nat) : Nat := \
             {source} (fun h => n + {name} (n - 1)) (fun h => 0)\n\
             termination_by n"
        );
        let note = refusal_of(&source, name);
        assert!(
            note.contains("`Nat.lt` already unfolded"),
            "an explicit `@dite` delta-unfolds the guard whatever instance is named, so \
             the GUARD refuses first — and the refusal must say that rather than call it \
             a `<=`: {note}"
        );
    }

    eprintln!(
        "PROBE-ROW | p6c instance check           | BACKSTOP — no source reaches it as a \
         refusal; explicit `@dite` delta-unfolds the guard first (5 spellings measured)"
    );
}

// ═══════ (p7) `n > 0` — the near-miss with the operand-order hint ═══════

/// `n > 0` is measured, elaborates, and is REFUSED — with a refusal that names
/// the one-word fix rather than restating the fragment.
///
/// It is a genuine near-miss: `GT.gt Nat instLTNat a b` is defeq to
/// `LT.lt Nat instLTNat b a` in this kernel. It stays outside anyway, because
/// side B renders `Nat.lt Nat.zero x` and NOTHING has measured the gate's
/// defeq through `GT.gt` on the stuck `dite` — and admitting an unmeasured
/// identification on the emit lane is precisely the move that produced the
/// C9 spelling gap. Fail-closed costs capability, never soundness; the hint
/// converts the cost into one edit.
#[test]
fn probe_p7_gt_guard_refuses_with_the_operand_order_hint() {
    let note = refusal_of(
        "def gtDown (n : Nat) : Nat := if h : n > 0 then n + gtDown (n - 1) else 0\n\
         termination_by n",
        "gtDown",
    );
    assert!(
        note.contains("the other way round"),
        "the refusal must name the ACTUAL difference — operand order — not tell the user \
         to write what they wrote: {note}"
    );
    assert!(note.contains("if h : 0 < n"), "and carry the fix: {note}");
    eprintln!(
        "PROBE-ROW | p7 `n > 0` guard             | REFUSES — operands reversed; hint names \
         the one-word fix"
    );
}

// ═══════ (p8) the SOUNDNESS-BEARING checks, unmoved ═══════

/// The carrier and arity decisions still refuse first, and still refuse with
/// their own text — they were not touched by the spelling re-derivation and
/// must not have been.
///
/// `check_wf_nat_signature` is the CARRIER decision: it selects bignum-`Nat`
/// MIR over machine-int MIR and is what `admit_wf_rec_lowering` re-checks the
/// emitted body's `arg_count` against. Relaxing it without moving the gate
/// would be guaranteed-refused work.
#[test]
fn probe_p8_signature_boundary_unmoved() {
    // Two parameters. This fixture IS rejected island-side — but **NOT for
    // the reason this probe used to state**, and the correction matters
    // because the conclusion drawn from it was backwards.
    //
    // RE-MEASURED 2026-08-25 from this pin (`r6_nat_mul_probes` q1/q5):
    //
    // * clean's elaborator SUPPORTS two-parameter well-founded recursion with
    //   a one-parameter measure — R3 (`27a46804e`) widened the signature and
    //   R4 (`1852198c0`) added the Bool-test spelling, and both are in the pin
    //   this crate builds against. `def gcd (a b : Nat) : Nat := if h : 0 < b
    //   then gcd b (a % b) else a  termination_by b` ELABORATES, kernel-checks
    //   with a foundational-only axiom closure, and computes `gcd 12 18 = 6`.
    // * `gcdish` below is refused because its MEASURE DOES NOT DECREASE —
    //   `termination_by b` against a call at `gcdish b (a - 1)` needs
    //   `a - 1 < b`, which no cascade tier can produce. The diagnostic says so:
    //   "no decreasing proof was found for a recursive call site".
    //
    // So the sentence this probe used to assert — "R2's single-parameter
    // boundary is not the binding constraint for `gcd`" — is false at this
    // pin. It IS the binding constraint: the island admits `gcd` and THIS
    // CRATE refuses it. The refused-fixture row is kept (an unsatisfiable
    // measure must still be an island rejection) with its true reason asserted.
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(&["def gcdish (a : Nat) (b : Nat) : Nat := \
         if h : 0 < b then gcdish b (a - 1) else a\n\
         termination_by b"]);
    assert!(batch.is_rejected(), "an unsatisfiable measure must be an ISLAND rejection");
    let why: String = batch
        .outcomes
        .iter()
        .flat_map(|o| o.errors.iter().map(|e| e.message.clone()))
        .collect::<Vec<_>>()
        .join(" | ");
    assert!(
        why.contains("no decreasing proof was found"),
        "the reason must be the MEASURE, not the arity — the arity is supported: {why}"
    );

    eprintln!(
        "PROBE-ROW | p8 signature boundary        | `gcdish`: refused ISLAND-side for its \
         UNSATISFIABLE MEASURE (not its arity — two-parameter WF is supported since R3); \
         non-Nat carrier: refused by check_wf_nat_signature (p6e)"
    );
}

// ═══════ (p9) REFUSALS THAT WERE FALSE OF THE PROGRAM ═══════

/// Three refusals that fired correctly but SAID something untrue about the
/// program in front of them. All three were found by adversarial review of the
/// spelling fix, all three are fixed here, and all three are pinned as
/// real-session rows so the class cannot come back.
///
/// v7/D3 is the ruling at stake: *"we state the rules but if somebody doesn't
/// follow the rules, then provide feedback via the compiler on how to fix the
/// situation."* A refusal whose stated reason is false of the program is worse
/// than a bare "unsupported" — it sends the reader to fix something that is
/// not wrong. The audit's own first diagnostic defect was exactly this shape,
/// and two of the three below were introduced in the arm written to fix it.
///
/// **None of these moved the fragment boundary.** Every source here still
/// refuses; only the stated reason changed.
#[test]
fn probe_p9_refusal_text_is_true_of_the_program() {
    // ── (a) `Nat.le (Nat.succ 0) n` written OUT, with no `@dite` anywhere ──
    //
    // The arm used to assert "which is what an explicit `@dite` elaborates
    // to" and prescribe "the `if h :` form". This source contains no `@dite`
    // and ALREADY uses `if h :`, so both halves were false of it. The kernel
    // term cannot distinguish the two routes, so the hint now names both.
    let note = refusal_of(
        "def leDown (n : Nat) : Nat := \
         if h : Nat.le (Nat.succ 0) n then n + leDown (n - 1) else 0\n\
         termination_by n",
        "leDown",
    );
    assert!(
        note.contains("either because"),
        "the unfolded-guard hint must not presuppose a source form it cannot observe — \
         this program has no `@dite`: {note}"
    );
    assert!(
        note.contains("if h : 0 < n"),
        "and must still carry the actionable fix, which is correct for both routes: {note}"
    );

    // ── (b) a bound that IS `0`, spelled one `OfNat` too deep ──
    //
    // Writing the numeral's instance explicitly makes the elaborator wrap it
    // AGAIN, so the guard arrives two `OfNat` deep and the reader (which reads
    // one) returns `None`. That `None` used to be reported as "a bound other
    // than `0`" — of a guard whose bound is `0`.
    let note = refusal_of(
        "def ofnDown (n : Nat) : Nat := \
         if h : @OfNat.ofNat Nat 0 (instOfNatNat 0) < n then n + ofnDown (n - 1) else 0\n\
         termination_by n",
        "ofnDown",
    );
    assert!(
        !note.contains("bound other than"),
        "the bound IS `0`; the refusal must not claim otherwise: {note}"
    );
    assert!(
        note.contains("one `OfNat` deep"),
        "it must name the SPELLING as what is unread, and say the value may be right: {note}"
    );

    // ── (c) a decrement that IS `1`, spelled the same way ──
    let note = refusal_of(
        "def ofnSub (n : Nat) : Nat := \
         if h : 0 < n then n + ofnSub (n - @OfNat.ofNat Nat 1 (instOfNatNat 1)) else 0\n\
         termination_by n",
        "ofnSub",
    );
    assert!(
        !note.contains("subtracts something other than"),
        "it subtracts exactly `1`; the refusal must not claim otherwise: {note}"
    );
    assert!(note.contains("one `OfNat` deep"), "same spelling diagnosis: {note}");

    // ── (d) no refusal on this lane double-wraps its backticks ──
    //
    // `render_spine_head` returns its OWN backticks; the instance arm wrapped
    // the result again and printed ``Nat.decLe``. That arm is unreachable from
    // source (the guard refuses first — p6c), so this sweeps every refusal a
    // source CAN reach instead.
    for (source, name) in [
        // NOT `n * m1 (n - 1)`: since §R6 that is FACTORIAL and it PLANS
        // (`r6_nat_mul_probes` q6). `/` is the operation that still refuses.
        (
            "def m1 (n : Nat) : Nat := if h : 0 < n then n / m1 (n - 1) else 1\n\
             termination_by n",
            "m1",
        ),
        // NOT `3 < n`: that one is refused ISLAND-side (clean finds no
        // decreasing proof), so it would measure the elaborator, not this
        // lane. Every row here elaborates and kernel-checks first.
        (
            "def m2 (n : Nat) : Nat := if h : n > 0 then n + m2 (n - 1) else 0\n\
             termination_by n",
            "m2",
        ),
        // WAS `n + n + m3 (n - 1)`, on the "no parameter twice in a branch"
        // rule. §R3b made that rule MOVE-AWARE and it now PLANS — measured, and
        // correctly: every one of those three uses of `n` lowers to a shared
        // borrow (`_7 = &_1; _8 = &_1; NatAdd(…)`), the emitter moves nothing,
        // and the gate admits the result against the real elaborated side A.
        // So the row is replaced by the shape the refined rule still refuses,
        // which is also the shape it EXISTS to refuse: a parameter handed to
        // the self-call BY ITSELF and used again in the same branch, whose
        // emission would borrow a local the call has already moved. That keeps
        // this sweep three-wide and points it at the new refusal's backticks.
        (
            "def m3 (a b : Nat) : Nat := if h : 0 < a then b + m3 (a - 1) b else 0\n\
             termination_by a",
            "m3",
        ),
    ] {
        let note = refusal_of(source, name);
        assert!(
            !note.contains("``"),
            "`{name}`: doubled backticks render as literal text, not code: {note}"
        );
    }

    eprintln!(
        "PROBE-ROW | p9 refusal-text truth        | 3 refusals that were FALSE of the \
         program, now true (unfolded guard, `OfNat`-nested bound, `OfNat`-nested \
         decrement) + no doubled backticks on any source-reachable refusal"
    );
}
