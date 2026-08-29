// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! **CONTROL 12 — §6f LANDING 5: the `==` producer, and the refusal that
//! ships in front of it.**
//!
//! `control_5`..`control_11` inject mutations into an EMITTED BODY. This
//! landing emits nothing — the `==` spelling has no MIR realization that side
//! B could tell apart from the propositional one — so there is no emitted body
//! to mutate, and the mutations that matter live in
//! `tests/landing5_selection_probes.rs::l5_p4`, where they are one-construct
//! changes to side B's TERM refused by the kernel.
//!
//! What is left for a control is everything a landing can get wrong when it
//! adds a producer nothing calls yet and a refusal everybody sees:
//!
//! * **half_0** — the row preflight: `select.eq` is untouched, and no row
//!   claims the `==` spelling.
//! * **half_1** — the producer mints the elaborator's tree CONSTRUCT FOR
//!   CONSTRUCT, not merely a definitionally-equal one. On a stuck `ite` those
//!   are the same thing (defeq is intensional here), but pinning the syntax is
//!   what makes a future elaborator change a failing test rather than a silent
//!   reliance on reduction.
//! * **half_2** — the FROZEN routes still mint the island's own `a = b` tree,
//!   construct for construct. Landing 5 added a fourth builder of one shape;
//!   this is the standing pin that it did not perturb the other three.
//! * **half_3** — the producer's own input guards fail closed BEFORE the
//!   kernel: an out-of-range numeral, an out-of-range index, mixed domains,
//!   and a non-machine domain.
//! * **half_4** — the refusal's v7/D3 contract, in full.
//! * **half_5** — the refusal does not fire on anything else, and — the one
//!   that matters for a new arm inserted into the planner's descent — **no
//!   body that planned before this landing plans differently after it**.
//! * **half_6** — E6 containment: the producer is not a reader, the
//!   `AdmissibleBody` vocabulary did not move, and the exhaustive match here
//!   makes a future variant a review event in this file too.

use clean_kernel::{Environment, Expr, ExprKind, Name};
use trust_clean_origin::table::{
    CarrierClass, MirShape, ReflectSpec, RowContext, UnwindDiscipline, row,
};
use trust_clean_origin::{CleanOriginShape, EmitRefusal, plan_clean_origin_body};
use trust_spec_elab::{Domain, MachineUIntWidth, SelectOperand};
use trust_types::admissible_body::{AdmissibleBody, ArithOperand, SelectCmp};

const WIDTHS: [u32; 4] = [8, 16, 32, 64];

fn island(sources: &[&str]) -> Environment {
    let mut session = trust_certify::clean_island::CleanIslandSession::new();
    let batch = session.check_all(sources);
    assert!(!batch.is_rejected(), "the island must kernel-check: {batch:?}");
    session.environment().expect("an untainted session has an environment").clone()
}

fn machine(bits: u32) -> Domain {
    Domain::Machine(match bits {
        8 => MachineUIntWidth::U8,
        16 => MachineUIntWidth::U16,
        32 => MachineUIntWidth::U32,
        64 => MachineUIntWidth::U64,
        other => panic!("{other} is not a machine width this control measures"),
    })
}

fn body_of(env: &Environment, name: &str) -> Expr {
    env.get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("the island registered no value for `{name}`"))
}

/// Peel every lambda: the binder METADATA is not what this landing is about,
/// and comparing bodies under the binders is the sharper comparison anyway —
/// it is where every construct a producer could get wrong actually lives.
fn peel(body: &Expr) -> &Expr {
    let mut cursor = body;
    while let ExprKind::Lam(_, _, inner) = cursor.kind() {
        cursor = &**inner;
    }
    cursor
}

fn mint(
    env: &Environment,
    mint: impl FnOnce(&mut Environment, &str) -> Result<trust_spec_elab::Admission, String>,
) -> Result<Expr, String> {
    let mut scratch = env.clone();
    let name = "control12_reflection";
    mint(&mut scratch, name)?;
    scratch
        .get_const(&Name::from_string(name))
        .and_then(|c| c.value.clone())
        .ok_or_else(|| "the reflected definition carries no value".to_owned())
}

fn refusal_text(refusal: &EmitRefusal) -> String {
    match refusal {
        EmitRefusal::NotEmittable { reason, .. } => reason.clone(),
        other => panic!("expected `NotEmittable`, got {other:?}"),
    }
}

// ── half_0 — the row preflight ──────────────────────────────────────────────

/// The `==` spelling did NOT become a row, and `select.eq` is byte for byte
/// the row landing 3 left behind.
///
/// A new row would have had to realize `MirShape::ComparisonBranch(Eq)` — the
/// realization `select.eq` already carries, at the same context, carrier and
/// gate — which `table_controls::h_c_shared_mir_realizations_are_declared_and_
/// separated` admits only for rows separated on side A **and** routed to
/// different gates. Neither escape exists here, and manufacturing one is what
/// landing 2 recorded as "the wrong unit".
///
/// # SUPERSEDED IN PART by §6f landing 6 — the row EXISTS, because the
/// REALIZATION changed
///
/// The paragraph above is still the reason a row could not exist *while the
/// `==` spelling realized `ComparisonBranch(Eq)`*. Landing 6 changed exactly
/// that: `select.beq` realizes `MirShape::BoolDecisionBranch` — the two-step
/// diamond — which no other row realizes, so the alias never arises and H-C has
/// nothing to separate. What this half now asserts is the half that did NOT
/// change: `select.eq` is byte for byte what landing 3 left behind, and
/// `select.ne` still does not exist. The row's own legality is executed by
/// `landing6_selection_probes::l6_p7`.
#[test]
fn half_0_the_select_eq_row_is_untouched_and_the_beq_spelling_has_no_row() {
    let eq = row("select.eq").expect("`select.eq` must still exist");
    assert_eq!(eq.context, RowContext::Body);
    assert_eq!(eq.carrier, CarrierClass::MachineUInt);
    assert_eq!(eq.mir, MirShape::ComparisonBranch(SelectCmp::Eq));
    assert_eq!(eq.unwind, UnwindDiscipline::NoCall);
    assert!(
        matches!(eq.reflect, ReflectSpec::ElabSurface(_)),
        "`select.eq` reflects through a FROZEN producer and rides its pedigree; the landing-5 \
         producer is a FOURTH route and deliberately does not become this row's reflection"
    );
    assert!(eq.tcb_row.is_none(), "nothing new is trusted in `select.eq`");
    assert!(
        row("select.ne").is_none(),
        "`!=` still has no row: its blocker moved in landing 6 but did not clear, and there is \
         no `Bool.not` in the emitted vocabulary, in side B's reader, or in the producer"
    );
    let beq = row("select.beq").expect("§6f landing 6 adds the `==` row");
    assert_ne!(
        beq.mir, eq.mir,
        "the `==` row exists ONLY because its realization differs. If these ever agree again, \
         H-C has an undeclarable alias — same layer, same carrier, same gate, same bytes — and \
         landing 5's refusal is back in force."
    );
}

// ── half_1 — the producer mints the elaborator's tree, construct for construct ──

/// **Not just defeq — IDENTICAL.**
///
/// `l5_p4` measures that the kernel ADMITS the producer's term against the
/// real elaboration. That is the verdict that matters, but on a stuck `ite` it
/// is also the weakest possible evidence, because defeq is intensional there:
/// an ADMIT on this shape means the terms were already the same. Pinning the
/// syntax says so out loud, and turns a future elaborator change from a silent
/// reliance on reduction into a failing test in this file.
#[test]
fn half_1_the_beq_producer_reproduces_the_elaborated_tree_exactly() {
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqbeq (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == b then a else b"
            ),
            &format!(
                "def eqlit (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a == 5 then 6 else b"
            ),
        ]);
        for (name, cmp_right, then_arm, else_arm) in [
            ("eqbeq", SelectOperand::Param(1), SelectOperand::Param(0), SelectOperand::Param(1)),
            (
                "eqlit",
                SelectOperand::Literal(5),
                SelectOperand::Literal(6),
                SelectOperand::Param(1),
            ),
        ] {
            let minted = mint(&env, |scratch, reflected| {
                trust_spec_elab::admit_select_beq_function(
                    scratch,
                    reflected,
                    &[machine(bits), machine(bits)],
                    0,
                    cmp_right,
                    then_arm,
                    else_arm,
                )
            })
            .expect("the `==` route mints");
            assert_eq!(
                peel(&minted),
                peel(&body_of(&env, name)),
                "u{bits} `{name}`: the `==` producer must reproduce the ELABORATED tree \
                 construct for construct. A term that is only definitionally equal would be \
                 admitted here by accident of reduction, and this shape has none: both sides \
                 are stuck on a neutral `Decidable`"
            );
        }
    }
}

// ── half_2 — the three frozen routes did not move ───────────────────────────

/// Landing 5 adds a FOURTH builder of one `ite` shape. `l5_p5` pins that it
/// differs from landing 3's general route in exactly the two condition
/// positions; this pins the other direction — that the three pre-existing
/// routes still mint the island's own tree, construct for construct, against
/// an anchor outside this crate entirely (the elaborator's `a = b`).
#[test]
fn half_2_the_frozen_select_routes_still_mint_the_islands_own_tree() {
    for bits in WIDTHS {
        let env = island(&[
            &format!(
                "def eqprop (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a = b then a else b"
            ),
            &format!(
                "def ltprop (a : UInt{bits}) (b : UInt{bits}) : UInt{bits} := \
                 if a < b then a else b"
            ),
        ]);
        let anchor = |name: &str, cmp: trust_spec_elab::SelectCmp| {
            let frozen = mint(&env, |scratch, reflected| {
                trust_spec_elab::admit_select_function(
                    scratch,
                    reflected,
                    &[machine(bits), machine(bits)],
                    cmp,
                    0,
                    1,
                    0,
                    1,
                )
            })
            .expect("the frozen route mints");
            assert_eq!(
                peel(&frozen),
                peel(&body_of(&env, name)),
                "u{bits} `{name}`: the frozen parameter-select route must still mint exactly \
                 what the island elaborates"
            );
            // …and landing 3's general route agrees with it on the overlap,
            // which is l3_p4's standing claim restated at this landing's
            // widths so that adding a fourth builder cannot quietly retire it.
            let general = mint(&env, |scratch, reflected| {
                trust_spec_elab::admit_select_operands_function(
                    scratch,
                    reflected,
                    &[machine(bits), machine(bits)],
                    cmp,
                    0,
                    SelectOperand::Param(1),
                    SelectOperand::Param(0),
                    SelectOperand::Param(1),
                )
            })
            .expect("the general route mints");
            assert_eq!(
                peel(&general),
                peel(&frozen),
                "u{bits} `{name}`: the general route must still reproduce the frozen route on \
                 the overlap (l3_p4)"
            );
        };
        anchor("eqprop", trust_spec_elab::SelectCmp::Eq);
        anchor("ltprop", trust_spec_elab::SelectCmp::Lt);
    }
}

// ── half_3 — the producer's input guards fail closed BEFORE the kernel ───────

/// Every guard the three sibling routes carry, carried here too and measured
/// here too. A producer that reached the kernel with a bad input would be
/// relying on the kernel to catch a class of error the kernel was never asked
/// about — an out-of-range numeral, for instance, is a perfectly well-typed
/// term at the wrong VALUE.
#[test]
fn half_3_the_producer_input_guards_fail_closed() {
    let env = island(&["def anchor (a : UInt64) : UInt64 := a"]);
    let attempt = |domains: Vec<Domain>,
                   cmp_left: usize,
                   cmp_right: SelectOperand,
                   then_arm: SelectOperand,
                   else_arm: SelectOperand| {
        mint(&env, |scratch, reflected| {
            trust_spec_elab::admit_select_beq_function(
                scratch, reflected, &domains, cmp_left, cmp_right, then_arm, else_arm,
            )
        })
    };
    let p0 = SelectOperand::Param(0);
    let p1 = SelectOperand::Param(1);

    // an out-of-range NUMERAL — 256 does not fit u8, and `Domain::numeral`
    // range-checks before the kernel rather than reducing modulo 2^8.
    assert!(
        attempt(vec![machine(8), machine(8)], 0, p1, SelectOperand::Literal(256), p1).is_err(),
        "an out-of-range arm numeral must fail closed; silently reducing it modulo the width \
         would emit a value the definition does not name"
    );
    assert!(
        attempt(vec![machine(8), machine(8)], 0, SelectOperand::Literal(300), p0, p1).is_err(),
        "…and so must an out-of-range comparison numeral"
    );
    // an out-of-range INDEX, in each of the three parameter positions.
    for (left, right, then_arm, else_arm) in [
        (2usize, p1, p0, p1),
        (0, SelectOperand::Param(9), p0, p1),
        (0, p1, SelectOperand::Param(4), p1),
        (0, p1, p0, SelectOperand::Param(7)),
    ] {
        assert!(
            attempt(vec![machine(64), machine(64)], left, right, then_arm, else_arm).is_err(),
            "an out-of-range parameter index must be refused before the kernel"
        );
    }
    // MIXED domains, and a non-machine domain.
    assert!(
        attempt(vec![machine(64), machine(32)], 0, p1, p0, p1).is_err(),
        "a select over mixed parameter domains has no single carrier and must be refused"
    );
    assert!(
        attempt(vec![Domain::Nat, Domain::Nat], 0, p1, p0, p1).is_err(),
        "the `==` spelling is stated over the machine widths; `Nat` is not measured here and \
         must not be minted on the strength of looking similar"
    );
    // and ZERO parameters, which has no comparison to make.
    assert!(attempt(Vec::new(), 0, p1, p0, p1).is_err(), "a nullary select is not a select");
}

// ── half_4 — the refusal's v7/D3 contract ───────────────────────────────────

/// Ruling v7/D3: *"we state the rules but if somebody doesn't follow the
/// rules, then provide feedback via the compiler on how to fix the situation
/// (provide options)"*. This executes the contract rather than describing it.
///
/// # NARROWED by §6f landing 6 — the CONTRACT is identical, the SUBJECT is not
///
/// `a == b` over the shared select operand vocabulary now PLANS, so the `==`
/// half of this control runs over the bodies that still do not: an `==` whose
/// OPERAND is outside the fragment. Every clause of the v7/D3 contract is kept
/// verbatim — name the operator, name the kernel tree, name the authenticated
/// instance, state the boundary as measured rather than as a rule, cite the
/// work item, offer options including the always-available `ensures` one — and
/// one clause is ADDED, which is the landing's own obligation: the refusal must
/// now blame the OPERAND rather than the operator, because blaming the operator
/// would send a user to change a character that is no longer the problem.
/// The `!=` half is untouched.
#[test]
fn half_4_the_refusal_carries_the_diagnosis_the_fix_and_the_options() {
    let env = island(&[
        "def eqcomputed (a : UInt64) (b : UInt64) : UInt64 := if a + 1 == b then a else b",
        "def neqbeq (a : UInt64) (b : UInt64) : UInt64 := if a != b then a else b",
    ]);

    let eq = plan_clean_origin_body(&env, "eqcomputed").expect_err("a computed operand has no row");
    assert!(!eq.is_compiler_defect(), "a fragment boundary is not a compiler defect");
    let text = refusal_text(&eq);
    for fragment in [
        "`==`",                         // what the user wrote
        "BEq.beq",                      // what the kernel saw
        "instBEqOfDecidableEq",         // …authenticated, so a different instance is not this
        "Bool.true",                    // the scrutinee the whole spelling turns on
        "an OPERAND, not the operator", // landing 6: WHERE the boundary now is
        "select.beq",                   // …and the row that does serve the operator
        "v7/D2",                        // a measured boundary, not a rule
        "§6f landing 6",                // the work item, by name
        "options:",
        "ensures", // the always-available third option
    ] {
        assert!(text.contains(fragment), "the `==` refusal must contain {fragment:?}:\n{text}");
    }
    assert!(
        !text.contains("write the condition as the PROPOSITION instead"),
        "landing 6: an out-of-fragment OPERAND must not be told to change the OPERATOR. `==` \
         is emittable now; changing it to `=` would not fix a computed operand and an option \
         that does not work is worse than no option:\n{text}"
    );

    let ne = refusal_text(&plan_clean_origin_body(&env, "neqbeq").expect_err("`!=` has no row"));
    assert!(ne.contains("`!=`"), "the `!=` refusal must name the operator it found:\n{ne}");
    assert!(
        ne.contains("Bool.not"),
        "…and the construct that distinguishes it from `==`, which is where the negation \
         lives:\n{ne}"
    );
    assert!(
        !ne.contains("- write the condition as the PROPOSITION instead"),
        "the `!=` refusal must NOT offer the `==` fix. There is no propositional disequality \
         this lane emits either, and an option that does not work is worse than no option:\n{ne}"
    );
    assert!(
        ne.contains("restate the branch positively"),
        "…it must offer the one that DOES work — swapping the arms of an `=` test:\n{ne}"
    );
}

// ── half_5 — the new arm changed no existing verdict ────────────────────────

/// **A new arm in the planner's descent is a chance to reorder somebody
/// else's verdict.** The arm added by this landing sits after every
/// recognizer, so by construction it cannot take a body that used to plan;
/// this executes that claim over one body per shipped rung rather than
/// trusting the reading of a `return`.
#[test]
fn half_5_no_body_that_planned_before_plans_differently_now() {
    let env = island(&[
        "def proj (a : UInt64) (b : UInt64) : UInt64 := a",
        "def sum (a : UInt64) (b : UInt64) : UInt64 := a + b",
        "def poly (a : UInt64) (b : UInt64) : UInt64 := a * b + a",
        "def konst (a : UInt64) : UInt64 := 6",
        "def lt (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else b",
        "def le (a : UInt64) (b : UInt64) : UInt64 := if a <= b then a else b",
        "def eq (a : UInt64) (b : UInt64) : UInt64 := if a = b then a else b",
        "def thr (a : UInt64) (b : UInt64) : UInt64 := if a < 10 then a else b",
        "def clampz (a : UInt64) (b : UInt64) : UInt64 := if a < b then a else 0",
    ]);
    let expected = [
        ("proj", CleanOriginShape::Projection { projected: 0 }),
        ("konst", CleanOriginShape::ConstantUint { value: 6 }),
        (
            "lt",
            CleanOriginShape::Select {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "le",
            CleanOriginShape::Select {
                cmp: SelectCmp::Le,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "eq",
            CleanOriginShape::Select {
                cmp: SelectCmp::Eq,
                cmp_left: 0,
                cmp_right: 1,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "thr",
            CleanOriginShape::SelectLiteral {
                cmp: SelectCmp::Lt,
                cmp_param: 0,
                literal: 10,
                then_param: 0,
                else_param: 1,
            },
        ),
        (
            "clampz",
            CleanOriginShape::SelectOperands {
                cmp: SelectCmp::Lt,
                cmp_left: 0,
                cmp_right: ArithOperand::Param(1),
                then_arm: ArithOperand::Param(0),
                else_arm: ArithOperand::Const(0),
            },
        ),
    ];
    for (name, shape) in expected {
        let plan = plan_clean_origin_body(&env, name)
            .unwrap_or_else(|refusal| panic!("`{name}` planned before landing 5: {refusal:?}"));
        assert_eq!(plan.shape(), &shape, "`{name}` planned a DIFFERENT shape after landing 5");
    }
    // the two arithmetic rungs, whose payloads are checked by their own
    // controls; here only that they still plan as themselves.
    assert!(
        matches!(
            plan_clean_origin_body(&env, "sum").map(|p| p.shape().clone()),
            Ok(CleanOriginShape::WrappingBinOp { .. })
        ),
        "the single wrapping op must still plan"
    );
    assert!(
        matches!(
            plan_clean_origin_body(&env, "poly").map(|p| p.shape().clone()),
            Ok(CleanOriginShape::Composed { .. })
        ),
        "the composed tree must still plan"
    );
}

// ── half_6 — E6 containment ────────────────────────────────────────────────

/// The landing added a PRODUCER, which is side B's minting half, and no
/// READER. So the E6 kernel-import direction — which consumes
/// `AdmissibleBody` and nothing else — cannot have moved, and this match
/// makes a future variant a review event here as well as in
/// `trust_certify::clean_island::admit_function_into`.
#[test]
fn half_6_the_e6_import_vocabulary_did_not_move() {
    fn e6_vocabulary(body: &AdmissibleBody) -> &'static str {
        match body {
            AdmissibleBody::ConstantUint { .. } => "constant",
            AdmissibleBody::Projection { .. } => "projection",
            AdmissibleBody::Arithmetic { .. } => "arithmetic",
            AdmissibleBody::Composed { .. } => "composed",
            AdmissibleBody::Select { .. } => "select",
            AdmissibleBody::SelectLiteral { .. } => "select-literal",
        }
    }
    let sample = AdmissibleBody::Projection { param: 0 };
    assert_eq!(
        e6_vocabulary(&sample),
        "projection",
        "the E6 vocabulary is pinned BY TYPE: this match is exhaustive with no wildcard, so a \
         new `AdmissibleBody` variant fails compilation HERE as well as in the gate-free \
         kernel-import direction. Landing 5 adds none — its capability half is a producer, and \
         a producer is not a reader."
    );
}
