// EXACT CALL FRAMES on a loop transition path.
//
// THE MEASURED BLOCKER this file covers. Before `exact_call_frame`, ANY
// `Terminator::Call` inside a loop body returned `e45.transition.call-effect`
// and the loop had "no complete exact transition model", so every clause row on
// it came back `UnsupportedMir`. ay's own probe file records the isolation:
// "the same loop with no call proves; adding one call turns every clause row
// into UNKNOWN". 96% of the corpus's loop-containing bodies contain a call, so
// that one refusal is why `proved_by_kind.invariant` is 0.
//
// WHAT IS AND IS NOT ASSUMED. An admitted call's destination receives a FRESH
// UNCONSTRAINED symbol. No fact about any callee is asserted anywhere — not the
// return value, not totality, not panic-freedom, not purity, and no name is
// consulted. What the admissibility conditions establish, entirely from the
// CALLER's own MIR, is the FRAME: that the callee cannot write any state entry
// the model carries across the call unchanged.
//
// Both directions are load-bearing and are checked separately here, because a
// lane that makes everything prove is worth nothing:
//
//   * `frame_proves_the_loop_carried_scalar_a_call_cannot_write` — a CONTINGENT
//     invariant (`shift == 0`, carried through the pre-state) proves through a
//     call, and kernel-certifies.
//   * `havoced_destination_refutes_an_invariant_that_depends_on_the_call_result`
//     — the SAME loop with the latch fed from the call's result must NOT prove.
//     This is the assertion that pins "nothing is assumed about the callee".
//   * `vacuity_table_*` — the codebase's signature failure is a widening whose
//     newly-provable set is exactly the tautologies. The table is measured, not
//     argued.
//   * `adversarial_*` — a callee that can write state the invariant depends on
//     must be REFUSED, with a diagnostic that names the construct.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

fn span(line: u32) -> SourceSpan {
    SourceSpan {
        file: "loop_call_frame.rs".to_string(),
        line_start: line,
        col_start: 0,
        line_end: line,
        col_end: 80,
    }
}

/// How the latch re-defines the loop-carried scalar `shift`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Latch {
    /// `shift = shift` — the loop-carried value survives the call. Proving an
    /// invariant about it requires the FRAME (the callee cannot write `shift`)
    /// and nothing about what the callee returns.
    CarryShift,
    /// `shift = chunk` — the loop-carried value is the CALL'S RESULT. Nothing
    /// is known about it, so no invariant constraining it may prove.
    TakeCallResult,
}

/// ```text
/// fn f(xs: &[u32], keep: bool) {
///     let mut shift: u32 = 0;
///     while keep {
///         // invariant: <parameter>
///         let chunk = observe(xs);   // CALL, dest `chunk`, arg a shared slice
///         shift = <latch>;
///     }
/// }
/// ```
///
/// Locals: `_0` unit return, `_1` `xs: &[u32]`, `_2` `keep: bool`,
/// `_3` `shift: u32`, `_4` `chunk: u32`.
fn call_in_loop(latch: Latch) -> VerifiableFunction {
    let latch_rvalue = match latch {
        Latch::CarryShift => Rvalue::Use(Operand::Copy(Place::local(3))),
        Latch::TakeCallResult => Rvalue::Use(Operand::Copy(Place::local(4))),
    };
    VerifiableFunction {
        name: "call_in_loop".to_string(),
        def_path: "test::call_in_loop".to_string(),
        span: span(1),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref {
                        mutable: false,
                        inner: Box::new(Ty::Slice { elem: Box::new(Ty::u32()) }),
                    },
                    name: Some("xs".to_string()),
                },
                LocalDecl { index: 2, ty: Ty::Bool, name: Some("keep".to_string()) },
                LocalDecl { index: 3, ty: Ty::u32(), name: Some("shift".to_string()) },
                LocalDecl { index: 4, ty: Ty::u32(), name: Some("chunk".to_string()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                        span: span(2),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(4),
                        exhaustive_enum_unreachable: false,
                        span: span(3),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![],
                    terminator: Terminator::Call {
                        func: "observe".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(3)),
                        span: span(4),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: None,
                        unwind: UnwindEdge::Unreachable,
                    },
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: latch_rvalue,
                        span: span(5),
                    }],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn loop_spec(body: &str) -> LoopContractSpec {
    LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        source_hir_local_id: None,
        mir_header: None,
        loop_head: SourceSpan { line_end: 6, ..span(3) },
        header_span: span(3),
        span: span(3),
        body: body.to_string(),
    }
}

struct LoopRows {
    initiation: Option<VerificationCondition>,
    consecution: Option<VerificationCondition>,
    unsupported: Vec<String>,
}

impl LoopRows {
    fn consecution(&self) -> &VerificationCondition {
        self.consecution
            .as_ref()
            .unwrap_or_else(|| panic!("no E4 consecution row; unsupported: {:?}", self.unsupported))
    }
}

/// Generate and discharge the loop rows for `invariant` on `func`.
///
/// The decision oracle is `trust_certify::certify_vc` — the CLEAN KERNEL, and
/// the actual production door for these rows. It is formula-driven rather than
/// kind-driven, so it decides a `LoopInvariantConsecution` row that the
/// in-process ay backend declines by kind (`can_handle` admits only L0 safety
/// obligations). Certification is also the verdict that counts under
/// `-Ztrust-policy=certify`: an uncertified UNSAT is reported Unknown.
fn rows(mut func: VerifiableFunction, invariant: &str) -> LoopRows {
    assert!(
        bind_compiler_loop_contracts(&mut func, &[loop_spec(invariant)]).is_empty(),
        "the compiler loop contract must bind"
    );
    let (mut vcs, preclassified) = generate_vcs_with_discharge(&func);
    let mut unsupported = Vec::new();
    for (vc, _) in &preclassified {
        if let VcKind::UnsupportedMir { detail, .. } = &vc.kind {
            unsupported.push(detail.clone());
        }
    }
    vcs.extend(preclassified.into_iter().map(|(vc, _)| vc));

    let mut initiation = None;
    let mut consecution = None;
    for vc in vcs {
        match vc.kind {
            VcKind::LoopInvariantInitiation { .. } => initiation = Some(vc),
            VcKind::LoopInvariantConsecution { .. } => consecution = Some(vc),
            _ => {}
        }
    }
    LoopRows { initiation, consecution, unsupported }
}

/// Kernel-certified UNSAT: the row is discharged.
fn certified(vc: &VerificationCondition) -> bool {
    trust_certify::certify_vc(vc).is_some()
}

/// Every free symbol the formula mentions.
fn symbols(formula: &Formula) -> Vec<String> {
    let mut names = Vec::new();
    formula.visit(&mut |node| match node {
        Formula::Var(name, _) => names.push(name.clone()),
        Formula::SymVar(name, _) => names.push(name.to_string()),
        _ => {}
    });
    names.sort();
    names.dedup();
    names
}

// ---------------------------------------------------------------------------
// The capability itself
// ---------------------------------------------------------------------------

/// A CONTINGENT loop invariant discharged across a call.
///
/// `shift == 0` is not a tautology: it is false in the sibling fixture below,
/// which differs only in what the latch assigns. It is carried by the PRE-state
/// (`shift = shift`), so the consecution formula is discharged by the frame
/// argument — `observe` cannot write `shift` — and by nothing else. No fact
/// about `observe` is available to the solver, and the formula proves anyway.
#[test]
fn frame_proves_the_loop_carried_scalar_a_call_cannot_write() {
    let rows = rows(call_in_loop(Latch::CarryShift), "shift == 0");
    assert!(
        rows.unsupported.is_empty(),
        "a call with an exact frame must not fail the loop closed: {:?}",
        rows.unsupported,
    );

    let initiation = rows.initiation.as_ref().expect("E4 initiation row must exist");
    assert!(
        matches!(initiation.kind, VcKind::LoopInvariantInitiation { .. }),
        "kind is the initiation row",
    );
    assert!(certified(initiation), "initiation must certify; formula: {:?}", initiation.formula);

    let consecution = rows.consecution();
    assert!(
        matches!(consecution.kind, VcKind::LoopInvariantConsecution { .. }),
        "kind is the consecution row",
    );

    // THE FORMULA MUST CONSTRAIN SOMETHING. A row that proves because it is
    // syntactically `false`, or because it mentions no program state, is a
    // vacuous discharge. This one must bind the loop-carried local by name.
    let names = symbols(&consecution.formula);
    assert!(
        names.iter().any(|name| name == "shift"),
        "the consecution formula must constrain the loop-carried local; symbols: {names:?}",
    );
    assert!(
        !matches!(consecution.formula, Formula::Bool(_)),
        "a constant consecution formula discharges nothing: {:?}",
        consecution.formula,
    );

    assert!(
        certified(consecution),
        "the consecution row must be KERNEL-CERTIFIED — an uncertified UNSAT is \
         reported Unknown under -Ztrust-policy=certify; formula: {:?}",
        consecution.formula,
    );
}

/// The direction that pins "NOTHING is assumed about the callee".
///
/// This fixture is the previous one with ONE statement changed: the latch takes
/// the call's RESULT instead of the loop-carried value. `observe` really can
/// return anything, so `shift == 0` is false of this program, and the row must
/// not prove. If a call summary had claimed a return value — or if the
/// destination were carried across unchanged instead of havoced — this would
/// come back Proved, and that would be a false proof.
#[test]
fn havoced_destination_refutes_an_invariant_that_depends_on_the_call_result() {
    let rows = rows(call_in_loop(Latch::TakeCallResult), "shift == 0");
    assert!(
        rows.unsupported.is_empty(),
        "the frame is still exact here; only the invariant is false: {:?}",
        rows.unsupported,
    );
    let consecution = rows.consecution();
    assert!(
        !certified(consecution),
        "an invariant constraining an unconstrained call result must not be \
         discharged; formula: {:?}",
        consecution.formula,
    );
    let names = symbols(&consecution.formula);
    assert!(
        names.iter().any(|name| name.starts_with("chunk#e45_call_bb")),
        "the call's destination must appear as a FRESH symbol, not as `chunk`; \
         symbols: {names:?}",
    );
}

// ---------------------------------------------------------------------------
// VACUITY TABLE
// ---------------------------------------------------------------------------

/// The mandated vacuity table, measured on a loop that CONTAINS A CALL — i.e.
/// on exactly the shape this lane newly admits.
///
/// The failure this guards against: a widening whose newly-provable set is the
/// TAUTOLOGIES. `1 == 1`, `x == x`, `x <= x` and `true` are tautologies and are
/// expected to prove (they proved before this lane too, on call-free loops, and
/// their proving carries no information). `false` must never prove. The row
/// that decides whether the lane is worth anything is the CONTINGENT one,
/// `shift == 0`, which is covered by its own test above: it proves here and is
/// refuted by the sibling fixture, so the newly-provable set is strictly larger
/// than the tautologies.
#[test]
fn vacuity_table_over_a_loop_containing_a_call() {
    let mut table = Vec::new();
    for predicate in ["1 == 1", "shift == shift", "shift <= shift", "true", "false", "shift >= 0"] {
        let rows = rows(call_in_loop(Latch::CarryShift), predicate);
        let cell = |row: Option<&VerificationCondition>| match row {
            Some(vc) if certified(vc) => "certified",
            Some(_) => "not-discharged",
            None => "no-row",
        };
        let outcome = if rows.unsupported.is_empty() {
            format!(
                "initiation={} consecution={}",
                cell(rows.initiation.as_ref()),
                cell(rows.consecution.as_ref()),
            )
        } else {
            "refused".to_string()
        };
        table.push((predicate, outcome));
    }
    let rendered = table
        .iter()
        .map(|(predicate, outcome)| format!("  {predicate:<16} {outcome}"))
        .collect::<Vec<_>>()
        .join("\n");
    println!("VACUITY TABLE (loop containing a call):\n{rendered}");

    // `false` is the row that matters, and it is NOT enough to look at
    // consecution alone. `false AND guard AND NOT false` is trivially UNSAT, so
    // the CONSECUTION row for `invariant false` certifies — correctly, since
    // `false` really is preserved vacuously. What must never happen is the pair
    // being discharged, and the INITIATION row is what forbids it: `false`
    // cannot be established on entry. Anyone counting `proved_by_kind.invariant`
    // from consecution rows alone would count this vacuous row as a proof.
    let false_row = table.iter().find(|(predicate, _)| *predicate == "false").expect("row");
    assert!(
        false_row.1.contains("initiation=not-discharged"),
        "`invariant false` must fail INITIATION. Table:\n{rendered}",
    );

    // The lane is only worth shipping if something OUTSIDE the tautologies
    // moved. Asserted directly rather than inferred from the table above.
    let contingent = rows(call_in_loop(Latch::CarryShift), "shift == 0");
    let contingent_proved = contingent.initiation.as_ref().is_some_and(certified)
        && contingent.consecution.as_ref().is_some_and(certified);
    let contingent_refuted = rows(call_in_loop(Latch::TakeCallResult), "shift == 0")
        .consecution
        .as_ref()
        .is_some_and(|vc| !certified(vc));
    assert!(
        contingent_proved && contingent_refuted,
        "the newly-provable set must not be the tautologies: `shift == 0` must be discharged \
         on the carried-latch fixture and NOT on the call-result-latch fixture \
         (discharged={contingent_proved}, refuted={contingent_refuted}).\nTable:\n{rendered}",
    );
}

/// The measured false proof that the `#e45_` havoc namespace exists to prevent,
/// pinned as a regression.
///
/// `invariant chunk == 0` is FALSE of this program: `chunk` is the destination
/// of `observe(xs)`, which may return anything. Before
/// `version_token_is_loop_transition_havoc` gated the final
/// `normalize_ssa_version_tokens` pass, `chunk` was single-static-assignment
/// (its only write is the call destination), the pass collapsed the havoc
/// `chunk#e45_call_bb2` onto the bare `chunk`, and the consecution row rendered
/// as `chunk == 0 AND guard AND NOT(chunk == 0)` — trivially UNSAT and
/// KERNEL-CERTIFIED.
///
/// MEASURED with that one guard removed and nothing else changed: this row
/// comes back certified. It is the whole reason the token namespace is not
/// cosmetic.
#[test]
fn a_havoced_local_is_never_collapsed_back_onto_its_bare_name() {
    for latch in [Latch::CarryShift, Latch::TakeCallResult] {
        let rows = rows(call_in_loop(latch), "chunk == 0");
        let consecution = rows.consecution();
        let names = symbols(&consecution.formula);
        assert!(
            names.iter().any(|name| name.starts_with("chunk#e45_call_bb")),
            "{latch:?}: the post-state read must keep the havoc token; symbols: {names:?}",
        );
        assert!(
            names.iter().any(|name| name == "chunk"),
            "{latch:?}: the PRE-state read must keep the bare name, or the two would \
             not be distinguishable at all; symbols: {names:?}",
        );
        assert!(
            !certified(consecution),
            "{latch:?}: an invariant that is false of the program must not certify; \
             formula: {:?}",
            consecution.formula,
        );
    }
}

// ---------------------------------------------------------------------------
// ADVERSARIAL — a callee that can write what the invariant depends on
// ---------------------------------------------------------------------------

fn blockers(func: VerifiableFunction, invariant: &str) -> Vec<String> {
    let rows = rows(func, invariant);
    assert!(
        rows.consecution.is_none() && rows.initiation.is_none(),
        "a refused loop must not mint E4 rows at all",
    );
    assert!(!rows.unsupported.is_empty(), "a refusal must be visible as an UnsupportedMir row");
    rows.unsupported
}

fn assert_refused_with(func: VerifiableFunction, code: &str) {
    let details = blockers(func, "shift == 0");
    assert!(
        details.iter().any(|detail| detail.contains(code)),
        "expected the refusal to name `{code}`; got {details:?}",
    );
}

/// THE ADVERSARIAL CASE. `let p = &mut shift;` runs ONCE in the entry block,
/// outside the loop, so the transition walk never revisits it — and it hands
/// out a pointer to the very local the invariant is about. The in-loop call
/// `tick()` then takes NO ARGUMENTS at all, so the argument screen alone says
/// nothing about it, yet `tick` could write `shift` through a stashed pointer.
/// Treating it as effect-free would prove `shift == 0` of a program that
/// violates it.
///
/// The loop MUST be refused, and it is. Note honestly WHICH screen refuses it:
/// MEASURED, this fixture is stopped by the pre-existing INITIATION model
/// (`e45.transition.entry-not-straight-line`) before
/// `caller_frame_creates_no_local_pointer` is ever consulted, because
/// `apply_symbolic_statements` already declines an `Rvalue::Ref` on the entry
/// path. Across every shape tried, no `Rvalue::Ref { mutable: true }` survives
/// far enough for condition (6) to be the load-bearing refusal — so condition
/// (6) is DEFENCE IN DEPTH, not a demonstrated false-proof barrier, and is
/// reported as such. It is retained because the entry and statement models are
/// widening lanes in their own right, and this screen is the one that states
/// the frame requirement directly. `caller_frame_creates_no_local_pointer` has
/// its own direct unit test in `contracts.rs`.
#[test]
fn adversarial_pointer_to_the_invariants_local_escapes_before_the_loop() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals.push(LocalDecl {
        index: 5,
        ty: Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) },
        name: Some("p".to_string()),
    });
    func.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(3) },
        span: span(2),
    });
    // The in-loop call takes no arguments — the argument screen cannot see the
    // capability, so only a whole-body screen could refuse on that ground.
    let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else {
        unreachable!("bb2 is the in-loop call")
    };
    args.clear();

    // The load-bearing assertion: NO E4 row is minted for this loop at all.
    let details = blockers(func, "shift == 0");
    assert!(
        details.iter().any(|detail| detail.contains("e45.transition.")),
        "a loop whose invariant's local has escaped by pointer must be refused by a \
         named e45 blocker; got {details:?}",
    );
}

/// The same capability handed over directly: the in-loop call takes a
/// `&mut u32` PARAMETER, so no `Rvalue::Ref` appears in the body at all and the
/// whole-body escape screen sees nothing. The argument screen must catch it.
#[test]
fn adversarial_mutable_reference_argument_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals[1].ty = Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) };
    assert_refused_with(func, "e45.transition.call-effect.arg-capability");
}

/// Interior mutability behind a SHARED reference. `&Cell<u32>` is a shared
/// reference through which a callee may legally write, so the "writing through
/// `&T` is UB" argument does not hold for it. The pointee grammar admits no
/// named type at all, which is exactly how every `Cell` / `UnsafeCell` /
/// `Mutex` / atomic is excluded.
#[test]
fn adversarial_shared_reference_to_an_interior_mutable_type_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::adt("core::cell::Cell<u32>", vec![("value".to_string(), Ty::u32())])),
    };
    assert_refused_with(func, "e45.transition.call-effect.arg-capability");
}

/// A raw pointer argument aliases anything and can be written through.
#[test]
fn adversarial_raw_pointer_argument_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals[1].ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) };
    assert_refused_with(func, "e45.transition.call-effect.arg-capability");
}

/// A foreign item is outside Rust's aliasing rules; an unsafe SIGNATURE means
/// the callee's contract, not the type system, bounds its writes; an atomic
/// intrinsic has a memory effect the frame argument does not cover. All three
/// flags are rustc-recorded at extraction, not name heuristics.
#[test]
fn adversarial_compiler_authenticated_identity_screens_refuse() {
    for (code, mutate) in [
        (
            "e45.transition.call-effect.foreign-callee",
            Box::new(|call: &mut Terminator| {
                let Terminator::Call { is_foreign, .. } = call else { unreachable!() };
                *is_foreign = true;
            }) as Box<dyn Fn(&mut Terminator)>,
        ),
        (
            "e45.transition.call-effect.unsafe-signature",
            Box::new(|call: &mut Terminator| {
                let Terminator::Call { is_unsafe_sig, .. } = call else { unreachable!() };
                *is_unsafe_sig = true;
            }),
        ),
    ] {
        let mut func = call_in_loop(Latch::CarryShift);
        mutate(&mut func.body.blocks[2].terminator);
        assert_refused_with(func, code);
    }
}

/// An unwind successor INSIDE the loop is a backedge path this walk never
/// explores. A partial transition model is how a loop mints authority it has
/// not earned, so the whole loop is refused.
#[test]
fn adversarial_unwind_edge_back_into_the_loop_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    let Terminator::Call { unwind, .. } = &mut func.body.blocks[2].terminator else {
        unreachable!()
    };
    *unwind = UnwindEdge::Cleanup(BlockId(3));
    assert_refused_with(func, "e45.transition.call-effect.unwind-into-loop");
}

/// A destination that is not a whole scalar local writes through a place the
/// model does not track exactly.
#[test]
fn adversarial_projected_destination_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    let Terminator::Call { dest, .. } = &mut func.body.blocks[2].terminator else { unreachable!() };
    *dest = Place { local: 4, projections: vec![Projection::Field(0)] };
    assert_refused_with(func, "e45.transition.call-effect.projected-destination");
}

/// A destination whose declared type is not a by-value scalar. The model has
/// no exact denotation for the value the callee wrote there, so havocing it
/// would be a claim about a shape this screen has not characterized.
///
/// (The narrower `collection-destination` code, for a destination that IS a
/// modeled slice base or length, is checked directly in `contracts.rs` — it
/// needs a fixture in which the collection model actually exists.)
#[test]
fn adversarial_nonscalar_destination_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    let Terminator::Call { dest, args, .. } = &mut func.body.blocks[2].terminator else {
        unreachable!()
    };
    *dest = Place::local(1);
    args.clear();
    assert_refused_with(func, "e45.transition.call-effect.nonscalar-destination");
}

/// THE HOLE AN INDEPENDENT REVIEW FOUND, pinned as a refusal.
///
/// `p: *mut u32` ARRIVES as a parameter, so no `Rvalue::Ref` is created in this
/// body and the whole-body escape screen sees nothing; and the in-loop call
/// takes NO ARGUMENTS, so the argument screen sees nothing either. The loop
/// reads `*p`, which `operand_to_formula` spells `p*` — a name that is not a
/// state key, so `substitute_formula_state` leaves it identical in the
/// pre-state and the post-state and the model ASSERTS the iteration did not
/// change it. A safe zero-argument callee holding an alias of `p` through
/// global state can change it, and `invariant seen == 0` would be discharged
/// for a program that violates it.
///
/// `caller_reads_no_untracked_memory` refuses the whole loop instead.
#[test]
fn adversarial_dereference_of_an_incoming_raw_pointer_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals[1].ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) };
    func.body.locals[1].name = Some("p".to_string());
    // The in-loop call takes no arguments at all.
    let Terminator::Call { args, .. } = &mut func.body.blocks[2].terminator else { unreachable!() };
    args.clear();
    // The latch reads `*p` into the loop-carried local, so the invariant really
    // does depend on memory this model does not represent.
    func.body.blocks[3].stmts[0] = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 1,
            projections: vec![Projection::Deref],
        })),
        span: span(5),
    };
    assert_refused_with(func, "e45.transition.call-effect.untracked-deref");
}

/// A local NAME carrying the version-token separator could spell the havoc
/// symbol itself and collapse a call destination's pre- and post-state onto one
/// SMT name. rustc cannot emit such an identifier; the public Trust IR boundary
/// accepts any string.
#[test]
fn adversarial_local_named_like_a_havoc_token_is_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.locals[4].name = Some("chunk#e45_call_bb2".to_string());
    let details = blockers(func, "shift == 0");
    assert!(
        details
            .iter()
            .any(|detail| detail.contains("e45.transition.call-effect.version-token-in-local-name")),
        "a local name that can forge a havoc symbol must be refused: {details:?}",
    );
}

/// A `Drop` terminator in a loop body remains refused: this lane widened calls
/// only, and a drop glue call runs a callee this screen has not characterized.
#[test]
fn drop_terminators_in_a_loop_body_remain_refused() {
    let mut func = call_in_loop(Latch::CarryShift);
    func.body.blocks[2].terminator = Terminator::Drop {
        place: Place::local(4),
        target: BlockId(3),
        unwind: UnwindEdge::Unreachable,
        span: span(4),
    };
    let details = blockers(func, "shift == 0");
    assert!(
        details.iter().any(|detail| detail.contains("e45.transition.drop-effect")),
        "drop stays refused: {details:?}",
    );
}
