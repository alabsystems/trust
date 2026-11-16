// THE VACUITY TABLE FOR THE PER-OPERAND WIDENING LANE, decided by the real
// in-process solver.
//
// The failure mode this table exists to catch has been measured twice in this
// campaign: a lane widens what the translator accepts, the newly "provable" set
// turns out to be exactly the LOGICAL TAUTOLOGIES, and the headline number
// moves for no reason at all. It happens when a verification condition
// degenerates to `Not(P)` with no path condition, no pre-state and no bound
// names, so UNSAT of the negation is just validity of `P`.
//
// The loop below is deliberately MIXED: `i: u32` and `total: u64` are stepped
// together, so a clause relating them has no single declared machine domain and
// was refused whole before this lane. Every row is run end to end — bind the
// clause, generate, discharge with `trust_router`'s deterministic in-process ay
// — and the table records what actually came back.
//
// THE DISCRIMINATOR is `i == total`: true of this loop at every iteration,
// false the moment the two updates disagree, and not a logical tautology by any
// reading — its validity depends on the zero extension of the 32-bit `i` into
// the 64-bit domain being exactly right. If that were the wrong extension the
// row would not prove.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::*;
use trust_vcgen::{bind_compiler_loop_contracts, generate_vcs_with_discharge};

#[path = "support/test_router.rs"]
mod test_router;

fn span(line_start: u32, line_end: u32) -> SourceSpan {
    SourceSpan { file: "mixed.rs".to_string(), line_start, col_start: 0, line_end, col_end: 80 }
}

/// ```text
/// let mut i: u32 = 0;
/// let mut total: u64 = 0;
/// while i < 100u32 { total = total + 1u64; i = i + 1u32; }
/// ```
/// Locals: `_1 = limit: u32` (argument), `_2 = i: u32`, `_3 = cond: bool`,
/// `_4 = total: u64`.
fn mixed_counted_loop() -> VerifiableFunction {
    VerifiableFunction {
        name: "mixed_counted".to_string(),
        def_path: "test::mixed_counted".to_string(),
        span: span(1, 20),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("_0".to_string()) },
                LocalDecl { index: 1, ty: Ty::u32(), name: Some("limit".to_string()) },
                LocalDecl { index: 2, ty: Ty::u32(), name: Some("i".to_string()) },
                LocalDecl { index: 3, ty: Ty::Bool, name: Some("cond".to_string()) },
                LocalDecl { index: 4, ty: Ty::u64(), name: Some("total".to_string()) },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                            span: span(7, 7),
                        },
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 64))),
                            span: span(7, 7),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(2)),
                            Operand::Constant(ConstValue::Uint(100, 32)),
                        ),
                        span: span(10, 10),
                    }],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(3)),
                        targets: vec![(1, BlockId(2))],
                        otherwise: BlockId(3),
                        exhaustive_enum_unreachable: false,
                        span: span(10, 10),
                    },
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(4)),
                                Operand::Constant(ConstValue::Uint(1, 64)),
                            ),
                            span: span(12, 12),
                        },
                        Statement::Assign {
                            place: Place::local(2),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Add,
                                Operand::Copy(Place::local(2)),
                                Operand::Constant(ConstValue::Uint(1, 32)),
                            ),
                            span: span(13, 13),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(1)),
                },
                BasicBlock { id: BlockId(3), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 1,
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

#[derive(Debug, PartialEq, Eq)]
enum Row {
    /// The clause produced no E4 obligation at all; the detail says why.
    Refused(String),
    /// Both E4 rows exist. Each column is a different DOOR:
    ///
    ///   * `unsat` — the violation formula is UNSAT, measured by handing the
    ///     SAME formula to the in-process ay backend under an L0 kind. The
    ///     contract kinds are excluded from that backend BY CONSTRUCTION
    ///     (`in_process_ay_backend::can_handle` lists only L0 safety kinds), so
    ///     routing an E4 row through the router returns
    ///     `Unknown{"no backend can handle this VC"}` no matter what it says.
    ///     That, and not the translator, is why `proved_by_kind.invariant` has
    ///     never moved.
    ///   * `certified` — `trust_certify::certify_vc`, the door that IS reached
    ///     for contract VCs and the one that returned PROVED for `1 == 1` in
    ///     this campaign's measured vacuity.
    ///   * `constrains` — the formula mentions at least one MIR name.
    Rows { initiation: Verdict, consecution: Verdict, constrains: bool },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Verdict {
    unsat: bool,
    certified: bool,
    /// The violation carries a syntactically reflexive disequality
    /// `Not(Eq(t, t))` among its conjuncts, so `Eq.refl t` refutes it with no
    /// hypothesis at all: a row with one is a tautology whatever else it says.
    reflexive: bool,
}

/// Whether some conjunct of `formula` is `Not(Eq(t, t))` for one term `t`.
fn has_reflexive_disequality(formula: &Formula) -> bool {
    match formula {
        Formula::And(parts) => parts.iter().any(has_reflexive_disequality),
        Formula::Not(inner) => matches!(inner.as_ref(), Formula::Eq(left, right) if left == right),
        _ => false,
    }
}

/// Decide the VC's formula on its merits, bypassing the kind filter by carrying
/// the identical formula under an L0 kind the in-process backend accepts. This
/// changes NOTHING about the formula — it is the same `Formula` value — it only
/// gets it past a routing table that refuses contract kinds outright.
fn formula_is_unsat(vc: &VerificationCondition) -> bool {
    let carrier = VerificationCondition {
        kind: VcKind::DivisionByZero,
        function: vc.function.clone(),
        location: vc.location.clone(),
        formula: vc.formula.clone(),
        contract_metadata: None,
        obligation: None,
    };
    let router = test_router::deterministic_test_router();
    let results = router.verify_all(std::slice::from_ref(&carrier));
    let (_, result) = results.into_iter().next().expect("one verdict");
    matches!(result, VerificationResult::Proved { .. })
}

/// The CONTROL: the identical loop with the `u64` counter removed, so every
/// leaf is `u32` and the clause takes the ORIGINAL single-domain path this lane
/// does not touch.
fn uniform_counted_loop() -> VerifiableFunction {
    let mut func = mixed_counted_loop();
    func.name = "uniform_counted".to_string();
    func.def_path = "test::uniform_counted".to_string();
    func.body.locals[4].ty = Ty::u32();
    func.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
        span: span(7, 7),
    };
    func.body.blocks[2].stmts[0] = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(4)),
            Operand::Constant(ConstValue::Uint(1, 32)),
        ),
        span: span(12, 12),
    };
    func
}

fn measure(invariant: &str) -> Row {
    measure_on(mixed_counted_loop(), invariant)
}

fn measure_on(mut func: VerifiableFunction, invariant: &str) -> Row {
    let spec = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        source_hir_local_id: None,
        mir_header: None,
        loop_head: span(9, 15),
        header_span: span(9, 11),
        span: span(11, 11),
        body: invariant.to_string(),
    };
    let failures = bind_compiler_loop_contracts(&mut func, &[spec]);
    if !failures.is_empty() {
        return Row::Refused(format!("bind: {failures:?}"));
    }
    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    if let Some(detail) = preclassified.iter().find_map(|(vc, _)| match &vc.kind {
        VcKind::UnsupportedMir { kind, detail } if kind == "UserLoopContractUnsupported" => {
            Some(detail.clone())
        }
        _ => None,
    }) {
        return Row::Refused(detail);
    }
    let e4: Vec<&VerificationCondition> = solver_vcs
        .iter()
        .filter(|vc| {
            matches!(
                vc.kind,
                VcKind::LoopInvariantInitiation { .. } | VcKind::LoopInvariantConsecution { .. }
            )
        })
        .collect();
    if e4.len() != 2 {
        let kinds: Vec<String> = solver_vcs
            .iter()
            .chain(preclassified.iter().map(|(vc, _)| vc))
            .map(|vc| format!("{:?}", std::mem::discriminant(&vc.kind)))
            .collect();
        return Row::Refused(format!(
            "no E4 pair: {} of 2 loop rows among {} VCs",
            e4.len(),
            kinds.len()
        ));
    }
    let blank = Verdict { unsat: false, certified: false, reflexive: false };
    let (mut initiation, mut consecution) = (blank, blank);
    let mut constrains = false;
    for vc in &e4 {
        // "The formula CONSTRAINS something": it must mention at least one MIR
        // name, not just literals and connectives.
        let mut names = Vec::new();
        vc.formula.visit(&mut |node| {
            if let Formula::Var(name, _) = node {
                names.push(name.clone());
            }
        });
        constrains |= !names.is_empty();
        let verdict = Verdict {
            unsat: formula_is_unsat(vc),
            certified: trust_certify::certify_vc(vc).is_some(),
            reflexive: has_reflexive_disequality(&vc.formula),
        };
        if std::env::var_os("TRUST_LANEB_VERBOSE").is_some() {
            println!("    {:?} -> {verdict:?}\n      formula: {:?}", vc.kind, vc.formula);
        }
        match vc.kind {
            VcKind::LoopInvariantInitiation { .. } => initiation = verdict,
            _ => consecution = verdict,
        }
    }
    Row::Rows { initiation, consecution, constrains }
}

/// THE TABLE. Printed as well as asserted, because the printed form is the
/// measurement and the assertions are only what it must not become.
#[test]
fn the_vacuity_table_over_the_newly_reachable_mixed_domain() {
    let table = [
        // ---- the tautology probes ----
        ("1 == 1", "closed tautology"),
        ("0 == 0", "closed tautology"),
        ("0 == 1", "closed falsehood"),
        ("i == i", "reflexive over one variable"),
        ("i <= i", "reflexive over one variable"),
        ("total == total", "reflexive over one variable"),
        // ---- true of every value of the type, NOT a logical tautology ----
        ("i <= 4294967295", "discriminator: every u32 satisfies it"),
        // ---- the real mixed-domain claim this lane makes reachable ----
        ("i == total", "THE DISCRIMINATOR: mixed u32/u64, loop-established"),
        ("i <= total", "mixed u32/u64, loop-established"),
        ("total <= i", "mixed u32/u64, loop-established (the other direction)"),
        // ---- a mixed claim that is FALSE and must not prove ----
        ("i < total", "mixed u32/u64, FALSE at entry (0 < 0)"),
    ];

    let mut measured = Vec::new();
    let mut controls = Vec::new();
    for (invariant, note) in table {
        let row = measure(invariant);
        println!("VACUITY  {invariant:<20} [{note}] -> {row:?}");
        measured.push((invariant, row));
        // The same invariant on the all-u32 control (section 4).
        let control = measure_on(uniform_counted_loop(), invariant);
        println!("CONTROL  {invariant:<20} [all-u32, untouched path] -> {control:?}");
        controls.push((invariant, control));
    }

    let row_of = |name: &str| {
        measured
            .iter()
            .find(|(invariant, _)| *invariant == name)
            .map(|(_, row)| row)
            .unwrap_or_else(|| panic!("{name} missing from the table"))
    };

    // ---- 1. THE PROVABLE SET IS NOT THE TAUTOLOGIES ----------------------
    //
    // `i == total` relates a `u32` to a `u64`. It has no single declared
    // machine domain, so before this lane the clause was refused whole and
    // NOTHING about it was provable. Both its rows are now UNSAT, and that
    // discharge is not a tautology by any reading: it holds only because the
    // 32-bit `i` is ZERO-extended into the 64-bit comparison, so `i == total`
    // forces `total < 2^32` and therefore `total + 1` cannot wrap. Swap the
    // extension and the link between the two domains is gone.
    let Row::Rows { initiation, consecution, constrains } = row_of("i == total") else {
        panic!("the mixed discriminator must produce an E4 pair: {:?}", row_of("i == total"));
    };
    assert!(constrains, "the discriminator's rows must mention MIR names");
    assert!(initiation.unsat && consecution.unsat, "both discriminator rows must be UNSAT");

    // ---- 2. …AND IT IS NOT EVERYTHING EITHER -----------------------------
    //
    // Two rows in the table are NOT discharged, and each fails for a reason
    // that is a property of the machine rather than of the prover:
    //
    //   * `i < total` is FALSE at entry (`0 < 0`), so its initiation stays SAT;
    //   * `i <= total` is genuinely NOT PRESERVED — at `total == u64::MAX` the
    //     `total + 1` step wraps to 0 and the relation breaks. The model finds
    //     that witness, which is exactly the wrap-exactness the Machine{w}
    //     reading exists for.
    //
    // A lane whose newly reachable set were the tautologies could not produce
    // either of these.
    let Row::Rows { initiation: false_initiation, .. } = row_of("i < total") else {
        panic!("`i < total` must still produce an E4 pair");
    };
    assert!(
        !false_initiation.unsat,
        "`i < total` is false at entry (0 < 0); a lane that discharges it is proving nothing",
    );
    let Row::Rows { consecution: wrapping_consecution, .. } = row_of("i <= total") else {
        panic!("`i <= total` must still produce an E4 pair");
    };
    assert!(
        !wrapping_consecution.unsat,
        "`i <= total` is not preserved at total == u64::MAX; the wrap witness must survive",
    );

    // ---- 3. THE CLOSED TAUTOLOGIES NEVER REACH AN E4 PAIR ----------------
    //
    // `1 == 1` / `0 == 0` — the exact predicates whose PROVED verdict was this
    // campaign's measured vacuity — produce no E4 pair on this loop at all, so
    // this lane cannot be the thing that mints them.
    for closed in ["1 == 1", "0 == 0", "0 == 1"] {
        assert!(
            matches!(row_of(closed), Row::Refused(_)),
            "`{closed}` must not reach an E4 pair here: {:?}",
            row_of(closed),
        );
    }

    // ---- 4. THE KERNEL DOOR TREATS THIS LANE AND THE CONTROL ALIKE ---------
    //
    // The CONTROL is the identical loop with the `u64` counter replaced by a
    // `u32` one, which takes the ORIGINAL single-domain path this lane does not
    // touch. If the control certified a row and the mixed lane did not, the
    // difference would be this lane's fault; so EVERY invariant of the table is
    // measured on both loops, and the two must certify ROW FOR ROW alike.
    //
    // Until `de718fe643` that meant "neither certifies anything". Its
    // `trust_certify::bv_equality` family (documented in `docs/TCB.md` by
    // `ca243a06a2`) refutes a violation by equality alone: each bitvector term is
    // an uninterpreted integer skolem and the kernel checks an
    // `Eq.refl`/`Eq.symm`/`Eq.trans` term, a weakening of the goal that
    // interprets no arithmetic. On this table it certifies EXACTLY the rows whose
    // violation carries a syntactically reflexive disequality `Not(Eq(t, t))`,
    // and it does so in both lanes:
    //
    //   * the initiations of the three equality invariants `i == i`,
    //     `total == total` and `i == total`, which the loop entry folds to the
    //     closed `Not(Eq(0, 0))`;
    //   * the CONSECUTIONS of the reflexive `i == i` and `total == total`, whose
    //     disequality is `Not(Eq(bvadd(t, 1), bvadd(t, 1)))`.
    //
    // So every certified row here is a tautology. The kernel door adds no
    // non-vacuous certification to this table, and its count must never be read
    // as one. The one non-tautological equality row, the `i == total`
    // consecution, certifies in neither lane. The control's needs congruence
    // (`i = total` to `bvadd(i, 1) = bvadd(total, 1)`), which the family
    // deliberately lacks; the mixed one needs arithmetic as well (that the zero
    // extension commutes with the `+ 1` step, which holds only because neither
    // addition wraps). The inequality rows have no equality to refute. (VCGEN-PERF-67-69-VERDICTS-1, 2026-11-07:
    // this section pinned "never" and went red on the sound new family.)
    //
    // What stays forbidden: a certified row the solver does not prove (a false
    // certification), any certification of a FALSE row, and a certification the
    // reflexive reading does not explain. The exact measured column is pinned,
    // so a change that moves the door comes here and says so.
    let certified_bits = |row: &Row| match row {
        Row::Rows { initiation, consecution, .. } => {
            Some((initiation.certified, consecution.certified))
        }
        Row::Refused(_) => None,
    };
    for (lane, rows) in [("mixed", &measured), ("control", &controls)] {
        for (invariant, row) in rows {
            if let Row::Rows { initiation: init, consecution: consec, .. } = row {
                for (half, verdict) in [("initiation", init), ("consecution", consec)] {
                    assert!(
                        !verdict.certified || verdict.unsat,
                        "{lane} `{invariant}` {half}: kernel-certified but the solver finds it SAT",
                    );
                    assert_eq!(
                        verdict.certified, verdict.reflexive,
                        "{lane} `{invariant}` {half}: on this table the equality family \
                         certifies exactly the rows with a reflexive disequality",
                    );
                }
            }
        }
    }
    assert!(!false_initiation.certified, "`i < total` is false at entry; it must never certify");
    assert!(
        !wrapping_consecution.certified,
        "`i <= total` is not preserved at total == u64::MAX; it must never certify",
    );
    for ((invariant, row), (_, control)) in measured.iter().zip(&controls) {
        assert_eq!(
            certified_bits(row),
            certified_bits(control),
            "`{invariant}`: the mixed rows must certify exactly as the untouched control \
             does: {row:?} against {control:?}",
        );
    }
    let Some((_, control)) = controls.iter().find(|(invariant, _)| *invariant == "i == total")
    else {
        panic!("`i == total` missing from the control table");
    };
    let Row::Rows { initiation: control_initiation, consecution: control_consecution, .. } =
        control
    else {
        panic!("the all-u32 control must produce an E4 pair: {control:?}");
    };
    assert!(
        control_initiation.unsat && control_consecution.unsat,
        "the control's rows are UNSAT on the untouched path",
    );
    let column: Vec<(&str, Option<(bool, bool)>)> =
        measured.iter().map(|(invariant, row)| (*invariant, certified_bits(row))).collect();
    assert_eq!(
        column,
        vec![
            ("1 == 1", None),
            ("0 == 0", None),
            ("0 == 1", None),
            ("i == i", Some((true, true))),
            ("i <= i", Some((false, false))),
            ("total == total", Some((true, true))),
            ("i <= 4294967295", Some((false, false))),
            ("i == total", Some((true, false))),
            ("i <= total", Some((false, false))),
            ("total <= i", Some((false, false))),
            ("i < total", Some((false, false))),
        ],
        "measured (initiation, consecution) certification: the equality initiations fold \
         to `Not(Eq(0, 0))` and the reflexive consecutions to `Not(Eq(t, t))`, both closed \
         by `Eq.refl`; the `i == total` consecution needs congruence or arithmetic, which \
         the equality family does not have",
    );
}

/// A SIGNED counter that goes NEGATIVE, widened into a `i64` companion. This is
/// the adversarial fixture for the extension rule at the VC level: `i >= total`
/// is FALSE after one iteration (`-1 >= 0`), and the only implementation that
/// discharges it is one that ZERO-extends the negative `i32`, reading `-1` as
/// `4294967295`.
///
/// So a wrong extension here does not merely lose a proof, it MINTS one. Both
/// halves are asserted: the emitted formula must carry `BvSignExt` and not
/// `BvZeroExt`, and the consecution row must stay SAT.
#[test]
fn a_zero_extended_negative_would_mint_a_false_proof_and_does_not() {
    let mut func = mixed_counted_loop();
    func.name = "signed_countdown".to_string();
    func.def_path = "test::signed_countdown".to_string();
    func.body.locals[1].ty = Ty::i32();
    func.body.locals[2].ty = Ty::i32();
    func.body.locals[4].ty = Ty::i64();
    // total: i64 = 0, and it never moves.
    func.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(0))),
        span: span(7, 7),
    };
    // while i > -100i32
    func.body.blocks[1].stmts[0] = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::BinaryOp(
            BinOp::Gt,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Int(-100)),
        ),
        span: span(10, 10),
    };
    // i = i - 1  (and nothing else in the body)
    func.body.blocks[2].stmts = vec![Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::BinaryOp(
            BinOp::Sub,
            Operand::Copy(Place::local(2)),
            Operand::Constant(ConstValue::Int(1)),
        ),
        span: span(13, 13),
    }];

    let spec = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        source_hir_local_id: None,
        mir_header: None,
        loop_head: span(9, 15),
        header_span: span(9, 11),
        span: span(11, 11),
        body: "i >= total".to_string(),
    };
    assert!(bind_compiler_loop_contracts(&mut func, &[spec]).is_empty());
    let (solver_vcs, preclassified) = generate_vcs_with_discharge(&func);
    assert!(
        !preclassified.iter().any(|(vc, _)| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "UserLoopContractUnsupported"
        )),
        "the i32/i64 mix must translate, or this fixture proves nothing: {preclassified:#?}",
    );
    let consecution = solver_vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("a consecution row");

    let (mut sign_extends, mut zero_extends) = (0, 0);
    consecution.formula.visit(&mut |node| match node {
        Formula::BvSignExt(..) => sign_extends += 1,
        Formula::BvZeroExt(..) => zero_extends += 1,
        _ => {}
    });
    assert!(
        sign_extends > 0,
        "a signed 32-bit operand meeting a 64-bit one must SIGN-extend: {:?}",
        consecution.formula,
    );
    assert_eq!(
        zero_extends, 0,
        "not one zero extension may appear over a signed source: {:?}",
        consecution.formula,
    );
    assert!(
        !formula_is_unsat(consecution),
        "`i >= total` is FALSE once `i` reaches -1, so its consecution must stay SAT. \
         UNSAT here is the false proof a zero-extending implementation would mint.",
    );
}

/// The exactness of the widening, isolated: swap the loop's `u64` step for a
/// `u32`-sized one so `i` and `total` diverge past `2^32`, and the same
/// discriminator must stop discharging. This is the mutation that separates
/// "the solver proved the relation" from "the solver proved anything you ask".
#[test]
fn the_discriminator_stops_discharging_when_the_relation_is_broken() {
    let mut func = mixed_counted_loop();
    // total = total + 2 instead of + 1: `i == total` is now false after one
    // iteration.
    func.body.blocks[2].stmts[0] = Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::BinaryOp(
            BinOp::Add,
            Operand::Copy(Place::local(4)),
            Operand::Constant(ConstValue::Uint(2, 64)),
        ),
        span: span(12, 12),
    };
    let spec = LoopContractSpec {
        kind: LoopContractKind::Invariant,
        source_loop_id: 0,
        source_hir_local_id: None,
        mir_header: None,
        loop_head: span(9, 15),
        header_span: span(9, 11),
        span: span(11, 11),
        body: "i == total".to_string(),
    };
    assert!(bind_compiler_loop_contracts(&mut func, &[spec]).is_empty());
    let (solver_vcs, _) = generate_vcs_with_discharge(&func);
    let consecution = solver_vcs
        .iter()
        .find(|vc| matches!(vc.kind, VcKind::LoopInvariantConsecution { .. }))
        .expect("the mutant still produces a consecution row");
    assert!(
        !formula_is_unsat(consecution),
        "with the two counters stepping differently the invariant is false, and a \
         lane that still discharges it is proving nothing",
    );
}
