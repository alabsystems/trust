//! REAL-ARTIFACT guards for the PROJECTED-OPERAND `Overflow(Div|Rem)` row.
//!
//! `18a0083876` wrote that `v2_eq_def_binds_operand_to_const` "refuses a PROJECTED
//! compared value, and this shape needs one" — and then applied the reasoning to
//! the zero-divisor row while leaving the overflow row three lines above bound to
//! the refusing helper. So under overflow checks, where the value rustc compares
//! against `INT_MIN` and then divides is `_3.0` (the value field of a
//! `CheckedAdd`/`CheckedSub` tuple), the canonical `let a = x + 1; a / b` kept BOTH
//! `arithmetic overflow (Div)` rows and the statement-lane one was `NOT _7 AND _7`
//! — UNSAT by construction, a `proved` row at the span of a genuinely-false
//! division. MEASURED on the extracted bundle, not on pretty-printed `--emit=mir`,
//! which folds the projection into a plain local and hides the whole family.
//!
//! Every fixture loaded here is the compiler's OWN extracted verification input
//! (`-Ztrust-dump=mir`, stage2 @ 17abbefc3) and its source is committed beside them
//! as `tests/data/divrem_projected_arms.rs`, so every row re-derives. The forged
//! arms MUTATE that real input one field at a time, so each guard has a planted
//! violation whose provenance is the real lowering.

use std::collections::HashMap;

use trust_types::{AssertMessage, BasicBlock, Place, Projection, VcKind};

use super::*;

fn load(name: &str) -> VerifiableFunction {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/");
    let text = std::fs::read_to_string(format!("{path}{name}.json"))
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must be readable: {e}"));
    serde_json::from_str(&text)
        .unwrap_or_else(|e| panic!("real-MIR fixture `{name}` must deserialize: {e}"))
}

/// The production predicate's verdict for every `Div`/`Rem` statement in the
/// body, in body order, decided over the production operands.
fn suppressed(func: &VerifiableFunction) -> Vec<bool> {
    let mut out = Vec::new();
    for block in &func.body.blocks {
        for (stmt_index, stmt) in block.stmts.iter().enumerate() {
            let Statement::Assign { rvalue: Rvalue::BinaryOp(op, lhs, rhs), .. } = stmt else {
                continue;
            };
            if !matches!(op, BinOp::Div | BinOp::Rem) {
                continue;
            }
            out.push(v2_divrem_overflow_assert_exactly_bound(
                func, *op, block.id, stmt_index, lhs, rhs,
            ));
        }
    }
    assert!(!out.is_empty(), "fixture must contain a Div/Rem statement");
    out
}

/// The shipped `arithmetic overflow (Div|Rem)` rows — both lanes emit this same
/// `VcKind`, at the same span, so the transport cannot tell them apart and the
/// count is the whole observable.
fn overflow_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    crate::generate_vcs(func)
        .into_iter()
        .filter(|vc| {
            matches!(vc.kind, VcKind::ArithmeticOverflow { op: BinOp::Div | BinOp::Rem, .. })
        })
        .collect()
}

/// Walk the VC's top-level conjunction, recording
///   * `defs` — flag definitions `flag = <condition>` (the MIR bool temps);
///   * `neg`  — flags asserted NEGATIVELY (`(not flag)`, i.e. a passed assert);
///   * `pos`  — everything asserted POSITIVELY, rendered.
fn collect(
    f: &Formula,
    defs: &mut HashMap<String, Formula>,
    neg: &mut Vec<String>,
    pos: &mut Vec<String>,
) {
    match f {
        Formula::And(parts) => {
            for p in parts {
                collect(p, defs, neg, pos);
            }
        }
        Formula::Not(inner) => {
            if let Formula::Var(name, _) = inner.as_ref() {
                neg.push(name.clone());
            }
        }
        Formula::Var(name, _) => pos.push(format!("VAR:{name}")),
        Formula::Eq(a, b) => {
            // `flag = <condition>` is a DEFINITION, not an assertion of `flag`.
            if let Formula::Var(name, _) = a.as_ref() {
                defs.insert(name.clone(), b.as_ref().clone());
            } else if let Formula::Var(name, _) = b.as_ref() {
                defs.insert(name.clone(), a.as_ref().clone());
            }
            pos.push(f.to_smtlib());
        }
        other => pos.push(other.to_smtlib()),
    }
}

/// The flags this VC asserts to be FALSE while also asserting every conjunct of
/// their defining condition TRUE — `flag != 0` and `flag == 0` at once. Such a
/// VC is UNSAT by construction: it can only ever come back `proved`, and it
/// proves nothing. That is precisely the shape shipping as a `proved`
/// `arithmetic overflow (Div)` row at the span of a genuinely-false division.
///
/// Resolution goes one level THROUGH the `BitAnd` carrier on purpose. This
/// family's cond is `_7 = _5 AND _6` with `_5 = (rhs == -1)` and
/// `_6 = (lhs == INT_MIN)`, and the statement-lane row asserts the two
/// COMPARISONS separately rather than the conjunction — so the zero-divisor
/// canary's rule (compare `defs[flag]` against the positive terms verbatim,
/// correct where the cond IS a single comparison) sees nothing here.
///
/// Shared with `signed_divzero_chain_tests` (SELF-GUARDED-LITERAL-OPERAND-1),
/// whose zero-divisor conds are the single-comparison case.
pub(super) fn vacuous_flags(vc: &VerificationCondition) -> Vec<String> {
    let mut defs = HashMap::new();
    let (mut neg, mut pos) = (Vec::new(), Vec::new());
    collect(&vc.formula, &mut defs, &mut neg, &mut pos);
    let conjuncts = |def: &Formula| -> Vec<Formula> {
        match def {
            Formula::And(parts) if !parts.is_empty() => parts
                .iter()
                .map(|part| match part {
                    Formula::Var(n, _) => defs.get(n).cloned().unwrap_or_else(|| part.clone()),
                    other => other.clone(),
                })
                .collect(),
            other => vec![other.clone()],
        }
    };
    let mut bad: Vec<String> = neg
        .iter()
        .filter(|flag| {
            defs.get(*flag)
                .is_some_and(|def| conjuncts(def).iter().all(|c| pos.contains(&c.to_smtlib())))
        })
        .cloned()
        .collect();
    bad.sort();
    bad.dedup();
    bad
}

fn assert_no_vacuous_row(name: &str, func: &VerifiableFunction) {
    for vc in overflow_rows(func) {
        let bad = vacuous_flags(&vc);
        assert!(
            bad.is_empty(),
            "{name}: a surviving `Overflow(Div|Rem)` row asserts {bad:?} false while \
             asserting every conjunct of its defining condition true — UNSAT by \
             construction, so it can only ever be `proved`: {}",
            vc.formula.to_smtlib()
        );
    }
}

/// The `Assert` terminator of `bb<index>`, with a fixture-drift message if the
/// dump ever stops having that shape there.
fn assert_terminator(func: &mut VerifiableFunction, index: usize) -> &mut Terminator {
    let block = &mut func.body.blocks[index];
    assert_eq!(block.id.0, index, "fixture drift: blocks are no longer in id order");
    assert!(
        matches!(block.terminator, Terminator::Assert { .. }),
        "fixture drift: expected an Assert terminator on bb{index}"
    );
    &mut block.terminator
}

/// Appends `bbN: goto -> target`, giving `target` a second predecessor.
fn add_goto_predecessor(func: &mut VerifiableFunction, target: usize) {
    let id = BlockId(func.body.blocks.len());
    func.body.blocks.push(BasicBlock {
        id,
        stmts: Vec::new(),
        terminator: Terminator::Goto(BlockId(target)),
    });
}

/// Moves `bb<from>`'s statement 0 to position `at` in `bb<to>`, leaving the
/// number of definitions of the value it writes UNCHANGED at one — so
/// `guards::value_local_is_unstable` still calls it stable and the arm isolates
/// a positional rewrite scan instead of the function-wide stability check.
fn relocate_first_stmt(func: &mut VerifiableFunction, from: usize, to: usize, at: usize) {
    let stmt = func.body.blocks[from].stmts.remove(0);
    func.body.blocks[to].stmts.insert(at, stmt);
}

// -----------------------------------------------------------------------
// THE DEFECT. A projected compared value is the canonical rustc lowering
// under overflow checks, and it kept the vacuous duplicate.
// -----------------------------------------------------------------------

#[test]
fn a_projected_dividend_keeps_exactly_one_overflow_row() {
    // `let a = x + 1; a / b`. Two `arithmetic overflow (Div)` rows before this
    // fix; the statement-lane one binds `_7 = (b == -1) & (_3.0 == INT_MIN)`,
    // asserts `(not _7)` as a path guard, and then asserts both conjuncts.
    let func = load("projected_dividend_div");
    assert_eq!(suppressed(&func), vec![true]);
    assert_eq!(overflow_rows(&func).len(), 1, "exactly one live obligation must remain");
    assert_no_vacuous_row("projected_dividend_div", &func);
}

#[test]
fn a_projected_divisor_keeps_exactly_one_overflow_row() {
    // The other side of the same cond: `Eq(_3.0, -1)` compares the projection.
    let func = load("projected_divisor_div");
    assert_eq!(suppressed(&func), vec![true]);
    assert_eq!(overflow_rows(&func).len(), 1);
    assert_no_vacuous_row("projected_divisor_div", &func);
}

#[test]
fn both_operands_projected_keeps_exactly_one_overflow_row() {
    for name in ["projected_both_div", "projected_both_rem"] {
        let func = load(name);
        assert_eq!(suppressed(&func), vec![true], "{name}");
        assert_eq!(overflow_rows(&func).len(), 1, "{name}");
        assert_no_vacuous_row(name, &func);
    }
}

// -----------------------------------------------------------------------
// THE SURFACE MUST NOT SHRINK. A suppression that deletes an honest row is a
// lost recovery, not a fix.
// -----------------------------------------------------------------------

#[test]
fn a_provably_safe_projected_division_keeps_a_dischargeable_obligation() {
    // `let a = (x & 1) + 1; a / b` provably cannot overflow — `a` is 1 or 2.
    // Exactly one REAL, refutable obligation must remain for the discharge
    // lanes to prove; deleting it would be a lost recovery, not a fix.
    let func = load("provably_safe_projected_dividend_div");
    assert_eq!(suppressed(&func), vec![true]);
    assert_eq!(overflow_rows(&func).len(), 1);
    assert_no_vacuous_row("provably_safe_projected_dividend_div", &func);
}

#[test]
fn two_distinct_projected_divisors_each_keep_their_own_obligation() {
    // Two divisions, two chains, one shared dividend `_4.0`. A skip keyed on
    // the BLOCK rather than on the OPERANDS collapses these into one. Pre-fix
    // this emitted FOUR rows, two honest and two vacuous.
    let func = load("two_distinct_projected_divisors");
    assert_eq!(suppressed(&func), vec![true, true]);
    assert_eq!(overflow_rows(&func).len(), 2, "each division keeps one row");
    assert_no_vacuous_row("two_distinct_projected_divisors", &func);
}

#[test]
fn the_unprojected_surface_is_untouched() {
    // The rule 18a0083876 shipped still decides plain-local code, and admitting
    // projections must not have moved it in either direction.
    //  * `plain_dividend_deep_div` is the CONTROL: identical block depth,
    //    identical assert-chain length, identical sole-entry topology, `Div` in
    //    the same block position — the ONE difference is that its dividend is a
    //    plain local. One row before this fix and one after.
    //  * `deref_operand_div` is `*p / *q`, which rustc lowers through
    //    projection-free temporaries, so it too is the plain shape.
    for name in ["plain_dividend_deep_div", "deref_operand_div"] {
        let func = load(name);
        assert_eq!(suppressed(&func), vec![true], "{name}");
        assert_eq!(overflow_rows(&func).len(), 1, "{name}");
        assert_no_vacuous_row(name, &func);
    }
}

#[test]
fn a_constant_compared_value_stays_suppressed() {
    // `i32::MIN / y` lowers to `_4 = Eq(const INT_MIN, const INT_MIN)` and is
    // suppressed TODAY. RED under: swapping the direct caller onto
    // `v2_eq_def_binds_projected_operand`, whose `let Copy | Move = var_side
    // else { return false }` refuses a constant outright — which would take
    // these back to two rows and RESURRECT the vacuous row at the span of a
    // genuinely-false division. The union of the two admissions is forced.
    for name in ["const_min_dividend_div", "const_min_dividend_rem"] {
        let func = load(name);
        assert_eq!(suppressed(&func), vec![true], "{name}");
        assert_eq!(overflow_rows(&func).len(), 1, "{name}");
        assert_no_vacuous_row(name, &func);
    }
}

#[test]
fn an_unsigned_projected_division_has_no_overflow_row_to_move() {
    // No signed `Overflow(Div)` obligation exists, and rustc emits no such
    // assert. Untouched in both directions.
    let func = load("projected_unsigned_div");
    assert_eq!(suppressed(&func), vec![false]);
    assert_eq!(overflow_rows(&func).len(), 0);
}

#[test]
fn an_unguarded_library_call_division_keeps_its_surface() {
    // `a.div_euclid(b)` lowers to a Call with NO MIR overflow assert, so the
    // projected-operand rewrite has nothing to bind to. Since 2026-09-30 the
    // CALL itself carries the one row its documented panic needs
    // (`signed_euclid_overflow_call`: `a == MIN && b == -1`), and that row
    // must be an honest, non-vacuous obligation.
    let func = load("unguarded_call_projected_div");
    assert_eq!(overflow_rows(&func).len(), 1);
    assert_no_vacuous_row("unguarded_call_projected_div", &func);
}

// -----------------------------------------------------------------------
// MEASURED NON-SUPPRESSIONS. These keep BOTH rows, one of which is vacuous —
// over-reporting, which is the safe direction, and the reason each refuses is
// a rule that must stay.
// -----------------------------------------------------------------------

#[test]
fn a_mismatched_comparison_constant_keeps_both_rows() {
    // `7 / y` lowers to `_4 = Eq(const 7, const INT_MIN)`. The constant does
    // not match the operation's INT_MIN, so no binding exists. RED under:
    // dropping the `const_int_value(const_side) != Some(value)` identity check.
    let func = load("nonmin_const_dividend_div");
    assert_eq!(suppressed(&func), vec![false]);
    assert_eq!(overflow_rows(&func).len(), 2);
}

#[test]
fn a_constant_divisor_keeps_both_rows() {
    // `a / 3` compares two constants on BOTH sides of the `== -1` conjunct, so
    // no place identity exists to bind. Two rows before this fix and two after.
    let func = load("provably_safe_projected_div");
    assert_eq!(suppressed(&func), vec![false]);
    assert_eq!(overflow_rows(&func).len(), 2);
}

#[test]
fn the_vacuity_detector_can_fail() {
    // A guard nobody has watched fail proves nothing. `7 / y`'s statement-lane
    // row IS the vacuous shape — it asserts `(not _5)` where
    // `_5 = (y == -1) & (7 == INT_MIN)`, then asserts both conjuncts — and it
    // is deliberately NOT suppressed (no constant identity to bind). So exactly
    // one of its two rows must be flagged. If this arm ever reports zero, the
    // detector has stopped detecting and every `assert_no_vacuous_row` above is
    // passing for free; check first that the block-def rendering of a comparison
    // still matches `v2_build_signed_div_overflow_vc`'s violation rendering
    // character for character.
    let func = load("nonmin_const_dividend_div");
    let rows = overflow_rows(&func);
    assert_eq!(rows.len(), 2);
    let flagged = rows.iter().filter(|vc| !vacuous_flags(vc).is_empty()).count();
    assert_eq!(flagged, 1, "exactly the self-guarded duplicate must be flagged");
}

// -----------------------------------------------------------------------
// FORGED ARMS. Each mutates REAL extracted MIR in one place and must restore
// BOTH rows: over-reporting is the safe direction. The comment on each names
// the loosening that turns it red, and only that loosening does.
// -----------------------------------------------------------------------

#[test]
fn an_index_projected_compared_value_keeps_both_rows() {
    // `_a[_i]` compared against INT_MIN, `_i` rewritten, then `_a[_i]` divided,
    // is two different values under one place spelling: the base-stability check
    // is asked about `_a`, and the name-keyed rewrite scans look for writes to
    // `a[_i]`, so a write to `_i` is invisible to BOTH. RED under: deleting
    // `v2_place_is_statically_addressed`, which is the only thing that refuses
    // this — `_1` is a never-assigned parameter, so the base is "stable".
    //
    // rustc copies an element read into a projection-free temporary before
    // comparing it, so the comparison and the division are retargeted onto the
    // element place itself. `_1` really is `[i32; 4]`, so `_1[_2]` types as
    // `i32` and every other clause of the binding still holds. The Move -> Copy
    // normalisation of the divisor is required only because
    // `v2_operands_structurally_equal` distinguishes the two spellings; without
    // it the arm would refuse for an unrelated reason and could never go red.
    let mut func = load("index_operand_div");
    let element = Operand::Copy(Place { local: 1, projections: vec![Projection::Index(2)] });
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, eq_lhs, _), .. } =
        &mut func.body.blocks[3].stmts[1]
    else {
        unreachable!("fixture drift: bb3[1] is the `Eq(dividend, INT_MIN)` conjunct")
    };
    *eq_lhs = element.clone();
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, div_lhs, div_rhs), .. } =
        &mut func.body.blocks[4].stmts[0]
    else {
        unreachable!("fixture drift: bb4[0] is the division")
    };
    *div_lhs = element;
    *div_rhs = Operand::Copy(Place::local(6));
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_deref_projected_compared_value_keeps_both_rows() {
    // `(*_p)` reaches through a pointer whose pointee no direct-def scan tracks,
    // so a store through an alias between the comparison and the division is
    // invisible to this binding. RED under the same loosening as the `Index`
    // arm; kept separate because a partial allowlist could admit one and not the
    // other. The unmutated fixture BINDS (it is the plain-local shape), so this
    // arm changes exactly one thing: which place the comparison and the division
    // name.
    let mut func = load("deref_operand_div");
    let pointee = Operand::Copy(Place { local: 1, projections: vec![Projection::Deref] });
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, eq_lhs, _), .. } =
        &mut func.body.blocks[1].stmts[1]
    else {
        unreachable!("fixture drift: bb1[1] is the `Eq(dividend, INT_MIN)` conjunct")
    };
    *eq_lhs = pointee.clone();
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, div_lhs, _), .. } =
        &mut func.body.blocks[2].stmts[0]
    else {
        unreachable!("fixture drift: bb2[0] is the division")
    };
    *div_lhs = pointee;
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_second_definition_of_the_base_in_a_third_block_keeps_both_rows() {
    // The plant has to sit in a THIRD block for this guard to be the one that
    // catches it: the same store inside the assert block, or in the division's
    // block before the division, is already caught by the two name-keyed scans
    // (`place_names_overlap("_3", "_3.0")` is true). Nowhere else in the
    // function is covered by anything but `guards::value_local_is_unstable` on
    // the BASE local, which counts field stores. RED under: dropping that check
    // from the compared-value stability clause.
    let mut func = load("projected_dividend_div");
    let redefinition = func.body.blocks[0].stmts[0].clone();
    let id = BlockId(func.body.blocks.len());
    func.body.blocks.push(BasicBlock {
        id,
        stmts: vec![redefinition],
        terminator: Terminator::Return,
    });
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_rewrite_after_the_comparison_keeps_both_rows() {
    // The `CheckedAdd` that defines `_3` is moved out of bb0 and INTO the
    // overflow-assert block AFTER the `Eq(_3.0, INT_MIN)` conjunct, so `_3`
    // still has exactly ONE definition function-wide and the base-stability
    // check still calls it stable — yet the assert now compares a value that is
    // redefined before its own terminator reads the flag. RED under: deleting
    // the `(k + 1..)` post-comparison rewrite scan.
    let mut func = load("projected_dividend_div");
    relocate_first_stmt(&mut func, 0, 2, 2);
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_rewrite_before_the_division_keeps_both_rows() {
    // Same relocation, into the DIVISION's block ahead of the division: the
    // assert compared one value and the division reads another. RED under:
    // deleting the caller's own pre-operation rewrite scan over `(0..stmt_index)`.
    let mut func = load("projected_dividend_div");
    relocate_first_stmt(&mut func, 0, 3, 0);
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_second_entry_into_the_division_block_keeps_both_rows() {
    // Control can reach the division without executing the overflow assert, so
    // the surviving assert row does not cover every execution of the operation.
    // RED under: dropping the sole-entry scan.
    let mut func = load("projected_dividend_div");
    add_goto_predecessor(&mut func, 3);
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_mismatched_opcode_keeps_both_rows() {
    // `Overflow(Rem)` guarding a `Div`. RED under: dropping the binder's
    // `*assert_op != op` test.
    let mut func = load("projected_dividend_div");
    let Terminator::Assert { msg, .. } = assert_terminator(&mut func, 2) else { unreachable!() };
    *msg = AssertMessage::Overflow(BinOp::Rem);
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn an_inverted_assert_polarity_keeps_both_rows() {
    // rustc's `Overflow(Div|Rem)` assert panics when the condition is TRUE, so
    // its normal edge is `expected: false`; an inverted one has different
    // semantics and cannot stand in. RED under: dropping `expected: false` from
    // the binder's terminator pattern.
    let mut func = load("projected_dividend_div");
    let Terminator::Assert { expected, .. } = assert_terminator(&mut func, 2) else {
        unreachable!()
    };
    *expected = true;
    assert_eq!(suppressed(&func), vec![false]);
}

#[test]
fn a_guard_over_a_different_value_keeps_both_rows() {
    // Bare target identity is NEVER suppression authority: the `== INT_MIN`
    // conjunct is retargeted from the projected dividend `_3.0` to the divisor
    // `_2`, so the assert is assert-shaped but does not guard this division's
    // dividend at all — and the duplicate it would suppress is genuinely
    // REFUTABLE (`b == -1` is consistent with `not((b == -1) & (b == INT_MIN))`).
    // RED under: keying the suppression on the block or the target instead of on
    // `v2_operands_structurally_equal`.
    let mut func = load("projected_dividend_div");
    let Statement::Assign { rvalue: Rvalue::BinaryOp(_, lhs, _), .. } =
        &mut func.body.blocks[2].stmts[1]
    else {
        unreachable!("fixture drift: bb2[1] is the `Eq(dividend, INT_MIN)` conjunct")
    };
    *lhs = Operand::Copy(Place::local(2));
    assert_eq!(suppressed(&func), vec![false]);
    assert_eq!(overflow_rows(&func).len(), 2);
}
