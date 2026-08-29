//! The PLANTED-VIOLATION guards on the entry-sentinel tie.
//!
//! An in-place update whose read renders BARE is pinned to the explicit entry
//! token `n#e` (`stamp_entry_valued_recurrent_read`). That symbol unifies with
//! nothing, so `conjoin_preconditions_versioned_recorded` ties it back to the bare
//! name in the same conjoin bucket: `Eq(n#e, n)`. The tie is TRUE only because both
//! spellings denote the function-entry value — and there are exactly two ways that
//! can fail. Each is refused, and each refusal is watched failing here.
//!
//! Both tests assert the ABSENCE of the tie, and both have been watched failing:
//!
//!  * delete the COLLISION check in `entry_sentinel_ties` and
//!    `no_tie_onto_a_local_…` fails with `Eq(Var("n#e"), Var("n"))`;
//!  * delete BOTH clauses of `entry_sentinel_tie_is_sound` and
//!    `no_tie_at_a_consumer_…` fails with the same conjunct.
//!
//! The second is stated as a PAIR deliberately, and this is the honest reading:
//! on a cleanup consumer the mint-side clause ("no block of this function could
//! have minted a `#e` that is not the entry value") and the consumer-side clause
//! ("this block versions the base, so the tie's bare side is not the subject")
//! both fire, so deleting either ALONE changes nothing — measured. They are one
//! guard with two independent reasons, kept apart because they close different
//! halves (which block minted the symbol vs. what bare means where it is read),
//! and a shape that defeats one is not thereby licensed by the other.
//!
//! `mint_side_subsumes_consumer_side` below pins WHY deleting the consumer-side
//! clause alone changes nothing: the mint side already implies it. That is the
//! testable claim; the clause itself is not independently falsifiable, and the
//! shapes that fail to isolate it are the negative controls in
//! `src/generate/entry_sentinel_tie_subsumption_tests.rs`.

use trust_types::*;

/// Every `Eq(Var(x), Var(y))` where `x` is literally `y#e` — the tie's shape.
fn ties(vcs: &[VerificationCondition]) -> Vec<String> {
    fn walk(f: &Formula, out: &mut Vec<String>) {
        if let Formula::Eq(l, r) = f
            && let (Some(a), Some(b)) = (l.var_name(), r.var_name())
            && a == format!("{b}#e")
        {
            out.push(format!("{f:?}"));
        }
        for c in f.children() {
            walk(c, out);
        }
    }
    let mut out = Vec::new();
    for vc in vcs {
        walk(&vc.formula, &mut out);
    }
    out
}

/// Every `Eq(Var(v), rhs)` with `v` free in `rhs` and `rhs` not `v` — the
/// recurrence the pin exists to prevent, in the split form the `entry.rs`
/// backstop cannot see (one conjunct per half).
fn recurrences(vcs: &[VerificationCondition]) -> Vec<String> {
    fn walk(f: &Formula, out: &mut Vec<String>) {
        if let Formula::Eq(l, r) = f
            && let Some(name) = l.var_name()
            && r.var_name() != Some(name)
            && r.free_variables().iter().any(|v| v.as_str() == name)
        {
            out.push(format!("{f:?}"));
        }
        for c in f.children() {
            walk(c, out);
        }
    }
    let mut out = Vec::new();
    for vc in vcs {
        walk(&vc.formula, &mut out);
    }
    out
}

fn func(name: &str, locals: Vec<LocalDecl>, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("tie_guard::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].ty.clone(),
            locals,
            blocks,
            arg_count: 1,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// `n = n / 3` in bb0 (so its read IS the entry value and gets `#e`), with the
/// consumer reached ONLY across an unwind edge.
///
/// `block_entry_versions` builds its predecessor lists from `v2_terminator_targets`,
/// which has no unwind arm, so bb2's entry-version map is EMPTY and every name
/// renders bare there — while `v2_path_def_fixpoint` DOES transport the pinned def
/// across `unwind: Cleanup(bb2)`. Bare is therefore NOT the entry value at bb2, and
/// the tie would assert `n#e == n` about the POST-write subject: together with the
/// pinned `n == n / 3` that pins `n` to 0 and vacuously discharges bb2's obligation.
/// `self_referential_definition` cannot catch it — neither conjunct is
/// self-referential on its own.
fn cleanup_consumer() -> VerifiableFunction {
    func(
        "cleanup_consumer",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("__ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::bool_ty(), name: Some("ok".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("out".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(3, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                    Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Lt,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(10, 32)),
                        ),
                        span: SourceSpan::default(),
                    },
                ],
                terminator: Terminator::Assert {
                    cond: Operand::Copy(Place::local(2)),
                    expected: true,
                    msg: AssertMessage::Custom("bound".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Cleanup(BlockId(2)),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Constant(ConstValue::Uint(100, 32)),
                        Operand::Copy(Place::local(1)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Resume,
            },
        ],
    )
}

/// A function that declares a local literally named `n#e` alongside `n`.
///
/// `validate_function` does not reserve `#` in local names and `place_to_var_name`
/// passes it through, so `Var("n#e")` in a shipped formula may be a real, unrelated
/// place rather than the pin's sentinel. Tying it to `n` asserts a relationship the
/// program never establishes — a false PROOF, not a weakening.
///
/// There is NO in-place update here on purpose: the pin's own mint fails closed on
/// the collision, so if the tie emitter only saw pin-minted symbols this fixture
/// would be empty. The point is that the emitter scans the FORMULA, where the
/// colliding local's own reads put `n#e` regardless of what the pin did.
fn colliding_local() -> VerifiableFunction {
    func(
        "colliding_local",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("__ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("n#e".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("out".into()) },
        ],
        vec![
            // `n` is REASSIGNED here, so the consumer below versions it (`n#s0_0`)
            // and the tie's other two clauses both pass — the collision check is
            // the only thing standing between `n#e` (a real, unrelated local) and
            // an asserted equality with `n`.
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(1)),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Copy(Place::local(2)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            },
        ],
    )
}

#[test]
fn no_tie_at_a_consumer_reached_only_across_an_unwind_edge() {
    let vcs = trust_vcgen::generate_vcs(&cleanup_consumer());
    let emitted = ties(&vcs);
    assert!(
        emitted.is_empty(),
        "a block with an EMPTY entry-version map renders every name bare, so the \
         tie's bare side is the pinned def's POST-write subject, not the entry \
         value — asserting it re-mints `n == n / 3`:\n  {}",
        emitted.join("\n  ")
    );
    let split = recurrences(&vcs);
    assert!(
        split.is_empty(),
        "an in-place update reaching a cleanup block must not carry a recurrence:\n  {}",
        split.join("\n  ")
    );
}

#[test]
fn no_tie_onto_a_local_that_is_literally_named_with_the_entry_sentinel() {
    let vcs = trust_vcgen::generate_vcs(&colliding_local());
    let emitted = ties(&vcs);
    assert!(
        emitted.is_empty(),
        "`n#e` here is a REAL local, not the pin's sentinel; tying it to `n` \
         asserts an equality the program never establishes:\n  {}",
        emitted.join("\n  ")
    );
}

/// Every real-MIR body in `tests/data`, the corpus the subsumption claim was
/// measured over.
fn corpus() -> Vec<(String, VerifiableFunction)> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).unwrap_or_else(|e| panic!("{dir} must be readable: {e}")) {
        let path = entry.expect("readable dir entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("MIR fixture {} must be readable: {e}", path.display()));
        out.push((
            path.file_stem().unwrap().to_string_lossy().into_owned(),
            serde_json::from_str(&text)
                .unwrap_or_else(|e| panic!("MIR fixture {} must deserialize: {e}", path.display())),
        ));
    }
    out
}

/// MINT SIDE ⟹ CONSUMER SIDE — the implication that makes the consumer-side clause
/// of `entry_sentinel_tie_is_sound` dead, and the only part of that story any test
/// can falsify.
///
/// The guard itself is the `debug_assert!` in the production function, so this test
/// only has to REACH it: `generate_vcs` over the real-MIR corpus plus both guard
/// fixtures. Asserting it here instead would need a hand-built stand-in for the
/// `renamed` formula the tie emitter scans, which is exactly the double the
/// reachability rule forbids.
///
/// PLANTED AND WATCHED: delete the mint-side clause (the `entry_map_covers` check)
/// and `cleanup_consumer` — a consumer with NO v2 in-edge, hence a bare `n` — trips
/// the assert here and in `no_tie_at_a_consumer_reached_only_across_an_unwind_edge`.
#[test]
fn mint_side_subsumes_consumer_side() {
    assert!(
        cfg!(debug_assertions),
        "`debug_assert!` is inert without debug assertions, so this guard would pass \
         vacuously; run it in the dev profile"
    );

    let mut tied: Vec<String> = Vec::new();
    for (label, func) in corpus().into_iter().chain([
        ("cleanup_consumer".to_string(), cleanup_consumer()),
        ("colliding_local".to_string(), colliding_local()),
    ]) {
        if !ties(&trust_vcgen::generate_vcs(&func)).is_empty() {
            tied.push(label);
        }
    }

    // Non-vacuity: the assert is only evaluated where a `#e` survives to a consumer
    // AND clears the collision check. Measured 2026-08-28 — these two bodies are the
    // whole of that population, and both PASS the clause, so on real input it never
    // even decides in the refusing direction.
    tied.sort();
    assert_eq!(
        tied,
        vec!["entry_block_in_place_update", "join_weakened_entry_sentinel"],
        "the corpus no longer exercises the tie where it was measured; re-anchor \
         this list or the subsumption guard is running over nothing"
    );
}

/// Laundering control for both fixtures: the guards must cost a HYPOTHESIS, never
/// an obligation. If refusing the tie also dropped the row, the tests above would
/// pass vacuously.
#[test]
fn both_guard_fixtures_still_raise_their_arithmetic_obligation() {
    for (label, f) in
        [("cleanup", cleanup_consumer()), ("collision", colliding_local())]
    {
        let vcs = trust_vcgen::generate_vcs(&f);
        assert!(
            vcs.iter().any(|vc| matches!(
                vc.kind,
                VcKind::DivisionByZero | VcKind::UnsupportedMir { .. }
            )),
            "{label}: the consumer's division must still raise an obligation; got {:?}",
            vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
        );
    }
}
