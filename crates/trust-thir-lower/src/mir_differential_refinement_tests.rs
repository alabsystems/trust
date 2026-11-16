//! The MIR differential's REFINEMENT HARNESS: the pinned oracle and the working tree, compiled
//! side by side and driven over one corpus.
//!
//! Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
//!
//! WHY. `src/mir_differential.rs` is blob-frozen (`scripts/frozen-files.txt`): it is the oracle
//! that decides `DerivedAgreed`, the one verdict `flip_registry::record_green` turns into a
//! flip. Its waiver row argues one sentence — "NEITHER SAMPLES NOR REFUSES DIFFERENTLY" — and
//! until this file that sentence was the one PROSE-ONLY row in `scripts/frozen-waivers.txt`:
//! nothing executed it. This file executes its verdict-core half and pins which tokens moved;
//! the half about `TyCtxt`-side tokens is still argued, not run, and the row says so in a
//! `PROSE-RESIDUAL:` clause the freeze gate counts. The build script compiles the file's
//! production section twice — once from the blob the manifest PINS, read out of git so the
//! baseline is the ratified one and moves only with the pin, and once from the working tree —
//! exactly as it does for `flip_registry.rs` (`flip_registry_refinement_tests.rs`, the
//! precedent this mirrors).
//!
//! THE TYCTXT-FREE VERDICT CORE. `compare_derived` takes a `TyCtxt`; most of its DECISION does
//! not. After the `TyCtxt` channels have produced two extracted `VerifiableBody`s and each
//! side's `CallArgKinds`, the verdict is made by four `TyCtxt`-free functions of the frozen
//! file, and this harness compares exactly those, per side:
//!
//! ```text
//!   canonicalize(body, kinds)      -> canonical lines | refusal reason, + normalization counts
//!   canon_markers(body)            -> marker lines | refusal reason        (the -O channel)
//!   derived_bare_local_borrow(body)-> the (2.75) refs-bootstrap refusal, if any
//!   canonical_cfg_roles(body)      -> every block's canonical role | refusal (read by the
//!                                     unfrozen source_provenance header channel, step 2.5)
//! ```
//!
//! and the pair verdict `compare_derived` builds from the first three in steps (2.75)–(5):
//! refused if the derived side trips the refs guard or either side fails to canonicalize;
//! `DerivedAgreed` iff the canonical forms are line-identical; `markers_exact` iff, in addition,
//! both marker channels succeed with identical lines. That composition is re-stated here ONCE
//! (`verdict`) and applied to both sides, so it cannot favour either; the census below is what
//! pins `compare_derived`'s own text. `canonical_cfg_roles` reaches the verdict through step
//! 2.5, whose composition — refuse the pair when either side's roles are refused, otherwise
//! MATCH role values — lives in the unfrozen `source_provenance.rs`. The harness does not
//! restate that composition; it holds the roles to the one PER-SIDE relation that cannot widen
//! it whatever the composition is (`cfg_role_widenings`).
//!
//! THE TWO RELATIONS.
//!
//! ```text
//!   THE RULE (every movement, pin-independent) — admits nothing new, at both acceptance bits
//!   the flip gate reads, and at step 2.5's input:
//!     for every (derived, built) pair:  current_agreed      => pinned_agreed
//!                                       current_agreed_exact => pinned_agreed_exact
//!     for every corpus point:           current_roles(x) = Ok(r) => pinned_roles(x) = Ok(r)
//!
//!   THE CURRENT WAIVER'S CLAIM — "NEITHER SAMPLES NOR REFUSES DIFFERENTLY":
//!     for every corpus point:  current_observation(x) == pinned_observation(x)
//!     (same canonical lines or the same refusal reason, same normalization counts, same
//!      marker lines, same refs-guard verdict, same CFG roles)
//! ```
//!
//! The second is strictly stronger; `waived_delta::VERDICT_CORE_IDENTICAL` says the current
//! waiver makes it, and at the ratified state (`pin_meta::PIN_IS_CURRENT`) it holds by
//! construction and is still asserted. A future movement that REFUSES MORE keeps the rule, sets
//! the flag false, and must then witness a strict refusal.
//!
//! THE CENSUS. The behavioural comparison above cannot see a movement in the file's `TyCtxt`
//! channels (the shim/extraction wiring in `compare_derived`, `raw_call_channel`,
//! `arg_borrow_kinds_by_block`, `arg_borrow_kind_of`, the `TRUST_DIFF_CANON_DUMP` filter).
//! Measured 2026-09-27: EVERY production token the current waiver moved is in exactly those —
//! the dump filter lifted into `canon_dump_filter_selects_this_def`, three
//! `#[allow(dead_code)]` attributes, and the uncalled `arg_borrow_kinds_in_dfs_order` —
//! so a behavioural test alone would be a test of code that did not move.
//! `the_production_delta_is_exactly_the_waived_one` closes that: with full-line comments and
//! blank lines removed (by a lexer that knows strings and block comments, so no code line is
//! ever dropped), the ordered line diff pin -> tree must equal `waived_delta::TEXT_DELTA`,
//! verbatim. A movement anywhere in the production section — `TyCtxt` channel or not — that no
//! waiver has named fails it. What it pins is WHICH tokens moved; that those tokens cannot
//! change a verdict is the row's argument, stated there (as its `PROSE-RESIDUAL`) and not
//! claimed here — at the waived blob the census holds by construction, since the blob already
//! fixes every token. (Measured on the frozen file, restored: turning the call channel's
//! `Diverge` arm into `DerivedAgreed` — a `TyCtxt`-side widening — passes every behavioural
//! test here and fails only the census; with its two lines written into `TEXT_DELTA`, it passes
//! everything.)
//!
//! WHAT THIS IS NOT. Evidence, not proof. The corpus is synthetic — the file's own fixtures
//! (the sequential-loop, borrow-shape and TailCall bodies) plus straight-line, branching,
//! phi-join, call and out-of-fragment bodies built the same way — not the differential's real
//! extractions, so a divergence only a real body reaches is not seen here. The `CallArgKinds`
//! are SUPPLIED by the corpus, not minted: `arg_borrow_kind_of` (the `Freeze` rule) is
//! `TyCtxt`-bound and is covered only by the census.
//!
//! MUTATION PROOF, IN TREE. `the_harness_catches_a_widened_oracle` runs the same checker
//! against the current observations with one decision disarmed (the refs guard, the constant
//! payload, the marker channel, the CFG-role refusals and the roles' distinctness) and requires
//! the widening each one causes relative to the undisarmed current oracle; and against a
//! refuse-more mutant of the pinned baseline, which the RULE must accept and the IDENTITY claim
//! must not. The same kinds of mutation were measured on the frozen file itself, restored
//! byte-exactly; the commits that added and extended this file record them.
//!
//! WHEN THE PIN MOVES. Two constants in `waived_delta` are about the CURRENT waiver. Ratifying
//! at the working tree's blob needs no edit here (at pinned == current the delta is empty and
//! the observations agree by construction). The next movement names its own delta and claim.

mod pin_meta {
    include!(concat!(env!("OUT_DIR"), "/mir_differential_pin_meta.rs"));
}

/// The current waiver adds a declared-opaque refusal before the TyCtxt-facing shim.
/// The compiled verdict core stays identical; the token census names the entry movement.
#[cfg(trust_frozen_pin_mir_differential)]
mod waived_delta {
    // Only the TyCtxt-facing entry gains an opaque-provenance refusal. The existing
    // TyCtxt-free verdict core is identical; real emitted-artifact controls own the new gate.
    pub(super) const VERDICT_CORE_IDENTICAL: bool = true;
    pub(super) const WITNESS_BIT_IS_EXACT: bool = false;
    pub(super) const WITNESS_PAIRS: &[&str] = &[];
    pub(super) const TEXT_DELTA: &[&str] = &[
        "+    if lowered.unsubstituted_opaque_return {",
        "+        return report(",
        "+            tcx,",
        "+            DerivedVerdict::DerivedUnsupported,",
        "+            \"unsubstituted body declares an opaque return (coverage-only)\",",
        "+            NO_NORMS,",
        "+        );",
        "+    }",
    ];
}

/// FAIL-CLOSED: no baseline, no green. The build script could not produce the pinned blob's
/// production section (no git, a checkout without the object, a manifest row missing or
/// malformed, a blob of a shape the cutter refuses), so nothing compared the two oracles.
#[cfg(not(trust_frozen_pin_mir_differential))]
#[test]
fn the_pinned_mir_differential_could_not_be_compiled() {
    panic!(
        "mir_differential refinement harness has NO BASELINE: {}. Until the blob \
         scripts/frozen-files.txt pins for crates/trust-thir-lower/src/mir_differential.rs can \
         be read out of git here, nothing checks the current oracle against the pinned one.",
        pin_meta::PIN_UNAVAILABLE
    );
}

#[cfg(trust_frozen_pin_mir_differential)]
pub(crate) mod armed {
    use trust_types::{
        AssertMessage, BasicBlock, BinOp, BlockId, ConstValue, LocalDecl, Operand, Place,
        Projection, Rvalue, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody,
    };

    use super::{pin_meta, waived_delta};

    /// A callee parameter's borrow kind, spelled once here and mapped onto each compiled
    /// side's own `ArgBorrowKind` (the two `include!`s define two distinct enums).
    #[derive(Clone, Copy, Debug)]
    pub(super) enum Kind {
        NotARef,
        Shared,
        Mut,
    }

    /// Everything the verdict core says about ONE body.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(super) struct Observation {
        canonical: Result<Vec<String>, String>,
        norms: Vec<(&'static str, usize)>,
        markers: Result<Vec<String>, String>,
        refs_guard: Option<String>,
        cfg_roles: Result<Vec<Option<Vec<u32>>>, String>,
    }

    /// ONE wrapper, expanded inside each compiled side so every name in it resolves to THAT
    /// side's items. A module's private items are reachable only from inside the module that
    /// `include!`s them. If a future pin's signatures differ, the pinned side gets its own.
    macro_rules! observe_wrapper {
        () => {
            pub(super) fn observe(
                body: &VerifiableBody,
                kinds: &[(usize, Vec<super::Kind>)],
            ) -> super::Observation {
                let arg_kinds: CallArgKinds = kinds
                    .iter()
                    .map(|(block, params)| {
                        let params = params
                            .iter()
                            .map(|kind| match kind {
                                super::Kind::NotARef => ArgBorrowKind::NotARef,
                                super::Kind::Shared => ArgBorrowKind::Shared,
                                super::Kind::Mut => ArgBorrowKind::Mut,
                            })
                            .collect();
                        (*block, params)
                    })
                    .collect();
                let (canonical, norms) = canonicalize(body, arg_kinds);
                super::Observation {
                    canonical,
                    norms: NORM_NAMES.iter().copied().zip(norms).collect(),
                    markers: canon_markers(body),
                    refs_guard: derived_bare_local_borrow(body),
                    // `role` is the type's only observable (its fields are private): ask it
                    // about every block, and one past the end.
                    cfg_roles: canonical_cfg_roles(body).map(|roles| {
                        (0..=body.blocks.len())
                            .map(|b| roles.role(b).map(<[u32]>::to_vec))
                            .collect()
                    }),
                }
            }
        };
    }

    /// The oracle as the manifest PINS it.
    mod pinned {
        #![allow(dead_code, unused_imports)]
        include!(concat!(env!("OUT_DIR"), "/mir_differential_pinned.rs"));
        observe_wrapper!();
    }

    /// The oracle as the working tree has it, compiled a second time so its private items are
    /// reachable — the instrument `mir_differential_tailcall_ratification_tests` already uses.
    /// Every token is the frozen file's own.
    mod current {
        #![allow(dead_code, unused_imports)]
        include!(concat!(env!("OUT_DIR"), "/mir_differential_current.rs"));
        observe_wrapper!();
    }

    // ----------------------------------------------------------------------------------------
    // The pair verdict: `compare_derived` steps (2.75)–(5), TyCtxt-free.
    // ----------------------------------------------------------------------------------------

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Verdict {
        Agreed { markers_exact: bool },
        Mismatch,
        Unsupported,
    }

    /// The two acceptance bits the flip gate reads: `DerivedAgreed` (every flip) and
    /// `DerivedAgreed && markers_exact` (the `-O` flip).
    #[derive(Clone, Copy, Debug)]
    enum Bit {
        Agreed,
        AgreedExact,
    }

    fn accepts(verdict: Verdict, bit: Bit) -> bool {
        match (verdict, bit) {
            (Verdict::Agreed { .. }, Bit::Agreed) => true,
            (Verdict::Agreed { markers_exact }, Bit::AgreedExact) => markers_exact,
            _ => false,
        }
    }

    /// (2.75) the refs guard reads the DERIVED body only; (3) either side's canonicalization
    /// failure is a refusal; (4) agreement is line-for-line equality; (5) the marker channel
    /// never downgrades the verdict, it only sets `markers_exact`.
    fn verdict(derived: &Observation, built: &Observation) -> Verdict {
        if derived.refs_guard.is_some() {
            return Verdict::Unsupported;
        }
        let (Ok(derived_lines), Ok(built_lines)) = (&derived.canonical, &built.canonical) else {
            return Verdict::Unsupported;
        };
        if derived_lines != built_lines {
            return Verdict::Mismatch;
        }
        let markers_exact = matches!((&built.markers, &derived.markers), (Ok(b), Ok(d)) if b == d);
        Verdict::Agreed { markers_exact }
    }

    // ----------------------------------------------------------------------------------------
    // The corpus.
    // ----------------------------------------------------------------------------------------

    struct Point {
        name: String,
        body: VerifiableBody,
        kinds: Vec<(usize, Vec<Kind>)>,
    }

    fn uint() -> Ty {
        Ty::Int { width: 32, signed: false }
    }

    fn copy(local: usize) -> Operand {
        Operand::Copy(Place::local(local))
    }

    fn konst(value: u128) -> Operand {
        Operand::Constant(ConstValue::Uint(value, 32))
    }

    fn assign(local: usize, rvalue: Rvalue) -> Statement {
        Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
    }

    fn block(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
        BasicBlock { id: BlockId(id), stmts, terminator }
    }

    /// One `u32` argument, `locals` `u32` locals in all (`_0` included), returning `u32`.
    fn body(locals: usize, blocks: Vec<BasicBlock>) -> VerifiableBody {
        VerifiableBody {
            locals: (0..locals)
                .map(|index| LocalDecl {
                    index,
                    ty: uint(),
                    name: (index == 1).then(|| "x".to_string()),
                })
                .collect(),
            blocks,
            arg_count: 1,
            return_ty: uint(),
            datatype_defs: Default::default(),
        }
    }

    fn ret(stmts: Vec<Statement>) -> VerifiableBody {
        body(3, vec![block(0, stmts, Terminator::Return)])
    }

    fn switch(on: usize, zero: usize, otherwise: usize) -> Terminator {
        Terminator::SwitchInt {
            discr: copy(on),
            targets: vec![(0, BlockId(zero))],
            otherwise: BlockId(otherwise),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        }
    }

    fn call(func: &str, arg: Operand, dest: usize, target: usize) -> Terminator {
        Terminator::Call {
            func: func.into(),
            args: vec![arg],
            dest: Place::local(dest),
            target: Some(BlockId(target)),
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            unwind: UnwindEdge::Unreachable,
            callee_identity: None,
            callee_key: None,
        }
    }

    fn call_to(func: &str, arg: Operand, dest: usize, target: usize) -> Terminator {
        call(func, arg, dest, target)
    }

    fn assert_true(target: usize) -> Terminator {
        Terminator::Assert {
            cond: Operand::Constant(ConstValue::Bool(true)),
            expected: true,
            msg: AssertMessage::Custom("canonical-latch".into()),
            target: BlockId(target),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Unreachable,
        }
    }

    /// The file's `sequential_loop_body`: two dominance-ordered natural loops, loop 1's
    /// post-state seeding loop 2.
    fn sequential_loop(first_step: u128) -> VerifiableBody {
        let sub = |local, step| Rvalue::BinaryOp(BinOp::Sub, copy(local), konst(step));
        body(
            3,
            vec![
                block(0, vec![], Terminator::Goto(BlockId(1))),
                block(1, vec![], switch(1, 3, 2)),
                block(2, vec![assign(1, sub(1, first_step))], Terminator::Goto(BlockId(1))),
                block(3, vec![assign(2, Rvalue::Use(copy(1)))], Terminator::Goto(BlockId(4))),
                block(4, vec![], switch(2, 6, 5)),
                block(5, vec![assign(2, sub(2, 1))], Terminator::Goto(BlockId(4))),
                block(6, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return),
            ],
        )
    }

    /// The file's `body_with_one_borrow`: `_2 = &proj(_1)` then return a constant.
    fn one_borrow(projections: Vec<Projection>, mutable: bool) -> VerifiableBody {
        ret(vec![
            assign(2, Rvalue::Ref { mutable, place: Place { local: 1, projections } }),
            assign(0, Rvalue::Use(konst(0))),
        ])
    }

    /// The file's `bare_borrow_then_call_body`: `_2 = &_1; observe(move _2) -> bb1;
    /// _0 = _3; return` — the shape that arms the shared-param exemption.
    fn bare_borrow_then_call() -> VerifiableBody {
        let mut b = body(
            4,
            vec![
                block(
                    0,
                    vec![assign(2, Rvalue::Ref { mutable: false, place: Place::local(1) })],
                    call("observe", Operand::Move(Place::local(2)), 3, 1),
                ),
                block(1, vec![assign(0, Rvalue::Use(copy(3)))], Terminator::Return),
            ],
        );
        b.locals[2].ty = Ty::Ref { mutable: false, inner: Box::new(uint()) };
        b
    }

    /// F3's witness shape: `_2 = _1; _3 = _2 + 1; _0 = _2 + _3`, with the markers of the first
    /// and second temp attached to `first` and `second`.
    fn markers_two_temps(first: usize, second: usize) -> VerifiableBody {
        let add = |l, r| Rvalue::BinaryOp(BinOp::Add, l, r);
        body(
            4,
            vec![block(
                0,
                vec![
                    Statement::StorageLive(first),
                    assign(2, Rvalue::Use(copy(1))),
                    Statement::StorageLive(second),
                    assign(3, add(copy(2), konst(1))),
                    assign(0, add(copy(2), copy(3))),
                    Statement::StorageDead(second),
                    Statement::StorageDead(first),
                ],
                Terminator::Return,
            )],
        )
    }

    /// Review case 1 (1b with `memory`): `SL(_2); _2 = _1; SL(_3); [_3 = 0;] _3 = _1; SD(_3);
    /// _0 = _<read>; SD(_2)`. Reading `_2` is bound; reading `_3` reads a dead temp.
    fn sd_half(memory: bool, read: usize) -> VerifiableBody {
        let mut stmts = vec![
            Statement::StorageLive(2),
            assign(2, Rvalue::Use(copy(1))),
            Statement::StorageLive(3),
        ];
        if memory {
            stmts.push(assign(3, Rvalue::Use(konst(0))));
        }
        stmts.extend([
            assign(3, Rvalue::Use(copy(1))),
            Statement::StorageDead(3),
            assign(0, Rvalue::Use(copy(read))),
            Statement::StorageDead(2),
        ]);
        body(4, vec![block(0, stmts, Terminator::Return)])
    }

    /// Review case 3b: a second live range of `_2`; `early` writes it BEFORE its own
    /// re-`StorageLive`, with an unmarked pure assign swapped in to keep marker positions equal.
    fn relive(early: bool) -> VerifiableBody {
        let mut stmts = vec![
            Statement::StorageLive(2),
            assign(2, Rvalue::Use(copy(1))),
            assign(3, Rvalue::Use(copy(2))),
            Statement::StorageDead(2),
        ];
        if early {
            stmts.extend([
                assign(2, Rvalue::Use(konst(7))),
                Statement::StorageLive(2),
                assign(4, Rvalue::Use(konst(0))),
            ]);
        } else {
            stmts.extend([
                assign(4, Rvalue::Use(konst(0))),
                Statement::StorageLive(2),
                assign(2, Rvalue::Use(konst(7))),
            ]);
        }
        stmts.extend([assign(0, Rvalue::Use(copy(2))), Statement::StorageDead(2)]);
        body(5, vec![block(0, stmts, Terminator::Return)])
    }

    /// The round-3 review's case (2026-09-30): a value carried ACROSS a `StorageDead` /
    /// `StorageLive` pair. `_2` is written in its first live range and read in its second with no
    /// write in between: `SL(_2); _2 = 0; _2 = 7; SD(_2); _4 = 0; SL(_2); _4 = 7; _0 = _2;
    /// SD(_2)`. Against `relive(false)` both canonical forms are `ret c:7` and the marker
    /// positions match; the read follows its own `StorageLive`, so the storage rule passes it. Only
    /// the access list tells them apart (built writes `_2` in the second range, this does not), and
    /// at `-O` the read is of storage `llvm.lifetime.start` has just reset.
    fn relive_stale() -> VerifiableBody {
        let stmts = vec![
            Statement::StorageLive(2),
            assign(2, Rvalue::Use(konst(0))),
            assign(2, Rvalue::Use(konst(7))),
            Statement::StorageDead(2),
            assign(4, Rvalue::Use(konst(0))),
            Statement::StorageLive(2),
            assign(4, Rvalue::Use(konst(7))),
            assign(0, Rvalue::Use(copy(2))),
            Statement::StorageDead(2),
        ];
        body(5, vec![block(0, stmts, Terminator::Return)])
    }

    /// The terminator-operand variants of case 1: the value read after `_3`'s `StorageDead` is
    /// a switch discriminant, or (`call`) a call argument.
    fn stale_terminator(call: bool, read: usize) -> VerifiableBody {
        let head = vec![
            Statement::StorageLive(2),
            assign(2, Rvalue::Use(copy(1))),
            Statement::StorageLive(3),
            assign(3, Rvalue::Use(copy(1))),
            Statement::StorageDead(3),
        ];
        if call {
            body(
                5,
                vec![
                    block(0, head, call_to("observe", copy(read), 4, 1)),
                    block(
                        1,
                        vec![assign(0, Rvalue::Use(copy(4))), Statement::StorageDead(2)],
                        Terminator::Return,
                    ),
                ],
            )
        } else {
            let tail = |v| vec![assign(0, Rvalue::Use(konst(v))), Statement::StorageDead(2)];
            body(
                4,
                vec![
                    block(0, head, switch(read, 1, 2)),
                    block(1, tail(0), Terminator::Return),
                    block(2, tail(1), Terminator::Return),
                ],
            )
        }
    }

    /// The file's TailCall fixture's `terminal_body`.
    fn terminal(terminator: Terminator) -> VerifiableBody {
        body(3, vec![block(0, vec![], terminator)])
    }

    fn corpus() -> Vec<Point> {
        let diamond = |then: u128, other: u128| {
            body(
                3,
                vec![
                    block(0, vec![], switch(1, 1, 2)),
                    block(
                        1,
                        vec![assign(0, Rvalue::Use(konst(then)))],
                        Terminator::Goto(BlockId(3)),
                    ),
                    block(
                        2,
                        vec![assign(0, Rvalue::Use(konst(other)))],
                        Terminator::Goto(BlockId(3)),
                    ),
                    block(3, vec![], Terminator::Return),
                ],
            )
        };
        let phi_join = |then: u128, other: u128| {
            body(
                3,
                vec![
                    block(0, vec![], switch(1, 1, 2)),
                    block(
                        1,
                        vec![assign(2, Rvalue::Use(konst(then)))],
                        Terminator::Goto(BlockId(3)),
                    ),
                    block(
                        2,
                        vec![assign(2, Rvalue::Use(konst(other)))],
                        Terminator::Goto(BlockId(3)),
                    ),
                    block(3, vec![], assert_true(4)),
                    block(4, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return),
                ],
            )
        };
        let call_then_return = |func: &str| {
            body(
                3,
                vec![
                    block(0, vec![], call(func, copy(1), 2, 1)),
                    block(1, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return),
                ],
            )
        };
        let binop =
            |op: BinOp, k: u128| ret(vec![assign(0, Rvalue::BinaryOp(op, copy(1), konst(k)))]);

        let mut plain: Vec<(&str, VerifiableBody)> = vec![
            // Straight-line: one observable, reached through every value normalization.
            ("ret-arg", ret(vec![assign(0, Rvalue::Use(copy(1)))])),
            (
                "ret-arg-via-temp",
                ret(vec![assign(2, Rvalue::Use(copy(1))), assign(0, Rvalue::Use(copy(2)))]),
            ),
            (
                "ret-arg-marked",
                ret(vec![
                    Statement::StorageLive(2),
                    assign(2, Rvalue::Use(copy(1))),
                    assign(0, Rvalue::Use(copy(2))),
                    Statement::StorageDead(2),
                ]),
            ),
            // F3: the same data statements under two marker placements. `markers-bound` opens
            // each temp before its own write; `markers-swapped` swaps the two temps' markers
            // CONSISTENTLY (both `u32`), so `_2` is written before its own StorageLive. Rendered
            // by first-marker alpha names alone, the two marker channels are line-identical.
            ("markers-bound", markers_two_temps(2, 3)),
            ("markers-swapped", markers_two_temps(3, 2)),
            // The review's cases (F3 rework): each pair agrees on the canonical channel, and
            // the pinned marker channel renders both identically.
            ("sd-half-bound", sd_half(false, 2)),
            ("sd-half-stale", sd_half(false, 3)),
            ("sd-half-memory-bound", sd_half(true, 2)),
            ("sd-half-memory-stale", sd_half(true, 3)),
            ("relive-bound", relive(false)),
            ("relive-early-write", relive(true)),
            ("relive-stale", relive_stale()),
            ("bound-switch", stale_terminator(false, 2)),
            ("stale-switch", stale_terminator(false, 3)),
            ("bound-call-arg", stale_terminator(true, 2)),
            ("stale-call-arg", stale_terminator(true, 3)),
            (
                "ret-arg-goto",
                body(
                    3,
                    vec![
                        block(
                            0,
                            vec![assign(2, Rvalue::Use(copy(1)))],
                            Terminator::Goto(BlockId(1)),
                        ),
                        block(1, vec![assign(0, Rvalue::Use(copy(2)))], Terminator::Return),
                    ],
                ),
            ),
            (
                "ret-arg-nop",
                ret(vec![
                    Statement::Nop,
                    Statement::PlaceMention(Place::local(1)),
                    assign(0, Rvalue::Use(copy(1))),
                ]),
            ),
            ("ret-arg-move", ret(vec![assign(0, Rvalue::Use(Operand::Move(Place::local(1))))])),
            ("ret-const-0", ret(vec![assign(0, Rvalue::Use(konst(0)))])),
            ("ret-const-1", ret(vec![assign(0, Rvalue::Use(konst(1)))])),
            ("add-1", binop(BinOp::Add, 1)),
            ("add-2", binop(BinOp::Add, 2)),
            ("sub-1", binop(BinOp::Sub, 1)),
            ("div-2", binop(BinOp::Div, 2)),
            (
                "assert-then-ret",
                body(
                    3,
                    vec![
                        block(0, vec![], assert_true(1)),
                        block(1, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
                    ],
                ),
            ),
            // Branching: a phi join, its mirror, and the return-split spelling of the same.
            ("switch-diamond", diamond(0, 1)),
            ("switch-diamond-swapped", diamond(1, 0)),
            (
                "switch-split-returns",
                body(
                    3,
                    vec![
                        block(0, vec![], switch(1, 1, 2)),
                        block(1, vec![assign(0, Rvalue::Use(konst(0)))], Terminator::Return),
                        block(2, vec![assign(0, Rvalue::Use(konst(1)))], Terminator::Return),
                    ],
                ),
            ),
            // A join that is NOT a return: the incoming values merge into a phi (L6), and the
            // phi's identity is its incoming expressions in edge order.
            ("switch-phi-join", phi_join(0, 1)),
            ("switch-phi-join-swapped", phi_join(1, 0)),
            // Calls: the callee's name is an observable.
            ("call-observe", call_then_return("observe")),
            ("call-other", call_then_return("other")),
            // The file's loop fixtures.
            ("seq-loop-1", sequential_loop(1)),
            ("seq-loop-2", sequential_loop(2)),
            ("seq-loop-latches", {
                let mut b = sequential_loop(1);
                b.blocks[2].terminator = assert_true(1);
                b.blocks[5].terminator = assert_true(4);
                b
            }),
            ("seq-loop-optional-later", {
                let mut b = sequential_loop(1);
                b.blocks[3].terminator = switch(1, 6, 4);
                b
            }),
            ("seq-loop-optional-earlier", {
                let mut b = sequential_loop(1);
                b.blocks[0].terminator = switch(1, 3, 1);
                b
            }),
            // Out of fragment, each refused by a different rule.
            ("unreachable", terminal(Terminator::Unreachable)),
            (
                "tail-call",
                terminal(Terminator::TailCall {
                    func: "crate::callee".into(),
                    args: vec![copy(1)],
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    callee_identity: None,
                    callee_key: None,
                }),
            ),
            (
                "drop",
                body(
                    3,
                    vec![
                        block(
                            0,
                            vec![],
                            Terminator::Drop {
                                place: Place::local(2),
                                target: BlockId(1),
                                span: SourceSpan::default(),
                                unwind: UnwindEdge::Unreachable,
                            },
                        ),
                        block(1, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
                    ],
                ),
            ),
            ("coverage", ret(vec![Statement::Coverage, assign(0, Rvalue::Use(copy(1)))])),
            (
                "misindexed",
                body(3, vec![block(1, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return)]),
            ),
            ("empty", body(3, vec![])),
            (
                "marker-in-dead-block",
                body(
                    3,
                    vec![
                        block(0, vec![assign(0, Rvalue::Use(copy(1)))], Terminator::Return),
                        block(1, vec![Statement::StorageLive(2)], Terminator::Return),
                    ],
                ),
            ),
        ];
        // The file's borrow-guard fixtures: the one refused shape in both mutabilities, and
        // every projected shape `to_mir` emits.
        let shapes: [(&str, Vec<Projection>); 4] = [
            ("bare", vec![]),
            ("deref", vec![Projection::Deref]),
            ("deref-field", vec![Projection::Deref, Projection::Field(0)]),
            (
                "deref-downcast-field",
                vec![Projection::Deref, Projection::Downcast(1), Projection::Field(0)],
            ),
        ];
        let mut borrow_names = Vec::new();
        for (shape, projections) in &shapes {
            for mutable in [false, true] {
                let name = format!("borrow-{shape}-{}", if mutable { "mut" } else { "shared" });
                borrow_names.push((name, one_borrow(projections.clone(), mutable)));
            }
        }

        let mut points: Vec<Point> = plain
            .drain(..)
            .map(|(name, body)| Point { name: name.to_string(), body, kinds: Vec::new() })
            .collect();
        points.extend(borrow_names.into_iter().map(|(name, body)| Point {
            name,
            body,
            kinds: Vec::new(),
        }));
        // The bare-borrow call under every recorded kind, and none: the exemption's arming.
        let kinds: [(&str, Option<Kind>); 4] = [
            ("unrecorded", None),
            ("Shared", Some(Kind::Shared)),
            ("Mut", Some(Kind::Mut)),
            ("NotARef", Some(Kind::NotARef)),
        ];
        for (label, kind) in kinds {
            points.push(Point {
                name: format!("bare-borrow-call/{label}"),
                body: bare_borrow_then_call(),
                kinds: kind.map(|k| vec![(0, vec![k])]).unwrap_or_default(),
            });
        }
        points
    }

    // ----------------------------------------------------------------------------------------
    // The checker.
    // ----------------------------------------------------------------------------------------

    /// Both sides' observations of every point, computed once.
    struct Observed {
        names: Vec<String>,
        pinned: Vec<Observation>,
        current: Vec<Observation>,
    }

    fn observed() -> Observed {
        let corpus = corpus();
        Observed {
            names: corpus.iter().map(|p| p.name.clone()).collect(),
            pinned: corpus.iter().map(|p| pinned::observe(&p.body, &p.kinds)).collect(),
            current: corpus.iter().map(|p| current::observe(&p.body, &p.kinds)).collect(),
        }
    }

    /// Every `(derived, built)` pair `new` accepts at `bit` and `old` does not — the rule as a
    /// function of two observation sets, so a MUTANT runs through the very same code path.
    fn widenings(
        names: &[String],
        new: &[Observation],
        old: &[Observation],
        bit: Bit,
    ) -> Vec<String> {
        let mut out = Vec::new();
        for d in 0..names.len() {
            for b in 0..names.len() {
                if accepts(verdict(&new[d], &new[b]), bit)
                    && !accepts(verdict(&old[d], &old[b]), bit)
                {
                    out.push(format!("derived={} built={}", names[d], names[b]));
                }
            }
        }
        out
    }

    /// Step (2.5)'s input, per side. `authenticate_source_header_correspondence` (unfrozen
    /// `source_provenance.rs`) refuses a pair when either side's `canonical_cfg_roles` does and
    /// otherwise MATCHES role values, so a movement widens step 2.5 if it admits a body the pin
    /// refused, or re-labels an admitted one (a coarser labelling can make two headers match
    /// that did not). Every point `new` admits must therefore carry exactly the roles `old`
    /// admitted it with. A refusal (`Ok` -> `Err`) passes. Stricter than "admits nothing new":
    /// a re-labelling that only REFINES is flagged too, and a waiver that makes one argues it
    /// and edits this function.
    fn cfg_role_widenings(
        names: &[String],
        new: &[Observation],
        old: &[Observation],
    ) -> Vec<String> {
        (0..names.len())
            .filter(|&i| new[i].cfg_roles.is_ok() && new[i].cfg_roles != old[i].cfg_roles)
            .map(|i| names[i].clone())
            .collect()
    }

    /// The points whose observation differs between the two sets.
    fn differences(names: &[String], new: &[Observation], old: &[Observation]) -> Vec<String> {
        (0..names.len()).filter(|&i| new[i] != old[i]).map(|i| names[i].clone()).collect()
    }

    fn pairs_with(
        names: &[String],
        obs: &[Observation],
        keep: impl Fn(usize, usize, Verdict) -> bool,
    ) -> Vec<String> {
        let mut out = Vec::new();
        for d in 0..names.len() {
            for b in 0..names.len() {
                if keep(d, b, verdict(&obs[d], &obs[b])) {
                    out.push(format!("derived={} built={}", names[d], names[b]));
                }
            }
        }
        out
    }

    /// THE RULE. Whatever a waiver claims, the moved oracle may admit no pair the pinned one
    /// refused, at either acceptance bit.
    #[test]
    fn the_current_mir_differential_refines_the_pinned_one() {
        let o = observed();
        for bit in [Bit::Agreed, Bit::AgreedExact] {
            let widened = widenings(&o.names, &o.current, &o.pinned, bit);
            assert!(
                widened.is_empty(),
                "the current MIR differential ADMITS at {bit:?} pairs the pinned oracle refused \
                 — a WIDENING of the frozen oracle, which no waiver row may excuse: {widened:?}"
            );
        }
        let relabelled = cfg_role_widenings(&o.names, &o.current, &o.pinned);
        assert!(
            relabelled.is_empty(),
            "the current canonical_cfg_roles ADMITS bodies the pinned one refused, or admits them \
             with different roles — a WIDENING of step 2.5's input: {relabelled:?}"
        );

        // NON-VACUITY: the pinned oracle must reach every verdict over this corpus, through
        // real normalizations, or the rule above could hold over a corpus nothing decides.
        let p = &o.pinned;
        let distinct_agreed =
            pairs_with(&o.names, p, |d, b, v| d != b && matches!(v, Verdict::Agreed { .. }));
        assert!(
            distinct_agreed.len() >= 4,
            "fewer than four DISTINCT bodies agree ({distinct_agreed:?}): no normalization is \
             exercised, so the corpus cannot tell a widening from equality"
        );
        let agreed_not_exact =
            pairs_with(&o.names, p, |_, _, v| v == Verdict::Agreed { markers_exact: false });
        assert!(
            !agreed_not_exact.is_empty(),
            "no agreed pair differs in its markers: the -O bit is untested"
        );
        let distinct_exact = pairs_with(&o.names, p, |d, b, v| {
            d != b && v == Verdict::Agreed { markers_exact: true }
        });
        assert!(!distinct_exact.is_empty(), "no two distinct bodies agree at the -O bit");
        let mismatched = pairs_with(&o.names, p, |_, _, v| v == Verdict::Mismatch);
        assert!(mismatched.len() >= 4, "fewer than four mismatches: {mismatched:?}");
        // The refs guard must front a genuinely ARMABLE path: a derived body it refuses whose
        // own canonicalization would otherwise have succeeded.
        let guard_only: Vec<&String> = o
            .names
            .iter()
            .zip(p)
            .filter(|(_, obs)| obs.refs_guard.is_some() && obs.canonical.is_ok())
            .map(|(name, _)| name)
            .collect();
        assert!(!guard_only.is_empty(), "the refs guard refuses nothing the canonicalizer admits");
        for (what, count) in [
            ("canonical refusals", p.iter().filter(|obs| obs.canonical.is_err()).count()),
            ("marker-channel refusals", p.iter().filter(|obs| obs.markers.is_err()).count()),
            (
                "non-empty marker channels",
                p.iter().filter(|obs| obs.markers.as_ref().is_ok_and(|m| !m.is_empty())).count(),
            ),
            ("CFG-role refusals", p.iter().filter(|obs| obs.cfg_roles.is_err()).count()),
            ("CFG-role successes", p.iter().filter(|obs| obs.cfg_roles.is_ok()).count()),
        ] {
            assert!(count >= 1, "the corpus has no {what} on the pinned side");
        }
        let fired: Vec<&str> = p
            .iter()
            .flat_map(|obs| obs.norms.iter())
            .filter(|(_, n)| *n > 0)
            .map(|(name, _)| *name)
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect();
        assert!(fired.len() >= 8, "fewer than eight normalizations ever fire: {fired:?}");
    }

    /// THE CURRENT WAIVER'S CLAIM, "NEITHER SAMPLES NOR REFUSES DIFFERENTLY": every point's
    /// observation is identical on both sides. At the ratified state (pin == tree) the same
    /// assertion is a check on the harness itself. A future REFUSES-MORE waiver clears
    /// `VERDICT_CORE_IDENTICAL` and must instead witness a strict refusal.
    #[test]
    fn the_verdict_core_neither_samples_nor_refuses_differently() {
        let o = observed();
        let differing = differences(&o.names, &o.current, &o.pinned);
        if waived_delta::VERDICT_CORE_IDENTICAL || pin_meta::PIN_IS_CURRENT {
            let detail: Vec<String> = differing
                .iter()
                .map(|name| {
                    let i = o.names.iter().position(|n| n == name).expect("named point");
                    format!("{name}:\n  pinned  {:?}\n  current {:?}", o.pinned[i], o.current[i])
                })
                .collect();
            assert!(
                differing.is_empty(),
                "the waiver says the verdict core NEITHER SAMPLES NOR REFUSES DIFFERENTLY, yet \
                 {} point(s) are observed differently:\n{}",
                differing.len(),
                detail.join("\n")
            );
        } else {
            let bit =
                if waived_delta::WITNESS_BIT_IS_EXACT { Bit::AgreedExact } else { Bit::Agreed };
            let strictly_more = widenings(&o.names, &o.pinned, &o.current, bit);
            for pair in waived_delta::WITNESS_PAIRS {
                assert!(
                    strictly_more.iter().any(|w| w == pair),
                    "REFUSES MORE was not witnessed at {bit:?}: `{pair}` is not refused now \
                     (strict refusals: {strictly_more:?}; points observed differently: \
                     {differing:?})"
                );
            }
            if waived_delta::WITNESS_BIT_IS_EXACT {
                // A movement of the marker channel alone: nothing but `markers` may differ.
                let moved: Vec<&String> = o
                    .names
                    .iter()
                    .enumerate()
                    .filter(|&(i, _)| {
                        let (p, c) = (&o.pinned[i], &o.current[i]);
                        p.canonical != c.canonical
                            || p.norms != c.norms
                            || p.refs_guard != c.refs_guard
                            || p.cfg_roles != c.cfg_roles
                    })
                    .map(|(_, name)| name)
                    .collect();
                assert!(
                    moved.is_empty(),
                    "the waiver moves the marker channel only, yet these points moved in another \
                     channel: {moved:?}"
                );
                assert!(
                    widenings(&o.names, &o.pinned, &o.current, Bit::Agreed).is_empty(),
                    "a marker-channel movement changed AGREEMENT itself"
                );
            }
        }
    }

    /// THE MUTATION PROOF. The same checkers, run against the current observations with one
    /// decision disarmed, must report exactly the widening that decision prevents — or the
    /// tests above are tests of nothing. (a)–(d) are measured against the CURRENT observations,
    /// so each isolates its own decision: under a real movement of the frozen file, the one
    /// that fails names the decision the movement disarmed, and no other. And (e), a mutant that
    /// only REFUSES more, must pass the rule and fail the identity claim: the two relations are
    /// different, and both are armed.
    #[test]
    fn the_harness_catches_a_widened_oracle() {
        let o = observed();
        let mutate = |f: &dyn Fn(&mut Observation)| {
            let mut m = o.current.clone();
            m.iter_mut().for_each(f);
            m
        };

        // (a) The (2.75) refs guard deleted: exactly the bare-borrow derived bodies widen.
        let no_guard = mutate(&|obs| obs.refs_guard = None);
        let widened = widenings(&o.names, &no_guard, &o.current, Bit::Agreed);
        assert!(!widened.is_empty(), "deleting the refs guard admitted nothing: DISARMED");
        assert!(
            widened.iter().all(|w| w.starts_with("derived=borrow-bare-")
                || w.starts_with("derived=bare-borrow-call/")),
            "the refs-guard mutant widened pairs the guard does not decide: {widened:?}"
        );
        assert!(
            widened
                .iter()
                .any(|w| w == "derived=bare-borrow-call/Shared built=bare-borrow-call/Shared"),
            "the armed exemption (a Shared kind) is not among the widenings: {widened:?}"
        );

        // (b) The constant payload erased from the rendering: `c:uint:<v>` -> `c:uint:_`.
        let constant_blind = mutate(&|obs| {
            if let Ok(lines) = &mut obs.canonical {
                lines.iter_mut().for_each(|line| *line = erase_uint_values(line));
            }
        });
        let widened = widenings(&o.names, &constant_blind, &o.current, Bit::Agreed);
        for expected in [
            "derived=ret-const-0 built=ret-const-1",
            "derived=add-1 built=add-2",
            "derived=seq-loop-1 built=seq-loop-2",
            "derived=switch-diamond built=switch-diamond-swapped",
            "derived=switch-phi-join built=switch-phi-join-swapped",
        ] {
            assert!(
                widened.iter().any(|w| w == expected),
                "the constant-blind mutant did not widen `{expected}`: {widened:?}"
            );
        }

        // (c) The marker channel blinded: widens the -O bit only, never agreement itself.
        let marker_blind = mutate(&|obs| obs.markers = Ok(Vec::new()));
        assert!(
            widenings(&o.names, &marker_blind, &o.current, Bit::Agreed).is_empty(),
            "blinding the marker channel changed AGREEMENT: the marker channel must never \
             decide the semantic verdict"
        );
        let widened = widenings(&o.names, &marker_blind, &o.current, Bit::AgreedExact);
        assert!(
            widened.iter().any(|w| w == "derived=ret-arg built=ret-arg-marked"),
            "the marker-blind mutant did not widen the -O bit: {widened:?}"
        );

        // (d) The CFG-role channel. (d1) Its refusals disarmed (`Err` -> `Ok`): exactly the
        // points the current oracle refuses are flagged, and no pair verdict moves — the pair
        // relation cannot see this channel, which is why it has its own. (d2) Its roles
        // collapsed to one value (the injectivity step 2.5 relies on, gone): exactly the
        // admitted points with more than one canonical block are flagged.
        let refused_roles: Vec<String> = o
            .names
            .iter()
            .zip(&o.current)
            .filter(|(_, obs)| obs.cfg_roles.is_err())
            .map(|(name, _)| name.clone())
            .collect();
        assert!(
            refused_roles.iter().any(|n| n == "tail-call"),
            "the TailCall fixture is not refused by canonical_cfg_roles: {refused_roles:?}"
        );
        let roles_admitted = mutate(&|obs| {
            if obs.cfg_roles.is_err() {
                obs.cfg_roles = Ok(Vec::new());
            }
        });
        assert_eq!(
            cfg_role_widenings(&o.names, &roles_admitted, &o.current),
            refused_roles,
            "disarming the CFG-role refusals must flag exactly the points they refused"
        );
        for bit in [Bit::Agreed, Bit::AgreedExact] {
            assert!(
                widenings(&o.names, &roles_admitted, &o.current, bit).is_empty(),
                "the CFG-role mutant moved a pair verdict at {bit:?}"
            );
        }
        let multi_block: Vec<String> = o
            .names
            .iter()
            .zip(&o.current)
            .filter(|(_, obs)| {
                obs.cfg_roles.as_ref().is_ok_and(|roles| {
                    roles.iter().any(|r| r.as_ref().is_some_and(|r| !r.is_empty()))
                })
            })
            .map(|(name, _)| name.clone())
            .collect();
        assert!(
            multi_block.iter().any(|n| n == "switch-diamond"),
            "no admitted body has a non-entry role: {multi_block:?}"
        );
        let roles_collapsed = mutate(&|obs| {
            if let Ok(roles) = &mut obs.cfg_roles {
                roles.iter_mut().flatten().for_each(|role| role.clear());
            }
        });
        assert_eq!(
            cfg_role_widenings(&o.names, &roles_collapsed, &o.current),
            multi_block,
            "collapsing the roles must flag exactly the bodies whose roles it changed"
        );

        // (f) The per-local ACCESS LIST stripped from every marker line (` acc:[..]` and the
        // ` via:[..]` that follows it), leaving liveness and positions: exactly the
        // `relive-stale`/`relive-bound` pair widens at the -O bit, in both orientations, and
        // agreement itself does not move. The storage rule refuses every other F3 witness on its
        // own (the round-3 review's finding), so without this mutant nothing would fail if the
        // access list were deleted.
        let access_blind = mutate(&|obs| {
            if let Ok(lines) = &mut obs.markers {
                for line in lines.iter_mut() {
                    if let Some(at) = line.find(" acc:[") {
                        line.truncate(at);
                    }
                }
            }
        });
        assert!(
            widenings(&o.names, &access_blind, &o.current, Bit::Agreed).is_empty(),
            "stripping the access lists changed AGREEMENT"
        );
        assert_eq!(
            widenings(&o.names, &access_blind, &o.current, Bit::AgreedExact),
            vec![
                "derived=relive-bound built=relive-stale".to_string(),
                "derived=relive-stale built=relive-bound".to_string(),
            ],
            "the access-blind mutant must widen exactly the carried-value pair"
        );

        // (e) REFUSES MORE only — every body carrying a `Nop` is refused, by the canonicalizer
        // and by the CFG-role channel alike. Built from the PINNED observations, so it is about
        // the two relations and not about what the working tree happens to refuse: the rule
        // accepts it (a refusal is never a widening), the identity claim does not, and the
        // strict refusal is witnessed.
        let refuses_more = {
            let corpus = corpus();
            let mut m = o.pinned.clone();
            for (obs, point) in m.iter_mut().zip(&corpus) {
                if point
                    .body
                    .blocks
                    .iter()
                    .any(|b| b.stmts.iter().any(|s| matches!(s, Statement::Nop)))
                {
                    obs.canonical = Err("harness mutant (e): Nop refused".to_string());
                    obs.cfg_roles = Err("harness mutant (e): Nop refused".to_string());
                }
            }
            m
        };
        for bit in [Bit::Agreed, Bit::AgreedExact] {
            assert!(
                widenings(&o.names, &refuses_more, &o.pinned, bit).is_empty(),
                "a mutant that only refuses more was reported as a widening at {bit:?}"
            );
        }
        assert!(
            cfg_role_widenings(&o.names, &refuses_more, &o.pinned).is_empty(),
            "a CFG-role refusal was reported as a widening of step 2.5's input"
        );
        assert_eq!(
            differences(&o.names, &refuses_more, &o.pinned),
            vec!["ret-arg-nop".to_string()],
            "the identity claim must see exactly the refused body"
        );
        assert!(
            widenings(&o.names, &o.pinned, &refuses_more, Bit::Agreed)
                .iter()
                .any(|w| w == "derived=ret-arg-nop built=ret-arg"),
            "the refuse-more mutant must be witnessed as a strict refusal"
        );
    }

    /// `c:uint:<digits>` -> `c:uint:_`, everywhere in one canonical line.
    fn erase_uint_values(line: &str) -> String {
        const TAG: &str = "c:uint:";
        let mut out = String::with_capacity(line.len());
        let mut rest = line;
        while let Some(at) = rest.find(TAG) {
            out.push_str(&rest[..at + TAG.len()]);
            rest = rest[at + TAG.len()..].trim_start_matches(|c: char| c.is_ascii_digit());
            out.push('_');
        }
        out.push_str(rest);
        out
    }

    // ----------------------------------------------------------------------------------------
    // The census: which production tokens moved.
    // ----------------------------------------------------------------------------------------

    /// The production section's lines with blank lines and FULL-LINE `//` comments removed
    /// (trailing whitespace trimmed). A line is dropped only when it begins OUTSIDE a string
    /// literal and outside a block comment, which a small lexer tracks across lines (string,
    /// raw string, block comment; char literals and lifetimes told apart). Everything else —
    /// code, attributes, trailing comments, lines inside strings or block comments — is kept
    /// and compared exactly, so the normalization can only make the census STRICTER than
    /// "production tokens", never blind to one.
    pub(crate) fn production_lines(source: &str) -> Vec<&str> {
        #[derive(Clone, Copy, PartialEq)]
        enum State {
            Code,
            Str,
            RawStr(usize),
            Block(usize),
        }
        let mut state = State::Code;
        let mut out = Vec::new();
        for raw in source.lines() {
            let line = raw.trim_end();
            let at_start = state;
            let chars: Vec<char> = line.chars().collect();
            let mut i = 0;
            while i < chars.len() {
                let c = chars[i];
                let next = chars.get(i + 1).copied();
                match state {
                    State::Code => match c {
                        '/' if next == Some('/') => break,
                        '/' if next == Some('*') => {
                            state = State::Block(1);
                            i += 2;
                            continue;
                        }
                        '"' => state = State::Str,
                        'r' if matches!(next, Some('"' | '#'))
                            && (i == 0
                                || !(chars[i - 1].is_alphanumeric() || chars[i - 1] == '_')
                                || (chars[i - 1] == 'b'
                                    && (i == 1
                                        || !(chars[i - 2].is_alphanumeric()
                                            || chars[i - 2] == '_')))) =>
                        {
                            let hashes = chars[i + 1..].iter().take_while(|&&h| h == '#').count();
                            if chars.get(i + 1 + hashes) == Some(&'"') {
                                state = State::RawStr(hashes);
                                i += hashes + 2;
                                continue;
                            }
                        }
                        '\'' => {
                            // A char literal (`'x'`, `'\n'`, `'\''`) or a lifetime/label (`'a`).
                            if next == Some('\\') {
                                let mut j = i + 3;
                                while j < chars.len() && chars[j] != '\'' {
                                    j += 1;
                                }
                                i = j + 1;
                                continue;
                            }
                            if chars.get(i + 2) == Some(&'\'') {
                                i += 3;
                                continue;
                            }
                        }
                        _ => {}
                    },
                    State::Str => match c {
                        '\\' => {
                            i += 2;
                            continue;
                        }
                        '"' => state = State::Code,
                        _ => {}
                    },
                    State::RawStr(hashes) => {
                        if c == '"'
                            && chars[i + 1..].iter().take(hashes).filter(|&&h| h == '#').count()
                                == hashes
                        {
                            state = State::Code;
                            i += hashes + 1;
                            continue;
                        }
                    }
                    State::Block(depth) => {
                        if c == '/' && next == Some('*') {
                            state = State::Block(depth + 1);
                            i += 2;
                            continue;
                        }
                        if c == '*' && next == Some('/') {
                            state = if depth == 1 { State::Code } else { State::Block(depth - 1) };
                            i += 2;
                            continue;
                        }
                    }
                }
                i += 1;
            }
            let comment_line = at_start == State::Code && line.trim_start().starts_with("//");
            if !line.trim().is_empty() && !comment_line {
                out.push(line);
            }
        }
        out
    }

    /// The ordered line diff `old -> new` (`-` old only, `+` new only), by longest common
    /// subsequence with a fixed tie-break, so the same pair of sections always prints the same
    /// delta.
    pub(crate) fn line_delta(old: &[&str], new: &[&str]) -> Vec<String> {
        let prefix = old.iter().zip(new).take_while(|(a, b)| a == b).count();
        let suffix = old[prefix..]
            .iter()
            .rev()
            .zip(new[prefix..].iter().rev())
            .take_while(|(a, b)| a == b)
            .count();
        let a = &old[prefix..old.len() - suffix];
        let b = &new[prefix..new.len() - suffix];
        // lcs[i][j] = LCS length of a[i..] and b[j..].
        let width = b.len() + 1;
        let mut lcs = vec![0u32; (a.len() + 1) * width];
        for i in (0..a.len()).rev() {
            for j in (0..b.len()).rev() {
                lcs[i * width + j] = if a[i] == b[j] {
                    lcs[(i + 1) * width + j + 1] + 1
                } else {
                    lcs[(i + 1) * width + j].max(lcs[i * width + j + 1])
                };
            }
        }
        let (mut i, mut j) = (0, 0);
        let mut out = Vec::new();
        while i < a.len() || j < b.len() {
            if i < a.len() && j < b.len() && a[i] == b[j] {
                i += 1;
                j += 1;
            } else if j == b.len()
                || (i < a.len() && lcs[(i + 1) * width + j] >= lcs[i * width + j + 1])
            {
                out.push(format!("-{}", a[i]));
                i += 1;
            } else {
                out.push(format!("+{}", b[j]));
                j += 1;
            }
        }
        out
    }

    const PINNED_SECTION: &str =
        include_str!(concat!(env!("OUT_DIR"), "/mir_differential_pinned.rs"));
    const CURRENT_SECTION: &str =
        include_str!(concat!(env!("OUT_DIR"), "/mir_differential_current.rs"));

    fn production_delta() -> Vec<String> {
        line_delta(&production_lines(PINNED_SECTION), &production_lines(CURRENT_SECTION))
    }

    /// THE CENSUS. The production-token delta pin -> tree is EXACTLY the one the waiver row
    /// names — so a movement in a `TyCtxt` channel, which the behavioural tests above cannot
    /// see, fails here until a waiver names it. At the ratified state the delta is empty.
    #[test]
    fn the_production_delta_is_exactly_the_waived_one() {
        let delta = production_delta();
        if pin_meta::PIN_IS_CURRENT {
            assert!(
                delta.is_empty(),
                "pinned == current, yet the census found a delta: {delta:#?}"
            );
            return;
        }
        let expected: Vec<String> =
            waived_delta::TEXT_DELTA.iter().map(|l| l.to_string()).collect();
        assert!(
            delta == expected,
            "the production section moved by a delta no waiver names. MEASURED delta (pin -> \
             tree, full-line comments and blank lines removed), in `waived_delta::TEXT_DELTA` \
             spelling:\n{}",
            delta.iter().map(|l| format!("        {l:?},")).collect::<Vec<_>>().join("\n")
        );
    }

    /// The census's normalizer drops comment LINES and nothing else: a `//` inside a string,
    /// a string or block comment whose continuation line begins with `//`, char literals that
    /// look like quotes, and lifetimes are all kept.
    #[test]
    fn the_census_drops_only_comment_lines() {
        let source = concat!(
            "//! inner doc\n",
            "/// outer doc\n",
            "    // indented comment\n",
            "\n",
            "fn a<'tcx>(x: &'tcx str) -> char { let _ = \"http://kept\"; '\"' } // trailing kept\n",
            "const S: &str = \"first \\\n",
            "// inside a string: kept\n",
            "\";\n",
            "const R: &str = r#\"raw \" still raw\n",
            "// inside a raw string: kept\n",
            "\"#;\n",
            "/* block\n",
            "// inside a block comment: kept\n",
            "*/ fn b() {}\n",
            "let q = '\\''; // escaped quote char\n",
            "// dropped again\n",
            "fn c() {}\n",
        );
        assert_eq!(
            production_lines(source),
            vec![
                "fn a<'tcx>(x: &'tcx str) -> char { let _ = \"http://kept\"; '\"' } // trailing kept",
                "const S: &str = \"first \\",
                "// inside a string: kept",
                "\";",
                "const R: &str = r#\"raw \" still raw",
                "// inside a raw string: kept",
                "\"#;",
                "/* block",
                "// inside a block comment: kept",
                "*/ fn b() {}",
                "let q = '\\''; // escaped quote char",
                "fn c() {}",
            ]
        );
        assert_eq!(
            line_delta(&["a", "b", "c", "d"], &["a", "x", "c", "d", "e"]),
            vec!["-b", "+x", "+e"],
            "the delta is ordered and minimal"
        );
        assert_eq!(line_delta(&["a", "b"], &["b", "a"]).len(), 2, "a reordering is a delta");
    }

    /// The baseline the build script compiled is the blob the MANIFEST pins right now, so a
    /// stale build output cannot quietly compare against yesterday's pin. `include_str!` also
    /// makes the manifest a compile-time dependency of this test target.
    #[test]
    fn the_compiled_baseline_is_the_manifest_pin() {
        let manifest = include_str!("../../../scripts/frozen-files.txt");
        let pin = manifest
            .lines()
            .map(str::trim)
            .filter(|row| !row.is_empty() && !row.starts_with('#'))
            .find_map(|row| {
                let mut cols = row.split('|');
                (cols.next() == Some("crates/trust-thir-lower/src/mir_differential.rs"))
                    .then(|| cols.next().unwrap_or_default())
            })
            .expect("scripts/frozen-files.txt pins mir_differential.rs");
        assert_eq!(
            pin_meta::PINNED_BLOB,
            pin,
            "the harness compiled a baseline that is not the manifest's pin"
        );
    }
}
