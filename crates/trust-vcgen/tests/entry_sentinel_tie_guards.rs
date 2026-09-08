//! The PLANTED-VIOLATION guards on the entry-sentinel tie.
//!
//! An in-place update whose read renders BARE is pinned to an explicit pre-write
//! token (`stamp_entry_valued_recurrent_read`). Since the 2026-08-29 mint gate,
//! that token is the entry sentinel `n#e` ONLY where
//! `full_graph_union_is_entry_only` proves the pre-write value IS the
//! function-entry value on every path into the minting block — normal or unwind —
//! and the never-tieable `n#pre_s{b}_{k}` everywhere else. `#e` unifies with
//! nothing on its own, so `conjoin_preconditions_versioned_recorded` ties it back
//! to the bare name in the same conjoin bucket: `Eq(n#e, n)`. The tie is TRUE only
//! because both spellings denote the function-entry value, and each way that can
//! fail is refused at its own site — and watched failing here:
//!
//!  * MINT GATE (left side: `#e` must denote entry). RE-ADJUDICATED
//!    2026-08-30 (dropped-def write-visibility fix): `block_entry_versions`
//!    now shares the mint gate's unwind-inclusive predecessor relation, so on
//!    the shapes below a post-write read is VERSIONED (`n#e_s1_0`, `n#s0_0`)
//!    rather than bare — the pin's stamp never fires and the false-`#e` route
//!    those shapes planted is closed by construction (one predecessor
//!    relation, no v2/full divergence to exploit). The gate is retained as
//!    fail-closed depth for the two corners where the maps still differ — a
//!    step-cap non-convergence (partial v2 map vs `None` full map) and a
//!    block unreachable across full-graph edges. The verdict-level evidence
//!    the shapes still carry: `mixed_unwind_mint`'s rows now REFUTE with the
//!    real unwind trace, and `cleanup_mint`'s row stays `Failed`.
//!  * CONSUMER CLAUSE (right side: bare must mean entry where the tie lands).
//!    RE-ADJUDICATED 2026-08-30: with the unwind-inclusive entry map, a
//!    consumer holding a threaded `#e` fact is downstream of the mint block's
//!    own write, so it versions the base and the clause ADMITS — the tie at a
//!    cleanup consumer is now the TRUE identity `entry == entry` (see
//!    `the_tie_at_a_cleanup_consumer_is_sound_and_the_stale_sibling_degrades`).
//!    The clause is retained fail-closed for empty-map/step-cap corners; the
//!    fixture that used to isolate it (`cleanup_consumer` with an EMPTY v2
//!    entry map) was retired with the unwind-blind map itself.
//!  * COLLISION. Delete the collision check in `entry_sentinel_ties` and
//!    `no_tie_onto_a_local_…` fails with the same conjunct; delete the mint-site
//!    `#pre` collision refusal and
//!    `no_pin_onto_a_local_that_is_literally_named_with_the_pre_token` fails.
//!
//! HISTORY, kept because the corrections carry the lesson. The whole-function
//! quantifier (`entry_map_covers` over EVERY block) existed because the consumer
//! could not tell which block minted a given `#e`. It was simultaneously too
//! strong — one droppable `String`'s cleanup cluster vetoed the tie at every
//! consumer, the measured cost in `entry_sentinel_unranged_overflow_realmir` —
//! and too weak: it quantified over the V2 map, which has no unwind edges, so a
//! mixed shape whose unwind path delivers a write into a v2-`{e}` block passed it
//! while `#e` named a post-write value (the false proof above). The root cause
//! fix moved the guarantee to the ONE mint site, which can see its own block;
//! the quantifier and the "mint-side ⟹ consumer-side" `debug_assert!` are gone,
//! and the consumer-side clause — once documented dead — is now load-bearing.

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

/// Every free variable whose version token is EXACTLY the entry sentinel `e` —
/// the spellings only `stamp_entry_valued_recurrent_read` can mint (mixed joins
/// like `n#e_s1_t` are a different, untieable token and deliberately excluded).
fn entry_sentinel_spellings(vcs: &[VerificationCondition]) -> Vec<String> {
    let mut out: Vec<String> = vcs
        .iter()
        .flat_map(|vc| vc.formula.free_variables())
        .filter(|v| v.split_once('#').is_some_and(|(_, tok)| tok == "e"))
        .collect();
    out.sort();
    out.dedup();
    out
}

/// Router verdicts for every VC of `func` matching `kind` — the production
/// discharge path, not a hand-built stand-in.
fn verdicts_of_kind(
    func: &VerifiableFunction,
    want: fn(&VcKind) -> bool,
) -> Vec<VerificationResult> {
    let router = trust_router::Router::deterministic_in_process_ay(30_000);
    trust_vcgen::generate_vcs(func)
        .into_iter()
        .filter(|vc| want(&vc.kind))
        .map(|vc| {
            router
                .verify_all(std::slice::from_ref(&vc))
                .into_iter()
                .next()
                .expect("one verdict per VC")
                .1
        })
        .collect()
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
/// HISTORY: `block_entry_versions` used to build its predecessor lists from
/// `v2_terminator_targets`, which had no unwind arm, so bb2's entry-version map
/// was EMPTY and every name rendered bare there — while `v2_path_def_fixpoint`
/// DID transport the pinned def across `unwind: Cleanup(bb2)`. Bare was
/// therefore NOT the entry value at bb2, and the tie would have asserted
/// `n#e == n` about the POST-write subject — the split recurrence
/// `self_referential_definition` cannot see.
///
/// RE-ADJUDICATED 2026-08-30 (dropped-def write-visibility fix): the entry map
/// is unwind-inclusive, so bb2 versions `n` to bb0's write token `s0_0`. The
/// pinned def's subject is stamped `n#s0_0` at the conjoin rename, the tie's
/// bare side meets ONLY the entry bucket, and `Eq(n#e, n)` becomes the true
/// identity `entry == entry`. The stale establish-stamped sibling
/// (`n#s0_0 == n / 3` with a bare read) re-stamps at bb2 into the recurrence
/// `n#s0_0 == n#s0_0 / 3`, which the scanner catches and DEGRADES — the
/// fail-closed route, watched below.
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
/// would be empty.
///
/// CORRECTED 2026-08-29 (twice — each correction measured). A first correction
/// claimed the colliding local's reads collapse to bare `n` before any VC ships,
/// so the collision check never decides. RE-MEASURED after the mint-gate
/// narrowing: deleting the collision check makes this fixture fail with
/// `Eq(Var("n#e"), Var("n"))` emitted — the local's read DOES reach the renamed
/// formula under its own spelling here (the extraction collapse pinned by
/// `versioned_param_type_range_guards` covers the DEF-subject route, not this
/// read route). The check is live and this fixture isolates it.
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

/// THE MINT GATE's false-proof shape: a mint block whose V2 reaching union is
/// `{e}` while an UNWIND edge can deliver a post-write value into it.
///
/// bb0 switches to the WRITER bb1 (`n = 3`, then `Drop { target: bb4,
/// unwind: Cleanup(bb3) }`) or to bb2 (`goto bb3`). bb3 does the in-place update
/// `n = n - 3`: its only V2 in-edge is from bb2, so the union is `{e}`, the read
/// renders bare, and the pin fires. But at runtime the entry path `n = 5` takes
/// bb1, sets `n = 3`, the drop panics into bb3, `3 - 3 = 0`, and bb5's `100 / n`
/// divides by zero — all while the preconditions `4 <= n < 30` hold at ENTRY.
///
/// Pre-gate, `stamp_entry_valued_recurrent_read` stamped `n#e` here and the
/// whole-function quantifier PASSED (every block has a v2 in-edge), so the tie
/// `Eq(n#e, n)` carried `4 <= n < 30` onto the post-write read and the
/// DivisionByZero row shipped `Proved { assurance: SmtBacked }` — a measured
/// FALSE PROOF on the pre-fix tree. The gate then refused `#e` (bb3's
/// unwind-inclusive union is `{e, s1_0}`, not `{e}`) and stamped the read
/// `n#pre_s3_0`. Since 2026-08-30 the v2 entry map shares the gate's
/// unwind-inclusive predecessor relation, so the read never renders bare at
/// all: it is versioned to the MIXED join `n#e_s1_0` — a partially-entry
/// spelling `entry_sentinel_ties` refuses by exact-token match — and the pin's
/// stamp has nothing left to do. Same severance, one map earlier.
///
/// rustc never emits this shape (no corpus fixture has an Assign in an
/// unwind-only-reachable block), but `trust-vcgen` accepts caller-built
/// `VerifiableFunction` JSON and `validate_function` checks no CFG/cleanup
/// invariant — asserted valid below so the front door stays the front door.
fn mixed_unwind_mint() -> VerifiableFunction {
    let u32_local = |index: usize, name: &str| LocalDecl {
        index,
        ty: Ty::u32(),
        name: Some(name.into()),
    };
    let int_var = |name: &str| Box::new(Formula::Var(name.into(), Sort::Int));
    VerifiableFunction {
        name: "mixed_unwind_mint".into(),
        def_path: "tie_guard::mixed_unwind_mint".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::u32(),
            locals: vec![
                u32_local(0, "__ret"),
                u32_local(1, "n"),
                u32_local(2, "c"),
                u32_local(3, "out"),
                u32_local(4, "tmp"),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(2))],
                        otherwise: BlockId(1),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Drop {
                        place: Place::local(4),
                        target: BlockId(4),
                        unwind: UnwindEdge::Cleanup(BlockId(3)),
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Goto(BlockId(3)) },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Sub,
                            Operand::Copy(Place::local(1)),
                            Operand::Constant(ConstValue::Uint(3, 32)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(5)),
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
                BasicBlock {
                    id: BlockId(5),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Constant(ConstValue::Uint(100, 32)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
            ],
            arg_count: 2,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![
            Formula::Ge(int_var("n"), Box::new(Formula::Int(4))),
            Formula::Lt(int_var("n"), Box::new(Formula::Int(30))),
        ],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// THE MINT GATE's cleanup-block shape: the mint itself sits in a block reached
/// ONLY across an unwind edge, downstream of a real write.
///
/// bb0 writes `n = 0`, then `Drop { target: bb1, unwind: Cleanup(bb2) }`. bb2
/// does `n = n / 3`; its consumer bb3 (`out = 100 / n`) versions `n`. Pre-gate
/// the pin stamped `n#e` here — a symbol naming bb2's post-write local value,
/// not the entry value — and only the whole-function quantifier kept the tie
/// out. Post-narrowing the gate refused (bb2's unwind-inclusive union is
/// `{s0_0}`) and stamped the never-tieable `n#pre_s2_0`. Since 2026-08-30 the
/// v2 entry map is unwind-inclusive too, so bb2's read of `n` never renders
/// bare: it carries bb0's write token `n#s0_0` — connected to the ACTUAL
/// `n = 0` write across the cleanup edge, strictly stronger than the `#pre`
/// havoc — and the pin's stamp has nothing to repair.
///
/// The row must stay `Failed`: the real unwind path is `n := 0`, panic, `0 / 3
/// = 0`, then `100 / 0`. Admitting the tie would carry the precondition
/// `n >= 3` onto the mint's read and MASK that division — the unsound flip this
/// fixture exists to refuse (watched red with the gate disabled).
fn cleanup_mint() -> VerifiableFunction {
    let mut f = func(
        "cleanup_mint",
        vec![
            LocalDecl { index: 0, ty: Ty::u32(), name: Some("__ret".into()) },
            LocalDecl { index: 1, ty: Ty::u32(), name: Some("n".into()) },
            LocalDecl { index: 2, ty: Ty::u32(), name: Some("tmp".into()) },
            LocalDecl { index: 3, ty: Ty::u32(), name: Some("out".into()) },
        ],
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(0, 32))),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Drop {
                    place: Place::local(2),
                    target: BlockId(1),
                    unwind: UnwindEdge::Cleanup(BlockId(2)),
                    span: SourceSpan::default(),
                },
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::BinaryOp(
                        BinOp::Div,
                        Operand::Copy(Place::local(1)),
                        Operand::Constant(ConstValue::Uint(3, 32)),
                    ),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Goto(BlockId(3)),
            },
            BasicBlock {
                id: BlockId(3),
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
    );
    f.preconditions = vec![Formula::Ge(
        Box::new(Formula::Var("n".into(), Sort::Int)),
        Box::new(Formula::Int(3)),
    )];
    f
}

/// [`cleanup_mint`] plus a local literally named `n#pre_s2_0` — the collision
/// fixture for the FALLBACK spelling, mirroring `colliding_local` for `n#e`.
/// `validate_function` does not reserve `#` in local names, so the pin's chosen
/// symbol may be a real, unrelated place; minting it anyway would alias the two.
/// The mint site fails closed: no repair (the bare def then collapses at the
/// consumer into the recurrence the scanners already report and degrade).
fn pre_token_colliding_local() -> VerifiableFunction {
    let mut f = cleanup_mint();
    f.name = "pre_token_colliding_local".into();
    f.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::u32(),
        name: Some("n#pre_s2_0".into()),
    });
    f
}

/// A def whose VERSION GEN-KEY is not its PIN SUBJECT.
///
/// `pin_in_place_update_reads` rebinds the subject to BARE `subj`, while every kill
/// and version token keyed on the def uses `formula_def_name` — the WHOLE lhs name.
/// `block_def_subject` SPLITS that name at '#', so the two disagree exactly when the
/// lhs name contains '#'. A def of a local named `n#x` then gens the token for `n#x`
/// and ships a fact whose subject is `n`, a name the entry-version dataflow never saw
/// written. The COLLISION check refuses only the exact spelling `n#e`, so this
/// near-miss walked straight past it.
///
/// Second ingredient: `block_def_establish_stmt` scans STATEMENTS while the gen-set is
/// built from DEFS, and `extract_block_definitions_until_impl`'s "skip complex rvalues"
/// arm emits no def for `CopyForDeref`. So `n = CopyForDeref(c)` establishes `n` and
/// versions nothing.
///
/// * bb1 (WRITER): `n#x = n / 3` — the def the pin fires on, subject splitting to `n` —
///   then `n = CopyForDeref(c)`, `n`'s establish point, which emits no def. bb1's
///   version gen-set is `{n#x}`: it never versions `n`.
/// * bb2 (SIBLING, not an ancestor of the consumer): `n = 7`, purely so `n` lands in
///   `all_names` and is TRACKED in every block's entry map — which is what makes the
///   MINT-SIDE clause pass.
/// * bb3 (CONSUMER): `out = 100 / n`. Entry map TRACKS `n` (mint side passes) with the
///   value `{e}` (consumer side would refuse).
///
/// This is the first fixture in the crate that planted a violation of the pin's
/// gen-key/subject invariant, and it is why that invariant is now enforced at the
/// mint site rather than assumed.
///
/// HISTORICAL SCOPE (2026-08-29, superseded 2026-08-30): under the pre-widening
/// gen-sets the establish-rebind landed on a BARE subject, the shape reached
/// `self_referential_definition` as a bare recurrence, and it degraded before
/// the pin ran. The write-visibility widening gives the base a real token at
/// the rebind point, so the gen-key refusal in `version_block_def_at_establish`
/// is fixture-isolated again — see the test below.
fn split_subject_escape() -> VerifiableFunction {
    let u32_local = |index: usize, name: &str| LocalDecl {
        index,
        ty: Ty::u32(),
        name: Some(name.into()),
    };
    VerifiableFunction {
        name: "split_subject_escape".into(),
        def_path: "tie_guard::split_subject_escape".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::u32(),
            locals: vec![
                u32_local(0, "__ret"),
                u32_local(1, "n"),
                u32_local(2, "c"),
                u32_local(3, "out"),
                // Literally named with a '#'. NOT `n#e` — the COLLISION check
                // refuses only that exact spelling.
                u32_local(4, "n#x"),
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![],
                    terminator: Terminator::SwitchInt {
                        discr: Operand::Copy(Place::local(2)),
                        targets: vec![(0, BlockId(1))],
                        otherwise: BlockId(2),
                        exhaustive_enum_unreachable: false,
                        span: SourceSpan::default(),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    stmts: vec![
                        Statement::Assign {
                            place: Place::local(4),
                            rvalue: Rvalue::BinaryOp(
                                BinOp::Div,
                                Operand::Copy(Place::local(1)),
                                Operand::Constant(ConstValue::Uint(3, 32)),
                            ),
                            span: SourceSpan::default(),
                        },
                        Statement::Assign {
                            place: Place::local(1),
                            rvalue: Rvalue::CopyForDeref(Place::local(2)),
                            span: SourceSpan::default(),
                        },
                    ],
                    terminator: Terminator::Goto(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    stmts: vec![Statement::Assign {
                        place: Place::local(1),
                        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Goto(BlockId(4)),
                },
                BasicBlock {
                    id: BlockId(3),
                    stmts: vec![Statement::Assign {
                        place: Place::local(3),
                        rvalue: Rvalue::BinaryOp(
                            BinOp::Div,
                            Operand::Constant(ConstValue::Uint(100, 32)),
                            Operand::Copy(Place::local(1)),
                        ),
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Return,
                },
                BasicBlock { id: BlockId(4), stmts: vec![], terminator: Terminator::Return },
            ],
            arg_count: 2,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// The split-subject shape — re-derived 2026-08-30 (dropped-def
/// write-visibility fix), and the gen-key guard is FIXTURE-ISOLATED again.
///
/// History: with the pre-widening gen-sets, `version_block_def_at_establish`
/// rebound this def's subject to BARE (`n`'s token at k+1 was `None`), the bare
/// recurrence `Eq(n, Div(n, 3))` shipped, and `self_referential_definition`
/// DEGRADED the function — the guard was unobservable here (re-derivation of
/// 2026-08-29). The widening gives `n` a real token at k+1 (`s1_1`, the
/// `CopyForDeref` write the extractor declines a def for), so the rebind would
/// now ship the FALSE hypothesis `Eq(n#s1_1, Div(n, 3))` — `n#s1_1` is
/// actually `CopyForDeref(c)` — and the gen-key refusal in
/// `version_block_def_at_establish` (raw lhs `n#x` ≠ recovered subject `n`) is
/// the ONLY thing standing between the extractor's '#'-splitting subject
/// recovery and that false hypothesis.
///
/// PLANTED AND WATCHED (2026-08-30): delete that refusal and the
/// no-false-rebind assertion below goes red with `Eq(n#s1_1, Div(n, 3))`
/// shipped.
#[test]
fn no_pin_when_the_defs_gen_key_is_not_its_subject() {
    let f = split_subject_escape();
    trust_vcgen::validate_function(&f).expect("the fixture must be VALID TrustIR");
    let vcs = trust_vcgen::generate_vcs(&f);
    // The route changed (2026-08-30): the def ships under its OWN gen-key
    // `n#x` (refusal fired, no rebind), the recurrence never forms, and the
    // shape emits a NORMAL DivisionByZero row instead of degrading.
    assert!(
        vcs.iter().any(|vc| matches!(vc.kind, VcKind::DivisionByZero)),
        "the split-subject shape must still raise its DivisionByZero row; \
         kinds: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    // THE GUARD, watched: no def may be rebound onto the base local's token —
    // `n#s1_1` denotes the `CopyForDeref(c)` value, not `n / 3`.
    let false_rebind = vcs.iter().any(|vc| {
        let mut found = false;
        vc.formula.visit(&mut |sub| {
            if let Formula::Eq(l, r) = sub
                && l.var_name() == Some("n#s1_1")
                && matches!(r.as_ref(), Formula::Div(..))
            {
                found = true;
            }
        });
        found
    });
    assert!(
        !false_rebind,
        "the establish-rebind fired on a def whose gen-key (`n#x`) is not its \
         recovered subject (`n`): `Eq(n#s1_1, Div(..))` is a false hypothesis \
         (`n#s1_1` is the CopyForDeref value)"
    );
    assert!(
        entry_sentinel_spellings(&vcs).is_empty(),
        "no `#e` may ship from a def whose gen-key is not its subject: {:?}",
        entry_sentinel_spellings(&vcs)
    );
    assert!(ties(&vcs).is_empty(), "{:?}", ties(&vcs));
    // The row stays refutable through the production router (`c = 0` makes the
    // divisor `CopyForDeref(c) = 0`).
    let rows = verdicts_of_kind(&f, |k| matches!(k, VcKind::DivisionByZero));
    assert!(!rows.is_empty());
    for r in &rows {
        assert!(
            matches!(r, VerificationResult::Failed { .. }),
            "the split-subject division must stay refutable: {r:?}"
        );
    }
}

/// THE MINT GATE's measured false-proof shape (see [`mixed_unwind_mint`]),
/// re-derived 2026-08-30 (dropped-def write-visibility fix).
///
/// The unwind-inclusive entry map now versions bb3's read to the MIXED join
/// `n#e_s1_0` — a partially-entry spelling `entry_sentinel_ties` refuses by
/// exact-token match — so the read never renders bare, the pin's stamp never
/// fires, and neither `#e` nor a `#pre` fallback appears. The severance the
/// gate provided on this shape now happens one map earlier, by construction
/// (the v2 and full-graph maps share one predecessor relation).
#[test]
fn no_entry_sentinel_when_an_unwind_path_can_deliver_a_write() {
    let f = mixed_unwind_mint();
    trust_vcgen::validate_function(&f).expect("the fixture must be VALID TrustIR");
    let vcs = trust_vcgen::generate_vcs(&f);
    assert!(
        entry_sentinel_spellings(&vcs).is_empty(),
        "bb3's unwind-inclusive reaching union is {{e, s1_0}}, not {{e}} — an `#e` \
         minted there does not denote the entry value: {:?}",
        entry_sentinel_spellings(&vcs)
    );
    assert!(ties(&vcs).is_empty(), "{:?}", ties(&vcs));
    // Not to silence, and not to the bare def: the post-write read must ship
    // under the mixed-join spelling the unwind-inclusive map mints for it.
    assert!(
        vcs.iter().any(|vc| {
            vc.formula.free_variables().iter().any(|v| v == "n#e_s1_0")
        }),
        "bb3's read of `n` must carry the mixed-join spelling `n#e_s1_0` \
         (partially entry, partially bb1's write) — bare would re-admit the \
         cross-path unification, `#e` would assert entry-hood falsely"
    );
    assert!(
        recurrences(&vcs).is_empty(),
        "the versioned read must keep the def split: {:?}",
        recurrences(&vcs)
    );
    // RE-DERIVED PIN (was `Proved`, the recorded known cost of 2026-08-29):
    // the semantic-guard-lane bare-read sibling shared the v2 map's unwind
    // blindness, and its bare `n` carried the entry-only `4 <= n < 30` onto
    // the post-write read. The unwind-inclusive map closed that adjacent hole:
    // the row now REFUTES with the real runtime trace (c = 0 takes bb1,
    // `n := 3`, the drop panics into bb3, `3 - 3 = 0`, bb5 divides `100 / 0`).
    let rows = verdicts_of_kind(&f, |k| matches!(k, VcKind::DivisionByZero));
    assert!(!rows.is_empty(), "bb5's `100 / n` must raise an obligation");
    for r in &rows {
        assert!(
            matches!(r, VerificationResult::Failed { .. }),
            "the unwind path delivers `n = 0` into bb5's division; anything but \
             `Failed` means an entry-only hypothesis reached the post-write \
             read again: {r:?}"
        );
    }
}

/// The cleanup-block mint shape (see [`cleanup_mint`]), re-derived 2026-08-30
/// (dropped-def write-visibility fix): the refusal must cost a HYPOTHESIS,
/// never the verdict.
///
/// The unwind-inclusive entry map versions bb2's read to bb0's write token
/// `n#s0_0` — connected to the ACTUAL `n = 0` write across the cleanup edge,
/// strictly stronger than the historical `n#pre_s2_0` havoc (which named the
/// pre-write value and nothing else). No `#e`, no tie, no recurrence, and the
/// row's correct `Failed` survives with the real unwind counterexample.
#[test]
fn a_cleanup_block_mint_is_stamped_pre_not_entry() {
    let f = cleanup_mint();
    trust_vcgen::validate_function(&f).expect("the fixture must be VALID TrustIR");
    let vcs = trust_vcgen::generate_vcs(&f);
    assert!(
        entry_sentinel_spellings(&vcs).is_empty(),
        "bb2 is reached only across an unwind edge downstream of `n = 0`; its \
         pre-write read is NOT the entry value: {:?}",
        entry_sentinel_spellings(&vcs)
    );
    assert!(
        vcs.iter().any(|vc| {
            vc.formula.free_variables().iter().any(|v| v == "n#s0_0")
        }),
        "bb2's pre-update read must carry bb0's write token `n#s0_0` across the \
         cleanup edge — bare would re-admit the entry unification, and the \
         historical `n#pre_s2_0` havoc would leave the write disconnected"
    );
    assert!(ties(&vcs).is_empty(), "{:?}", ties(&vcs));
    assert!(
        recurrences(&vcs).is_empty(),
        "the versioned read must keep the def split — a bare fallback re-mints \
         the recurrence: {:?}",
        recurrences(&vcs)
    );
    let rows = verdicts_of_kind(&f, |k| matches!(k, VcKind::DivisionByZero));
    assert!(!rows.is_empty(), "bb3's `100 / n` must raise an obligation");
    for r in &rows {
        assert!(
            matches!(r, VerificationResult::Failed { .. }),
            "the real unwind path is `n := 0`, panic, `0 / 3 = 0`, `100 / 0` — \
             anything but `Failed` means a hypothesis reached the mint's read \
             that no execution justifies: {r:?}"
        );
    }
}

/// The `#pre` COLLISION refusal (see [`pre_token_colliding_local`]).
///
/// PLANTED AND WATCHED (2026-08-29): delete the `minted_symbol` collision check
/// in `pin_in_place_update_reads` and the first assertion failed — the pin
/// stamped `n#pre_s2_0`, which here is a REAL local, aliasing the two.
///
/// SCOPE NOTE (2026-08-30, dropped-def write-visibility fix): the
/// unwind-inclusive entry map versions this fixture's read (`n#s0_0`), so the
/// `#pre` fallback no longer fires here and the collision refusal is not
/// currently fixture-isolated — the fallback's remaining triggers are the
/// step-cap and unreachable-block corners. The refusal is KEPT (dropping a
/// refusal is never the safer direction); this test still pins that no such
/// aliasing spelling ships and that the obligation survives.
#[test]
fn no_pin_onto_a_local_that_is_literally_named_with_the_pre_token() {
    let f = pre_token_colliding_local();
    let vcs = trust_vcgen::generate_vcs(&f);
    assert!(
        !vcs.iter().any(|vc| {
            vc.formula.free_variables().iter().any(|v| v == "n#pre_s2_0")
        }),
        "`n#pre_s2_0` here is a REAL local, not the pin's fallback token; \
         stamping it aliases an unrelated place"
    );
    assert!(ties(&vcs).is_empty(), "{:?}", ties(&vcs));
    assert!(
        vcs.iter().any(|vc| matches!(
            vc.kind,
            VcKind::DivisionByZero | VcKind::UnsupportedMir { .. }
        )),
        "the refusal must cost a hypothesis, never the obligation; got {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
}

/// RE-DERIVED 2026-08-30 (dropped-def write-visibility fix) from
/// `no_tie_at_a_consumer_reached_only_across_an_unwind_edge`, whose premise —
/// "a cleanup consumer has an EMPTY entry-version map, so bare there is the
/// POST-write subject" — was retired with the unwind-blind map itself.
///
/// The new adjudication, each half measured:
///  * bb2 versions the pinned def's subject to `n#s0_0`, so the tie's bare
///    side meets ONLY the `Fact::entry` bucket, where bare means entry — the
///    tie `Eq(n#e, n)` is the TRUE identity `entry == entry` and may ship.
///  * The stale establish-stamped sibling (`n#s0_0 == n / 3`, bare read)
///    re-stamps at bb2 into the recurrence `n#s0_0 == n#s0_0 / 3` — a FALSE
///    hypothesis — and the `self_referential_definition` scanner catches it
///    and DEGRADES that row (fail-closed, `Unknown`), instead of shipping it.
///  * The DivisionByZero obligation survives and stays refutable — no
///    hypothesis reaches the cleanup read that masks it.
#[test]
fn the_tie_at_a_cleanup_consumer_is_sound_and_the_stale_sibling_degrades() {
    let f = cleanup_consumer();
    trust_vcgen::validate_function(&f).expect("the fixture must be VALID TrustIR");
    let vcs = trust_vcgen::generate_vcs(&f);
    // Any tie that ships must be the exact sound spelling `Eq(n#e, n)` — the
    // identity between two entry-denoting spellings — never anything else.
    for tie in ties(&vcs) {
        assert!(
            tie.contains("n#e"),
            "only the entry identity may ship as a tie here: {tie}"
        );
    }
    // No recurrence may SHIP: the stale sibling's recurrence is degraded, not
    // conjoined (the degraded row's formula carries no variables).
    let split = recurrences(&vcs);
    assert!(
        split.is_empty(),
        "an in-place update reaching a cleanup block must not ship a recurrence:\n  {}",
        split.join("\n  ")
    );
    // The fail-closed route, watched: the stale sibling is DEGRADED by the
    // recurrence scanner rather than silently dropped or shipped.
    assert!(
        vcs.iter().any(|vc| matches!(
            &vc.kind,
            VcKind::UnsupportedMir { kind, .. } if kind == "SelfReferentialDefinition"
        )),
        "the stale establish-stamped sibling must degrade fail-closed; kinds: {:?}",
        vcs.iter().map(|vc| &vc.kind).collect::<Vec<_>>()
    );
    // Laundering control: the cleanup division's obligation survives and no
    // hypothesis (tie included) masks it.
    let rows = verdicts_of_kind(&f, |k| matches!(k, VcKind::DivisionByZero));
    assert!(!rows.is_empty(), "bb2's `100 / n` must raise an obligation");
    for r in &rows {
        // Every real trace into bb2 has `n#s0_0 >= 10` (the assert FAILED),
        // but the cleanup lane does not carry the assert-failed guard, so
        // nothing the pipeline currently conjoins justifies a discharge —
        // `Proved` here could only come from a stale hypothesis. If the lane
        // ever learns the failed-assert guard, re-derive this pin.
        assert!(
            !matches!(r, VerificationResult::Proved { .. }),
            "no conjoined hypothesis justifies discharging the cleanup division: {r:?}"
        );
    }
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

/// THE TIED POPULATION, anchored. (Re-derived 2026-08-29: this was
/// `mint_side_subsumes_consumer_side`, a reachability driver for the
/// "mint-side ⟹ consumer-side" `debug_assert!`; that assert was deleted with
/// the whole-function quantifier, so the implication it watched no longer
/// exists. What remains load-bearing is the POPULATION: exactly which bodies
/// carry a tie.)
///
/// The narrowing's whole measurable payoff is the two String-bearing fixtures
/// joining this list — the old quantifier let one droppable local's cleanup
/// cluster veto the tie function-wide. If either drops OUT again, the gate has
/// regressed toward the quantifier; if a GUARD fixture joins (they are chained
/// in on purpose), a refusal has silently stopped firing.
#[test]
fn the_tied_population_is_exactly_the_gate_admitted_corpus() {
    let mut tied: Vec<String> = Vec::new();
    for (label, func) in corpus().into_iter().chain([
        ("cleanup_consumer".to_string(), cleanup_consumer()),
        ("colliding_local".to_string(), colliding_local()),
        ("split_subject_escape".to_string(), split_subject_escape()),
        ("mixed_unwind_mint".to_string(), mixed_unwind_mint()),
        ("cleanup_mint".to_string(), cleanup_mint()),
        ("pre_token_colliding_local".to_string(), pre_token_colliding_local()),
    ]) {
        if !ties(&trust_vcgen::generate_vcs(&func)).is_empty() {
            tied.push(label);
        }
    }

    tied.sort();
    // Re-anchored 2026-08-30 (dropped-def write-visibility fix):
    // `cleanup_consumer` JOINED the tied population. Derivation: its cleanup
    // consumer now versions the pinned def's subject (`n#s0_0`, unwind-
    // inclusive entry map), so the consumer-side clause of
    // `entry_sentinel_tie_is_sound` legitimately ADMITS — the tie is the true
    // identity `entry == entry` there (see
    // `the_tie_at_a_cleanup_consumer_is_sound_and_the_stale_sibling_degrades`,
    // which also pins that the row stays unmasked). No guard fixture joined;
    // no admission dropped out.
    assert_eq!(
        tied,
        vec![
            "cleanup_consumer",
            "entry_block_in_place_update",
            "entry_sentinel_precondition_gap",
            "entry_sentinel_unranged_overflow",
            "entry_sentinel_unranged_overflow_tied_control",
            "join_weakened_entry_sentinel",
        ],
        "the tie population moved; re-derive which admissions/refusals changed \
         before re-anchoring this list"
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
