//! REGRESSION PINS for the `_0`-preservation rule that gates
//! [`super::witness_grounding`]'s return-producer walk, plus the corpus
//! instrument that measured what the rule costs.
//!
//! WHAT WAS WRONG. `block_preserves_return_place`'s STATEMENT loop is an
//! allow-list with `_ => return false`, and its doc says why: "a wrong `true`
//! would let a STALE `_0` definition be attributed to a return path, so the
//! asymmetry is deliberate." Its TERMINATOR test was the opposite — a
//! two-entry DENY-LIST naming only `Call { dest: _0 }` and `Drop { place: _0 }`,
//! with everything else answering `true`.
//!
//! `Terminator::Opaque { kind, targets, span }` (trust-types/src/model.rs) has
//! NO destination field, because `opaque_terminator(kind, targets, span)`
//! (trust-mir-extract/src/convert.rs:1976) takes none: every call site DISCARDS
//! the MIR terminator's destination place and keeps only the successors. So a
//! block whose entire effect is `_0 = <indirect>()` (convert.rs:1704),
//! `_0 = <atomic>()` with unparseable metadata (convert.rs:1752), or an
//! `InlineAsm` `out(reg) _0` / coroutine `Yield` (the `_ =>` arm,
//! convert.rs:1943) read as `_0`-PRESERVING, and the walk stepped past it to
//! attribute an earlier, stale `_0` definition to the return path.
//! `Terminator::TailCall` was the same hole by a different route: its
//! destination IS the return place, implicitly (convert.rs:1838), so it has no
//! `dest` field for a deny-list to name.
//!
//! A second, independent hole sat in the walk's ORDER. The loop pushed the sole
//! predecessor onto the chain and only then made it `current`, so the block
//! that HOLDS the definition — the one whose `_0` statement stops the walk on
//! the next iteration — never reached the terminator test at all. That admitted
//! `bb = { _0 = Ok(5); Call { dest: _0, target: .. } }`: an ordinary modelled
//! call, the exact shape the deny-list already named, missed purely by
//! position, with NO `Opaque` anywhere and therefore no `UnsupportedMir` row to
//! backstop it.
//!
//! A THIRD hole sat one level up, in the resolver's search ORDER. The window
//! `[vc_block, block]` + ancestors is one linear path, but it was read
//! EARLIEST-first and the first hit won — statement order included — so a DEAD
//! store beat the live definition below it. That one was LIVE end to end: three
//! lines of ordinary Rust (`let mut r = Some(5); r = g(); r`) verified
//! `2 proved, 0 failed, 0 unknown`, exit 0, against a postcondition the
//! compiled program violates whenever `g()` returns `None`.
//!
//! And a FOURTH in the gate that consumes it: `enum_return_grounded_model_vars`
//! walks `Terminator::Return` blocks only, while the pin loop it feeds pins over
//! `Return | TailCall`, so a body whose exit the gate never saw was credited
//! having inspected nothing at all.
//!
//! WHAT IS PINNED HERE. Every fixture below was written by the adversarial
//! prober as a DEMONSTRATION — each one used to pass while asserting that the
//! compiler grounded a return witness on a value the function did not return.
//! They are inverted here into refusals: the resolver must find nothing, the
//! gate must credit nothing, no refutable body-aware `Postcondition` VC may be
//! emitted, and the honest fail-closed `SpecModelUngrounded` row must appear.
//! The POSITIVE twins alongside them pin the walk's reason for existing — the
//! drop-elaboration join it was built to look past still resolves.

use trust_types::{
    AggregateKind, BasicBlock, BlockId, ConstValue, Contract, ContractKind, LocalDecl, Operand,
    Place, Rvalue, SourceSpan, Statement, Terminator, Ty, VariantDef, VcKind, VerifiableBody,
    VerifiableFunction, VerificationCondition,
};

use super::{
    enum_return_grounded_model_vars, generate_v2_contract_vcs_impl,
    resolve_enum_return_aggregate_with_block,
};

// ---------------------------------------------------------------------------
// fixtures — the prober's shapes, unchanged
// ---------------------------------------------------------------------------

fn i64_ty() -> Ty {
    Ty::Int { width: 64, signed: true }
}

/// `core::result::Result<i64, i64>` in the flattened lowering shape used by
/// `result_return_grounding_tests` (machine tags: Ok = 0, Err = 1).
fn std_result_ty() -> Ty {
    Ty::Adt {
        arbitrary_precision: None,
        adt_kind: None,
        layout: None,
        name: "core::result::Result".into(),
        fields: vec![
            ("__tag".into(), i64_ty()),
            ("__v0_0".into(), i64_ty()),
            ("__v1_0".into(), i64_ty()),
        ],
        variants: vec![
            VariantDef { name: "Ok".into(), discriminant: 0, fields: vec![("0".into(), i64_ty())] },
            VariantDef { name: "Err".into(), discriminant: 1, fields: vec![("0".into(), i64_ty())] },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
}

/// `_0 = Result::<variant>(v)` — the in-body aggregate the resolver looks for.
fn assign_variant(variant: usize, v: i128) -> Statement {
    Statement::Assign {
        place: Place::local(0),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::result::Result".to_string(),
                variant,
                active_field: None,
                args: None,
            },
            vec![Operand::Constant(ConstValue::Int(v))],
        ),
        span: SourceSpan::default(),
    }
}

/// `_dest = inner()` as an ORDINARY modelled call.
fn call_into(dest: usize, target: usize) -> Terminator {
    Terminator::Call {
        func: "test::inner".to_string(),
        args: vec![],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        unwind: Default::default(),
    }
}

/// `_0 = <indirect>()` AFTER extraction: `opaque_terminator` kept the normal
/// successor and threw the destination place away
/// (trust-mir-extract/src/convert.rs:1704 — `func_name == "<indirect>"` with a
/// normal target and no admissible `FnPtr` signature).
fn opaque_indirect_call_into_ret(target: usize) -> Terminator {
    Terminator::Opaque {
        kind: "Call(indirect)".to_string(),
        targets: vec![BlockId(target)],
        span: SourceSpan::default(),
    }
}

/// `_0 = <atomic>()` after the malformed-intrinsic-metadata bail
/// (convert.rs:1752). This is the ONLY dest-discarding `Opaque` lowering that
/// actually occurs in the 37,612-body closed corpus, so it is pinned by name.
fn opaque_atomic_into_ret(target: usize) -> Terminator {
    Terminator::Opaque {
        kind: "Call::core::intrinsics::atomic_load::<usize, SeqCst>::UnsupportedAtomicMetadata(unrecognized suffix)"
            .to_string(),
        targets: vec![BlockId(target)],
        span: SourceSpan::default(),
    }
}

fn bb(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn func_with(blocks: Vec<BasicBlock>, ensures: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "stale_ret".to_string(),
        def_path: "test::stale_ret".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![LocalDecl { index: 0, ty: std_result_ty(), name: None }],
            blocks,
            arg_count: 0,
            return_ty: std_result_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

fn postcondition_vcs(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| matches!(vc.kind, VcKind::Postcondition))
        .collect()
}

fn ungrounded_rows(func: &VerifiableFunction) -> Vec<VerificationCondition> {
    generate_v2_contract_vcs_impl(func, None)
        .into_iter()
        .filter(|vc| {
            matches!(&vc.kind, VcKind::UnsupportedMir { kind, .. }
                if kind == crate::contracts::SPEC_MODEL_UNGROUNDED_KIND)
        })
        .collect()
}

/// The full fail-closed assertion: nothing resolved, nothing credited, no
/// refutable body-aware VC, and the honest `SpecModelUngrounded` Unknown row.
#[track_caller]
fn assert_refused(func: &VerifiableFunction, vc_block: usize, ret_block: usize) {
    let resolved = resolve_enum_return_aggregate_with_block(
        func,
        &func.body.blocks[vc_block],
        &func.body.blocks[ret_block],
    );
    assert!(resolved.is_none(), "a stale `_0` definition was still resolved: {resolved:?}");
    assert!(
        enum_return_grounded_model_vars(func).is_empty(),
        "nothing may be credited when a chain block writes `_0`"
    );
    assert!(postcondition_vcs(func).is_empty(), "no refutable body-aware Postcondition VC");
    assert_eq!(ungrounded_rows(func).len(), 1, "the honest fail-closed Unknown row is emitted");
}

// ===========================================================================
// PIN 1 — an unmodelled terminator on the chain must STOP the walk.
//
//   bb0:  _0 = Result::<variant>(payload)      <-- STALE (a dead store)
//         goto bb1
//   bb1:  <real_write>            -> bb2       <-- the REAL last write of _0
//   bb2:  goto bb3                             <-- vc_block (pred of Return)
//   bb3:  return
// ===========================================================================

fn stale_then_write(variant: usize, payload: i128, real_write: Terminator, ensures: &str)
-> VerifiableFunction {
    func_with(
        vec![
            bb(0, vec![assign_variant(variant, payload)], Terminator::Goto(BlockId(1))),
            bb(1, vec![], real_write),
            bb(2, vec![], Terminator::Goto(BlockId(3))),
            bb(3, vec![], Terminator::Return),
        ],
        ensures,
    )
}

/// The prober's headline fixture, inverted. `bb1` is `r = g()` for an indirect
/// callee: the extractor kept the successor and discarded the destination, so
/// under the old deny-list the walk stepped past it and grounded bb0's dead
/// `Ok(5)`, making `#[ensures(result.is_ok())]` PROVE vacuously for a function
/// that returns whatever `g()` returned.
#[test]
fn an_opaque_indirect_call_stops_the_walk() {
    assert_refused(
        &stale_then_write(0, 5, opaque_indirect_call_into_ret(2), "result.is_ok()"),
        2,
        3,
    );
}

/// The twin that made the old behaviour self-evidently wrong: the SAME body
/// with the dead store flipped to `Err(7)` proved the OPPOSITE postcondition.
/// Two bodies with identical observable behaviour cannot both hold.
#[test]
fn the_contradictory_opaque_twin_is_refused_too() {
    assert_refused(
        &stale_then_write(1, 7, opaque_indirect_call_into_ret(2), "result.is_err()"),
        2,
        3,
    );
}

/// The one dest-discarding `Opaque` lowering that actually occurs in the closed
/// corpus (33 sites, all with a normal successor). Pinned by its own kind
/// string so a future narrowing of the atomic-metadata bail cannot silently
/// re-open the lane.
#[test]
fn an_opaque_atomic_metadata_bail_stops_the_walk() {
    assert_refused(&stale_then_write(0, 5, opaque_atomic_into_ret(2), "result.is_ok()"), 2, 3);
}

/// `TailCall`'s destination is the return place IMPLICITLY, so it has no `dest`
/// field for a deny-list to name. It is unreachable as a chain predecessor
/// today only because `v2_terminator_targets` returns `[]` for it; this pins
/// the PREDICATE rather than that accident.
#[test]
fn a_tail_call_never_counts_as_return_place_preserving() {
    let tail = Terminator::TailCall {
        func: "test::inner".to_string(),
        args: vec![],
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
    };
    assert!(
        !super::terminator_preserves_return_place(&tail),
        "TailCall writes `_0` implicitly (convert.rs:1838)"
    );
}

// ===========================================================================
// PIN 2 — the block that HOLDS the definition has its own terminator checked.
//
//   bb0:  _0 = Ok(5)                     <-- STALE, and the def the resolver used
//         call inner() -> _0, goto bb1   <-- the REAL last write of _0
//   bb1:  goto bb2                       <-- vc_block
//   bb2:  return
//
// No `Opaque`, so `collect_terminator_unsupported` emits nothing and this
// function used to ship a STRICT-GREEN vacuous PROVE with no backstop at all.
// ===========================================================================

fn def_holder_overwrites_its_own_def(variant: usize, payload: i128, ensures: &str)
-> VerifiableFunction {
    func_with(
        vec![
            bb(0, vec![assign_variant(variant, payload)], call_into(0, 1)),
            bb(1, vec![], Terminator::Goto(BlockId(2))),
            bb(2, vec![], Terminator::Return),
        ],
        ensures,
    )
}

#[test]
fn the_chain_tails_own_terminator_is_checked_before_it_is_pushed() {
    assert_refused(&def_holder_overwrites_its_own_def(0, 5, "result.is_ok()"), 1, 2);
}

/// The prober's control for PIN 2, kept as a pin of its own: the SAME two
/// shapes one position apart already refused, because the `Call { dest: _0 }`
/// block was an intermediate hop and so did reach the terminator test. Both
/// positions must now agree.
#[test]
fn the_same_shape_one_block_earlier_is_refused_identically() {
    let func = func_with(
        vec![
            bb(0, vec![assign_variant(0, 5)], Terminator::Goto(BlockId(1))),
            bb(1, vec![], call_into(0, 2)),
            bb(2, vec![], Terminator::Goto(BlockId(3))),
            bb(3, vec![], Terminator::Return),
        ],
        "result.is_ok()",
    );
    assert_refused(&func, 2, 3);
}

/// And the `Opaque` spelling of PIN 2: the def and the unmodelled write share
/// one block, so the walk must refuse to push it even though its statements
/// look like the definition the resolver wants.
#[test]
fn a_chain_tail_that_ends_in_an_opaque_write_is_refused() {
    let func = func_with(
        vec![
            bb(0, vec![assign_variant(0, 5)], opaque_indirect_call_into_ret(1)),
            bb(1, vec![], Terminator::Goto(BlockId(2))),
            bb(2, vec![], Terminator::Return),
        ],
        "result.is_ok()",
    );
    assert_refused(&func, 1, 2);
}

// ===========================================================================
// POSITIVE TWINS — the walk still does the job it exists for.
// ===========================================================================

/// THE REASON THE WALK EXISTS. Drop elaboration splices a join block between
/// the block that builds the returned value and the `Return`, so the return
/// path's predecessor assigns nothing. The spliced blocks carry only `Drop`s of
/// OTHER locals and `StorageDead` markers — none of which touch `_0` — and the
/// walk must still step past all of them.
///
///   bb0:  _0 = Ok(5)
///         drop(_7)         -> bb1        <-- drop elaboration, not `_0`
///   bb1:  StorageDead(_7)
///         drop(_8)         -> bb2        <-- another spliced join
///   bb2:  StorageDead(_8)
///         goto bb3                       <-- vc_block: assigns nothing
///   bb3:  return
#[test]
fn the_walk_still_steps_past_a_genuine_drop_elaboration_join() {
    let drop_of = |local: usize, target: usize| Terminator::Drop {
        place: Place::local(local),
        target: BlockId(target),
        span: SourceSpan::default(),
        unwind: Default::default(),
    };
    let func = func_with(
        vec![
            bb(0, vec![assign_variant(0, 5)], drop_of(7, 1)),
            bb(1, vec![Statement::StorageDead(7)], drop_of(8, 2)),
            bb(2, vec![Statement::StorageDead(8)], Terminator::Goto(BlockId(3))),
            bb(3, vec![], Terminator::Return),
        ],
        "result.is_ok()",
    );
    let (kind, variant, _ops, def_block) = resolve_enum_return_aggregate_with_block(
        &func,
        &func.body.blocks[2],
        &func.body.blocks[3],
    )
    .expect("the drop-elaboration join must still resolve — this is why the walk exists");
    assert_eq!(def_block, BlockId(0), "the aggregate is found two joins back");
    assert_eq!(variant, 0);
    assert_eq!(format!("{kind:?}"), "Result");
    let grounded = enum_return_grounded_model_vars(&func);
    assert!(grounded.contains("_0__discr") && grounded.contains("_0__value"), "{grounded:?}");
    assert_eq!(postcondition_vcs(&func).len(), 1, "one refutable body-aware Postcondition VC");
    assert!(ungrounded_rows(&func).is_empty(), "no fail-closed row: the witness IS grounded");
}

/// A chain block may still end in a `Call` or a `Drop` — the stricter rule
/// narrows ONLY the place they name. `_9 = inner()` and `drop(_9)` on the way
/// to the return leave `_0` alone, so the aggregate two blocks back is still
/// reached.
#[test]
fn calls_and_drops_that_do_not_name_the_return_slot_still_pass() {
    let func = func_with(
        vec![
            bb(0, vec![assign_variant(0, 5)], call_into(9, 1)),
            bb(
                1,
                vec![],
                Terminator::Drop {
                    place: Place::local(9),
                    target: BlockId(2),
                    span: SourceSpan::default(),
                    unwind: Default::default(),
                },
            ),
            bb(2, vec![], Terminator::Goto(BlockId(3))),
            bb(3, vec![], Terminator::Return),
        ],
        "result.is_ok()",
    );
    let (_k, _v, _ops, def_block) = resolve_enum_return_aggregate_with_block(
        &func,
        &func.body.blocks[2],
        &func.body.blocks[3],
    )
    .expect("a call/drop naming another local must not stop the walk");
    assert_eq!(def_block, BlockId(0));
    assert!(!enum_return_grounded_model_vars(&func).is_empty());
}

/// `SwitchInt` and `Assert` write nothing, and both are common on a return
/// path. They stay admitted by NAME here, so a future refactor of the
/// allow-list that drops them is caught by a test rather than by a coverage
/// regression nobody attributes.
#[test]
fn the_no_value_write_terminators_are_all_still_admitted() {
    for term in [
        Terminator::Goto(BlockId(1)),
        Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(3)),
            targets: vec![(0, BlockId(1))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
        Terminator::Return,
        Terminator::Unreachable,
        Terminator::Resume,
        Terminator::Assert {
            cond: Operand::Copy(Place::local(3)),
            expected: true,
            msg: trust_types::AssertMessage::Custom("x".into()),
            target: BlockId(1),
            span: SourceSpan::default(),
            unwind: Default::default(),
        },
    ] {
        assert!(
            super::terminator_preserves_return_place(&term),
            "{term:?} writes no value and must stay admitted"
        );
    }
    // ...and the fail-closed default really is closed.
    assert!(!super::terminator_preserves_return_place(
        &opaque_indirect_call_into_ret(1)
    ));
    assert!(!super::terminator_preserves_return_place(&call_into(0, 1)));
    assert!(super::terminator_preserves_return_place(&call_into(9, 1)));
}

// ===========================================================================
// THE COST INSTRUMENT
// ===========================================================================

/// A/B the return-value grounding gate over a `-Ztrust-dump=mir` corpus.
///
/// Prints one line per body that grounds anything or resolves any return path,
/// so two runs — one on this commit, one with `witness_grounding.rs` reverted —
/// diff to the exact set of bodies and witnesses the stricter rule refuses that
/// the deny-list previously granted.
///
/// `#[ignore]`d because it needs a corpus.
///
/// ```text
/// TRUST_RETURN_WALK_CORPUS=~/trust-corpora/mir-closed-mono \
///   targo --unverified test -p trust-vcgen --lib \
///   return_walk_grounding_corpus_ab -- --ignored --nocapture
/// ```
///
/// MEASURED 2026-09-01, dependency-closed corpus `~/trust-corpora/
/// mir-closed-mono`, 37,612 bodies, 16 s per run. Pre-fix baseline: 5,469
/// credited body-rows / 2,269 grounded bodies / 9,390 resolved return paths.
/// After all four fixes: 5,438 / 2,238 / 9,390 — 31 rows lost, 0 gained.
///
/// The three fixes to the walk and the resolver — the terminator ALLOW-LIST,
/// the chain-tail pre-push check, and the latest-first search order — cost
/// EXACTLY ZERO: byte-identical output, every row and every resolved path.
/// All 31 lost rows come from the gate's ungateable-exit guard, and they are
/// 16 distinct contract-free DIVERGING bodies (`csv::serializer` / `serde`
/// shims and `<Infallible as Debug>::fmt`) with **no `Return` block at all** —
/// 30 `Call` terminators and one `Unreachable` between them. Their credit named
/// model variables for a return that cannot happen, and the pin loop, which
/// iterates the same exits, emitted no VC for them either.
///
/// CEILING, stated plainly: NO body in this corpus carries a contract (it is
/// third-party code harvested under `-Ztrust-policy=advisory`), so this
/// measures the GATE'S DECISION SURFACE — which runs regardless of contracts —
/// and not obligation counts. A contracted body of the lost shape would move
/// from a SILENTLY DROPPED postcondition (credited, admitted to the pin loop,
/// then no VC because there is no exit block to pin over) to an honest
/// fail-closed `SpecModelUngrounded` Unknown.
///
/// CONTROLS, so the +0 is not a dead experiment (same command, one edit each):
/// making `return_producer_ancestors` return an empty chain moves 153 rows;
/// making the terminator allow-list reject `Call`/`Drop` moves 141; making the
/// PRE-PUSH position alone reject a `Drop` candidate moves 115. All three
/// pieces of the changed code are exercised by this corpus.
#[test]
#[ignore = "needs a -Ztrust-dump=mir corpus; set TRUST_RETURN_WALK_CORPUS"]
fn return_walk_grounding_corpus_ab() {
    let root = std::env::var("TRUST_RETURN_WALK_CORPUS")
        .expect("set TRUST_RETURN_WALK_CORPUS to a directory of -Ztrust-dump=mir output");
    let mut files = Vec::new();
    collect_json(std::path::Path::new(&root), &mut files);
    files.sort();
    assert!(!files.is_empty(), "no MIR dumps under {root}");

    let n_threads = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4);
    let chunks: Vec<&[std::path::PathBuf]> = files.chunks(files.len().div_ceil(n_threads)).collect();
    let out: Vec<(usize, usize, usize, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> =
            chunks.into_iter().map(|chunk| scope.spawn(move || scan(chunk))).collect();
        handles.into_iter().map(|h| h.join().expect("scan thread")).collect()
    });

    let (mut bodies, mut grounded_bodies, mut resolved_paths) = (0usize, 0usize, 0usize);
    let mut lines = Vec::new();
    for (b, g, r, mut l) in out {
        bodies += b;
        grounded_bodies += g;
        resolved_paths += r;
        lines.append(&mut l);
    }
    lines.sort();
    for line in &lines {
        println!("{line}");
    }
    println!(
        "[return-walk-ab] files={} bodies={bodies} grounded_bodies={grounded_bodies} resolved_return_paths={resolved_paths}",
        files.len()
    );
}

fn scan(files: &[std::path::PathBuf]) -> (usize, usize, usize, Vec<String>) {
    let (mut bodies, mut grounded, mut resolved) = (0usize, 0usize, 0usize);
    let mut lines = Vec::new();
    for path in files {
        let Ok(text) = std::fs::read_to_string(path) else { continue };
        let Ok(func) = serde_json::from_str::<VerifiableFunction>(&text) else { continue };
        bodies += 1;
        let mut credited: Vec<String> = enum_return_grounded_model_vars(&func).into_iter().collect();
        credited.sort();
        let mut paths = Vec::new();
        for block in &func.body.blocks {
            if !matches!(block.terminator, Terminator::Return) {
                continue;
            }
            let preds: Vec<&BasicBlock> = func
                .body
                .blocks
                .iter()
                .filter(|p| super::v2_terminator_targets(&p.terminator).contains(&block.id))
                .collect();
            let vc_blocks: Vec<&BasicBlock> = if preds.is_empty() { vec![block] } else { preds };
            for vc_block in vc_blocks {
                if let Some((kind, variant, ops, def_block)) =
                    resolve_enum_return_aggregate_with_block(&func, vc_block, block)
                {
                    resolved += 1;
                    paths.push(format!(
                        "bb{}->bb{}={kind:?}/v{variant}/ops{}@bb{}",
                        vc_block.id.0,
                        block.id.0,
                        ops.len(),
                        def_block.0
                    ));
                }
            }
        }
        if credited.is_empty() && paths.is_empty() {
            continue;
        }
        if !credited.is_empty() {
            grounded += 1;
        }
        lines.push(format!(
            "{}\tcredited=[{}]\tpaths=[{}]",
            func.def_path,
            credited.join(","),
            paths.join(" ")
        ));
    }
    (bodies, grounded, resolved, lines)
}

fn collect_json(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_json(&path, out);
        } else if path.extension().is_some_and(|e| e == "json") {
            out.push(path);
        }
    }
}

// ===========================================================================
// PIN 3 — the search window is read in PROGRAM ORDER, latest first.
//
// The prober's headline finding, and the one that was LIVE: a dead store in
// the predecessor beat the live definition in the return block, because the
// window was built `[vc_block, block]` (earliest first) and both the block
// scan and the statement scan took the FIRST hit. Reproduced end to end
// through the stage1 driver on three lines of ordinary Rust — see the banner
// on `resolve_enum_return_aggregate_with_block`.
//
//   bb0: _3 = Option::Some(5)                      <-- DEAD; rustc warns
//        _4 = _1()  -> dest _4, target bb1
//   bb1: _3 = move _4                              <-- the LIVE def of _3
//        _0 = move _3
//        return
// ===========================================================================

fn std_option_ty() -> Ty {
    Ty::Adt {
        arbitrary_precision: None,
        adt_kind: None,
        layout: None,
        name: "core::option::Option".into(),
        fields: vec![("__tag".into(), i64_ty()), ("__v1_0".into(), i64_ty())],
        variants: vec![
            VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), i64_ty())],
            },
        ],
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
    }
}

fn assign_option(local: usize, variant: usize, v: i128) -> Statement {
    Statement::Assign {
        place: Place::local(local),
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "core::option::Option".to_string(),
                variant,
                active_field: None,
                args: None,
            },
            if variant == 1 { vec![Operand::Constant(ConstValue::Int(v))] } else { vec![] },
        ),
        span: SourceSpan::default(),
    }
}

fn move_local(dest: usize, src: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Move(Place::local(src))),
        span: SourceSpan::default(),
    }
}

/// The MIR the real compiler emitted for the false-verifying `h`, transcribed
/// one-for-one (the unused closure slot is dropped; nothing reads it).
fn dead_store_then_live_def(dead_variant: usize, ensures: &str) -> VerifiableFunction {
    VerifiableFunction {
        name: "h".to_string(),
        def_path: "probe::h".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: std_option_ty(), name: None },
                LocalDecl { index: 1, ty: i64_ty(), name: None },
                LocalDecl { index: 2, ty: std_option_ty(), name: None },
                LocalDecl { index: 3, ty: std_option_ty(), name: None },
                LocalDecl { index: 4, ty: std_option_ty(), name: None },
            ],
            blocks: vec![
                bb(
                    0,
                    vec![assign_option(3, dead_variant, 5)],
                    Terminator::Call {
                        func: "@trust_indirect_callee".to_string(),
                        args: vec![Operand::Copy(Place::local(1))],
                        dest: Place::local(4),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_foreign: false,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        unwind: Default::default(),
                    },
                ),
                bb(1, vec![move_local(3, 4), move_local(0, 3)], Terminator::Return),
            ],
            arg_count: 1,
            return_ty: std_option_ty(),
            datatype_defs: Default::default(),
        },
        contracts: vec![Contract {
            kind: ContractKind::Ensures,
            span: SourceSpan::default(),
            body: ensures.to_string(),
        }],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

#[test]
fn a_dead_store_in_the_predecessor_never_beats_the_return_blocks_live_def() {
    assert_refused(&dead_store_then_live_def(1, "result.is_some()"), 0, 1);
}

/// The twin that made it undeniable: the SAME body with the dead store flipped
/// to `None` proved `is_none()`. Both must now fail closed.
#[test]
fn the_contradictory_dead_store_twin_is_refused_too() {
    assert_refused(&dead_store_then_live_def(0, "result.is_none()"), 0, 1);
}

/// The same defect at STATEMENT granularity: put both definitions in one block,
/// in program order. The last one is the live one, and it is a call dest with
/// no in-body aggregate, so the resolver must bottom out rather than reach back
/// over it to the dead store above.
#[test]
fn within_one_block_the_last_definition_wins_not_the_first() {
    let mut func = dead_store_then_live_def(1, "result.is_some()");
    let dead = func.body.blocks[0].stmts.remove(0);
    func.body.blocks[1].stmts.insert(0, dead);
    assert_refused(&func, 0, 1);
}

/// POSITIVE TWIN. Program order cuts both ways: a definition in the RETURN
/// block is what reaches `Return`, and it must still be found — this is the
/// ordinary `if c { Some(x) } else { None }` tail, whose aggregate the
/// optimizer parks on a temp in the predecessor and moves into `_0` in the
/// return block.
#[test]
fn a_live_definition_in_the_return_block_still_grounds() {
    let func = VerifiableFunction {
        body: VerifiableBody {
            blocks: vec![
                bb(0, vec![assign_option(3, 1, 5)], Terminator::Goto(BlockId(1))),
                bb(1, vec![move_local(0, 3)], Terminator::Return),
            ],
            ..dead_store_then_live_def(1, "result.is_some()").body
        },
        ..dead_store_then_live_def(1, "result.is_some()")
    };
    let (_k, variant, _ops, def_block) =
        resolve_enum_return_aggregate_with_block(&func, &func.body.blocks[0], &func.body.blocks[1])
            .expect("the single live definition must still resolve");
    assert_eq!(def_block, BlockId(0), "one def, in the predecessor — order cannot change it");
    assert_eq!(variant, 1);
    let grounded = enum_return_grounded_model_vars(&func);
    assert!(grounded.contains("_0__discr") && grounded.contains("_0__value"), "{grounded:?}");
    assert_eq!(postcondition_vcs(&func).len(), 1);
    assert!(ungrounded_rows(&func).is_empty());
}

/// POSITIVE TWIN. Two definitions, and the LATER one is the wrapper aggregate:
/// the resolver must take it (not refuse, and not take the earlier one).
#[test]
fn a_later_aggregate_overrides_an_earlier_one() {
    let func = VerifiableFunction {
        body: VerifiableBody {
            blocks: vec![
                bb(0, vec![assign_option(3, 0, 0)], Terminator::Goto(BlockId(1))),
                bb(1, vec![assign_option(3, 1, 5), move_local(0, 3)], Terminator::Return),
            ],
            ..dead_store_then_live_def(1, "result.is_some()").body
        },
        ..dead_store_then_live_def(1, "result.is_some()")
    };
    let (_k, variant, ops, def_block) =
        resolve_enum_return_aggregate_with_block(&func, &func.body.blocks[0], &func.body.blocks[1])
            .expect("the LAST definition resolves");
    assert_eq!(def_block, BlockId(1), "the return block's `Some(5)`, not bb0's `None`");
    assert_eq!(variant, 1);
    assert_eq!(ops.len(), 1);
}


// ===========================================================================
// PIN 4 — the gate must refuse an exit it cannot inspect.
//
// `enum_return_grounded_model_vars` walks `Terminator::Return` blocks only,
// while the pin loop it feeds (`contract_vcs.rs`) pins over
// `Return | TailCall`. So a body whose exit this gate never sees was credited
// having inspected NOTHING — `n_return_paths == 0` fell straight through to
// `set.insert("_0__discr")`.
// ===========================================================================

fn only_exit(terminator: Terminator) -> VerifiableFunction {
    func_with(vec![bb(0, vec![assign_variant(0, 5)], terminator)], "result.is_ok()")
}

/// A `TailCall`'s destination IS the return place, implicitly
/// (convert.rs:1838), so the `Ok(5)` above it is stale by construction and
/// nothing in the body can ground the returned value. Measured before the
/// guard: BOTH `_0__discr` and `_0__value` were credited and the pin loop
/// emitted a refutable `Postcondition` VC pinned to the stale variant.
#[test]
fn a_tail_call_exit_grounds_nothing() {
    let func = only_exit(Terminator::TailCall {
        func: "test::inner".to_string(),
        args: vec![],
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
    });
    assert!(
        enum_return_grounded_model_vars(&func).is_empty(),
        "a tail-call exit is ungroundable — the callee writes the return place"
    );
    assert!(postcondition_vcs(&func).is_empty(), "no refutable body-aware VC");
    assert_eq!(ungrounded_rows(&func).len(), 1, "the honest fail-closed Unknown row");
}

/// A DIVERGING body — no `Return` block at all. This is the shape the corpus
/// measurement found: 31 credited rows across 16 contract-free `csv`/`serde`
/// shims and `<Infallible as Debug>::fmt`, every one of them ending in a
/// diverging call or `Unreachable`. The credit named model variables for a
/// return that cannot happen.
#[test]
fn a_body_with_no_return_block_grounds_nothing() {
    for exit in [
        Terminator::Unreachable,
        Terminator::Call {
            func: "core::panicking::panic".to_string(),
            args: vec![],
            dest: Place::local(6),
            target: None,
            span: SourceSpan::default(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            unwind: Default::default(),
        },
    ] {
        let func = only_exit(exit);
        assert!(
            enum_return_grounded_model_vars(&func).is_empty(),
            "nothing may be credited when the gate inspected zero return paths"
        );
        assert!(postcondition_vcs(&func).is_empty());
        // The postcondition is no longer SILENTLY DROPPED either: before the
        // guard it was credited, admitted to the pin loop, and then produced no
        // VC at all because the loop found no exit block to pin over.
        assert_eq!(ungrounded_rows(&func).len(), 1, "the honest fail-closed Unknown row");
    }
}

// ===========================================================================
// PIN 5 — the FORWARDED-CALL path-region no-write check asks the EXHAUSTIVE
// per-local classifier, not a two-case deny-list.
//
// `resolve_forwarded_call_return_variant` grounds the return discriminant of a
// path that forwards a callee's `Result`/`Option` WHOLE into `_0`, using the
// dominating `match inner()` switch. Its step (2d) is the whole soundness
// argument for that: `discriminant(call_dest)` at the switch equals its
// discriminant at `Return` IFF nothing in the path region S writes `call_dest`.
//
// That scan used to name exactly two shapes —
//
//     Statement::Assign { place, .. } if place.local == call_dest
//     Terminator::Call  { dest,  .. } if dest.local  == call_dest
//
// — so every OTHER channel by which a local's value changes walked straight
// through the guard: `Statement::SetDiscriminant` (the statement whose entire
// job is to change a discriminant — the very fact under protection),
// `Statement::Deinit`, `Terminator::Drop` (whose glue takes `&mut place`), and
// `Terminator::Opaque`, whose destination place the EXTRACTOR DISCARDS
// (`opaque_terminator(kind, targets, span)`, trust-mir-extract/src/
// convert.rs:1976) so that no scan keyed on a place can rule it out at all.
//
// It now asks `Statement::local_write` / `Terminator::write_effect` — the
// classifiers in `trust-types`, which owns the `#[non_exhaustive]` enums and is
// therefore WILDCARD-FREE over them. A new MIR write channel cannot reach
// "preserving" here without first being classified there, which does not
// compile until someone writes it.
//
// THE GEOMETRY, `match inner() { Ok(..) => .., Err(..) => <forward it> }` after
// the optimizer forwards the callee result whole into `_0`:
//
//   bb0: _1 = inner()                     -> bb1     <-- `call_dest` = _1
//   bb1: _2 = discriminant(_1)
//        switchInt(_2) -> [0: bb2] else bb3          <-- the DOMINATING switch
//   bb2: goto bb5                                    <-- the `Ok` arm
//   bb3: <region stmts> <region terminator>          <-- INSIDE the region S
//   bb4: _0 = move _1                     -> bb5     <-- `fwd_block` = 4
//   bb5: return
//
// The `otherwise` edge is the only one reaching bb4 while avoiding bb1, its
// complement over the decoded tags is the single variant `Err` (index 1), and
// `Err` is the non-payload variant for `Result` — so with bb3 clean the lane
// grounds, and every negative below differs from that baseline by ONE
// perturbation inside S.
// ===========================================================================

/// `_dest = discriminant(_src)` — the switch scrutinee step (2a) looks for.
fn discriminant_of(dest: usize, src: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Discriminant(Place::local(src)),
        span: SourceSpan::default(),
    }
}

/// The local the callee result lands in, and the block that forwards it into
/// `_0` — the two arguments the resolver is called with.
const FWD_CALL_DEST: usize = 1;
const FWD_BLOCK: usize = 4;

/// The geometry above, with `bb3` — a block strictly inside the path region S —
/// carrying whatever perturbation the caller wants to test.
fn forwarded_err_region(
    region_stmts: Vec<Statement>,
    region_term: Terminator,
) -> VerifiableFunction {
    let mut func = func_with(
        vec![
            bb(0, vec![], call_into(1, 1)),
            bb(
                1,
                vec![discriminant_of(2, 1)],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(3),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            bb(2, vec![], Terminator::Goto(BlockId(5))),
            bb(3, region_stmts, region_term),
            bb(4, vec![move_local(0, 1)], Terminator::Goto(BlockId(5))),
            bb(5, vec![], Terminator::Return),
        ],
        "result.is_err()",
    );
    // `func_with` declares only `_0`; this lane also needs the forwarded value
    // and the discriminant temp, and the temp's INT type is what lets
    // `decode_switch_label` read the arm labels (an undecodable label fails the
    // lane closed, which would confound every pin below).
    func.body.locals = vec![
        LocalDecl { index: 0, ty: std_result_ty(), name: None },
        LocalDecl { index: FWD_CALL_DEST, ty: std_result_ty(), name: None },
        LocalDecl { index: 2, ty: i64_ty(), name: None },
    ];
    func
}

/// `drop(_local) -> bb4`, staying inside the region.
fn drop_in_region(local: usize) -> Terminator {
    Terminator::Drop {
        place: Place::local(local),
        target: BlockId(FWD_BLOCK),
        span: SourceSpan::default(),
        unwind: Default::default(),
    }
}

#[track_caller]
fn assert_region_refused(func: &VerifiableFunction, why: &str) {
    let got = super::resolve_forwarded_call_return_variant(func, FWD_CALL_DEST, FWD_BLOCK);
    assert!(got.is_none(), "{why} — but the forwarded variant was still grounded: {got:?}");
}

#[track_caller]
fn assert_region_grounds(func: &VerifiableFunction, why: &str) {
    let got = super::resolve_forwarded_call_return_variant(func, FWD_CALL_DEST, FWD_BLOCK);
    assert_eq!(
        got.map(|(k, v)| (format!("{k:?}"), v)),
        Some(("Result".to_string(), 1)),
        "{why}"
    );
}

/// THE CONTROL, and the reason every negative below is worth having. With `bb3`
/// carrying nothing, the lane grounds `Err` — so a refusal in the tests that
/// follow is attributable to the ONE perturbation each adds, and a hardening
/// that had silently disabled the lane rather than narrowing it would fail HERE.
#[test]
fn a_clean_forwarded_err_region_still_grounds() {
    assert_region_grounds(
        &forwarded_err_region(vec![], Terminator::Goto(BlockId(FWD_BLOCK))),
        "the unperturbed forwarding geometry is what the lane exists to ground",
    );
}

/// THE SHARPEST CASE. The guard protects exactly one fact —
/// "`discriminant(call_dest)` at the switch equals its discriminant at
/// `Return` along this path" — and `SetDiscriminant` is the MIR statement whose
/// entire purpose is to change a discriminant. Under the old two-case scan it
/// was not looked for at all: the region check saw an `Assign`-shaped hole and
/// answered "no write", so the resolver returned the switch edge's `Err` for a
/// value the region had since made `Ok`.
#[test]
fn a_set_discriminant_on_the_forwarded_local_refuses_the_region() {
    let func = forwarded_err_region(
        vec![Statement::SetDiscriminant { place: Place::local(FWD_CALL_DEST), variant_index: 0 }],
        Terminator::Goto(BlockId(FWD_BLOCK)),
    );
    assert_region_refused(
        &func,
        "SetDiscriminant is a discriminant write, and discriminant stability is the \
         whole fact this guard protects",
    );
}

/// `Deinit` makes the place uninitialized: a value change with no `Rvalue` to
/// name, classified `LocalWrite::Partial`. The switch's tag says nothing about
/// what is in `call_dest` afterwards.
#[test]
fn a_deinit_on_the_forwarded_local_refuses_the_region() {
    let func = forwarded_err_region(
        vec![Statement::Deinit { place: Place::local(FWD_CALL_DEST) }],
        Terminator::Goto(BlockId(FWD_BLOCK)),
    );
    assert_region_refused(&func, "Deinit changes the value with nothing to name");
}

/// A custom `Drop::drop` takes `&mut self`, so drop glue on `call_dest` is a
/// write the region check must see. The old scan named `Terminator::Call` only.
#[test]
fn a_drop_of_the_forwarded_local_refuses_the_region() {
    let func =
        forwarded_err_region(vec![], drop_in_region(FWD_CALL_DEST));
    assert_region_refused(&func, "drop glue takes `&mut call_dest`");
}

/// The `Call`-terminator half of the OLD deny-list, kept as a pin so the
/// rewrite onto `terminator_preserves_local` cannot lose the case it already
/// covered.
#[test]
fn a_call_dest_in_the_region_still_refuses() {
    let func = forwarded_err_region(vec![], call_into(FWD_CALL_DEST, FWD_BLOCK));
    assert_region_refused(&func, "a Call whose dest IS `call_dest` overwrites the value");
}

/// The `Assign` half of the OLD deny-list, likewise. `_1 = Ok(0)` in the region
/// was already caught before this hardening, and must still be.
#[test]
fn an_assign_to_the_forwarded_local_still_refuses_the_region() {
    let func = forwarded_err_region(
        vec![Statement::Assign {
            place: Place::local(FWD_CALL_DEST),
            rvalue: Rvalue::Aggregate(
                AggregateKind::Adt {
                    name: "core::result::Result".to_string(),
                    variant: 0,
                    active_field: None,
                    args: None,
                },
                vec![Operand::Constant(ConstValue::Int(0))],
            ),
            span: SourceSpan::default(),
        }],
        Terminator::Goto(BlockId(FWD_BLOCK)),
    );
    assert_region_refused(&func, "a whole-local Assign was the one case the old scan DID name");
}

/// A PROJECTED store is a write too — `_1.0 = 7` perturbs the value the switch
/// tag was read from even though it is not a whole-local definition
/// (`LocalWrite::Partial`). The old scan tested `place.local` and so happened to
/// catch this one; the rewrite must keep it.
#[test]
fn a_projected_store_into_the_forwarded_local_still_refuses_the_region() {
    let func = forwarded_err_region(
        vec![Statement::Assign {
            place: Place {
                local: FWD_CALL_DEST,
                projections: vec![trust_types::Projection::Field(1)],
            },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
            span: SourceSpan::default(),
        }],
        Terminator::Goto(BlockId(FWD_BLOCK)),
    );
    assert_region_refused(&func, "a field store changes the forwarded value");
}

/// THE POSITIVE TWINS, and they are what make the four negatives above worth
/// having: the SAME geometry with the SAME perturbation aimed at a DIFFERENT
/// local must still ground. A hardening that refused these would have disabled
/// the lane rather than narrowed it, and every negative above would then be
/// passing for the wrong reason.
#[test]
fn the_same_perturbations_on_another_local_still_ground() {
    const OTHER: usize = 9;
    for (what, stmts, term) in [
        (
            "SetDiscriminant(_9)",
            vec![Statement::SetDiscriminant { place: Place::local(OTHER), variant_index: 0 }],
            Terminator::Goto(BlockId(FWD_BLOCK)),
        ),
        (
            "Deinit(_9)",
            vec![Statement::Deinit { place: Place::local(OTHER) }],
            Terminator::Goto(BlockId(FWD_BLOCK)),
        ),
        ("drop(_9)", vec![], drop_in_region(OTHER)),
        ("_9 = inner()", vec![], call_into(OTHER, FWD_BLOCK)),
        (
            "_9 = 7",
            vec![Statement::Assign {
                place: Place::local(OTHER),
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            }],
            Terminator::Goto(BlockId(FWD_BLOCK)),
        ),
        (
            "_9.0 = 7",
            vec![Statement::Assign {
                place: Place {
                    local: OTHER,
                    projections: vec![trust_types::Projection::Field(0)],
                },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            }],
            Terminator::Goto(BlockId(FWD_BLOCK)),
        ),
        (
            "StorageDead(_9) — a marker, no value at all",
            vec![Statement::StorageDead(OTHER)],
            Terminator::Goto(BlockId(FWD_BLOCK)),
        ),
    ] {
        assert_region_grounds(
            &forwarded_err_region(stmts, term),
            &format!("{what} does not touch `call_dest` and must not refuse the region"),
        );
    }
}

/// `Terminator::Opaque` in the region. Its destination place is DISCARDED at
/// extraction (convert.rs:1976 takes no destination), so `call_dest` cannot be
/// ruled out and the region must fail closed.
///
/// HONEST SCOPE, because this one pin is NOT load-bearing on its own, and the
/// mutation proof says so: with the region check reverted to the old two-case
/// deny-list, the `SetDiscriminant`/`Deinit`/`Drop` pins above all fail and this
/// one still PASSES. An `Opaque` ANYWHERE in the body makes
/// `Terminator::local_write` answer `Unlocatable` for EVERY local, so
/// `unique_value_def(_2)` — the discriminant temp that step (2a) must resolve to
/// `Rvalue::Discriminant(call_dest)` — goes ambiguous and the lane declines one
/// step EARLIER as well. That confound is structural: it is a fact about the
/// whole body, not about where the `Opaque` sits, so no geometry in this shape
/// can separate the two refusals. Both are the same fail-closed direction. The
/// assertions below EVIDENCE the confound rather than asserting around it, and
/// the check that IS attributable to the hardening is the predicate pin after
/// this one.
#[test]
fn an_opaque_in_the_region_refuses_the_forwarded_grounding() {
    let func = forwarded_err_region(vec![], opaque_indirect_call_into_ret(FWD_BLOCK));
    assert_region_refused(&func, "an Opaque's destination is discarded, so no local is ruled out");
    // The confound, stated as a fact: the SAME geometry with a `Goto` resolves
    // the step-(2a) scrutinee, and the `Opaque` alone destroys it.
    let clean = forwarded_err_region(vec![], Terminator::Goto(BlockId(FWD_BLOCK)));
    assert!(
        matches!(crate::local_defs::unique_value_def(&clean, 2), Some(Rvalue::Discriminant(p))
            if p.local == FWD_CALL_DEST),
        "the clean shape's `_2 = discriminant(_1)` is what step (2a) reads"
    );
    assert!(
        crate::local_defs::unique_value_def(&func, 2).is_none(),
        "an Opaque is `Unlocatable` for EVERY local, so it also refuses at (2a) — \
         this pin cannot be attributed to the region check alone"
    );
}

/// The predicate the region check now asks, pinned directly at a NON-ZERO local
/// — this is what generalizing `terminator_preserves_return_place` onto any
/// local actually bought, and it is the attributable pin for the `Opaque` and
/// `Drop` cases.
#[test]
fn terminator_preserves_local_is_the_allow_list_at_any_local() {
    // Refused for `_1`: the two place-bearing writes that NAME it, plus the
    // dest-discarding `Opaque` that names nothing.
    assert!(!super::terminator_preserves_local(&call_into(1, 4), 1));
    assert!(!super::terminator_preserves_local(&drop_in_region(1), 1));
    assert!(!super::terminator_preserves_local(&opaque_indirect_call_into_ret(4), 1));
    assert!(!super::terminator_preserves_local(&opaque_atomic_into_ret(4), 1));
    // Admitted for `_1`: the same two writes aimed elsewhere, and the
    // no-value-write terminators.
    assert!(super::terminator_preserves_local(&call_into(9, 4), 1));
    assert!(super::terminator_preserves_local(&drop_in_region(9), 1));
    assert!(super::terminator_preserves_local(&Terminator::Goto(BlockId(4)), 1));
    assert!(super::terminator_preserves_local(&Terminator::Return, 1));
    // And the generalization is EXACTLY the old `_0` rule at `local == 0`, so
    // the return-place walk's behaviour cannot have moved with it.
    for term in [
        call_into(0, 4),
        call_into(9, 4),
        drop_in_region(0),
        drop_in_region(9),
        opaque_indirect_call_into_ret(4),
        Terminator::Goto(BlockId(4)),
        Terminator::Return,
        Terminator::Unreachable,
    ] {
        assert_eq!(
            super::terminator_preserves_local(&term, 0),
            super::terminator_preserves_return_place(&term),
            "{term:?}"
        );
    }
}

// ===========================================================================
// PIN 6 — the PRED-CHAIN forward-move hop obeys the terminator, and takes the
// LAST write rather than the first `Assign`.
//
// `resolve_enum_return_aggregate_with_block`'s None branch walks
// single-predecessor blocks up from `fwd_block` looking for THIS path's
// `_local = move/copy _src`, so that the optimizer's `Err(e) => return Err(e)`
// arm — whose assign sits ABOVE the `[block, vc_block]` window, with a bare
// drop-landing between it and the return — can still be resolved.
//
// THAT WALK USED TO READ ONLY `Statement::Assign`, AND ONLY THE FIRST ONE.
// Two holes came out of that, and they are the same stale-value class as the
// `_0` walk's terminator hole (PIN 1/2) and the region check (PIN 5):
//
//  * IT NEVER LOOKED AT THE TERMINATOR. A block whose terminator writes `local`
//    — `Call { dest: local }`, a `Drop` of it, the dest-discarding `Opaque` —
//    was stepped straight through, or hopped INTO, so a definition from further
//    up the chain was attributed to a path whose own exit had overwritten it.
//    The terminator runs AFTER the statements, so it is what decides the value
//    that leaves the block.
//  * IT TOOK THE FIRST `Assign`, NOT THE LAST WRITE. `_3 = move _1;
//    SetDiscriminant(_3, Ok)` handed back the move and hopped, discarding the
//    write that actually reaches the successor — earliest-first, the identical
//    defect PIN 3 fixed one level up in `whole_def`.
//
// Both are now one rule each: `terminator_preserves_local` first, then
// `stmts.iter().rev().find(|s| local_write(local) != Untouched)` and a REQUIREMENT
// that the last write be exactly the whole-local forward-move this hop models —
// a projected store, a `SetDiscriminant`, a `Deinit` or an unlocatable write
// fails closed instead of being hopped over.
//
// THE GEOMETRY — `match inner() { Ok(..) => .., Err(e) => return Err(e) }` with
// a drop-landing block between the Err arm and the return, which is exactly the
// shape the walk was written for:
//
//   bb0: _1 = inner()                  -> bb1
//   bb1: _2 = discriminant(_1)
//        switchInt(_2) -> [0: bb2] else bb3
//   bb2: goto bb6                                 <-- the Ok arm
//   bb3: _3 = move _1     <err-arm term>          <-- HOLDS the forward-move
//   bb4:                  <landing term>          <-- the drop landing, stepped THROUGH
//   bb5: _0 = move _3     goto bb6                <-- vc_block; writes `_0`, so
//                                                     `return_producer_ancestors`
//                                                     stops dead and the window is
//                                                     just [bb6, bb5] — which is
//                                                     what forces the pred-chain
//                                                     walk to be used at all
//   bb6: return                                   <-- block
//
// Clean, this resolves `(Result, Err)` with `def_block == bb3` — and that
// `bb3` IS the evidence the hop ran, since without it the window holds no
// definition of `_3` at all and the whole lane answers `None`.
// ===========================================================================

/// vc_block / Return block / the two chain blocks, by name.
const CHAIN_VC_BLOCK: usize = 5;
const CHAIN_RET_BLOCK: usize = 6;
const CHAIN_ERR_ARM: usize = 3;
const CHAIN_LANDING: usize = 4;

/// The geometry above. `err_arm_stmts`/`err_arm_term` perturb the block that
/// HOLDS the forward-move; `landing_term` perturbs the block the walk merely
/// steps THROUGH.
fn forwarded_err_chain(
    err_arm_stmts: Vec<Statement>,
    err_arm_term: Terminator,
    landing_term: Terminator,
) -> VerifiableFunction {
    let mut func = func_with(
        vec![
            bb(0, vec![], call_into(1, 1)),
            bb(
                1,
                vec![discriminant_of(2, 1)],
                Terminator::SwitchInt {
                    discr: Operand::Copy(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(CHAIN_ERR_ARM),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            bb(2, vec![], Terminator::Goto(BlockId(CHAIN_RET_BLOCK))),
            bb(CHAIN_ERR_ARM, err_arm_stmts, err_arm_term),
            bb(CHAIN_LANDING, vec![], landing_term),
            bb(CHAIN_VC_BLOCK, vec![move_local(0, 3)], Terminator::Goto(BlockId(CHAIN_RET_BLOCK))),
            bb(CHAIN_RET_BLOCK, vec![], Terminator::Return),
        ],
        "result.is_err()",
    );
    func.body.locals = vec![
        LocalDecl { index: 0, ty: std_result_ty(), name: None },
        LocalDecl { index: 1, ty: std_result_ty(), name: None },
        LocalDecl { index: 2, ty: i64_ty(), name: None },
        LocalDecl { index: 3, ty: std_result_ty(), name: None },
        LocalDecl { index: 9, ty: std_result_ty(), name: None },
    ];
    func
}

/// The unperturbed chain: the Err arm forwards the callee result, the landing
/// block does nothing.
fn clean_chain() -> VerifiableFunction {
    forwarded_err_chain(
        vec![move_local(3, 1)],
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        Terminator::Goto(BlockId(CHAIN_VC_BLOCK)),
    )
}

/// The Err arm with `stmts` after the forward-move, everything else clean.
fn chain_with_err_arm_stmts(stmts: Vec<Statement>) -> VerifiableFunction {
    let mut all = vec![move_local(3, 1)];
    all.extend(stmts);
    forwarded_err_chain(
        all,
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        Terminator::Goto(BlockId(CHAIN_VC_BLOCK)),
    )
}

#[track_caller]
fn assert_chain_grounds(func: &VerifiableFunction, why: &str) {
    let got = resolve_enum_return_aggregate_with_block(
        func,
        &func.body.blocks[CHAIN_VC_BLOCK],
        &func.body.blocks[CHAIN_RET_BLOCK],
    );
    assert_eq!(
        got.map(|(k, v, ops, b)| (format!("{k:?}"), v, ops.len(), b)),
        Some(("Result".to_string(), 1, 0, BlockId(CHAIN_ERR_ARM))),
        "{why}"
    );
}

#[track_caller]
fn assert_chain_refused(func: &VerifiableFunction, why: &str) {
    let got = resolve_enum_return_aggregate_with_block(
        func,
        &func.body.blocks[CHAIN_VC_BLOCK],
        &func.body.blocks[CHAIN_RET_BLOCK],
    );
    let shown = got.map(|(k, v, ops, b)| (format!("{k:?}"), v, ops.len(), b));
    assert!(shown.is_none(), "{why} — but a stale value was still resolved: {shown:?}");
}

/// THE CONTROL. Without the pred-chain hop this whole shape answers `None`, so
/// a `def_block` of `bb3` is positive evidence that the walk ran, stepped
/// through the landing block, and found the Err arm's forward-move. Every
/// negative below differs from this by ONE perturbation.
#[test]
fn a_clean_forwarded_err_chain_still_hops_and_grounds() {
    assert_chain_grounds(
        &clean_chain(),
        "the drop-landing chain is exactly what the pred-chain hop exists to walk",
    );
}

/// A terminator write on a block the walk STEPS THROUGH. The landing block's
/// exit is `_3 = <callee>()`, so the Err arm's `_3 = move _1` two blocks up
/// never reaches `_0`. The old walk read no terminator at all, hopped past it,
/// and resolved the switch edge's `Err` for a value the landing block had
/// replaced with an unknown callee result.
#[test]
fn a_call_dest_on_a_stepped_through_chain_block_stops_the_hop() {
    let func = forwarded_err_chain(
        vec![move_local(3, 1)],
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        call_into(3, CHAIN_VC_BLOCK),
    );
    assert_chain_refused(&func, "the landing block's own Call overwrites `_3` on the way out");
}

/// The same, on the block that HOLDS the definition — the direct analogue of
/// `the_chain_tails_own_terminator_is_checked_before_it_is_pushed` one level
/// up. `bb3 = { _3 = move _1; Call { dest: _3 } }` is an ordinary modelled call
/// whose own terminator overwrites the move the walk wants to hop on.
#[test]
fn a_call_dest_on_the_def_holding_chain_block_stops_the_hop() {
    let func = forwarded_err_chain(
        vec![move_local(3, 1)],
        call_into(3, CHAIN_LANDING),
        Terminator::Goto(BlockId(CHAIN_VC_BLOCK)),
    );
    assert_chain_refused(&func, "the def-holding block's own terminator overwrites `_3`");
}

/// Drop glue takes `&mut place`, so a `Drop` of `_3` on the chain is a write
/// the walk must stop at. The old two-shape reading named no terminator, so
/// this walked through as well.
#[test]
fn a_drop_of_the_hopped_local_on_the_chain_stops_the_hop() {
    let func = forwarded_err_chain(
        vec![move_local(3, 1)],
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        Terminator::Drop {
            place: Place::local(3),
            target: BlockId(CHAIN_VC_BLOCK),
            span: SourceSpan::default(),
            unwind: Default::default(),
        },
    );
    assert_chain_refused(&func, "drop glue takes `&mut _3`");
}

/// LAST-WRITE-WINS, the sharpest statement case. `SetDiscriminant` is the
/// statement whose whole job is to change a discriminant, and here it sits
/// AFTER the forward-move: the value leaving `bb3` is `Ok`, not the callee's
/// `Err`. The old search took the FIRST `Assign`, found the move, and hopped —
/// grounding the switch edge's `Err` for a value the same block had since
/// rewritten.
#[test]
fn a_set_discriminant_after_the_forward_move_stops_the_hop() {
    let func = chain_with_err_arm_stmts(vec![Statement::SetDiscriminant {
        place: Place::local(3),
        variant_index: 0,
    }]);
    assert_chain_refused(
        &func,
        "the LAST write to `_3` is a discriminant write, not the forward-move",
    );
}

/// The same at `Deinit`: the local is uninitialized on exit, and the move above
/// it is not what reaches the successor.
#[test]
fn a_deinit_after_the_forward_move_stops_the_hop() {
    let func = chain_with_err_arm_stmts(vec![Statement::Deinit { place: Place::local(3) }]);
    assert_chain_refused(&func, "the LAST write to `_3` is a `Deinit`");
}

/// A PROJECTED store after the move. It is a write (`LocalWrite::Partial`) and
/// it is not the whole-local forward-move this hop models, so the walk must
/// fail closed rather than skip it and take the move above.
#[test]
fn a_projected_store_after_the_forward_move_stops_the_hop() {
    let func = chain_with_err_arm_stmts(vec![Statement::Assign {
        place: Place { local: 3, projections: vec![trust_types::Projection::Field(1)] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
        span: SourceSpan::default(),
    }]);
    assert_chain_refused(&func, "the LAST write to `_3` is a field store");
}

/// LAST-WRITE-WINS IS A WIDENING TOO, not only a narrowing — and this is the
/// pin that proves the rewrite did not simply make the walk stricter. Two
/// whole-local `Assign`s to `_3`, the LAST of which is the forward-move: the
/// old first-match search took the DEAD `Ok(0)` above it, saw a non-`Use`
/// rvalue, and gave up. The value that reaches the successor is the move, so
/// the hop must be taken and the lane must ground.
#[test]
fn a_dead_store_above_the_forward_move_no_longer_blocks_the_hop() {
    let func = forwarded_err_chain(
        vec![
            Statement::Assign {
                place: Place::local(3),
                rvalue: Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "core::result::Result".to_string(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    vec![Operand::Constant(ConstValue::Int(0))],
                ),
                span: SourceSpan::default(),
            },
            move_local(3, 1),
        ],
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        Terminator::Goto(BlockId(CHAIN_VC_BLOCK)),
    );
    assert_chain_grounds(&func, "the LAST write to `_3` is the forward-move, so the hop is taken");
}

/// THE POSITIVE TWINS. The same perturbations aimed at a DIFFERENT local must
/// still hop and still ground — otherwise the three negatives above would be
/// passing because the lane had been disabled rather than narrowed.
#[test]
fn the_same_chain_perturbations_on_another_local_still_ground() {
    const OTHER: usize = 9;
    for (what, func) in [
        (
            "landing block exits `_9 = inner()`",
            forwarded_err_chain(
                vec![move_local(3, 1)],
                Terminator::Goto(BlockId(CHAIN_LANDING)),
                call_into(OTHER, CHAIN_VC_BLOCK),
            ),
        ),
        (
            "def-holding block exits `_9 = inner()`",
            forwarded_err_chain(
                vec![move_local(3, 1)],
                call_into(OTHER, CHAIN_LANDING),
                Terminator::Goto(BlockId(CHAIN_VC_BLOCK)),
            ),
        ),
        (
            "landing block exits `drop(_9)`",
            forwarded_err_chain(
                vec![move_local(3, 1)],
                Terminator::Goto(BlockId(CHAIN_LANDING)),
                Terminator::Drop {
                    place: Place::local(OTHER),
                    target: BlockId(CHAIN_VC_BLOCK),
                    span: SourceSpan::default(),
                    unwind: Default::default(),
                },
            ),
        ),
        (
            "SetDiscriminant(_9) after the move",
            chain_with_err_arm_stmts(vec![Statement::SetDiscriminant {
                place: Place::local(OTHER),
                variant_index: 0,
            }]),
        ),
        (
            "Deinit(_9) after the move",
            chain_with_err_arm_stmts(vec![Statement::Deinit { place: Place::local(OTHER) }]),
        ),
        (
            "_9.0 = 7 after the move",
            chain_with_err_arm_stmts(vec![Statement::Assign {
                place: Place { local: OTHER, projections: vec![trust_types::Projection::Field(0)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            }]),
        ),
        (
            "StorageDead(_9) after the move — a marker, no value at all",
            chain_with_err_arm_stmts(vec![Statement::StorageDead(OTHER)]),
        ),
    ] {
        assert_chain_grounds(&func, &format!("{what} does not touch `_3` and must not stop the hop"));
    }
}

/// `Terminator::Opaque` on the chain. Its destination is discarded at
/// extraction, so `_3` cannot be ruled out and the walk must stop.
///
/// HONEST SCOPE, and the mutation proof says so: with the walk reverted, every
/// other negative in this section fails and THIS ONE STILL PASSES. It is the
/// same structural confound PIN 5's `Opaque` case carries — an `Opaque`
/// anywhere in the body makes `Terminator::local_write` answer `Unlocatable`
/// for EVERY local, so `unique_value_def(_2)` goes ambiguous and the forwarded
/// switch this chain bottoms out in declines at its own step (2a). Both
/// refusals are the same fail-closed direction, and no geometry in this shape
/// separates them, because the confound is a fact about the whole body rather
/// than about where the `Opaque` sits. (`Statement::Unsupported` after the
/// forward-move is the statement-side twin of exactly this, confounded for
/// exactly the same reason, so it is not pinned separately.) The attributable
/// check for `Opaque` is `terminator_preserves_local_is_the_allow_list_at_any_local`
/// above — the walk's terminator test is a call to that same predicate.
#[test]
fn an_opaque_on_the_chain_stops_the_hop() {
    let func = forwarded_err_chain(
        vec![move_local(3, 1)],
        Terminator::Goto(BlockId(CHAIN_LANDING)),
        opaque_indirect_call_into_ret(CHAIN_VC_BLOCK),
    );
    assert_chain_refused(&func, "an Opaque's destination is discarded, so no local is ruled out");
    // The confound, stated as a fact rather than asserted around.
    assert!(
        matches!(crate::local_defs::unique_value_def(&clean_chain(), 2), Some(Rvalue::Discriminant(p))
            if p.local == 1),
        "the clean chain's `_2 = discriminant(_1)` is what the forwarded switch reads"
    );
    assert!(
        crate::local_defs::unique_value_def(&func, 2).is_none(),
        "an Opaque is `Unlocatable` for EVERY local, so the switch also declines at (2a) — \
         this pin cannot be attributed to the walk's terminator test alone"
    );
}

/// The clean chain with `stmts` in the block the walk STEPS THROUGH, the
/// forward-move still one block above it.
fn chain_with_landing_stmts(stmts: Vec<Statement>) -> VerifiableFunction {
    let mut func = clean_chain();
    func.body.blocks[CHAIN_LANDING].stmts = stmts;
    func
}

/// THE CASE THE "last write must BE the forward-move" REQUIREMENT UNIQUELY
/// PROTECTS, and the reason that requirement is a `break` rather than a
/// "keep looking". Here the non-move write sits in the block the walk steps
/// THROUGH, with the forward-move one block ABOVE it:
///
///   bb3: _3 = move _1            <-- the definition the walk wants
///   bb4: <SetDiscriminant / Deinit / _3.0 = 7>   <-- and then this happens
///   bb5: _0 = move _3
///
/// A walk that merely FAILED TO RECOGNISE the perturbation and carried on up
/// the chain would find `bb3`'s move and hop on it — attributing the callee's
/// `Err` to a `_3` that `bb4` has since rewritten. Refusing at the block is the
/// only sound reading, and it is what separates part 3 of this hardening from
/// part 2.
#[test]
fn a_non_move_last_write_on_a_stepped_through_chain_block_stops_the_hop() {
    for (what, stmt) in [
        (
            "SetDiscriminant(_3, Ok)",
            Statement::SetDiscriminant { place: Place::local(3), variant_index: 0 },
        ),
        ("Deinit(_3)", Statement::Deinit { place: Place::local(3) }),
        (
            "_3.0 = 7",
            Statement::Assign {
                place: Place { local: 3, projections: vec![trust_types::Projection::Field(1)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            },
        ),
    ] {
        assert_chain_refused(
            &chain_with_landing_stmts(vec![stmt]),
            &format!("{what} rewrites `_3` after the move above it — the walk may not step past"),
        );
    }
}

/// The positive twins for the stepped-through statement cases: the same writes
/// aimed at `_9` leave `_3` alone, so the walk must still step through the
/// block and hop on the move above.
#[test]
fn stepped_through_writes_to_another_local_still_ground() {
    const OTHER: usize = 9;
    for (what, stmt) in [
        (
            "SetDiscriminant(_9, Ok)",
            Statement::SetDiscriminant { place: Place::local(OTHER), variant_index: 0 },
        ),
        ("Deinit(_9)", Statement::Deinit { place: Place::local(OTHER) }),
        (
            "_9.0 = 7",
            Statement::Assign {
                place: Place { local: OTHER, projections: vec![trust_types::Projection::Field(0)] },
                rvalue: Rvalue::Use(Operand::Constant(ConstValue::Int(7))),
                span: SourceSpan::default(),
            },
        ),
        ("StorageDead(_9)", Statement::StorageDead(OTHER)),
    ] {
        assert_chain_grounds(
            &chain_with_landing_stmts(vec![stmt]),
            &format!("{what} does not touch `_3`, so the walk must still step through"),
        );
    }
}
