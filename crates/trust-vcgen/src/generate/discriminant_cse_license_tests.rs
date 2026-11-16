//! Unit cover for arm (c) of [`super::build_discriminant_cse_facts`] and its license,
//! `unaliased_aggregate_licensed_reads` (class `v-refuted-unreachable`, 2026-09-27).
//!
//! Every case starts from the REAL verified MIR of
//!
//! ```text
//! pub trait Src { fn get(&self) -> Option<u32>; }
//! pub fn pair<S: Src>(a: &S, b: &S) -> u32 {
//!     match (a.get(), b.get()) {
//!         (None, None) => 0, (None, _) => 1, (_, None) => 2, (Some(x), Some(y)) => x ^ y,
//!     }
//! }
//! ```
//!
//! whose shape is (`_3` is the tuple, built in bb2 AFTER both calls):
//!
//! ```text
//! bb2: _3 = (move _4, move _5); ..; _7 = discriminant(_3.0); switch _7 [0: bb4, 1: bb3, _: bb5]
//! bb3: _9 = discriminant(_3.1); switch _9 [0: bb8, 1: bb6, _: bb5]
//! bb4: _6 = discriminant(_3.1); switch _6 [0: bb10, 1: bb9, _: bb5]
//! bb5: unreachable
//! bb6: _8 = discriminant(_3.0); switch _8 [1: bb7, _: bb5]
//! ```
//!
//! and then plants ONE invalidating event or disqualifier, asserting the license and
//! the emitted ties move exactly as the license's doc says. Each negative case differs
//! from its positive twin by exactly the event its check exists for: the bare body, or,
//! for an event arm (b) does not count (a move, a storage marker), the body with arm (b)
//! taken out (`without_arm_b`, `the_license_alone_ties_the_real_pair_body`).
use trust_types::fx::FxHashSet;
use trust_types::{
    BlockId, Formula, Operand, Place, Projection, Rvalue, Sort, SourceSpan, Statement, Terminator,
    VerifiableFunction,
};

fn pair() -> VerifiableFunction {
    serde_json::from_str(include_str!("../../tests/fixtures/discriminant_cse_owned_pair_mir.json"))
        .expect("fixture MIR must deserialize")
}

fn field(local: usize, f: usize) -> Place {
    Place { local, projections: vec![Projection::Field(f)] }
}

fn licensed(func: &VerifiableFunction) -> Option<FxHashSet<(usize, usize)>> {
    super::unaliased_aggregate_licensed_reads(func, 3)
}

/// True iff the CSE facts tie the two named discriminant temps.
fn tied(func: &VerifiableFunction, a: &str, b: &str) -> bool {
    let va = Formula::Var(a.into(), Sort::Int);
    let vb = Formula::Var(b.into(), Sort::Int);
    super::build_discriminant_cse_facts(func).iter().any(|f| {
        matches!(f, Formula::Eq(l, r)
            if (**l == va && **r == vb) || (**l == vb && **r == va))
    })
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// Take arm (b) out of the builder, so arm (c) is the only admission left: a `Drop` of
/// `_3.1` planted on the `(None, None)` arm's return edge (bb10 -> bb11), which no read
/// follows. Arm (b) refuses a post-call read of an aggregate any `Drop` names
/// (`local_defs::storage_never_aliased`); the license is unchanged, because the drop's
/// only successor is the return block.
///
/// A case about an event arm (b) does not count needs this. Arm (b) ties the post-call
/// reads of a tuple no pointer reaches whatever moves or storage markers lie between
/// them (its argument: MIR does not read a moved-from place before re-initialising
/// it), so on the bare fixture a tie would come from arm (b) and say nothing about the
/// license.
fn without_arm_b(mut func: VerifiableFunction) -> VerifiableFunction {
    let new = func.body.blocks.len();
    func.body.blocks.push(trust_types::BasicBlock {
        id: BlockId(new),
        stmts: vec![],
        terminator: Terminator::Drop {
            place: field(3, 1),
            target: BlockId(11),
            span: SourceSpan::default(),
            unwind: Default::default(),
        },
    });
    let Terminator::Goto(target) = &mut func.body.blocks[10].terminator else {
        panic!("bb10 returns through bb11");
    };
    *target = BlockId(new);
    func
}

#[test]
fn every_match_read_of_the_real_pair_body_is_licensed_and_tied() {
    let func = pair();
    let reads = licensed(&func).expect("an unborrowed tuple built once is licensable");
    let expected: FxHashSet<(usize, usize)> =
        [(2, 3), (3, 0), (4, 0), (6, 0)].into_iter().collect();
    assert_eq!(reads, expected);
    // The two reads of `_3.0` and the two reads of `_3.1`, each pair tied — the
    // facts that discharge bb6's subset switch.
    assert!(tied(&func, "_7", "_8"), "{:?}", super::build_discriminant_cse_facts(&func));
    assert!(tied(&func, "_9", "_6"), "{:?}", super::build_discriminant_cse_facts(&func));
    // Different fields are never tied.
    assert!(!tied(&func, "_7", "_9"));
    assert!(!tied(&func, "_8", "_6"));
}

/// With arm (b) taken out, the license ALONE ties the real body's re-reads — what the
/// post-call ties rest on wherever arm (b) refuses (a drop ladder, a nested payload
/// path). The other negative cases below differ from this one by exactly their event.
#[test]
fn the_license_alone_ties_the_real_pair_body() {
    let func = without_arm_b(pair());
    assert!(!crate::local_defs::storage_never_aliased(&func, 3), "arm (b) is out");
    let reads = licensed(&func).expect("the planted drop reaches no read");
    let expected: FxHashSet<(usize, usize)> =
        [(2, 3), (3, 0), (4, 0), (6, 0)].into_iter().collect();
    assert_eq!(reads, expected);
    assert!(tied(&func, "_7", "_8"), "{:?}", super::build_discriminant_cse_facts(&func));
    assert!(tied(&func, "_9", "_6"), "{:?}", super::build_discriminant_cse_facts(&func));
}

/// The path-guard splice renders each tied temp through its group's FIRST read: the
/// anchor map is exactly the ties, restricted to single-assignment destinations.
#[test]
fn the_anchor_map_is_the_ties_of_the_real_pair_body() {
    let func = pair();
    let anchors = super::discriminant_cse_anchor_map(&func);
    let mut got: Vec<(String, String)> =
        anchors.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
    got.sort();
    assert_eq!(got, vec![("_6".to_string(), "_9".to_string()), ("_8".into(), "_7".into())]);
}

/// A guard rendered through its anchor CARRIES the tie it rests on: every occurrence
/// of the tied temp left in the spliced path condition is inside `anchor == temp`
/// (each side spelled at the guard's source block, like the rest of the guard), so
/// the rendered condition is the original one conjoined with a true fact, whatever
/// lane splices it — the termination lanes conjoin no global facts, so the global tie
/// cannot be assumed to sit beside it. Without the carried tie `_8`'s subset switch
/// would constrain only `_7`'s version at bb6, a name nothing else on a path that
/// skips bb2's read ties to the field.
#[test]
fn a_rendered_guard_carries_the_tie_it_rests_on() {
    let func = pair();
    let guard_map = super::guard_map_for(&func);
    let paths = guard_map.get(&BlockId(5)).expect("the Unreachable block has guard paths");
    let spliced = super::v2_formula_with_path_guards(
        &func,
        &super::stmt_versions_for(&func),
        BlockId(5),
        paths,
        Formula::Bool(true),
    );
    let base = |f: &Formula| match f {
        Formula::Var(name, _) => Some(name.split('#').next().unwrap_or(name).to_string()),
        _ => None,
    };
    let mut ties = 0usize;
    let mut loose_8 = 0usize;
    let mut stack = vec![&spliced];
    while let Some(f) = stack.pop() {
        if let Formula::Eq(l, r) = f
            && base(l).as_deref() == Some("_7")
            && base(r).as_deref() == Some("_8")
        {
            ties += 1;
            continue;
        }
        if base(f).as_deref() == Some("_8") {
            loose_8 += 1;
        }
        stack.extend(f.children());
    }
    assert!(ties > 0, "the subset switch over `_8` is rendered through `_7`: {spliced:?}");
    assert_eq!(loose_8, 0, "`_8` survives only inside its tie: {spliced:?}");
}

/// A destination written twice keeps its tie FACT out of the anchor map as well: the
/// guard over it is rendered unchanged.
#[test]
fn a_reassigned_destination_is_not_an_anchor_alias() {
    let mut func = pair();
    func.body.blocks[7].stmts.push(assign(
        Place::local(8),
        Rvalue::Use(Operand::Constant(trust_types::ConstValue::Int(1))),
    ));
    let anchors = super::discriminant_cse_anchor_map(&func);
    assert!(!anchors.contains_key("_8"), "{anchors:?}");
    assert_eq!(anchors.get("_6").map(String::as_str), Some("_9"));
}

/// A MOVE out of the tuple before a read: the moved bytes may be de-initialized
/// (UCG#188) and, for a niche-encoded enum, they hold the tag.
#[test]
fn a_move_out_of_the_tuple_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    // bb6: `_10 = move (_3.0 as Some).0` ahead of `_8 = discriminant(_3.0)`.
    let payload = Place {
        local: 3,
        projections: vec![Projection::Field(0), Projection::Downcast(1), Projection::Field(0)],
    };
    func.body.blocks[6]
        .stmts
        .insert(0, assign(Place::local(10), Rvalue::Use(Operand::Move(payload))));
    let reads = licensed(&func).expect("a move is an event, not a disqualifier");
    assert!(!reads.contains(&(6, 1)), "the read after the move must not be licensed: {reads:?}");
    assert!(reads.contains(&(2, 3)) && reads.contains(&(3, 0)) && reads.contains(&(4, 0)));
    assert!(!tied(&func, "_7", "_8"));
    assert!(tied(&func, "_9", "_6"), "reads the move does not reach keep their tie");
}

/// `StorageDead` ends the tuple's value; everything the marker reaches is unlicensed.
#[test]
fn a_storage_dead_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    func.body.blocks[3].stmts.insert(0, Statement::StorageDead(3));
    let reads = licensed(&func).expect("a storage marker is an event");
    assert!(!reads.contains(&(3, 1)), "bb3's read follows the marker: {reads:?}");
    assert!(!reads.contains(&(6, 0)), "bb6 is reached from bb3: {reads:?}");
    assert!(reads.contains(&(4, 0)) && reads.contains(&(2, 3)));
    assert!(!tied(&func, "_7", "_8"));
}

/// `StorageLive` of a live local re-allocates it too.
#[test]
fn a_storage_live_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    func.body.blocks[6].stmts.insert(0, Statement::StorageLive(3));
    let reads = licensed(&func).expect("a storage marker is an event");
    assert!(!reads.contains(&(6, 1)), "{reads:?}");
    assert!(!tied(&func, "_7", "_8"));
}

/// A `Drop` of a tuple field hands its glue `&mut` to that field. Planted as a new
/// block on the bb3 -> bb6 edge.
#[test]
fn a_drop_of_a_field_unlicenses_the_reads_it_reaches() {
    let mut func = pair();
    let new = func.body.blocks.len();
    func.body.blocks.push(trust_types::BasicBlock {
        id: BlockId(new),
        stmts: vec![],
        terminator: Terminator::Drop {
            place: field(3, 1),
            target: BlockId(6),
            span: SourceSpan::default(),
            unwind: Default::default(),
        },
    });
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[3].terminator else {
        panic!("bb3 ends in a switch");
    };
    for (_, t) in targets.iter_mut() {
        if t.0 == 6 {
            *t = BlockId(new);
        }
    }
    let reads = licensed(&func).expect("a drop is an event");
    assert!(!reads.contains(&(6, 0)), "bb6 follows the drop: {reads:?}");
    assert!(!tied(&func, "_7", "_8"));
}

/// ANY borrow of the tuple — a shared one included — disqualifies the whole local:
/// through it, a callee could reach the tuple.
#[test]
fn any_borrow_of_the_tuple_disqualifies_it() {
    let mut func = pair();
    func.body.blocks[7]
        .stmts
        .push(assign(Place::local(10), Rvalue::Ref { mutable: false, place: field(3, 0) }));
    assert_eq!(licensed(&func), None);
    assert!(!tied(&func, "_7", "_8"));
}

/// An `Opaque` terminator is a write the oracle cannot locate (`Unlocatable`).
#[test]
fn an_opaque_terminator_disqualifies_every_local() {
    let mut func = pair();
    func.body.blocks[1].terminator = Terminator::Opaque {
        kind: "asm".into(),
        targets: vec![BlockId(2)],
        span: SourceSpan::default(),
    };
    assert_eq!(licensed(&func), None);
}

/// A second whole write: the reads could observe either construction.
#[test]
fn a_second_construction_disqualifies_the_tuple() {
    let mut func = pair();
    let Some(Statement::Assign { rvalue, .. }) = func.body.blocks[2].stmts.first().cloned() else {
        panic!("bb2 starts with the construction");
    };
    func.body.blocks[3].stmts.insert(0, assign(Place::local(3), rvalue));
    assert_eq!(licensed(&func), None);
}

/// The tie is keyed on the DESTINATION's bare name: a destination written twice is
/// refused even though its read is licensed.
#[test]
fn a_reassigned_destination_is_not_tied() {
    let mut func = pair();
    func.body.blocks[7].stmts.push(assign(
        Place::local(8),
        Rvalue::Use(Operand::Constant(trust_types::ConstValue::Int(1))),
    ));
    assert!(licensed(&func).is_some_and(|r| r.contains(&(6, 0))));
    assert!(!tied(&func, "_7", "_8"));
    assert!(tied(&func, "_9", "_6"));
}

/// Rename local `a` to `b` and `b` to `a` everywhere in the body: every `Place`'s
/// `local`, every storage marker, and the two declarations.
fn with_locals_swapped(func: &VerifiableFunction, a: usize, b: usize) -> VerifiableFunction {
    fn swap(v: &mut serde_json::Value, a: u64, b: u64) {
        match v {
            serde_json::Value::Object(m) => {
                for (k, x) in m.iter_mut() {
                    let names_a_local =
                        matches!(k.as_str(), "local" | "StorageLive" | "StorageDead");
                    match x.as_u64() {
                        Some(n) if names_a_local && n == a => *x = b.into(),
                        Some(n) if names_a_local && n == b => *x = a.into(),
                        _ => swap(x, a, b),
                    }
                }
            }
            serde_json::Value::Array(xs) => xs.iter_mut().for_each(|x| swap(x, a, b)),
            _ => {}
        }
    }
    let mut body = serde_json::to_value(&func.body).expect("the body serializes");
    swap(&mut body["blocks"], a as u64, b as u64);
    let mut out = func.clone();
    out.body = serde_json::from_value(body).expect("the swapped body deserializes");
    out.body.locals.swap(a, b);
    out.body.locals[a].index = a;
    out.body.locals[b].index = b;
    out
}

/// Parameters and the return place hold a value from before ENTRY (a parameter's is
/// the caller's; the return place's may be the caller's destination), so neither is
/// ever licensed. Each case is the real body with the tuple moved into that role, its
/// twin the same move into a plain temp, which stays licensed.
#[test]
fn parameters_and_the_return_place_are_never_licensed() {
    // The tuple as a parameter: `_3` is a parameter once `arg_count` reaches it.
    let mut as_param = pair();
    assert!(licensed(&as_param).is_some_and(|r| r.contains(&(6, 0))), "the twin");
    as_param.body.arg_count = 3;
    assert_eq!(licensed(&as_param), None);

    // The tuple as the return place: `_3` and `_0` swapped (the match's results go to
    // `_3`, which is no aggregate). The twin swaps it with the last temp instead.
    let last = pair().body.locals.len() - 1;
    let as_temp = with_locals_swapped(&pair(), 3, last);
    assert!(
        super::unaliased_aggregate_licensed_reads(&as_temp, last)
            .is_some_and(|r| r.contains(&(6, 0))),
        "the twin"
    );
    let as_return = with_locals_swapped(&pair(), 3, 0);
    assert_eq!(super::unaliased_aggregate_licensed_reads(&as_return, 0), None);
}

/// ENTRY is an event. With the tuple's storage markers removed (an always-live local,
/// whose entry value is whatever an earlier loop iteration or nothing left), a read
/// placed BEFORE the construction is reached from entry without passing it, so it must
/// not be licensed; the reads after the construction still are.
#[test]
fn entry_is_an_event() {
    let mut func = pair();
    for b in &mut func.body.blocks {
        b.stmts.retain(|s| !matches!(s, Statement::StorageLive(3) | Statement::StorageDead(3)));
    }
    func.body.blocks[1]
        .stmts
        .insert(0, assign(Place::local(12), Rvalue::Discriminant(field(3, 0))));
    let reads = licensed(&func).expect("licensable");
    assert!(!reads.contains(&(1, 0)), "a read before the construction is licensed: {reads:?}");
    assert!(reads.contains(&(2, 3)), "{reads:?}");
}

/// An UNWIND edge carries an event. A `Drop` of `_3.1` whose normal edge returns and
/// whose cleanup edge reaches a read: the cleanup read follows the drop, so it must not
/// be licensed; the match's own reads, which no path from the drop reaches, still are.
#[test]
fn an_event_reaches_a_read_through_its_unwind_edge() {
    let mut func = pair();
    let drop_bb = func.body.blocks.len();
    let cleanup_bb = drop_bb + 1;
    func.body.blocks.push(trust_types::BasicBlock {
        id: BlockId(drop_bb),
        stmts: vec![],
        terminator: Terminator::Drop {
            place: field(3, 1),
            target: BlockId(11),
            span: SourceSpan::default(),
            unwind: trust_types::UnwindEdge::Cleanup(BlockId(cleanup_bb)),
        },
    });
    func.body.blocks.push(trust_types::BasicBlock {
        id: BlockId(cleanup_bb),
        stmts: vec![assign(Place::local(12), Rvalue::Discriminant(field(3, 0)))],
        terminator: Terminator::Resume,
    });
    let Terminator::Goto(target) = &mut func.body.blocks[10].terminator else {
        panic!("bb10 returns through bb11");
    };
    *target = BlockId(drop_bb);
    let reads = licensed(&func).expect("a drop is an event, not a disqualifier");
    assert!(!reads.contains(&(cleanup_bb, 0)), "the cleanup read follows the drop: {reads:?}");
    assert!(reads.contains(&(2, 3)) && reads.contains(&(6, 0)), "{reads:?}");
}

/// A reborrow or fake-borrow sentinel, which the extractor emits as an
/// `Rvalue::Unsupported` carrying the borrowed place as an operand, disqualifies the
/// tuple: the scan cannot see what the sentinel lets reach it, and `stmt_escapes_local`
/// flags only `&mut`, `&raw` and a shared borrow that covers a cell.
#[test]
fn an_unsupported_borrow_sentinel_disqualifies_the_tuple() {
    let mut func = pair();
    func.body.blocks[7].stmts.push(assign(
        Place::local(12),
        Rvalue::Unsupported {
            kind: "fake_borrow".into(),
            detail: String::new(),
            operands: vec![Operand::Copy(field(3, 0))],
        },
    ));
    assert_eq!(licensed(&func), None);
}

/// The payload `(_3.0 as Some).0` of the first field.
fn payload() -> Place {
    Place {
        local: 3,
        projections: vec![Projection::Field(0), Projection::Downcast(1), Projection::Field(0)],
    }
}

/// Plant a new block on the bb3 -> bb6 edge whose terminator is `terminator` (its
/// successor already set to bb6), and return its index.
fn on_the_edge_to_bb6(func: &mut VerifiableFunction, terminator: Terminator) -> usize {
    let new = func.body.blocks.len();
    func.body.blocks.push(trust_types::BasicBlock { id: BlockId(new), stmts: vec![], terminator });
    let Terminator::SwitchInt { targets, .. } = &mut func.body.blocks[3].terminator else {
        panic!("bb3 ends in a switch");
    };
    for (_, t) in targets.iter_mut() {
        if t.0 == 6 {
            *t = BlockId(new);
        }
    }
    new
}

/// A move out of the tuple as a CALL ARGUMENT is an event, as a statement move is: a
/// call on the bb3 -> bb6 edge passes `move (_3.0 as Some).0`.
#[test]
fn a_call_argument_move_out_of_the_tuple_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    let mut call = func.body.blocks[0].terminator.clone();
    let Terminator::Call { args, target, dest, .. } = &mut call else {
        panic!("bb0 ends in a call");
    };
    *args = vec![Operand::Move(payload())];
    *target = Some(BlockId(6));
    *dest = Place::local(10);
    on_the_edge_to_bb6(&mut func, call);
    let reads = licensed(&func).expect("a move is an event, not a disqualifier");
    assert!(!reads.contains(&(6, 0)), "bb6 follows the call's move: {reads:?}");
    assert!(reads.contains(&(2, 3)), "{reads:?}");
    assert!(!tied(&func, "_7", "_8"));
}

/// A move out of the tuple as a `SwitchInt` scrutinee is an event: a switch on the
/// bb3 -> bb6 edge on `move (_3.0 as Some).0`.
#[test]
fn a_switch_on_a_move_out_of_the_tuple_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    on_the_edge_to_bb6(
        &mut func,
        Terminator::SwitchInt {
            discr: Operand::Move(payload()),
            targets: vec![(0, BlockId(6))],
            otherwise: BlockId(6),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    );
    let reads = licensed(&func).expect("a move is an event, not a disqualifier");
    assert!(!reads.contains(&(6, 0)), "bb6 follows the switch's move: {reads:?}");
    assert!(reads.contains(&(2, 3)), "{reads:?}");
    assert!(!tied(&func, "_7", "_8"));
}

/// A move out of the tuple as an AGGREGATE OPERAND (`Mode::Backtrack(move e)`) is an
/// event.
#[test]
fn an_aggregate_operand_move_out_of_the_tuple_unlicenses_the_reads_it_reaches() {
    let mut func = without_arm_b(pair());
    let Some(Statement::Assign { rvalue: Rvalue::Aggregate(kind, _), .. }) =
        func.body.blocks[2].stmts.first().cloned()
    else {
        panic!("bb2 starts with the construction");
    };
    func.body.blocks[6].stmts.insert(
        0,
        assign(Place::local(10), Rvalue::Aggregate(kind, vec![Operand::Move(payload())])),
    );
    let reads = licensed(&func).expect("a move is an event, not a disqualifier");
    assert!(!reads.contains(&(6, 1)), "the read after the move must not be licensed: {reads:?}");
    assert!(reads.contains(&(2, 3)), "{reads:?}");
    assert!(!tied(&func, "_7", "_8"));
}

/// Arm (c) admits `Field`/`Downcast` paths only: a read THROUGH a pointer stored in the
/// tuple (`disc((*_3.0))`) reads memory the license does not track, so two such reads
/// are never tied by it.
#[test]
fn a_read_through_a_pointer_in_the_tuple_is_not_tied() {
    let mut func = pair();
    let decl = func.body.locals[7].clone();
    while func.body.locals.len() < 14 {
        let mut d = decl.clone();
        d.index = func.body.locals.len();
        func.body.locals.push(d);
    }
    let through = Place { local: 3, projections: vec![Projection::Field(0), Projection::Deref] };
    func.body.blocks[3]
        .stmts
        .insert(0, assign(Place::local(12), Rvalue::Discriminant(through.clone())));
    func.body.blocks[6].stmts.insert(0, assign(Place::local(13), Rvalue::Discriminant(through)));
    // The license itself covers both reads (it is about the tuple's own bytes); the
    // admission is what refuses them.
    assert!(licensed(&func).is_some_and(|r| r.contains(&(3, 0)) && r.contains(&(6, 0))));
    assert!(!tied(&func, "_12", "_13"), "a read through a field's pointer was tied");
    assert!(tied(&func, "_7", "_8"), "the twin: the field reads stay tied");
}

/// A block an event enters MID-WAY is still walked from its TOP when another path
/// reaches it: a move after bb6's read, then a back edge bb7 -> bb6, reaches the read
/// again without passing the construction.
#[test]
fn a_block_entered_by_an_event_is_still_walked_from_its_top() {
    let mut func = pair();
    func.body.blocks[6]
        .stmts
        .insert(1, assign(Place::local(10), Rvalue::Use(Operand::Move(payload()))));
    let Terminator::Goto(target) = &mut func.body.blocks[7].terminator else {
        panic!("bb7 ends in a goto");
    };
    *target = BlockId(6);
    let reads = licensed(&func).expect("a move is an event, not a disqualifier");
    assert!(!reads.contains(&(6, 0)), "the back edge reaches bb6's read after the move: {reads:?}");
    assert!(reads.contains(&(2, 3)), "{reads:?}");
}
