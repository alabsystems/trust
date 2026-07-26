use super::*;
use std::collections::BTreeMap;
use trust_types::{
    AggregateKind, Operand, Projection, Rvalue, Statement, Terminator, VerifiableFunction,
};

fn load_dump(name: &str) -> VerifiableFunction {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures/w6-map-closure-2026-07-18/dumps")
        .join(name);
    let bytes = std::fs::read(&path).unwrap_or_else(|e| panic!("read {name}: {e}"));
    serde_json::from_slice(&bytes).unwrap_or_else(|e| panic!("parse {name}: {e}"))
}

/// The non-capturing `Option::<i32>::map::<i32, {closure@main.rs:5:11:5:14}>`
/// harvested body (closure `map_add1::{closure#0}`, upvars []).
const MAP_NONCAP: &str = "trust-mir-cf03b1afc08ab26c-fd79f5371eb3347e.json";
/// The shape-identical CAPTURING `map_cap` instance (closure `map_cap::{closure#0}`,
/// upvars [i32]).
const MAP_CAP: &str = "trust-mir-662622c351281e79-4734a1ade17cec94.json";
/// The `Option::<i32>::and_then::<i32, {closure@main.rs:15:16:15:19}>` harvested
/// body (closure `and_then_pos::{closure#0}`, whose declared return is the SAME
/// `Option<i32>` — the AndThenFlat mode: the CALL dest IS `_0`, no Some-rewrap).
const AND_THEN: &str = "trust-mir-b0282c69c16082e4-e11fb07682484adc.json";
/// The `Option::<i32>::filter::<{closure@main.rs:20:14:20:17}>` harvested body
/// (closure `filter_pos::{closure#0}`, `FnOnce(&i32) -> bool`) — the 11-block
/// predicate-filter shape (ref arg, second Bool switch, Drop plumbing, Resume).
const FILTER: &str = "trust-mir-4fc5e5e1c0f8ba5c-a45a703cdd36ac11.json";

/// A spec-free, arg_count-2 (env + untupled x) certified closure fact.
fn closure_fact() -> CalleeFact {
    CalleeFact { arg_count: 2, requires: Some(vec![]), param_names: vec![None, Some("x".into())] }
}

fn registry(key: &str) -> BTreeMap<String, CalleeFact> {
    let mut m = BTreeMap::new();
    m.insert(key.to_string(), closure_fact());
    m
}

#[test]
fn recognizes_corpus_noncapturing_map() {
    let func = load_dump(MAP_NONCAP);
    let callees = registry("map_add1::{closure#0}");
    let shape = sem_adt_map_compose_of_discriminant_switch(&func, &callees)
        .expect("the non-capturing mono map must be recognized");
    assert_eq!(shape.call_variant, 1, "Some is variant 1");
    assert_eq!(shape.none_variant, 0, "None is variant 0");
    assert_eq!(shape.callee, "map_add1::{closure#0}");
    assert_eq!(shape.callee_id, 0);
    assert_eq!(shape.env_operand, SemOperand::Var(1), "the FnOnce env is closure param _2 = Var(1)");
    assert_eq!(shape.kind, super::ComposeReturn::MapWrap, "map is the Some-rewrap mode");
}

/// W6 increment 2: the mono `and_then` over the certified `and_then_pos::{closure#0}`
/// (whose declared return is the SAME `Option<i32>`) is recognized as the
/// AndThenFlat mode — the CALL dest is `_0`, no Some-rewrap continuation.
#[test]
fn recognizes_corpus_and_then() {
    let func = load_dump(AND_THEN);
    let callees = registry("and_then_pos::{closure#0}");
    let shape = sem_adt_map_compose_of_discriminant_switch(&func, &callees)
        .expect("the mono and_then must be recognized");
    assert_eq!(shape.kind, super::ComposeReturn::AndThenFlat, "and_then is the flat mode");
    assert_eq!(shape.call_variant, 1, "Some is variant 1");
    assert_eq!(shape.none_variant, 0, "None is variant 0");
    assert_eq!(shape.callee, "and_then_pos::{closure#0}");
    assert_eq!(shape.env_operand, SemOperand::Var(1), "the FnOnce env is closure param _2 = Var(1)");
}

/// The AndThenFlat mode obeys the SAME mandatory exact-match gate: a registry
/// with ONLY the suffix decoy must NOT certify the flat and_then instance.
#[test]
fn and_then_exact_match_only_declines_suffix_decoy() {
    let func = load_dump(AND_THEN);
    let callees = registry("inner::and_then_pos::{closure#0}"); // ONLY the decoy.
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a unique-suffix nested-module decoy must NOT resolve on the and_then lane"
    );
}

/// An and_then whose closure is NOT in the registry stays declined (baseline:
/// the leaf must have minted its certificate first).
#[test]
fn and_then_empty_registry_declines() {
    let func = load_dump(AND_THEN);
    let callees: BTreeMap<String, CalleeFact> = BTreeMap::new();
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

/// FORGERY: retarget the and_then None arm's `Drop(_2)` to `Drop(_1)` — a Drop
/// of anything but the bare closure param declines on the flat lane too.
#[test]
fn and_then_drop_of_non_closure_place_declines() {
    let mut func = load_dump(AND_THEN);
    if let Terminator::Drop { place, .. } = &mut block_mut(&mut func, 2).terminator {
        place.local = 1;
    }
    let callees = registry("and_then_pos::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

/// FORGERY: inject a stray `_0 := Aggregate(Some, [Move _4])` Some-rewrap into the
/// and_then CALL continuation (bb4). The flat mode requires the continuation to
/// carry NO `Statement::Assign` (the CALL wrote `_0` via its dest); a second `_0`
/// write breaks the write-count-1 discipline and declines.
#[test]
fn and_then_extra_continuation_write_declines() {
    let mut func = load_dump(AND_THEN);
    let some_rewrap = Statement::Assign {
        place: trust_types::Place { local: 0, projections: vec![] },
        rvalue: Rvalue::Aggregate(
            AggregateKind::Adt {
                name: "std::option::Option".into(),
                variant: 1,
                active_field: None,
            },
            vec![Operand::Move(trust_types::Place { local: 4, projections: vec![] })],
        ),
        span: trust_types::SourceSpan::default(),
    };
    block_mut(&mut func, 4).stmts.push(some_rewrap);
    let callees = registry("and_then_pos::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a stray `_0` write in the flat continuation must decline"
    );
}

// --- W6 increment 2: filter (`FnOnce(&i32) -> bool`) ---

/// The mono `filter` over the certified `filter_pos::{closure#0}` is recognized
/// (ref arg, Bool second switch, Drop plumbing, unreachable Resume).
#[test]
fn recognizes_corpus_filter() {
    let func = load_dump(FILTER);
    let callees = registry("filter_pos::{closure#0}");
    let shape = sem_adt_filter_compose_of_discriminant_switch(&func, &callees)
        .expect("the mono filter must be recognized");
    assert_eq!(shape.some_variant, 1, "Some/keep is variant 1");
    assert_eq!(shape.none_variant, 0, "None is variant 0");
    assert_eq!(shape.callee, "filter_pos::{closure#0}");
    assert_eq!(shape.env_operand, SemOperand::Var(1));
}

/// The filter lane's mandatory exact-match gate: only the suffix decoy ⇒ decline.
#[test]
fn filter_exact_match_only_declines_suffix_decoy() {
    let func = load_dump(FILTER);
    let callees = registry("inner::filter_pos::{closure#0}");
    assert!(sem_adt_filter_compose_of_discriminant_switch(&func, &callees).is_none());
}

/// The map/and_then recognizer must DECLINE the filter shape (11 blocks, two
/// switches) and vice-versa — the lanes are disjoint.
#[test]
fn map_recognizer_declines_filter_shape() {
    let func = load_dump(FILTER);
    let callees = registry("filter_pos::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "the map/and_then recognizer must not accept the filter shape"
    );
}

/// FORGERY (requirement #3): the KEEP arm's reconstruct `_9 = Move _4` re-pointed
/// to a SUBSTITUTE local (not the extracted payload `_4`) must DECLINE — the Some
/// reconstruction may only reuse the ORIGINAL payload.
#[test]
fn filter_forged_reconstruct_off_substitute_local_declines() {
    let mut func = load_dump(FILTER);
    // bb3 = KEEP arm: `_9 = Move _4`. Re-point the source to `_5` (the Bool temp).
    for s in &mut block_mut(&mut func, 3).stmts {
        if let Statement::Assign {
            place,
            rvalue: Rvalue::Use(Operand::Move(p) | Operand::Copy(p)),
            ..
        } = s
        {
            if place.local == 9 && p.local == 4 {
                p.local = 5; // reconstruct off a DIFFERENT value.
            }
        }
    }
    let callees = registry("filter_pos::{closure#0}");
    assert!(
        sem_adt_filter_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a reconstruct off a substitute local must decline"
    );
}

/// FORGERY: retarget the KEEP arm's payload Drop (bb4 `Drop(_4)`) to the return
/// `_0` — a Drop of anything but the bare payload/closure declines.
#[test]
fn filter_drop_of_non_payload_place_declines() {
    let mut func = load_dump(FILTER);
    if let Terminator::Drop { place, .. } = &mut block_mut(&mut func, 4).terminator {
        place.local = 0;
    }
    let callees = registry("filter_pos::{closure#0}");
    assert!(sem_adt_filter_compose_of_discriminant_switch(&func, &callees).is_none());
}

/// FORGERY: retarget the KEEP arm's `Goto JOIN` to the unwind `Resume` block (bb8)
/// — a control-flow edge into the unwind sink must decline (it trips the
/// join-convergence + fail-closed reachability gates; a reachable Resume is an
/// unmodeled path).
#[test]
fn filter_edge_into_resume_declines() {
    let mut func = load_dump(FILTER);
    block_mut(&mut func, 3).terminator = Terminator::Goto(trust_types::BlockId(8));
    let callees = registry("filter_pos::{closure#0}");
    assert!(
        sem_adt_filter_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a KEEP-arm edge into the Resume sink must decline"
    );
}

/// An uncertified filter closure stays declined (empty registry baseline).
#[test]
fn filter_empty_registry_declines() {
    let func = load_dump(FILTER);
    let callees: BTreeMap<String, CalleeFact> = BTreeMap::new();
    assert!(sem_adt_filter_compose_of_discriminant_switch(&func, &callees).is_none());
}

/// THE MANDATORY adversarial gate: a registry containing ONLY a DIFFERENT
/// nested-module closure `inner::map_add1::{closure#0}` whose def-path
/// SUFFIX-matches the env's `map_add1::{closure#0}` must DECLINE — never
/// resolve-by-suffix (which would borrow the wrong closure's certificate).
#[test]
fn exact_match_only_declines_suffix_decoy() {
    let func = load_dump(MAP_NONCAP);
    let callees = registry("inner::map_add1::{closure#0}"); // ONLY the decoy.
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a unique-suffix nested-module decoy must NOT resolve on the closure lane"
    );
}

/// Regression pin: the EXACT-only resolver declines exactly where the
/// (suffix-admitting) production resolver would silently misresolve.
#[test]
fn exact_resolver_declines_where_suffix_resolver_matches() {
    let mut callees = BTreeMap::new();
    callees.insert("inner::map_add1::{closure#0}".to_string(), closure_fact());
    // The production resolver ADMITS the unique suffix (the unsound behavior).
    assert!(
        resolve_certified_callee(&callees, "map_add1::{closure#0}").is_some(),
        "the production resolver admits the unique `::`-suffix"
    );
    // The closure-lane EXACT resolver DECLINES it.
    assert!(
        resolve_certified_callee_exact(&callees, "map_add1::{closure#0}").is_none(),
        "the EXACT-only resolver must reject a suffix-only match"
    );
    // Both agree on an EXACT hit.
    let mut exact = BTreeMap::new();
    exact.insert("map_add1::{closure#0}".to_string(), closure_fact());
    assert!(resolve_certified_callee_exact(&exact, "map_add1::{closure#0}").is_some());
}

/// Trust: W6 increment-3 (CAPTURING closures, 2026-07-18) — the increment-1
/// `upvars ≠ [] ⇒ decline` pin is SUPERSEDED. A capturing closure whose call
/// kind is IMMUTABLE (`Fn`/`FnOnce`) and whose leaf is a certified spec-free
/// callee is now ADMITTED: the env is passed WHOLE (captures ride inside the env
/// VALUE the callResult carrier pins), the SAME MODEL-ONLY claim the non-capturing
/// lane already makes — NOT an `f(x, k)` value claim over the captures.
#[test]
fn capturing_closure_admitted_when_certified() {
    let func = load_dump(MAP_CAP);
    let callees = registry("map_cap::{closure#0}");
    let shape = sem_adt_map_compose_of_discriminant_switch(&func, &callees)
        .expect("a capturing FnOnce closure with a certified spec-free leaf is now admitted");
    // The env operand is the BARE closure-param `Var` (the captures live inside it).
    assert!(
        matches!(shape.env_operand, SemOperand::Var(_)),
        "the env operand must be the bare closure-param Var (captures ride inside)"
    );
    assert_eq!(shape.callee, "map_cap::{closure#0}");
}

#[test]
fn empty_registry_declines() {
    let func = load_dump(MAP_NONCAP);
    let callees: BTreeMap<String, CalleeFact> = BTreeMap::new();
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn requires_bearing_closure_declines() {
    let func = load_dump(MAP_NONCAP);
    let mut fact = closure_fact();
    // A non-vacuous requires (a real declared precondition) is DEFERRED (increment 2).
    fact.requires = Some(vec![trust_types::Formula::Bool(true)]);
    let mut callees = BTreeMap::new();
    callees.insert("map_add1::{closure#0}".to_string(), fact);
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn unknown_requires_closure_declines() {
    let func = load_dump(MAP_NONCAP);
    let mut fact = closure_fact();
    fact.requires = None; // an unparsed precondition — fail closed.
    let mut callees = BTreeMap::new();
    callees.insert("map_add1::{closure#0}".to_string(), fact);
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn wrong_arg_count_closure_declines() {
    let func = load_dump(MAP_NONCAP);
    let mut fact = closure_fact();
    fact.arg_count = 1; // must be env + untupled x == 2.
    let mut callees = BTreeMap::new();
    callees.insert("map_add1::{closure#0}".to_string(), fact);
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

// --- programmatic forgery mutations on the harvested body ---

fn block_mut(func: &mut VerifiableFunction, id: usize) -> &mut trust_types::BasicBlock {
    func.body.blocks.iter_mut().find(|b| b.id == trust_types::BlockId(id)).expect("block")
}

#[test]
fn wrong_downcast_variant_declines() {
    let mut func = load_dump(MAP_NONCAP);
    // bb3 = call setup: flip the payload extract's Downcast(1) to Downcast(0).
    for s in &mut block_mut(&mut func, 3).stmts {
        if let Statement::Assign { rvalue: Rvalue::Use(Operand::Move(p) | Operand::Copy(p)), .. } = s {
            if matches!(p.projections.as_slice(), [Projection::Downcast(_), Projection::Field(_)]) {
                p.projections[0] = Projection::Downcast(0); // != call_tag (1)
            }
        }
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a TAG↔DOWNCAST mismatch must decline"
    );
}

#[test]
fn tuple_arity_two_declines() {
    let mut func = load_dump(MAP_NONCAP);
    for s in &mut block_mut(&mut func, 3).stmts {
        if let Statement::Assign { rvalue: Rvalue::Aggregate(AggregateKind::Tuple, elems), .. } = s {
            // Duplicate the sole element ⇒ arity 2 ≠ closure call arity 1.
            let e0 = elems[0].clone();
            elems.push(e0);
        }
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn tuple_element_not_payload_declines() {
    let mut func = load_dump(MAP_NONCAP);
    for s in &mut block_mut(&mut func, 3).stmts {
        if let Statement::Assign { rvalue: Rvalue::Aggregate(AggregateKind::Tuple, elems), .. } = s {
            // The sole element is a DIFFERENT local (the env temp _6), not the
            // Downcast-field payload temp _4.
            if let Operand::Copy(p) | Operand::Move(p) = &mut elems[0] {
                p.local = 6;
            }
        }
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn drop_of_non_closure_place_declines() {
    let mut func = load_dump(MAP_NONCAP);
    // bb2 = None arm: retarget the Drop from the closure param _2 to self _1.
    if let Terminator::Drop { place, .. } = &mut block_mut(&mut func, 2).terminator {
        place.local = 1; // Drop(_1) — not the bare closure param.
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "a Drop of anything but the bare closure param must decline"
    );
}

#[test]
fn env_field_projection_declines() {
    let mut func = load_dump(MAP_NONCAP);
    // Turn the env chain `_6 := Move(_2)` into a field read `_6 := Move(_2.0)`
    // (the capturing-upvar shape) — must decline even though upvars is [].
    for s in &mut block_mut(&mut func, 3).stmts {
        if let Statement::Assign { rvalue: Rvalue::Use(Operand::Move(p) | Operand::Copy(p)), .. } = s {
            if p.local == 2 && p.projections.is_empty() {
                p.projections.push(Projection::Field(0));
            }
        }
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn effectful_residue_statement_declines() {
    let mut func = load_dump(MAP_NONCAP);
    block_mut(&mut func, 4)
        .stmts
        .push(Statement::Deinit { place: trust_types::Place::local(5) });
    let callees = registry("map_add1::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "an effectful non-Assign statement must not be treated as a storage marker"
    );
}

#[test]
fn payload_definition_after_tuple_use_declines() {
    let mut func = load_dump(MAP_NONCAP);
    let stmts = &mut block_mut(&mut func, 3).stmts;
    let payload_index = stmts
        .iter()
        .position(|s| {
            matches!(
                s,
                Statement::Assign {
                    rvalue: Rvalue::Use(Operand::Move(p) | Operand::Copy(p)),
                    ..
                } if matches!(p.projections.as_slice(), [Projection::Downcast(_), Projection::Field(_)])
            )
        })
        .expect("payload assignment");
    let payload = stmts.remove(payload_index);
    let tuple_index = stmts
        .iter()
        .position(|s| {
            matches!(
                s,
                Statement::Assign { rvalue: Rvalue::Aggregate(AggregateKind::Tuple, _), .. }
            )
        })
        .expect("tuple assignment");
    stmts.insert(tuple_index + 1, payload);
    let callees = registry("map_add1::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "the payload definition must precede the tuple use at the exact statement site"
    );
}

#[test]
fn duplicate_block_identity_declines() {
    let mut func = load_dump(MAP_NONCAP);
    let duplicate = func.body.blocks[1].clone();
    func.body.blocks.push(duplicate);
    let callees = registry("map_add1::{closure#0}");
    assert!(
        sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none(),
        "duplicate block identities must not hide an unvalidated block behind `find`"
    );
}

#[test]
fn non_exhaustive_switch_declines() {
    let mut func = load_dump(MAP_NONCAP);
    // Flip the exhaustiveness flag on bb0's SwitchInt — a non-exhaustive
    // discriminant switch (otherwise not proven Unreachable) declines.
    if let Terminator::SwitchInt { exhaustive_enum_unreachable, .. } =
        &mut block_mut(&mut func, 0).terminator
    {
        *exhaustive_enum_unreachable = false;
    }
    let callees = registry("map_add1::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}

#[test]
fn second_call_in_none_arm_declines() {
    let mut func = load_dump(MAP_NONCAP);
    // Replace the None arm's `Drop(_2) -> JOIN` with a SECOND Call terminator.
    // The recognizer requires the None arm to end in Drop (and admits exactly one
    // Call, in the CALL-setup block), so a second call declines.
    block_mut(&mut func, 2).terminator = Terminator::Call {
        func: "<{closure@main.rs:5:11: 5:14} as std::ops::FnOnce<(i32,)>>::call_once".into(),
        args: vec![Operand::Move(trust_types::Place { local: 6, projections: vec![] })],
        dest: trust_types::Place { local: 5, projections: vec![] },
        target: Some(trust_types::BlockId(5)),
        unwind: trust_types::UnwindEdge::Unreachable,
        span: trust_types::SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
    };
    let callees = registry("map_add1::{closure#0}");
    assert!(sem_adt_map_compose_of_discriminant_switch(&func, &callees).is_none());
}
