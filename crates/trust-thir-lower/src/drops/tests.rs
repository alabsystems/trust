//! Unit tests for the drop planner's pure kernel (`drops::kernel`): the elaboration rules on
//! small control-flow shapes, driven through the same state / edge / plan API the THIR walker
//! uses, with no `TyCtxt`. The THIR walker itself and the placement hooks are pinned end to end
//! (`tests/ui/trust/trust_ir_lower_drops_placed.rs`, `tests/run-make/trust-effect-conservation`).
//!
//! Each case is the shape design §7.2 names; the comment says what rustc's elaboration does
//! with it (`rustc_mir_transform::elaborate_drops`), which is what the plan must reproduce.

use super::kernel::{Edge, ExitClass, ExitKey, Infeasible, Init, Plan, State, Style};
use super::{DropIdentity, DropKey, LiveStyle};

/// The drops an edge crosses, in emission order, classified from `st`.
fn edge(key: ExitKey, class: ExitClass, st: &State, frames: &[&[usize]]) -> Edge {
    let mut drops = Vec::new();
    for f in frames.iter().rev() {
        for r in f.iter().rev() {
            drops.push((*r, Style::of(st.get(*r))));
        }
    }
    Edge { key, class, drops }
}

fn plan(edges: Vec<Edge>) -> Plan {
    Plan { edges }
}

/// `fn f(x: String) {}` — the parameter is initialized on every path to the body end: one
/// static drop at `BodyEnd`.
#[test]
fn a_parameter_never_moved_is_dropped_statically_at_the_body_end() {
    let mut st = State::entry(1);
    st.set(0, Init::Init);
    let p = plan(vec![edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &st, &[&[0]])]);
    assert_eq!(p.feasible(), Ok(()));
    assert_eq!(p.emission(ExitKey::BodyEnd), vec![0]);
    assert_eq!(p.required(), [ExitKey::BodyEnd].into_iter().collect());
    assert_eq!(p.joined().get(&(0, ExitClass::ArgsFallthrough)), Some(&Style::Static));
}

/// `fn f(x: String) { consume(x) }` — moved on every path: the drop is dead, nothing is
/// emitted and no exit is required.
#[test]
fn a_value_moved_on_every_path_is_dead() {
    let mut st = State::entry(1);
    st.set(0, Init::Init);
    st.set(0, Init::Uninit); // `consume(x)`
    let p = plan(vec![edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &st, &[&[0]])]);
    assert_eq!(p.feasible(), Ok(()));
    assert!(p.emission(ExitKey::BodyEnd).is_empty());
    assert!(p.required().is_empty());
    assert_eq!(p.joined().get(&(0, ExitClass::ArgsFallthrough)), Some(&Style::Dead));
}

/// `fn f(x: String, c: bool) { if c { consume(x) } }` — moved on one arm: maybe-initialized at
/// the body end, so rustc guards the drop with a flag. One edge, `Conditional`: this cut cannot
/// place it without a flag and the plan is infeasible (the body keeps no drop at all).
#[test]
fn a_conditional_move_needs_a_flag_and_is_refused() {
    let mut entry = State::entry(1);
    entry.set(0, Init::Init);
    let mut then_arm = entry.clone();
    then_arm.set(0, Init::Uninit);
    let joined = then_arm.join(&entry);
    assert_eq!(joined.get(0), Init::Maybe);
    let p = plan(vec![edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &joined, &[&[0]])]);
    assert_eq!(p.feasible(), Err(Infeasible::ConditionalOnEdge));
}

/// `fn f(x: String, c: bool) { if c { consume(x); return; } }` — two edges of different classes:
/// the return tree's drop is dead (moved), the fallthrough's static. Both placeable statically;
/// each class matches rustc's node.
#[test]
fn a_move_before_an_early_return_is_dead_on_that_edge_only() {
    let mut entry = State::entry(1);
    entry.set(0, Init::Init);
    let mut ret = entry.clone();
    ret.set(0, Init::Uninit);
    let p = plan(vec![
        edge(ExitKey::Return(7), ExitClass::ReturnTree, &ret, &[&[0]]),
        edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &entry, &[&[0]]),
    ]);
    assert_eq!(p.feasible(), Ok(()));
    assert!(p.emission(ExitKey::Return(7)).is_empty());
    assert_eq!(p.emission(ExitKey::BodyEnd), vec![0]);
    let j = p.joined();
    assert_eq!(j.get(&(0, ExitClass::ReturnTree)), Some(&Style::Dead));
    assert_eq!(j.get(&(0, ExitClass::ArgsFallthrough)), Some(&Style::Static));
}

/// Two `return`s, one after a move: rustc builds ONE return-tree node for `x`, reached in both
/// states, and guards it with a flag (`Conditional`). The producer places the drop statically on
/// the edge where `x` is live and nothing on the other — the same drops on every path — and its
/// joined class style is `Conditional`, which is what the oracle reports for that node.
#[test]
fn two_returns_share_one_tree_node_whose_joined_style_is_conditional() {
    let mut live = State::entry(1);
    live.set(0, Init::Init);
    let mut moved = live.clone();
    moved.set(0, Init::Uninit);
    let p = plan(vec![
        edge(ExitKey::Return(1), ExitClass::ReturnTree, &live, &[&[0]]),
        edge(ExitKey::Return(2), ExitClass::ReturnTree, &moved, &[&[0]]),
    ]);
    assert_eq!(p.feasible(), Ok(()));
    assert_eq!(p.emission(ExitKey::Return(1)), vec![0]);
    assert!(p.emission(ExitKey::Return(2)).is_empty());
    assert_eq!(p.required(), [ExitKey::Return(1)].into_iter().collect());
    assert_eq!(p.joined().get(&(0, ExitClass::ReturnTree)), Some(&Style::Conditional));
}

/// `loop { let s = make(); if c { break } consume(s); }` — loop-carried: `s` is re-initialized
/// every iteration, so at the `break` it is live (static drop on the break edge) and at the body
/// end it is moved (dead). The loop head fixpoint does not change `s` (it is out of scope there).
#[test]
fn a_loop_body_binding_is_live_at_the_break_and_dead_at_the_back_edge() {
    let mut head = State::entry(1);
    head.set(0, Init::Init); // `let s = make();`
    let at_break = head.clone();
    let mut at_end = head.clone();
    at_end.set(0, Init::Uninit); // `consume(s)`
    // The back edge feeds the head; joining it changes nothing for a root re-declared there.
    let mut next_head = head.join(&at_end);
    next_head.set(0, Init::Init);
    assert_eq!(next_head, head);
    let p = plan(vec![
        edge(ExitKey::Break(3), ExitClass::BreakTree(9), &at_break, &[&[0]]),
        edge(ExitKey::BlockEnd(4), ExitClass::BlockFallthrough(4), &at_end, &[&[0]]),
    ]);
    assert_eq!(p.feasible(), Ok(()));
    assert_eq!(p.emission(ExitKey::Break(3)), vec![0]);
    assert!(p.emission(ExitKey::BlockEnd(4)).is_empty());
}

/// A value declared BEFORE a loop and moved inside it: at the loop head the back edge carries
/// "moved", so the head is maybe-initialized; any exit after the loop sees `Maybe`. rustc needs a
/// flag; the plan is infeasible.
#[test]
fn a_move_inside_a_loop_of_an_outer_value_makes_the_head_maybe() {
    let mut entry = State::entry(1);
    entry.set(0, Init::Init);
    let mut back = entry.clone();
    back.set(0, Init::Uninit);
    let head = entry.join(&back);
    assert_eq!(head.get(0), Init::Maybe);
    let p = plan(vec![edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &head, &[&[0]])]);
    assert_eq!(p.feasible(), Err(Infeasible::ConditionalOnEdge));
}

/// `'a: loop { let a = A; loop { let b = B; break 'a; } }` — the break crosses two block frames:
/// the drops run innermost first, reverse schedule order within a frame (`b`, then `a`).
#[test]
fn a_break_out_of_two_scopes_drops_innermost_first() {
    let mut st = State::entry(2);
    st.set(0, Init::Init);
    st.set(1, Init::Init);
    let e = edge(ExitKey::Break(5), ExitClass::BreakTree(1), &st, &[&[0], &[1]]);
    assert_eq!(e.drops, vec![(1, Style::Static), (0, Style::Static)]);
    // Two bindings in ONE frame drop in reverse declaration order too.
    let e = edge(ExitKey::BlockEnd(2), ExitClass::BlockFallthrough(2), &st, &[&[0, 1]]);
    assert_eq!(e.drops, vec![(1, Style::Static), (0, Style::Static)]);
}

/// `fn f(s: String) -> Result<u8, E> { let v = g()?; .. }` — the `?` early return is a `return`
/// edge: it drops every frame including the parameters.
#[test]
fn a_question_mark_return_drops_every_frame() {
    let mut st = State::entry(2);
    st.set(0, Init::Init); // parameter `s`
    st.set(1, Init::Init); // an earlier binding
    let e = edge(ExitKey::Return(11), ExitClass::ReturnTree, &st, &[&[0], &[1]]);
    assert_eq!(e.drops, vec![(1, Style::Static), (0, Style::Static)]);
}

/// Drop-and-replace of a maybe-initialized local (`let mut x; if c { x = a() } x = b();`): the
/// `Replace` edge sees `Maybe` — a flag in rustc — and the plan is infeasible; of an initialized
/// one, a static drop of the old value; of an uninitialized one, a dead drop.
#[test]
fn drop_and_replace_follows_the_state_at_the_assignment() {
    for (init, want) in [
        (Init::Init, Ok(vec![0])),
        (Init::Uninit, Ok(vec![])),
        (Init::Maybe, Err(Infeasible::ConditionalOnEdge)),
    ] {
        let mut st = State::entry(1);
        st.set(0, init);
        let p = plan(vec![Edge {
            key: ExitKey::Replace(8),
            class: ExitClass::Replace(8),
            drops: vec![(0, Style::of(st.get(0)))],
        }]);
        match want {
            Ok(roots) => {
                assert_eq!(p.feasible(), Ok(()), "{init:?}");
                assert_eq!(p.emission(ExitKey::Replace(8)), roots, "{init:?}");
            }
            Err(e) => assert_eq!(p.feasible(), Err(e), "{init:?}"),
        }
    }
}

/// An unreachable edge (after `return`) contributes nothing to a join.
#[test]
fn an_unreachable_side_contributes_nothing_to_a_join() {
    let mut live = State::entry(1);
    live.set(0, Init::Init);
    let dead = State::unreachable(1);
    assert_eq!(live.join(&dead), live);
    assert_eq!(dead.join(&live), live);
}

/// The placement tripwire's input: an exit with a static drop is REQUIRED; one whose drops are
/// all dead is not (its hook may or may not fire).
#[test]
fn only_exits_with_a_static_drop_are_required() {
    let mut st = State::entry(2);
    st.set(0, Init::Init);
    let p = plan(vec![
        edge(ExitKey::BlockEnd(1), ExitClass::BlockFallthrough(1), &st, &[&[1]]),
        edge(ExitKey::BodyEnd, ExitClass::ArgsFallthrough, &st, &[&[0]]),
    ]);
    assert_eq!(p.required(), [ExitKey::BodyEnd].into_iter().collect());
}

/// The same exit recorded twice with different drops is a walker defect, and refused.
#[test]
fn an_exit_planned_twice_differently_is_refused() {
    let p = plan(vec![
        Edge {
            key: ExitKey::BodyEnd,
            class: ExitClass::ArgsFallthrough,
            drops: vec![(0, Style::Static)],
        },
        Edge { key: ExitKey::BodyEnd, class: ExitClass::ArgsFallthrough, drops: vec![] },
    ]);
    assert_eq!(p.feasible(), Err(Infeasible::KeyConflict));
}

/// The interpretation hazard (design §1.6): a body carrying an `Inst::Drop` is forced NOT
/// interpretation-eligible whatever its own `contains_call` bookkeeping says, so it is deferred
/// to the crate seam (`differential::deferred_to_seam_parts`) and `compare` returns `NotRun`
/// before the interpreter can meet the instruction and report its `TypeError` as a THIR defect.
#[test]
fn a_body_with_a_drop_is_never_interpreted() {
    use crate::differential::deferred_to_seam_parts;
    let forced = super::drops_force_not_interpretable(false, true);
    assert!(forced);
    // Clean, no pending const: deferred only because of the forcing.
    assert!(deferred_to_seam_parts(true, true, forced));
    assert!(!deferred_to_seam_parts(
        true,
        true,
        super::drops_force_not_interpretable(false, false)
    ));
    // And the module reading is structural: an `Inst::Drop` anywhere in the function.
    use trust_ir::{Block, BlockId, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId};
    let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body.push(
        InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None })
            .with_result(ValueId::new(1)),
    );
    b.body.push(InstrNode::new(Inst::Drop { ty: Ty::I64, ptr: ValueId::new(1) }));
    b.body.push(InstrNode::new(Inst::Return { values: vec![] }));
    f.blocks.push(b);
    assert!(super::function_has_drop(&f));
    f.blocks[0].body.remove(1);
    assert!(!super::function_has_drop(&f));
}

/// The claim's comparison key is (identity, type, span, style): two drops of the same local
/// with different styles are different drops.
#[test]
fn a_drop_key_distinguishes_style() {
    let k = |style| DropKey {
        identity: DropIdentity::Param(0),
        ty: 1,
        span: rustc_span::DUMMY_SP,
        style,
    };
    assert_ne!(k(LiveStyle::Static), k(LiveStyle::Conditional));
}

/// trust-ir v55 refuses a `Drop` of a trivially droppable or refined type (`NonCanonicalDrop`,
/// which fails the whole crate module), so a root spelled at one is not placed, on the promoted
/// slot path as on the SSA path: an `Option<(i32, Vec<u8>)>` collapsed to its discriminant
/// `bool`, a promoted `(i32, Option<(i32, Vec<u8>)>)` spelled `(i32, bool)`, a scalar, a
/// pointer, or a tuple or array of them. A struct, or a non-empty array of one, keeps its `Drop`.
#[test]
fn a_root_spelled_at_a_trivially_droppable_or_refined_type_has_no_drop_spelling() {
    use trust_ir::{PredId, StructId, Ty, TyId};
    let types = vec![Ty::Struct(StructId::new(0)), Ty::U8];
    for ty in [
        Ty::Bool,
        Ty::I32,
        Ty::Unit,
        Ty::Ptr,
        Ty::Tuple(vec![Ty::I32, Ty::Bool]),
        Ty::Array(TyId::new(1), 4),
        Ty::Array(TyId::new(0), 0),
    ] {
        let why = super::unspellable_drop_type(&ty, &types)
            .unwrap_or_else(|| panic!("{ty} must have no drop spelling"));
        assert!(why.contains("trivially droppable"), "{why}");
    }
    let refined = Ty::Refine(TyId::new(0), PredId::new(0));
    let why = super::unspellable_drop_type(&refined, &types).expect("a refinement is not spelled");
    assert!(why.contains("refined"), "{why}");
    for ty in [Ty::Struct(StructId::new(0)), Ty::Array(TyId::new(0), 2)] {
        assert_eq!(super::unspellable_drop_type(&ty, &types), None, "{ty} keeps its drop");
    }
}

// ---------------------------------------------------------------------------------------------
// Step 2 increment 4b residuals: temporaries, drop-and-replace through a pointer, the guards.
// ---------------------------------------------------------------------------------------------

/// A root declared on ONE side of a branch (a temporary created in a then-arm whose scope is
/// outside the `if`) is `Uninit` on the other side: the join is `Maybe`, never silently `Dead`.
/// (Before the residuals the join zipped the two vectors and DROPPED the root, which read as
/// `Uninit` — a dead drop where rustc needs a flag.)
#[test]
fn a_root_declared_on_one_side_of_a_join_is_maybe_after_it() {
    let at_branch = State::entry(1);
    let mut then_arm = at_branch.clone();
    then_arm.grow(2);
    then_arm.set(1, Init::Init);
    let joined = at_branch.join(&then_arm);
    assert_eq!(joined.init.len(), 2);
    assert_eq!(joined.get(1), Init::Maybe);
    assert_eq!(then_arm.join(&at_branch).get(1), Init::Maybe);
    // An unreachable side still contributes nothing.
    let mut dead = State::unreachable(1);
    dead.grow(1);
    assert_eq!(dead.join(&then_arm).get(1), Init::Init);
}

/// `fn f(c: bool) -> usize { let n = g(&mk()); if c { return n; } n }` — a statement's
/// temporary is dropped at the statement's end (its own class), and a `return` crossing an
/// enclosing scope's temporary drops it on the return edge (the return tree). Each class has
/// its one node, statically.
#[test]
fn a_temporary_is_dropped_at_its_scope_end_and_on_a_return_crossing_it() {
    let mut st = State::entry(2);
    st.set(0, Init::Init); // the statement temporary
    st.set(1, Init::Init); // a temporary of the body's tail scope
    let stmt_end = edge(ExitKey::StmtEnd(3), ExitClass::StmtFallthrough(3), &st, &[&[0]]);
    let ret = edge(ExitKey::Return(9), ExitClass::ReturnTree, &st, &[&[1]]);
    let tail = edge(ExitKey::ScopeEnd(4), ExitClass::ScopeFallthrough(4), &st, &[&[1]]);
    let p = plan(vec![stmt_end, ret, tail]);
    assert_eq!(p.feasible(), Ok(()));
    assert_eq!(p.emission(ExitKey::StmtEnd(3)), vec![0]);
    assert_eq!(p.emission(ExitKey::Return(9)), vec![1]);
    assert_eq!(p.emission(ExitKey::ScopeEnd(4)), vec![1]);
    let j = p.joined();
    assert_eq!(j.get(&(0, ExitClass::StmtFallthrough(3))), Some(&Style::Static));
    assert_eq!(j.get(&(1, ExitClass::ReturnTree)), Some(&Style::Static));
    assert_eq!(j.get(&(1, ExitClass::ScopeFallthrough(4))), Some(&Style::Static));
    assert_eq!(
        p.required(),
        [ExitKey::StmtEnd(3), ExitKey::Return(9), ExitKey::ScopeEnd(4)].into_iter().collect()
    );
}

/// A block's fallthrough drops its `let` bindings (innermost first) and THEN the temporaries of
/// the block's own scope: `ast_block` pops the remainder scopes before the block scope.
#[test]
fn a_block_end_drops_its_bindings_before_its_own_temporaries() {
    let mut st = State::entry(3);
    st.set(0, Init::Init); // a temporary of the block's own scope
    st.set(1, Init::Init); // `let a`
    st.set(2, Init::Init); // `let b`
    let e = edge(ExitKey::BlockEnd(5), ExitClass::BlockFallthrough(5), &st, &[&[0], &[1, 2]]);
    let p = plan(vec![e]);
    assert_eq!(p.emission(ExitKey::BlockEnd(5)), vec![2, 1, 0]);
}

/// `*p = v` through a `&mut`: one unconditional drop of the old pointee at the assignment.
#[test]
fn a_drop_and_replace_through_a_pointer_is_static_at_the_assignment() {
    let p = plan(vec![Edge {
        key: ExitKey::Replace(11),
        class: ExitClass::Replace(11),
        drops: vec![(0, Style::Static)],
    }]);
    assert_eq!(p.feasible(), Ok(()));
    assert_eq!(p.emission(ExitKey::Replace(11)), vec![0]);
    assert_eq!(p.joined().get(&(0, ExitClass::Replace(11))), Some(&Style::Static));
}

/// A CFG of `blocks` (id, successors), each block in `with_drop` carrying one `Inst::Drop`.
fn cfg(blocks: &[(u32, &[u32])], with_drop: &[u32]) -> trust_ir::Module {
    use trust_ir::{Block, BlockId, FuncId, FuncTyId, Function, Inst, InstrNode, Ty, ValueId};
    let mut m = trust_ir::Module::new("t");
    let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    for (id, succ) in blocks {
        let mut b = Block::new(BlockId::new(*id));
        if with_drop.contains(id) {
            b.body.push(InstrNode::new(Inst::Drop { ty: Ty::Ptr, ptr: ValueId::new(0) }));
        }
        let term = match succ {
            [] => Inst::Return { values: Vec::new() },
            [t] => Inst::Br { target: BlockId::new(*t), args: Vec::new() },
            [t, e, ..] => Inst::CondBr {
                cond: ValueId::new(1),
                then_target: BlockId::new(*t),
                then_args: Vec::new(),
                else_target: BlockId::new(*e),
                else_args: Vec::new(),
            },
        };
        b.body.push(InstrNode::new(term));
        f.blocks.push(b);
    }
    m.functions.push(f);
    m
}

fn fired(
    key: ExitKey,
    blocks: &[u32],
) -> std::collections::BTreeMap<ExitKey, Vec<trust_ir::BlockId>> {
    [(key, blocks.iter().map(|b| trust_ir::BlockId::new(*b)).collect())].into_iter().collect()
}

/// THE DOUBLE-PLACEMENT GUARD (`finish_drops`). One exit lowered twice IN SEQUENCE (a lane that
/// lowered the same scope again after the first lowering) would run its drops twice on one
/// execution — a double drop the oracle comparison cannot see (it compares one node per class).
/// Two placements on disjoint paths (an or-pattern arm lowered twice, a duplicated tail) are
/// one drop per execution; a placement inside a loop runs once per iteration.
#[test]
fn an_exit_placed_twice_on_one_path_is_refused_and_on_disjoint_paths_is_not() {
    use super::placed_twice_on_one_path as twice;
    let k = ExitKey::ScopeEnd(7);
    // 0 -> 1 -> 2 -> ret: both firings on one path.
    let seq = cfg(&[(0, &[1]), (1, &[2]), (2, &[])], &[1, 2]);
    assert_eq!(twice(&seq, &fired(k, &[1, 2])), Some(k));
    // Twice in ONE block.
    let one = cfg(&[(0, &[])], &[0]);
    assert_eq!(twice(&one, &fired(k, &[0, 0])), Some(k));
    // 0 -> {1, 2} -> 3: disjoint arms.
    let diamond = cfg(&[(0, &[1, 2]), (1, &[3]), (2, &[3]), (3, &[])], &[1, 2]);
    assert_eq!(twice(&diamond, &fired(k, &[1, 2])), None);
    // A loop 0 -> 1 -> {1, 2}: one placement per iteration is not a repeat; two placements in
    // the body, one after the other, are.
    let lp = cfg(&[(0, &[1]), (1, &[3, 2]), (3, &[1]), (2, &[])], &[1, 3]);
    assert_eq!(twice(&lp, &fired(k, &[1])), None);
    assert_eq!(twice(&lp, &fired(k, &[1, 3])), Some(k));
}

/// A value partially moved out of (`if let Some(s) = o { take(s) }`): its drop is OPEN. On an
/// edge where the open drop's elaboration drops nothing (every needs-drop part moved or in an
/// inactive variant) nothing is emitted and no exit is required; on an edge where it would drop
/// part of the value (field drops, a variant switch) the plan is infeasible — refused by name,
/// never approximated by a whole drop or by nothing.
#[test]
fn an_open_drop_is_placed_only_where_it_drops_nothing() {
    let nothing = plan(vec![Edge {
        key: ExitKey::BodyEnd,
        class: ExitClass::ArgsFallthrough,
        drops: vec![(0, Style::Open)],
    }]);
    assert_eq!(nothing.feasible(), Ok(()));
    assert!(nothing.emission(ExitKey::BodyEnd).is_empty());
    assert!(nothing.required().is_empty());
    let live = plan(vec![Edge {
        key: ExitKey::BodyEnd,
        class: ExitClass::ArgsFallthrough,
        drops: vec![(0, Style::OpenLive)],
    }]);
    assert_eq!(live.feasible(), Err(Infeasible::OpenOnEdge));
}

// ---- The 4b residuals review (2026-10-08) ----

/// A catch-all arm is entered from the discriminant switch's otherwise edge, where only the
/// variants the arms BEFORE it test are inactive. `match o { None => 0, _ => 1, Some(g) => .. }`:
/// the unreachable `Some(g)` arm after `_` tests nothing on that edge, and `o` may be `Some(g)`
/// in `_`, its payload live (rustc drops it). The first cut took the set over EVERY arm (`{0, 1}`
/// here), killed the payload's path in `_` and placed nothing where rustc drops it.
#[test]
fn a_catch_all_kills_only_the_variants_tested_before_it() {
    use super::variants_tested_before as before;
    let tops = [Some(0), None, Some(1)];
    assert_eq!(before(&tops, 1), [0].into_iter().collect());
    assert!(before(&tops, 0).is_empty());
    assert_eq!(before(&tops, 3), [0, 1].into_iter().collect());
    assert_eq!(before(&tops, 9), [0, 1].into_iter().collect());
}

/// The placement's validation guard compares the rendered errors as a MULTISET: a placement
/// that adds one error while the stripped module carries a different one of its own (equal
/// counts) still made the module worse — the first cut's count comparison passed it.
#[test]
fn a_new_validation_error_is_found_whatever_the_counts() {
    use super::new_validation_error as new;
    assert_eq!(new(&["A", "B"], &["A", "C"]), Some("\"B\"".to_string()));
    assert_eq!(new(&["A", "A"], &["A"]), Some("\"A\"".to_string()));
    assert_eq!(new(&["A"], &["A", "C"]), None);
    assert_eq!(new::<&str>(&[], &["C"]), None);
}

/// THE VALIDATION GUARD FIRES (`finish_drops`): a drop through a pointer nothing defines makes
/// the module invalid where the same module without the drop is not worse; a module the drop
/// does not make worse passes.
#[test]
fn the_validation_guard_fires_on_a_drop_that_breaks_the_module() {
    let slots = std::collections::BTreeSet::new();
    let with_drop = cfg(&[(0, &[])], &[0]);
    assert!(super::validation_regression(&with_drop, &slots).is_some());
    let without = cfg(&[(0, &[])], &[]);
    assert_eq!(super::validation_regression(&without, &slots), None);
}

mod home {
    use trust_ir::{FuncId, Inst, InstrNode, Ty, ValueId};

    pub(super) fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }
    pub(super) fn t() -> Ty {
        Ty::I64
    }
    pub(super) fn call(r: u32, args: &[u32]) -> InstrNode {
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: args.iter().map(|a| v(*a)).collect(),
        })
        .with_result(v(r))
    }
    pub(super) fn alloca(r: u32) -> InstrNode {
        InstrNode::new(Inst::Alloca { ty: t(), count: None, align: None }).with_result(v(r))
    }
    pub(super) fn store(ty: Ty, value: u32, ptr: u32) -> InstrNode {
        InstrNode::new(Inst::Store {
            ty,
            ptr: v(ptr),
            value: v(value),
            volatile: false,
            align: None,
        })
    }
    pub(super) fn load(r: u32, ty: Ty, ptr: u32) -> InstrNode {
        InstrNode::new(Inst::Load { ty, ptr: v(ptr), volatile: false, align: None })
            .with_result(v(r))
    }
    pub(super) fn field(r: u32, of: u32) -> InstrNode {
        InstrNode::new(Inst::ExtractField { ty: Ty::I32, aggregate: v(of), field: 0 })
            .with_result(v(r))
    }
    pub(super) fn ret(x: u32) -> InstrNode {
        InstrNode::new(Inst::Return { values: vec![v(x)] })
    }
    pub(super) fn drop(ptr: u32) -> InstrNode {
        InstrNode::new(Inst::Drop { ty: t(), ptr: v(ptr) })
    }
    /// `%1 = mk(); %2 = alloca; store %1, %2` — the borrow's slot, then `rest`.
    pub(super) fn body(rest: Vec<InstrNode>) -> Vec<InstrNode> {
        let mut b = vec![call(1, &[]), alloca(2), store(t(), 1, 2)];
        b.extend(rest);
        b
    }
    pub(super) fn home_of(nodes: &[InstrNode]) -> Result<ValueId, &'static str> {
        let refs: Vec<&InstrNode> = nodes.iter().collect();
        super::super::borrowed_temp_home(&refs, v(1), v(2), &t())
    }
}

/// THE BORROWED TEMPORARY'S HOME (DROPS-RES-1 as corrected by the review). The shared-borrow
/// snapshot lane lowers `bump(&mk())` as a load of the borrow's slot `%2` into a fresh slot `%4`
/// the callee receives: the object's home is `%4`, so the drop goes where `bump` wrote (the first
/// cut dropped `%2`: a stale `Cell`, a double free through a `RefCell`). A borrow the callee
/// receives directly, and a whole read only taken apart, keep the slot.
#[test]
fn a_borrowed_temporary_is_dropped_where_the_program_used_it() {
    use home::*;
    // `bump(&mk())`, the snapshot: the object moved to %4.
    let snap = body(vec![load(3, t(), 2), alloca(4), store(t(), 3, 4), call(5, &[4])]);
    assert_eq!(home_of(&snap), Ok(v(4)));
    // ...and still %4 with its drop placed.
    let mut placed = snap.clone();
    placed.push(drop(4));
    assert_eq!(home_of(&placed), Ok(v(4)));
    // `mk().peek()`: the autoref receiver is the slot itself.
    assert_eq!(home_of(&body(vec![call(3, &[2])])), Ok(v(2)));
    // `let g = &mk(); g.0`: a whole load taken apart and only read.
    assert_eq!(home_of(&body(vec![load(3, t(), 2), field(4, 3), ret(4)])), Ok(v(2)));
}

/// Forwarding a reborrow keeps the callee on the original slot. The hostile
/// drop must use a DISTINCT stale copy to remain an effective wrong-home case.
#[test]
fn a_forwarded_borrow_cannot_drop_a_new_stale_copy() {
    use home::*;
    assert_eq!(home_of(&body(vec![call(3, &[2]), drop(2)])), Ok(v(2)));
    let wrong = body(vec![call(3, &[2]), alloca(4), store(t(), 1, 4), drop(4)]);
    assert!(home_of(&wrong).is_err());
    let mut module = cfg(&[(0, &[])], &[]);
    module.functions[0].blocks[0].body = wrong;
    assert!(super::homes_still_proved(&module, &[(v(1), v(2), t(), v(2))], &[]).is_some());
}

/// Where the program reaches the object some other way the proof fails (and the placement is
/// refused unless any copy is the same drop): a copy beside the slot the callee receives, the
/// slot used again after the snapshot, the temporary's value stored twice, the address stored
/// into memory, a part copied into a fresh slot.
#[test]
fn a_borrowed_temporary_reached_another_way_is_unproved() {
    use home::*;
    // The slot is snapshotted AND passed on: two objects.
    let both =
        body(vec![load(3, t(), 2), alloca(4), store(t(), 3, 4), call(5, &[4]), call(6, &[2])]);
    assert!(home_of(&both).is_err());
    // The value is stored into a second slot the callee receives.
    let twice = body(vec![alloca(4), store(t(), 1, 4), call(5, &[4])]);
    assert!(home_of(&twice).is_err());
    // The address escapes into memory.
    let escapes = body(vec![alloca(4), store(trust_ir::Ty::Ptr, 2, 4)]);
    assert!(home_of(&escapes).is_err());
    // A part read out and stored into a fresh slot (a part's snapshot).
    let part = body(vec![
        load(3, t(), 2),
        field(4, 3),
        alloca(5),
        store(trust_ir::Ty::I32, 4, 5),
        call(6, &[5]),
    ]);
    assert!(home_of(&part).is_err());
    // The whole value returned.
    let whole = body(vec![load(3, t(), 2), ret(3)]);
    assert!(home_of(&whole).is_err());
    // The slot is not initialized from the temporary's value.
    let refs: Vec<&trust_ir::InstrNode> = Vec::new();
    assert!(super::borrowed_temp_home(&refs, v(1), v(2), &t()).is_err());
}

/// First materialization of a non-Freeze owned temporary needs its own placed drop and
/// exact home proof. A different root's otherwise valid proof cannot authorize the borrow.
#[test]
fn an_owned_shared_temporary_requires_its_own_finished_home() {
    use home::*;
    let mut module = cfg(&[(0, &[])], &[]);
    module.functions[0].blocks[0].body = body(vec![call(3, &[2]), drop(2)]);
    let proved = [(v(1), v(2), t(), v(2))];
    let owned = [(v(1), v(2), t())];
    assert_eq!(super::homes_still_proved(&module, &proved, &owned), None);
    assert!(super::homes_still_proved(&module, &[], &owned).is_some());
    for other in [(v(9), v(2), t()), (v(1), v(9), t()), (v(1), v(2), trust_ir::Ty::I32)] {
        assert!(super::homes_still_proved(&module, &proved, &[other]).is_some());
    }
    module.functions[0].blocks[0].body = body(vec![call(3, &[2])]);
    assert!(super::homes_still_proved(&module, &proved, &owned).is_some());
}

/// A proof valid when a drop hook fired must fail if later lowering copied the object or
/// leaked its address. The original drop and proof record are deliberately left intact.
#[test]
fn an_owned_shared_temporary_rejects_uses_lowered_after_its_drop() {
    use home::*;
    let mut module = cfg(&[(0, &[])], &[]);
    let proved = [(v(1), v(2), t(), v(2))];
    let owned = [(v(1), v(2), t())];
    for later in [
        vec![load(4, t(), 2), alloca(5), store(t(), 4, 5), call(6, &[5])],
        vec![alloca(5), store(trust_ir::Ty::Ptr, 2, 5)],
    ] {
        let mut nodes = body(vec![call(3, &[2]), drop(2)]);
        nodes.extend(later);
        module.functions[0].blocks[0].body = nodes;
        assert!(super::homes_still_proved(&module, &proved, &owned).is_some());
    }
}

#[test]
fn an_interior_read_keeps_the_whole_temporary_home() {
    use home::*;
    let nodes = body(vec![
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: trust_ir::Ty::I64,
            value: trust_ir::Constant::Int(4),
        })
        .with_result(v(3)),
        trust_ir::InstrNode::new(trust_ir::Inst::GEP {
            pointee_ty: trust_ir::Ty::I8,
            base: v(2),
            indices: vec![v(3)],
            inbounds: true,
        })
        .with_result(v(4)),
        load(5, trust_ir::Ty::I32, 4),
        drop(2),
        ret(5),
    ]);
    assert_eq!(home_of(&nodes), Ok(v(2)));
}

#[test]
fn copying_an_interior_value_to_another_home_is_rejected() {
    use home::*;
    let nodes = body(vec![
        trust_ir::InstrNode::new(trust_ir::Inst::Const {
            ty: trust_ir::Ty::I64,
            value: trust_ir::Constant::Int(4),
        })
        .with_result(v(3)),
        trust_ir::InstrNode::new(trust_ir::Inst::GEP {
            pointee_ty: trust_ir::Ty::I8,
            base: v(2),
            indices: vec![v(3)],
            inbounds: true,
        })
        .with_result(v(4)),
        load(5, trust_ir::Ty::I32, 4),
        alloca(6),
        store(trust_ir::Ty::I32, 5, 6),
        call(7, &[6]),
        drop(2),
    ]);
    assert!(home_of(&nodes).is_err());
}
