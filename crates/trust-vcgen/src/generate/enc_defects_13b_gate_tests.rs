// Trust (ENC-DEFECTS 13b, salvage reconciliation 2026-09-28): the GATES of
// `path_defs::frozen_shared_reborrow_roots` and its place in the call havoc,
// asked directly rather than through a verdict.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0
//
// WHY THIS FILE. `tests/enc_defects_precision_realmir.rs` pins 13b by verdict:
// a row PROVED or REFUTED after the whole havoc pipeline. Two things made that
// blind to 13b's own fences:
//   * deleting the escape gate (`local_pointee_may_escape`) left every one of
//     those rows green — the fixture that needs it (`escaped_then_shared`) was
//     refuted for other reasons as well;
//   * since TRUST-10 (`callee_write_set::refine_shared_reborrow_havoc`) the same
//     call site carries a SIBLING narrowing on the same protector premise, so a
//     verdict no longer says which of the two lanes produced it.
// The tests below ask the 13b narrowing itself (every refusal on real MIR), and
// ask `terminator_def_names` about the composition: the sibling runs first, 13b
// acts only where the sibling declined, and 13b honours the sibling's
// `unsafe`-signature and atomic fences.

use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::path_defs::frozen_shared_reborrow_roots;
use crate::generate::terminator_def_names;

fn load(json: &str) -> VerifiableFunction {
    serde_json::from_str(json).expect("fixture MIR must deserialize")
}

const CONSUME_SHARED: &str = include_str!("../../tests/fixtures/enc_consume_shared_mir.json");
const ESCAPED_THEN_SHARED: &str =
    include_str!("../../tests/fixtures/enc_escaped_then_shared_mir.json");
const FIELD_REBORROW: &str = include_str!("../../tests/fixtures/enc_field_reborrow_mir.json");
const CONSUME_CELL: &str = include_str!("../../tests/fixtures/enc_consume_cell_mir.json");
const CONSUME_MUT_CALL: &str = include_str!("../../tests/fixtures/enc_consume_mut_call_mir.json");
const TICK_PARAM: &str = include_str!("../../tests/fixtures/enc_tick_param_mir.json");

/// The block whose terminator calls `callee` (exactly one in every fixture used here).
fn call_block<'a>(func: &'a VerifiableFunction, callee: &str) -> &'a BasicBlock {
    let mut hits = func
        .body
        .blocks
        .iter()
        .filter(|b| matches!(&b.terminator, Terminator::Call { func: f, .. } if f == callee));
    let block = hits.next().unwrap_or_else(|| panic!("{}: no call to `{callee}`", func.name));
    assert!(hits.next().is_none(), "{}: more than one call to `{callee}`", func.name);
    block
}

/// 13b's answer at the call to `callee`, sorted.
fn roots_at(func: &VerifiableFunction, callee: &str) -> Option<Vec<String>> {
    let Terminator::Call { args, .. } = &call_block(func, callee).terminator else {
        unreachable!()
    };
    frozen_shared_reborrow_roots(func, args).map(|set| {
        let mut v: Vec<String> = set.into_iter().collect();
        v.sort();
        v
    })
}

/// Does any havoc name in `names` rebind the read `read`?
fn rebinds(names: &[String], read: &str) -> bool {
    names.iter().any(|n| crate::generate::write_rebinds(n, read))
}

// ---- the 13b narrowing, gate by gate, on real MIR ----

#[test]
fn a_whole_frozen_self_reborrow_names_its_root() {
    // Positive control for every refusal below: `self.remaining()` on
    // `&mut self` of `Quota { used: u32, limit: u32 }` — the one shape 13b admits.
    let func = load(CONSUME_SHARED);
    assert_eq!(roots_at(&func, "enc13b::Quota::remaining"), Some(vec!["self".to_string()]));
}

#[test]
fn a_stashed_mutable_child_of_the_root_refuses_the_narrowing() {
    // `stash(&mut self.used)` earlier in the body: a `&mut` of a place rooted at
    // `self` escaped. Every OTHER gate passes here (same `Q { used, limit }`
    // pointee, whole `&*self` reborrow, one-valued parameter root, no laundering),
    // so this row is the escape gate alone: deleting `local_pointee_may_escape`
    // turns it red.
    let func = load(ESCAPED_THEN_SHARED);
    assert_eq!(roots_at(&func, "enc13x::Q::peek"), None);
}

#[test]
fn a_field_reborrow_a_cell_pointee_and_a_mut_receiver_are_refused() {
    // `look(&self.limit)` covers one field only; `Cq` holds a `Cell` (not
    // `Freeze`, refused by name and by walk); `self.bump()` passes `&mut`.
    for (json, callee) in [
        (FIELD_REBORROW, "enc13x::look"),
        (CONSUME_CELL, "enc13b::Cq::peek"),
        (CONSUME_MUT_CALL, "enc13b::Quota::bump"),
    ] {
        let func = load(json);
        assert_eq!(roots_at(&func, callee), None, "{}", func.name);
    }
}

// ---- the composition with the TRUST-10 sibling, through `terminator_def_names` ----

#[test]
fn unsafe_atomic_or_foreign_callees_keep_the_full_havoc() {
    // The fences 13b took over from the sibling (fail closed). On the admitted
    // shape of `a_whole_frozen_self_reborrow_names_its_root`, flipping any one of
    // them must leave `self`'s fields havocked by BOTH lanes.
    for which in 0..3 {
        let mut func = load(CONSUME_SHARED);
        let at = func
            .body
            .blocks
            .iter()
            .position(|b| {
                matches!(&b.terminator, Terminator::Call { func: f, .. }
                    if f == "enc13b::Quota::remaining")
            })
            .expect("the `remaining` call");
        let Terminator::Call { is_foreign, is_unsafe_sig, atomic, .. } =
            &mut func.body.blocks[at].terminator
        else {
            unreachable!()
        };
        match which {
            0 => *is_foreign = true,
            1 => *is_unsafe_sig = true,
            _ => {
                *atomic = Some(trust_types::AtomicOperation {
                    place: Place {
                        local: 1,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    },
                    dest: None,
                    op_kind: trust_types::AtomicOpKind::Store,
                    ordering: trust_types::AtomicOrdering::SeqCst,
                    failure_ordering: None,
                    span: SourceSpan::default(),
                })
            }
        }
        let names = terminator_def_names(&func, &func.body.blocks[at]);
        assert!(rebinds(&names, "self*.0"), "case {which}: {names:?}");
    }
}

#[test]
fn where_the_sibling_fires_its_answer_stands() {
    // `Quota`'s fields are scalars on a struct-field path, so the TRUST-10 sibling
    // replaces `self` by the names of what it does NOT spare; 13b then finds no
    // `self` to drop. Neither field is rebound.
    let func = load(CONSUME_SHARED);
    let names = terminator_def_names(&func, call_block(&func, "enc13b::Quota::remaining"));
    assert!(!names.iter().any(|n| n == "self"), "{names:?}");
    for read in ["self*.0", "self*.1"] {
        assert!(!rebinds(&names, read), "`{read}` is frozen across the call: {names:?}");
    }
}

/// `enc13a::Motion` exactly as the extractor renders it (a stamped fieldless enum).
fn motion_ty() -> Ty {
    let func = load(TICK_PARAM);
    let Ty::Ref { inner, .. } = &func.body.locals[1].ty else { panic!("`self` is a reference") };
    let Ty::Adt { fields, .. } = inner.as_ref() else { panic!("`Elevator` is an ADT") };
    fields.iter().find(|(n, _)| n == "motion").expect("the `motion` field").1.clone()
}

/// `fn f(self: &mut Motion)` whose bb0 is `_2 = &(*_1); p::Motion::check(move _2)`.
fn enum_self_shared_call() -> VerifiableFunction {
    let motion = motion_ty();
    VerifiableFunction {
        name: "f".into(),
        def_path: "p::Motion::f".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl {
                    index: 1,
                    ty: Ty::Ref { mutable: true, inner: Box::new(motion.clone()) },
                    name: Some("self".into()),
                },
                LocalDecl {
                    index: 2,
                    ty: Ty::Ref { mutable: false, inner: Box::new(motion) },
                    name: None,
                },
                LocalDecl { index: 3, ty: Ty::Unit, name: None },
            ],
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    stmts: vec![Statement::Assign {
                        place: Place::local(2),
                        rvalue: Rvalue::Ref {
                            mutable: false,
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                        },
                        span: SourceSpan::default(),
                    }],
                    terminator: Terminator::Call {
                        unwind: UnwindEdge::Continue,
                        func: "p::Motion::check".into(),
                        args: vec![Operand::Move(Place::local(2))],
                        dest: Place::local(3),
                        target: Some(BlockId(1)),
                        span: SourceSpan::default(),
                        atomic: None,
                        is_unsafe_sig: false,
                        callee_identity: None,
                        callee_key: crate::sep_engine::tests::fixture_key("p::Motion::check"),
                        is_foreign: false,
                    },
                },
                BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
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

#[test]
fn where_the_sibling_declines_a_frozen_enum_pointee_is_narrowed_by_13b() {
    // A `&mut self` method on a fieldless enum handing `&*self` to a `&self`
    // helper: no scalar leaf on a struct-field path, so the sibling declines and
    // the base name `self` would kill the discriminant fact — this is 13b's own
    // coverage (the 13a enum link surviving a `&self` call).
    let func = enum_self_shared_call();
    let names = terminator_def_names(&func, &func.body.blocks[0]);
    assert!(!rebinds(&names, "self*"), "the protected enum is not rebound: {names:?}");
    // ... and the same call with the escape channel open keeps the full havoc.
    let mut escaped = enum_self_shared_call();
    escaped.body.locals.push(LocalDecl {
        index: 4,
        ty: Ty::Ref { mutable: true, inner: Box::new(escaped.body.locals[1].ty.clone()) },
        name: None,
    });
    escaped.body.blocks[0].stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref { mutable: true, place: Place::local(1) },
        span: SourceSpan::default(),
    });
    let names = terminator_def_names(&escaped, &escaped.body.blocks[0]);
    assert!(rebinds(&names, "self*"), "`&mut self` escaped — `self` may be reseated: {names:?}");
}

#[test]
fn drop_glue_or_a_tail_call_on_the_root_refuses_the_narrowing() {
    // The two terminator channels the escape scan names since the seam-lint
    // reconciliation. bb1 of the enum shape becomes either `drop((*_1))` — drop
    // glue is handed `&mut` to a place rooted at `self` — or `become g(copy _1)`,
    // which hands the pointer itself on. Either one keeps the full havoc at bb0.
    for which in 0..2 {
        let mut func = enum_self_shared_call();
        func.body.blocks[1].terminator = if which == 0 {
            Terminator::Drop {
                place: Place { local: 1, projections: vec![Projection::Deref] },
                target: BlockId(2),
                span: SourceSpan::default(),
                unwind: UnwindEdge::Continue,
            }
        } else {
            Terminator::TailCall {
                func: "p::g".into(),
                args: vec![Operand::Copy(Place::local(1))],
                span: SourceSpan::default(),
                atomic: None,
                is_foreign: false,
                is_unsafe_sig: false,
                callee_identity: None,
                callee_key: crate::sep_engine::tests::fixture_key("p::g"),
            }
        };
        func.body.blocks.push(BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Return,
        });
        let names = terminator_def_names(&func, &func.body.blocks[0]);
        assert!(rebinds(&names, "self*"), "case {which}: {names:?}");
    }
}
