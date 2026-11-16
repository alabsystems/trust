// trust_vcgen/sep_engine_box_deref_tests.rs: the safe `*box` false refutation.
//
// Trust (2026-09-23): rustc's `ElaborateBoxDerefs` rewrites a SAFE `*b` into a
// raw deref of a `Transmute` of `b.0.0` (`Unique` -> `NonNull`), so the separation
// engine used to charge it three `[unsafe:sep:deref]` rows over an unconstrained
// pointer — refuted in every lane. `validity_rooted_box_deref_ops` now intersects
// the compiler's `collect_synthesized_box_deref_ops` set with the engine's own
// root walk, and `SepEngine::place_has_raw_deref` treats a nominated deref like
// the `&T` deref it is. These pin both roots that land (a parameter, an in-body
// `Box::new`), every root and fence that must keep its rows, and the provenance
// side-fixes. Every "no rows" assertion is paired with a control that shows the
// same instrument producing rows.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use trust_types::fx::FxHashSet;
use trust_types::{
    AdtKind, BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue,
    SourceSpan, Statement, Terminator, Ty, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition,
};

use super::check_sep_unsafe_blocked_ops;
use crate::unsafe_verify::MirOp;

fn span() -> SourceSpan {
    SourceSpan::default()
}

fn sysroot_struct(name: &str, field: Ty) -> Ty {
    let mut ty = Ty::adt(name, vec![("0".to_string(), field)]);
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Struct);
    }
    ty
}

fn raw(pointee: Ty) -> Ty {
    Ty::RawPtr { mutable: false, pointee: Box::new(pointee) }
}

/// `alloc::boxed::Box<T>` as the extractor renders it: `Box` -> `Unique` ->
/// `NonNull` -> `*const T`, each an authenticated sysroot struct.
fn box_of(pointee: Ty) -> Ty {
    let nonnull = sysroot_struct("core::ptr::non_null::NonNull", raw(pointee));
    let unique = sysroot_struct("core::ptr::unique::Unique", nonnull);
    sysroot_struct("alloc::boxed::Box", unique)
}

fn local(index: usize, ty: Ty) -> LocalDecl {
    LocalDecl { index, ty, name: None }
}

fn func(
    name: &str,
    locals: Vec<LocalDecl>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.to_string(),
        def_path: format!("test::{name}"),
        span: span(),
        body: VerifiableBody {
            return_ty: locals[0].ty.clone(),
            locals,
            arg_count,
            blocks,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// `_t = copy ((_box.0: Unique).0: NonNull) as *const T` — the temp
/// `ElaborateBoxDerefs` mints (the extractor drops the `Transmute` kind).
fn box_temp(temp: usize, box_local: usize, pointee: Ty) -> Statement {
    Statement::Assign {
        place: Place::local(temp),
        rvalue: Rvalue::Cast(
            Operand::Copy(Place {
                local: box_local,
                projections: vec![Projection::Field(0), Projection::Field(0)],
            }),
            raw(pointee),
        ),
        span: span(),
    }
}

/// `_dest = copy (*_ptr)`.
fn read_through(dest: usize, ptr: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: ptr,
            projections: vec![Projection::Deref],
        })),
        span: span(),
    }
}

fn drop_then(place: usize, target: usize) -> Terminator {
    Terminator::Drop {
        place: Place::local(place),
        target: BlockId(target),
        span: span(),
        unwind: UnwindEdge::Unreachable,
    }
}

fn call_into(
    callee: &str,
    dest: usize,
    target: usize,
    foreign: bool,
    unsafe_sig: bool,
) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args: vec![Operand::Constant(ConstValue::Uint(3, 32))],
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: span(),
        atomic: None,
        is_foreign: foreign,
        is_unsafe_sig: unsafe_sig,
        callee_identity: None,
        callee_key: super::tests::fixture_key(callee),
    }
}

fn ops(entries: &[(usize, usize)]) -> FxHashSet<(BlockId, usize)> {
    entries.iter().map(|&(block, stmt)| (BlockId(block), stmt)).collect()
}

/// The rows the engine charged to statement `stmt` of block `block`.
fn rows_at(
    f: &VerifiableFunction,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    block: usize,
    stmt: usize,
) -> Vec<VerificationCondition> {
    check_sep_unsafe_blocked_ops(f, &FxHashSet::default(), box_deref_ops)
        .into_iter()
        .filter(|(_, b, op)| *b == BlockId(block) && *op == MirOp::Statement(stmt))
        .map(|(vc, ..)| vc)
        .collect()
}

fn messages(rows: &[VerificationCondition]) -> Vec<String> {
    rows.iter()
        .map(|vc| match &vc.kind {
            VcKind::Assertion { message } => message.clone(),
            other => format!("{other:?}"),
        })
        .collect()
}

/// `fn f(b: Box<u32>) -> u32 { *b }` after `ElaborateBoxDerefs` (the measured
/// `v2.mir`, UB-check asserts elided). The deref is statement 1 of `bb0`.
fn param_box_deref(extra: Vec<Statement>) -> VerifiableFunction {
    let mut stmts = extra;
    stmts.push(box_temp(2, 1, Ty::u32()));
    stmts.push(read_through(0, 2));
    func(
        "param_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, box_of(Ty::u32())),
            local(2, raw(Ty::u32())),
            local(3, Ty::Ref { mutable: false, inner: Box::new(box_of(Ty::u32())) }),
        ],
        1,
        vec![
            BasicBlock { id: BlockId(0), stmts, terminator: drop_then(1, 1) },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    )
}

/// `let b = <callee>(3); *b` (the measured `v1.mir` shape): `bb0` calls into
/// `_1`, `bb1` mints the temp and reads through it at statement 1.
fn called_box_deref(callee: &str, foreign: bool, unsafe_sig: bool) -> VerifiableFunction {
    func(
        "called_box_deref",
        vec![local(0, Ty::u32()), local(1, box_of(Ty::u32())), local(2, raw(Ty::u32()))],
        0,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_into(callee, 1, 1, foreign, unsafe_sig),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![box_temp(2, 1, Ty::u32()), read_through(0, 2)],
                terminator: drop_then(1, 2),
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ],
    )
}

const BOX_NEW: &str = "alloc::boxed::Box::<u32>::new";

// ── root (b): a parameter ────────────────────────────────────────────────

#[test]
fn a_parameter_box_deref_nominated_by_the_compiler_mints_no_deref_rows() {
    let f = param_box_deref(vec![]);
    // CONTROL: the same body, the same instrument, no compiler set — the three
    // unconstrained rows the false refutation was built from.
    let control = messages(&rows_at(&f, &FxHashSet::default(), 0, 1));
    assert!(
        control.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "control must mint the deref rows: {control:?}"
    );
    let rooted = rows_at(&f, &ops(&[(0, 1)]), 0, 1);
    assert!(rooted.is_empty(), "a rooted safe `*box` must mint no rows: {:?}", messages(&rooted));
}

#[test]
fn the_compiler_set_is_required_an_empty_or_foreign_set_keeps_every_row() {
    let f = param_box_deref(vec![]);
    for set in [ops(&[]), ops(&[(0, 0)]), ops(&[(1, 1)])] {
        let rows = messages(&rows_at(&f, &set, 0, 1));
        for needle in ["null check", "allocation validity", "alignment check"] {
            assert!(
                rows.iter().any(|m| m.starts_with("[unsafe:sep:deref]") && m.contains(needle)),
                "`{needle}` row must stay without a matching compiler nomination {set:?}: {rows:?}"
            );
        }
    }
}

#[test]
fn a_write_through_a_rooted_box_temp_mints_no_rows_unless_unnominated() {
    // `*b = 5` (2026-10-09): the compiler now nominates the DESTINATION deref of a
    // synthesized box pointer, and a store through a valid, uniquely-owned box is
    // as sound as the read. Without the nomination the write keeps its rows.
    let mut f = param_box_deref(vec![]);
    f.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
        span: span(),
    };
    let unnominated = rows_at(&f, &ops(&[]), 0, 1);
    assert!(!unnominated.is_empty(), "an un-nominated write keeps its rows");
    let nominated = rows_at(&f, &ops(&[(0, 1)]), 0, 1);
    assert!(
        nominated.is_empty(),
        "a nominated write through a rooted box mints no rows: {:?}",
        messages(&nominated)
    );
}

#[test]
fn a_genuine_raw_write_sharing_a_statement_with_a_box_read_keeps_its_rows() {
    // `*raw = *b`: `(*_3) = copy (*_2)`. The statement derefs a raw pointer that
    // is not a synthesized box pointer, so the operation is not a safe `*box` as
    // a whole and nothing in it is rooted.
    let mut f = param_box_deref(vec![]);
    f.body.locals.push(local(4, Ty::u32()));
    if let Some(decl) = f.body.locals.iter_mut().find(|decl| decl.index == 3) {
        decl.ty = Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) };
    }
    f.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place { local: 3, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Copy(Place {
            local: 2,
            projections: vec![Projection::Deref],
        })),
        span: span(),
    };
    let rows = messages(&rows_at(&f, &ops(&[(0, 1)]), 0, 1));
    assert!(keeps_deref_rows(&rows), "the box read sharing it is not rooted: {rows:?}");
}

#[test]
fn a_nominated_write_through_a_rooted_box_temp_mints_no_rows() {
    // `*b = 5` on a validity-rooted box (2026-10-01; before, writes were never
    // nominated and kept four rows — every `&mut self` setter of a boxed field,
    // docs/issues/2026-09-30-verified-lane-blockers-measured-on-alab-repos.md
    // item 3). Borrowck admitted the write as a mutable access to a valid,
    // unique `Box`, so it is as sound as the read. CONTROL: the same body
    // without the compiler's nomination keeps the deref and write rows.
    let mut f = param_box_deref(vec![]);
    f.body.blocks[0].stmts[1] = Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
        span: span(),
    };
    let control = messages(&rows_at(&f, &FxHashSet::default(), 0, 1));
    for needle in ["[unsafe:sep:deref] null check", "[unsafe:sep:write]"] {
        assert!(
            control.iter().any(|m| m.starts_with(needle)),
            "control must mint `{needle}`: {control:?}"
        );
    }
    let rooted = rows_at(&f, &ops(&[(0, 1)]), 0, 1);
    assert!(
        rooted.is_empty(),
        "a rooted safe `*box = v` must mint no rows: {:?}",
        messages(&rooted)
    );
}

#[test]
fn a_nominated_write_keeps_its_rows_in_a_body_with_any_unsafe_operation() {
    // `let p = &mut *b as *mut u32; dealloc(p, ..); *b = 5` writes freed memory:
    // the root walk watches the box SLOT, not the pointee, so the free through a
    // derived pointer is invisible to it. The write credit therefore requires a
    // body with no unsafe operation at all (docs/KNOWN_HAZARDS.md, OPEN
    // 2026-10-01; D33 is the read side). Here the unsafe operation is a `Box`
    // minted from bits (a lowered `transmute`); the control is the same write
    // with that statement replaced by an unrelated scalar store.
    let with_extra = |extra: Statement| {
        let mut f = param_box_deref(vec![extra]);
        f.body.locals.push(local(4, box_of(Ty::u32())));
        f.body.locals.push(local(5, Ty::u32()));
        f.body.blocks[0].stmts[2] = Statement::Assign {
            place: Place { local: 2, projections: vec![Projection::Deref] },
            rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
            span: span(),
        };
        f
    };
    let control = with_extra(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
        span: span(),
    });
    let rows = rows_at(&control, &ops(&[(0, 2)]), 0, 2);
    assert!(
        rows.is_empty(),
        "control: no unsafe operation, the write is credited: {:?}",
        messages(&rows)
    );

    let unsafe_body = with_extra(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Uint(8, 64)), box_of(Ty::u32())),
        span: span(),
    });
    let rows = messages(&rows_at(&unsafe_body, &ops(&[(0, 2)]), 0, 2));
    for needle in ["[unsafe:sep:deref] null check", "[unsafe:sep:write]"] {
        assert!(
            rows.iter().any(|m| m.starts_with(needle)),
            "a write in a body with an unsafe operation must keep `{needle}`: {rows:?}"
        );
    }
}

#[test]
fn a_nominated_read_keeps_its_rows_in_a_body_with_any_unsafe_operation() {
    // D33 (ruled (a) 2026-10-01): `let p = &mut *b as *mut u32; dealloc(p, ..);
    // let x = *b` read freed memory and minted no row for `*b`. The read side now
    // takes the write side's fence. Same construction as the write test: the
    // unsafe operation is a `Box` minted from bits; the control replaces it with
    // an unrelated scalar store.
    let with_extra = |extra: Statement| {
        let mut f = param_box_deref(vec![extra]);
        f.body.locals.push(local(4, box_of(Ty::u32())));
        f.body.locals.push(local(5, Ty::u32()));
        f
    };
    let control = with_extra(Statement::Assign {
        place: Place::local(5),
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
        span: span(),
    });
    let rows = rows_at(&control, &ops(&[(0, 2)]), 0, 2);
    assert!(
        rows.is_empty(),
        "control: no unsafe operation, the read is credited: {:?}",
        messages(&rows)
    );
    let unsafe_body = with_extra(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Cast(Operand::Constant(ConstValue::Uint(8, 64)), box_of(Ty::u32())),
        span: span(),
    });
    let rows = messages(&rows_at(&unsafe_body, &ops(&[(0, 2)]), 0, 2));
    assert!(
        rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "a read in a body with an unsafe operation must keep its rows: {rows:?}"
    );
}

#[test]
fn a_write_through_an_unrooted_box_temp_keeps_its_rows_even_when_nominated() {
    // The nomination alone grants nothing: a reseated box slot is not a
    // validity root, so the write keeps its rows.
    let mut f = param_box_deref(vec![Statement::Assign {
        place: Place::local(1),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(1))),
        span: span(),
    }]);
    f.body.blocks[0].stmts[2] = Statement::Assign {
        place: Place { local: 2, projections: vec![Projection::Deref] },
        rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
        span: span(),
    };
    let rows = messages(&rows_at(&f, &ops(&[(0, 2)]), 0, 2));
    assert!(
        rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "an unrooted box write must keep its rows: {rows:?}"
    );
}

#[test]
fn a_shared_borrow_of_the_box_slot_keeps_its_rows() {
    // `let r = &b;` — `unsafe { ptr::read(r) }` could duplicate the box and free
    // its allocation with no whole-local write, so the slot is fenced.
    let borrow = Statement::Assign {
        place: Place::local(3),
        rvalue: Rvalue::Ref { mutable: false, place: Place::local(1) },
        span: span(),
    };
    let f = param_box_deref(vec![borrow]);
    let rows = messages(&rows_at(&f, &ops(&[(0, 2)]), 0, 2));
    assert!(
        rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "a borrowed box slot must keep its rows: {rows:?}"
    );
}

#[test]
fn every_escape_reseat_and_unmodeled_fence_on_a_parameter_root_keeps_its_rows() {
    // The root walk had no consumer before 2026-09-23, so no test pinned its
    // refusals; every one is load-bearing now that a rooted deref mints nothing.
    // `param_box_deref(extra)` puts `extra` ahead of the temp, so the deref is
    // statement `extra.len() + 1` of `bb0`.
    let assign = |place: Place, rvalue: Rvalue| Statement::Assign { place, rvalue, span: span() };
    let with_spare_box = |mut f: VerifiableFunction| {
        f.body.locals.push(local(4, box_of(Ty::u32())));
        f.body.locals.push(local(5, Ty::u32()));
        f
    };
    let deref_rows = |f: &VerifiableFunction, extra: usize| {
        let op = extra + 1;
        messages(&rows_at(f, &ops(&[(0, op)]), 0, op))
    };
    // CONTROL: one statement that touches nothing the fence reads, same index.
    let control = with_spare_box(param_box_deref(vec![assign(
        Place::local(5),
        Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32))),
    )]));
    assert!(deref_rows(&control, 1).is_empty(), "control: an unrelated write fences nothing");

    let cases: Vec<(&str, Statement)> = vec![
        (
            "`&mut b`",
            assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(1) }),
        ),
        ("`&raw const b`", assign(Place::local(3), Rvalue::AddressOf(false, Place::local(1)))),
        (
            "a partial write `b.0 = ..`",
            assign(
                Place { local: 1, projections: vec![Projection::Field(0)] },
                Rvalue::Use(Operand::Constant(ConstValue::Uint(8, 64))),
            ),
        ),
        (
            "a second whole definition of the parameter",
            assign(Place::local(1), Rvalue::Use(Operand::Move(Place::local(4)))),
        ),
        ("a `Deinit` of the parameter", Statement::Deinit { place: Place::local(1) }),
    ];
    for (what, stmt) in cases {
        let f = with_spare_box(param_box_deref(vec![stmt]));
        let rows = deref_rows(&f, 1);
        assert!(
            rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
            "{what} must keep the deref's rows: {rows:?}"
        );
    }

    // An unmodeled write channel anywhere in the body refuses the whole walk.
    let mut asm = with_spare_box(param_box_deref(vec![]));
    asm.body.blocks[1].terminator =
        Terminator::Opaque { kind: "InlineAsm".into(), targets: vec![], span: span() };
    let rows = deref_rows(&asm, 0);
    assert!(
        rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "an unmodeled write channel must keep the deref's rows: {rows:?}"
    );
}

// ── the in-body `Box::new` root ──────────────────────────────────────────

#[test]
fn an_in_body_box_new_root_mints_no_deref_rows() {
    let f = called_box_deref(BOX_NEW, false, false);
    let control = rows_at(&f, &FxHashSet::default(), 1, 1);
    assert!(!control.is_empty(), "control: a `Box::new` deref is charged without the set");
    let rooted = rows_at(&f, &ops(&[(1, 1)]), 1, 1);
    assert!(
        rooted.is_empty(),
        "a `Box::new`-rooted `*box` must mint no rows: {:?}",
        messages(&rooted)
    );
}

#[test]
fn an_unsafe_signature_call_root_keeps_its_rows() {
    // The `Box::new` key alone is not enough: an unsafe-signature call is refused,
    // and so is the real `Box::from_raw` (untagged, unsafe) spelling.
    for callee in [BOX_NEW, "alloc::boxed::Box::<u32>::from_raw"] {
        let f = called_box_deref(callee, false, true);
        let rows = rows_at(&f, &ops(&[(1, 1)]), 1, 1);
        assert!(!rows.is_empty(), "`{callee}` with an unsafe signature must keep its rows");
    }
}

#[test]
fn a_foreign_call_root_keeps_its_rows() {
    let f = called_box_deref(BOX_NEW, true, false);
    let rows = rows_at(&f, &ops(&[(1, 1)]), 1, 1);
    assert!(!rows.is_empty(), "a foreign call root must keep its rows");
}

// ── D8: the returned-`Box` root (compiler-certified call blocks) ───────────
//
// D8 (2026-09-24, decision: YES with exclusions) replaced the
// old `a_box_returned_by_an_arbitrary_safe_call_keeps_its_rows`. A returned box
// is rooted ONLY through the compiler's certificate
// (`trust_mir_extract::returned_box_root_call_blocks`, installed with
// `VcgenContext::with_returned_box_root_blocks`); without one — the case that
// test pinned — every row is kept, which the control below re-asserts.

const DEFAULTS: &str = "mycrate::defaults";

fn identity() -> trust_types::CalleeIdentity {
    trust_types::CalleeIdentity { stable_crate_id: 7, def_index: 11, substs_digest: [0, 0] }
}

/// `called_box_deref(DEFAULTS, ..)` with a DIRECT, concrete callee identity on
/// the `bb0` call — the shape the extractor emits for `let b = defaults(); *b`.
fn returned_box_deref(foreign: bool, unsafe_sig: bool) -> VerifiableFunction {
    let mut f = called_box_deref(DEFAULTS, foreign, unsafe_sig);
    if let Terminator::Call { callee_identity, .. } = &mut f.body.blocks[0].terminator {
        *callee_identity = Some(identity());
    }
    f
}

/// The compiler's certificate for `f`: these call blocks are returned-`Box`
/// roots (`trust_mir_extract::returned_box_root_call_blocks`).
fn certified(f: &VerifiableFunction, blocks: &[usize]) -> crate::VcgenContext {
    crate::VcgenContext::for_function(f.def_path.clone())
        .with_returned_box_root_blocks(blocks.iter().map(|&b| BlockId(b)).collect())
}

/// The deref rows of `bb1` statement 1 under `context` (or none installed).
fn returned_rows(f: &VerifiableFunction, context: Option<&crate::VcgenContext>) -> Vec<String> {
    let run = || messages(&rows_at(f, &ops(&[(1, 1)]), 1, 1));
    match context {
        Some(context) => crate::with_vcgen_context(context, run),
        None => run(),
    }
}

fn keeps_deref_rows(rows: &[String]) -> bool {
    rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check"))
}

#[test]
fn a_box_returned_by_a_certified_safe_direct_call_mints_no_deref_rows() {
    let f = returned_box_deref(false, false);
    // CONTROL: same body, same instrument, no compiler certificate installed —
    // the three rows the motivating `*defaults()` refusal was built from.
    let control = returned_rows(&f, None);
    for needle in ["null check", "allocation validity", "alignment check"] {
        assert!(
            control.iter().any(|m| m.starts_with("[unsafe:sep:deref]") && m.contains(needle)),
            "control must mint the `{needle}` deref row: {control:?}"
        );
    }
    let rooted = returned_rows(&f, Some(&certified(&f, &[0])));
    assert!(rooted.is_empty(), "a certified returned box must mint no deref rows: {rooted:?}");
}

#[test]
fn the_certificate_is_required_and_is_per_block_and_per_function() {
    let f = returned_box_deref(false, false);
    // Empty set, a set naming another block, and a set owned by another fn.
    let other_fn = crate::VcgenContext::for_function("test::someone_else")
        .with_returned_box_root_blocks([BlockId(0)].into_iter().collect());
    for (what, context) in [
        ("an empty certificate", certified(&f, &[])),
        ("a certificate for another block", certified(&f, &[1])),
        ("a certificate owned by another function", other_fn),
    ] {
        let rows = returned_rows(&f, Some(&context));
        assert!(keeps_deref_rows(&rows), "{what} must keep the rows: {rows:?}");
    }
}

#[test]
fn a_certificate_does_not_widen_the_compiler_deref_nomination() {
    // The returned-box root only feeds `validity_rooted_box_deref_ops`; the
    // compiler's `collect_synthesized_box_deref_ops` nomination is still
    // required, exactly as for the parameter and `Box::new` roots.
    let f = returned_box_deref(false, false);
    let rows = crate::with_vcgen_context(&certified(&f, &[0]), || {
        messages(&rows_at(&f, &FxHashSet::default(), 1, 1))
    });
    assert!(keeps_deref_rows(&rows), "no nomination must keep the rows: {rows:?}");
}

#[test]
fn a_certified_block_whose_call_disagrees_on_its_own_flags_keeps_its_rows() {
    // vcgen re-checks the terminator: a certificate can never root a call this
    // side sees as unsafe, foreign, indirect (no identity) or atomic.
    let mut cases = vec![
        ("an unsafe-signature call (`Box::from_raw`)", returned_box_deref(false, true)),
        ("a foreign call", returned_box_deref(true, false)),
        ("an indirect call (no identity)", called_box_deref(DEFAULTS, false, false)),
    ];
    let mut atomic = returned_box_deref(false, false);
    if let Terminator::Call { atomic: slot, .. } = &mut atomic.body.blocks[0].terminator {
        *slot = Some(trust_types::AtomicOperation {
            place: Place::local(1),
            dest: None,
            op_kind: trust_types::AtomicOpKind::Load,
            ordering: trust_types::AtomicOrdering::SeqCst,
            failure_ordering: None,
            span: span(),
        });
    }
    cases.push(("an atomic intrinsic", atomic));
    for (what, f) in cases {
        let rows = returned_rows(&f, Some(&certified(&f, &[0])));
        assert!(keeps_deref_rows(&rows), "{what} must keep the rows: {rows:?}");
    }
}

#[test]
fn a_certified_returned_box_behind_a_data_flow_fence_keeps_its_rows() {
    let assign = |place: Place, rvalue: Rvalue| Statement::Assign { place, rvalue, span: span() };
    // Each case edits `bb1` AHEAD of the temp, so the deref moves to statement 2.
    let fenced = |extra: Statement, extra_local: Option<LocalDecl>| {
        let mut f = returned_box_deref(false, false);
        if let Some(decl) = extra_local {
            f.body.locals.push(decl);
        }
        f.body.blocks[1].stmts.insert(0, extra);
        f
    };
    let rows_after = |f: &VerifiableFunction| {
        crate::with_vcgen_context(&certified(f, &[0]), || {
            messages(&rows_at(f, &ops(&[(1, 2)]), 1, 2))
        })
    };
    // CONTROL: an unrelated write at the same position fences nothing.
    let control = fenced(
        assign(Place::local(3), Rvalue::Use(Operand::Constant(ConstValue::Uint(7, 32)))),
        Some(local(3, Ty::u32())),
    );
    let control_rows = rows_after(&control);
    assert!(
        control_rows.is_empty(),
        "control: an unrelated write fences nothing: {control_rows:?}"
    );

    let spare_box = || Some(local(3, box_of(Ty::u32())));
    let borrow = || Some(local(3, Ty::Ref { mutable: true, inner: Box::new(box_of(Ty::u32())) }));
    let cases: Vec<(&str, Statement, Option<LocalDecl>)> = vec![
        (
            "a second whole definition (an `Assign` beside the call)",
            assign(Place::local(1), Rvalue::Use(Operand::Move(Place::local(3)))),
            spare_box(),
        ),
        (
            "an escaped `&mut` of the slot",
            assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(1) }),
            borrow(),
        ),
        (
            "a partial write into the slot",
            assign(
                Place { local: 1, projections: vec![Projection::Field(0)] },
                Rvalue::Use(Operand::Constant(ConstValue::Uint(8, 64))),
            ),
            None,
        ),
        ("a `Deinit` of the slot", Statement::Deinit { place: Place::local(1) }, None),
    ];
    for (what, stmt, decl) in cases {
        let f = fenced(stmt, decl);
        let rows = rows_after(&f);
        assert!(keeps_deref_rows(&rows), "{what} must keep the rows: {rows:?}");
    }

    // An unmodeled write channel anywhere in the body refuses the whole walk.
    let mut asm = returned_box_deref(false, false);
    asm.body.blocks[2].terminator =
        Terminator::Opaque { kind: "InlineAsm".into(), targets: vec![], span: span() };
    let rows = returned_rows(&asm, Some(&certified(&asm, &[0])));
    assert!(keeps_deref_rows(&rows), "an unmodeled write channel must keep the rows: {rows:?}");
}

#[test]
fn a_certified_call_into_a_projection_or_a_non_box_local_keeps_its_rows() {
    // (1) the call writes `_1.0`, not `_1`: not a whole-local root.
    let mut projected = returned_box_deref(false, false);
    if let Terminator::Call { dest, .. } = &mut projected.body.blocks[0].terminator {
        dest.projections.push(Projection::Field(0));
    }
    let rows = returned_rows(&projected, Some(&certified(&projected, &[0])));
    assert!(keeps_deref_rows(&rows), "a projected call destination must keep the rows: {rows:?}");

    // (2) a USER `mycrate::boxed::Box` look-alike destination.
    let mut forged = returned_box_deref(false, false);
    let nonnull = sysroot_struct("core::ptr::non_null::NonNull", raw(Ty::u32()));
    let unique = sysroot_struct("core::ptr::unique::Unique", nonnull);
    forged.body.locals[1].ty = sysroot_struct("mycrate::boxed::Box", unique);
    let rows = returned_rows(&forged, Some(&certified(&forged, &[0])));
    assert!(keeps_deref_rows(&rows), "a forged `Box` destination must keep the rows: {rows:?}");

    // (3) v1 boundary: the box is a FIELD of the returned value (`W { b }`),
    // reached as `_1.0`; only a whole-local `Box` destination is a root.
    let wrapped_ty = {
        let mut ty = Ty::adt("mycrate::W", vec![("b".to_string(), box_of(Ty::u32()))]);
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Struct);
        }
        ty
    };
    let mut wrapped = returned_box_deref(false, false);
    wrapped.body.locals[1].ty = wrapped_ty;
    wrapped.body.blocks[1].stmts[0] = Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::Cast(
            Operand::Copy(Place {
                local: 1,
                projections: vec![Projection::Field(0), Projection::Field(0), Projection::Field(0)],
            }),
            raw(Ty::u32()),
        ),
        span: span(),
    };
    let rows = returned_rows(&wrapped, Some(&certified(&wrapped, &[0])));
    assert!(keeps_deref_rows(&rows), "a box inside a returned struct must keep the rows: {rows:?}");
}

#[test]
fn a_transmuted_box_root_keeps_its_rows() {
    // `let b: Box<u32> = unsafe { transmute(8usize) }; *b` — a `Cast` definition
    // is never a root.
    let f = func(
        "transmuted_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, box_of(Ty::u32())),
            local(2, raw(Ty::u32())),
            local(3, Ty::usize()),
        ],
        0,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Use(Operand::Constant(ConstValue::Uint(8, 64))),
                    span: span(),
                },
                Statement::Assign {
                    place: Place::local(1),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(3)), box_of(Ty::u32())),
                    span: span(),
                },
                box_temp(2, 1, Ty::u32()),
                read_through(0, 2),
            ],
            terminator: Terminator::Return,
        }],
    );
    let rows = rows_at(&f, &ops(&[(0, 3)]), 0, 3);
    assert!(!rows.is_empty(), "a transmuted box must keep its rows");
}

#[test]
fn a_deref_after_the_box_new_allocation_was_freed_keeps_its_rows() {
    // The heap tracks a `Box::new` allocation; once the walk has freed it, the
    // rooted deref is the use-after-free finding it always was.
    let f = func(
        "freed_box_deref",
        vec![local(0, Ty::u32()), local(1, box_of(Ty::u32())), local(2, raw(Ty::u32()))],
        0,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_into(BOX_NEW, 1, 1, false, false),
            },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: drop_then(1, 2) },
            BasicBlock {
                id: BlockId(2),
                stmts: vec![box_temp(2, 1, Ty::u32()), read_through(0, 2)],
                terminator: Terminator::Return,
            },
        ],
    );
    let rows = rows_at(&f, &ops(&[(2, 1)]), 2, 1);
    assert!(!rows.is_empty(), "a deref of a freed `Box::new` allocation must keep its rows");
}

// ── provenance side-fixes ────────────────────────────────────────────────

#[test]
fn a_pointer_loaded_through_a_rooted_box_does_not_inherit_the_box_provenance() {
    // `let b = Box::new(p); let q = *b; unsafe { *q }` — `q` is the box's
    // CONTENTS. Inheriting the box-good `alloc_1` provenance would discharge
    // `*q`'s null/validity rows by the allocator's postcondition.
    let ptr = raw(Ty::u32());
    let f = func(
        "stored_pointer_deref",
        vec![
            local(0, Ty::u32()),
            local(1, box_of(ptr.clone())),
            local(2, raw(ptr.clone())),
            local(3, ptr.clone()),
        ],
        0,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: vec![],
                terminator: call_into("alloc::boxed::Box::<*const u32>::new", 1, 1, false, false),
            },
            BasicBlock {
                id: BlockId(1),
                stmts: vec![box_temp(2, 1, ptr), read_through(3, 2), read_through(0, 3)],
                terminator: drop_then(1, 2),
            },
            BasicBlock { id: BlockId(2), stmts: vec![], terminator: Terminator::Return },
        ],
    );
    let set = ops(&[(1, 1)]);
    // D33 (ruled (a) 2026-10-01): the body also performs an unsafe operation
    // (`*q`, a raw deref), so the box read is NOT credited and keeps its rows.
    let box_read = messages(&rows_at(&f, &set, 1, 1));
    assert!(
        box_read.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check")),
        "a box read in a body with an unsafe operation keeps its rows: {box_read:?}"
    );
    let rows = messages(&rows_at(&f, &set, 1, 2));
    assert!(
        rows.iter().any(|m| m == "[unsafe:sep:deref] null check for *_3.*")
            && rows.iter().any(|m| m.contains("allocation validity for *_3.*")),
        "`*q` must be charged as an untracked pointer, not as the box: {rows:?}"
    );
    assert!(!rows.iter().any(|m| m.contains("alloc_1")), "no box provenance on `*q`: {rows:?}");
}

#[test]
fn a_cast_of_a_pointer_loaded_through_a_reference_does_not_inherit_its_provenance() {
    // `fn f(s: &S) -> u32 { let q = s.p as *const u32; unsafe { *q } }` (the
    // measured `c6` shape). The loaded field is not `s`.
    let s_ty = Ty::adt("test::S", vec![("p".to_string(), raw(Ty::u32()))]);
    let f = func(
        "cast_through_ref",
        vec![
            local(0, Ty::u32()),
            local(1, Ty::Ref { mutable: false, inner: Box::new(s_ty.clone()) }),
            local(2, raw(Ty::u32())),
            local(3, raw(s_ty.clone())),
            local(4, raw(Ty::u32())),
        ],
        1,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                Statement::Assign {
                    place: Place::local(2),
                    rvalue: Rvalue::Cast(
                        Operand::Copy(Place {
                            local: 1,
                            projections: vec![Projection::Deref, Projection::Field(0)],
                        }),
                        raw(Ty::u32()),
                    ),
                    span: span(),
                },
                read_through(0, 2),
                // CONTROL: a cast of the reference ITSELF still carries `arg_1`.
                Statement::Assign {
                    place: Place::local(3),
                    rvalue: Rvalue::Cast(Operand::Copy(Place::local(1)), raw(s_ty.clone())),
                    span: span(),
                },
                Statement::Assign {
                    place: Place::local(4),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: 3,
                        projections: vec![Projection::Deref, Projection::Field(0)],
                    })),
                    span: span(),
                },
            ],
            terminator: Terminator::Return,
        }],
    );
    let none = FxHashSet::default();
    let control = messages(&rows_at(&f, &none, 0, 3));
    assert!(
        control.iter().any(|m| m.contains("arg_1")),
        "control: `&s as *const S` is `arg_1`: {control:?}"
    );
    let rows = messages(&rows_at(&f, &none, 0, 1));
    assert!(
        rows.iter().any(|m| m == "[unsafe:sep:deref] null check for *_2.*"),
        "`*q` must be charged as its own pointer: {rows:?}"
    );
    assert!(!rows.iter().any(|m| m.contains("arg_1")), "no `arg_1` provenance on `*q`: {rows:?}");
}

// ── the production entry threads the compiler's set ──────────────────────

#[test]
fn generate_threads_the_box_deref_set_into_the_separation_engine() {
    let f = param_box_deref(vec![]);
    let deref_rows = |set: &FxHashSet<(BlockId, usize)>| {
        let (vcs, discharged) = crate::generate_vcs_with_discharge_and_summaries_with_box_deref_ops(
            &f,
            &crate::modular::SummaryDatabase::default(),
            set,
        );
        vcs.iter()
            .chain(discharged.iter().map(|(vc, _)| vc))
            .filter(|vc| {
                matches!(&vc.kind, VcKind::Assertion { message }
                    if message.starts_with("[unsafe:sep:deref]"))
            })
            .count()
    };
    assert!(deref_rows(&FxHashSet::default()) > 0, "control: the entry mints the deref rows");
    assert_eq!(deref_rows(&ops(&[(0, 1)])), 0, "the compiler's set reaches the engine");
}

// ── ENC-DEFECTS 13c (2026-09-26): a box read THROUGH a validity-rooted reference ──
//
// `fn f(b: &Box<u32>) -> u32 { **b }` lowers to `_2 = copy (*_1)` (the box, copied
// out of the reference), the temp `_3 = copy ((_2.0).0) as *const u32`, and the read
// `_0 = copy (*_3)`. Before 13c the root walk refused the `Deref` in `(*_1)`
// outright, so this deref kept its three `[unsafe:sep:deref]` rows although a
// valid `&Box<u32>` points to a valid `Box<u32>`. Every refusal below is paired
// with the SAME body minus the one hazard, measured by the same instrument.

fn shared_ref(inner: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(inner) }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: span() }
}

fn deref_of(local: usize, rest: Vec<Projection>) -> Place {
    let mut projections = vec![Projection::Deref];
    projections.extend(rest);
    Place { local, projections }
}

/// `**b` for a parameter `b: <param_ty>` whose pointee is `Box<u32>`. `extra` goes
/// ahead of the three deref statements, so the read is statement `extra.len() + 2`.
fn ref_param_box_deref(param_ty: Ty, extra: Vec<Statement>) -> (VerifiableFunction, usize) {
    let mut stmts = extra;
    stmts.push(assign(Place::local(2), Rvalue::CopyForDeref(deref_of(1, vec![]))));
    stmts.push(box_temp(3, 2, Ty::u32()));
    stmts.push(read_through(0, 3));
    let read = stmts.len() - 1;
    let f = func(
        "ref_param_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, param_ty),
            local(2, box_of(Ty::u32())),
            local(3, raw(Ty::u32())),
            local(4, raw(box_of(Ty::u32()))),
        ],
        1,
        vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
    );
    (f, read)
}

fn keeps_null_row(rows: &[String]) -> bool {
    rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check"))
}

/// Trust (2026-10-14, DECISION_QUEUE D100): [`rows_at`] with the REFERENCE_ARG_BOX_VALID
/// premise installed for EVERY argument of `f` — more than the compiler ever installs
/// (it offers only reference arguments, and installs only where
/// `reference_box_root_would_fire` fires). Since D100 a 13c root THROUGH a reference
/// argument roots only under that premise, so the 13c pins in this file measure under
/// it: a positive pin then shows the lane roots once the premise is in place (its
/// demotion is pinned by [`d100_gate`]), and a negative pin shows that the lane's OWN
/// fence refuses, not merely the missing premise.
fn rows_at_installed(
    f: &VerifiableFunction,
    box_deref_ops: &FxHashSet<(BlockId, usize)>,
    block: usize,
    stmt: usize,
) -> Vec<VerificationCondition> {
    let every_argument: Vec<usize> = (1..=f.body.arg_count).collect();
    let context = crate::VcgenContext::for_function(f.def_path.clone())
        .with_reference_box_root_params(every_argument);
    crate::with_vcgen_context(&context, || rows_at(f, box_deref_ops, block, stmt))
}

/// D100: the compiler's candidates (`argument_premise::reference_box_candidate_args`):
/// EVERY argument of a local item body since the 2026-10-15 amendment, so a reference
/// stored inside a by-value argument is offered too. The gate itself decides which
/// of them root anything.
fn reference_args(f: &VerifiableFunction) -> Vec<usize> {
    (1..=f.body.arg_count).collect()
}

/// D100: the compiler's install gate for `f` with `box_deref_ops` nominated, over its
/// reference arguments. Non-empty means the premise is installed, the body's
/// `KernelCertified` rows whose VC the premise-free generation does not reproduce are
/// demoted to `ArgumentPremiseKernelDischarge` (per row since 2026-10-17), the premise
/// is disclosed, and the `argument-premise` transport row is published.
fn d100_gate(f: &VerifiableFunction, box_deref_ops: &FxHashSet<(BlockId, usize)>) -> Vec<usize> {
    super::reference_box_root_would_fire(f, box_deref_ops, &reference_args(f))
}

#[test]
fn a_box_read_through_a_shared_reference_parameter_mints_no_deref_rows() {
    let (f, read) = ref_param_box_deref(shared_ref(box_of(Ty::u32())), vec![]);
    let control = messages(&rows_at_installed(&f, &FxHashSet::default(), 0, read));
    assert!(keeps_null_row(&control), "control: uncredited, the deref is charged: {control:?}");
    let rooted = rows_at_installed(&f, &ops(&[(0, read)]), 0, read);
    assert!(rooted.is_empty(), "`**b` through `b: &Box<u32>`: {:?}", messages(&rooted));
    // D100: only under the installed premise, and the gate installs it for `b`.
    let bare = messages(&rows_at(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&bare), "no premise, no 13c argument root: {bare:?}");
    assert_eq!(d100_gate(&f, &ops(&[(0, read)])), vec![1], "the premise is installed for `b`");
}

#[test]
fn a_box_read_through_a_raw_pointer_parameter_keeps_its_rows() {
    // Same body, `b: *const Box<u32>`: a raw deref carries no validity guarantee.
    let (f, read) = ref_param_box_deref(raw(box_of(Ty::u32())), vec![]);
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&rows), "a raw-pointer root must keep its rows: {rows:?}");
}

#[test]
fn a_reference_cast_to_a_raw_pointer_anywhere_keeps_its_rows() {
    // `let p = b as *const Box<u32>;` mints a raw pointer to the pointee with no
    // `&raw`/`&mut` of a place — the one channel `is_stable` cannot see.
    let cast = assign(
        Place::local(4),
        Rvalue::Cast(Operand::Copy(Place::local(1)), raw(box_of(Ty::u32()))),
    );
    let (f, read) = ref_param_box_deref(shared_ref(box_of(Ty::u32())), vec![cast]);
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&rows), "a cast reference root must keep its rows: {rows:?}");
}

#[test]
fn a_write_or_mutable_reborrow_through_the_reference_keeps_its_rows() {
    let mut_ref = Ty::Ref { mutable: true, inner: Box::new(box_of(Ty::u32())) };
    // CONTROL: the `&mut Box<u32>` root with nothing else is credited (D100: under
    // the premise, which the gate installs for `b`).
    let (f, read) = ref_param_box_deref(mut_ref.clone(), vec![]);
    assert!(
        rows_at_installed(&f, &ops(&[(0, read)]), 0, read).is_empty(),
        "control: `&mut` root credited"
    );
    assert_eq!(d100_gate(&f, &ops(&[(0, read)])), vec![1], "control: demoted and disclosed");
    let cases: Vec<(&str, Statement)> = vec![
        (
            "a store through the reference `(*b).0 = ..`",
            assign(
                deref_of(1, vec![Projection::Field(0)]),
                Rvalue::Use(Operand::Constant(ConstValue::Uint(8, 64))),
            ),
        ),
        (
            "a `&mut (*b)` reborrow",
            assign(Place::local(4), Rvalue::Ref { mutable: true, place: deref_of(1, vec![]) }),
        ),
        (
            "a `&raw mut (*b)`",
            assign(Place::local(4), Rvalue::AddressOf(true, deref_of(1, vec![]))),
        ),
    ];
    for (what, stmt) in cases {
        let (f, read) = ref_param_box_deref(mut_ref.clone(), vec![stmt]);
        let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
        assert!(keeps_null_row(&rows), "{what} must keep the deref's rows: {rows:?}");
        assert!(d100_gate(&f, &ops(&[(0, read)])).is_empty(), "{what}: nothing to install");
    }
}

fn enum_with_box(kind: trust_types::AdtKind) -> Ty {
    let mut ty = Ty::adt_enum(
        "test::Expr",
        vec![
            trust_types::VariantDef {
                name: "Num".into(),
                discriminant: 0,
                fields: vec![("0".into(), Ty::u32())],
            },
            trust_types::VariantDef {
                name: "Neg".into(),
                discriminant: 1,
                fields: vec![("0".into(), box_of(Ty::u32()))],
            },
        ],
    );
    if let Ty::Adt { adt_kind, fields, .. } = &mut ty {
        *adt_kind = Some(kind);
        // Trust (OD-1 T3 class D, 2026-10-10): the flat `__tag` / `__v{v}_{f}` view
        // `ty_convert::lower_enum_adt` gives every extracted enum. `Ty::adt_enum`
        // dedups variant fields by name, so `Num.0` and `Neg.0` shared one `"0"`
        // slot and the D33 census, which now types `(*e as Neg).0` relative to its
        // downcast (`place_ty_step`), could not find variant 1's field at all.
        // `__tag` is `isize`-wide in the extractor (`pointer_width(tcx)`); 64 here
        // stands for a 64-bit target. The census never reads `__tag`, so the width
        // is not load-bearing for these tests.
        *fields = vec![
            ("__tag".to_string(), Ty::Int { width: 64, signed: true }),
            ("__v0_0".to_string(), Ty::u32()),
            ("__v1_0".to_string(), box_of(Ty::u32())),
        ]
        .into();
    }
    ty
}

/// `match e { Expr::Neg(a) => **a, .. }` for `e: &Expr`: the binding is the borrow
/// `_5 = &((*_1) as Neg).0`, the box is copied out of it, then dereferenced.
fn match_binding_box_deref(scrutinee: Ty, binding_mut: bool) -> (VerifiableFunction, usize) {
    let binding = Rvalue::Ref {
        mutable: binding_mut,
        place: deref_of(1, vec![Projection::Downcast(1), Projection::Field(0)]),
    };
    let stmts = vec![
        assign(Place::local(5), binding),
        assign(Place::local(2), Rvalue::CopyForDeref(deref_of(5, vec![]))),
        box_temp(3, 2, Ty::u32()),
        read_through(0, 3),
    ];
    let read = stmts.len() - 1;
    let f = func(
        "match_binding_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, shared_ref(scrutinee)),
            local(2, box_of(Ty::u32())),
            local(3, raw(Ty::u32())),
            local(4, Ty::u32()),
            local(5, Ty::Ref { mutable: binding_mut, inner: Box::new(box_of(Ty::u32())) }),
        ],
        1,
        vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
    );
    (f, read)
}

#[test]
fn a_match_binding_on_a_reference_parameter_reaches_the_parameter_root() {
    // d3/p09's `Expr::Neg(a) => .. **a ..` shape through `e: &Expr`.
    let (f, read) = match_binding_box_deref(enum_with_box(trust_types::AdtKind::Enum), false);
    let control = messages(&rows_at_installed(&f, &FxHashSet::default(), 0, read));
    assert!(keeps_null_row(&control), "control: {control:?}");
    let rooted = rows_at_installed(&f, &ops(&[(0, read)]), 0, read);
    assert!(rooted.is_empty(), "the binding hop must root at `e`: {:?}", messages(&rooted));
    // D100: the `eval(e: &Expr)` family D100 names. The binding hop re-spells the
    // path to `((*e) as Neg).0`, a root THROUGH the reference argument `e`: no row
    // drops without the premise, and the gate installs (so demotes and discloses) it.
    let bare = messages(&rows_at(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&bare), "no premise, no root through `e`: {bare:?}");
    assert_eq!(d100_gate(&f, &ops(&[(0, read)])), vec![1], "the premise is installed for `e`");
}

#[test]
fn a_union_or_unstamped_scrutinee_keeps_its_rows() {
    // A union's field bytes carry no validity guarantee; an ADT whose kind the
    // extractor did not stamp cannot be read as an enum at all.
    for kind in [trust_types::AdtKind::Union, trust_types::AdtKind::Struct] {
        let (f, read) = match_binding_box_deref(enum_with_box(kind), false);
        let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
        assert!(keeps_null_row(&rows), "{kind:?} scrutinee must keep its rows: {rows:?}");
    }
}

#[test]
fn a_binding_local_with_a_second_value_keeps_its_rows() {
    // `_5` reassigned to another borrow: the `(*_5)` read no longer names ONE place.
    let (mut f, _) = match_binding_box_deref(enum_with_box(trust_types::AdtKind::Enum), false);
    f.body.locals.push(local(6, box_of(Ty::u32())));
    f.body.blocks[0]
        .stmts
        .insert(1, assign(Place::local(5), Rvalue::Ref { mutable: false, place: Place::local(6) }));
    let read = f.body.blocks[0].stmts.len() - 1;
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&rows), "a reseated binding must keep its rows: {rows:?}");
}

#[test]
fn a_box_behind_an_interior_mutability_cell_keeps_its_rows() {
    // `&UnsafeCell<Box<u32>>`-shaped: a shared reference does not freeze the cell,
    // so `(*c).0` is refused even though every other gate passes. CONTROL: the same
    // wrapper under a plain struct name is credited.
    let wrap = |name: &str| sysroot_struct(name, box_of(Ty::u32()));
    let body = |wrapper: Ty| {
        let stmts = vec![
            assign(Place::local(2), Rvalue::CopyForDeref(deref_of(1, vec![Projection::Field(0)]))),
            box_temp(3, 2, Ty::u32()),
            read_through(0, 3),
        ];
        func(
            "cell_box_deref",
            vec![
                local(0, Ty::u32()),
                local(1, shared_ref(wrapper)),
                local(2, box_of(Ty::u32())),
                local(3, raw(Ty::u32())),
            ],
            1,
            vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
        )
    };
    let control = body(wrap("test::Plain"));
    assert!(
        rows_at_installed(&control, &ops(&[(0, 2)]), 0, 2).is_empty(),
        "control: a plain wrapper"
    );
    let cell = body(wrap("core::cell::UnsafeCell"));
    let rows = messages(&rows_at_installed(&cell, &ops(&[(0, 2)]), 0, 2));
    assert!(keeps_null_row(&rows), "an `UnsafeCell` hop must keep its rows: {rows:?}");
}

// ── The reference lane's liveness fences (2026-09-28, independent review of 13c) ──
//
// 13c roots a box read THROUGH a reference at the parameter: the box was valid at
// ENTRY. The review measured the gap that left: `probe(h: &H) { drop(unsafe {
// ptr::read(&h.b) }); *h.b }` duplicates the box through a shared borrow of its
// slot — a place under a `Deref`, which the by-value slot-borrow fence exempts —
// and the read after the drop lost its three rows. Each case below is the same
// `*h.b` read, measured by the same instrument, with ONE hazard added; each
// control is the same body with the hazard made harmless.

fn struct_of(name: &str, fields: Vec<(&str, Ty)>) -> Ty {
    let mut ty = Ty::adt(name, fields.into_iter().map(|(n, t)| (n.to_string(), t)).collect());
    if let Ty::Adt { adt_kind, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Struct);
    }
    ty
}

/// `struct H { b: Box<u32>, n: u32 }`.
fn holder() -> Ty {
    struct_of("test::H", vec![("b", box_of(Ty::u32())), ("n", Ty::u32())])
}

fn call_with(callee: &str, args: Vec<Operand>, dest: usize, unsafe_sig: bool) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: callee.to_string(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(1)),
        span: span(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: unsafe_sig,
        callee_identity: None,
        callee_key: super::tests::fixture_key(callee),
    }
}

/// `fn f(h: &H) -> u32 { <pre>; *h.b }`: `bb0` runs `pre` and ends in `term`
/// (a call into `bb1`, or a plain `goto`); `bb1` reads the box through `reader`
/// (`_1`, or a copy of it in `_9`) as `_2 = copy ((*reader).0)`, mints the temp
/// and reads through it at statement `2` (+1 when `copy_ref` puts `_9 = copy _1`
/// first).
fn ref_struct_box_deref(
    pre: Vec<Statement>,
    term: Option<Terminator>,
    copy_ref: bool,
) -> (VerifiableFunction, usize) {
    let reader = if copy_ref { 9 } else { 1 };
    let mut read_block = Vec::new();
    if copy_ref {
        read_block.push(assign(Place::local(9), Rvalue::Use(Operand::Copy(Place::local(1)))));
    }
    read_block.push(assign(
        Place::local(2),
        Rvalue::Use(Operand::Copy(deref_of(reader, vec![Projection::Field(0)]))),
    ));
    read_block.push(box_temp(3, 2, Ty::u32()));
    read_block.push(read_through(0, 3));
    let read = read_block.len() - 1;
    let union_ty = {
        let mut ty = Ty::adt("test::U", vec![("w".into(), Ty::u32()), ("v".into(), Ty::u32())]);
        if let Ty::Adt { adt_kind, .. } = &mut ty {
            *adt_kind = Some(AdtKind::Union);
        }
        ty
    };
    let f = func(
        "ref_struct_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, shared_ref(holder())),
            local(2, box_of(Ty::u32())),
            local(3, raw(Ty::u32())),
            local(4, shared_ref(box_of(Ty::u32()))),
            local(5, raw(box_of(Ty::u32()))),
            local(6, box_of(Ty::u32())),
            local(7, Ty::Unit),
            local(8, shared_ref(Ty::u32())),
            local(9, shared_ref(holder())),
            local(10, union_ty),
            local(11, Ty::u32()),
        ],
        1,
        vec![
            BasicBlock {
                id: BlockId(0),
                stmts: pre,
                terminator: term.unwrap_or(Terminator::Goto(BlockId(1))),
            },
            BasicBlock { id: BlockId(1), stmts: read_block, terminator: Terminator::Return },
        ],
    );
    (f, read)
}

/// The read's rows with the D100 premise installed ([`rows_at_installed`]), so a
/// refusal below is the liveness fence's, not the missing premise's.
fn ref_lane_rows(f: &VerifiableFunction, read: usize) -> Vec<String> {
    messages(&rows_at_installed(f, &ops(&[(1, read)]), 1, read))
}

/// `_4 = &((*_1).0)` — a shared borrow of the box SLOT, which lives behind `h`.
fn borrow_slot() -> Statement {
    assign(
        Place::local(4),
        Rvalue::Ref { mutable: false, place: deref_of(1, vec![Projection::Field(0)]) },
    )
}

#[test]
fn a_box_read_through_a_reference_to_a_struct_mints_no_deref_rows() {
    // CONTROL for every case below: `*h.b` alone (d3/iso rc11), and with a borrow
    // of the SIBLING field `h.n` handed to a safe call — a disjoint path.
    let (f, read) = ref_struct_box_deref(vec![], None, false);
    let control = messages(&rows_at(&f, &FxHashSet::default(), 1, read));
    assert!(keeps_null_row(&control), "control: uncredited, the deref is charged: {control:?}");
    assert!(ref_lane_rows(&f, read).is_empty(), "`*h.b` through `h: &H` is credited");
    // D100: `&S.b` is a root through the reference argument `h`.
    let bare = messages(&rows_at(&f, &ops(&[(1, read)]), 1, read));
    assert!(keeps_null_row(&bare), "no premise, no root through `h`: {bare:?}");
    assert_eq!(d100_gate(&f, &ops(&[(1, read)])), vec![1], "the premise is installed for `h`");

    let sibling = assign(
        Place::local(8),
        Rvalue::Ref { mutable: false, place: deref_of(1, vec![Projection::Field(1)]) },
    );
    let (f, read) = ref_struct_box_deref(
        vec![sibling],
        Some(call_with("test::helper", vec![Operand::Move(Place::local(8))], 7, false)),
        false,
    );
    assert!(ref_lane_rows(&f, read).is_empty(), "a sibling-field borrow does not reach the slot");

    // A copy of the reference, read only through: still credited.
    let (f, read) = ref_struct_box_deref(vec![], None, true);
    assert!(ref_lane_rows(&f, read).is_empty(), "`let r = h; *r.b` is credited");
}

#[test]
fn a_box_duplicated_through_a_borrow_of_its_slot_behind_a_reference_keeps_its_rows() {
    // The review's rc06: `_4 = &((*_1).0); _5 = &raw const (*_4); _6 = ptr::read(_5)`.
    let raw_of_borrow = assign(Place::local(5), Rvalue::AddressOf(false, deref_of(4, vec![])));
    let (f, read) = ref_struct_box_deref(
        vec![borrow_slot(), raw_of_borrow],
        Some(call_with(
            "core::ptr::read::<alloc::boxed::Box<u32>>",
            vec![Operand::Move(Place::local(5))],
            6,
            true,
        )),
        false,
    );
    let rows = ref_lane_rows(&f, read);
    assert!(keeps_null_row(&rows), "rc06 must keep the deref's rows: {rows:?}");
}

#[test]
fn an_alias_of_the_slot_or_the_reference_handed_to_a_safe_call_keeps_its_rows() {
    // No unsafe operation in the body: the alias fence alone must refuse.
    let helper = |arg: Operand| Some(call_with("test::dup_and_free", vec![arg], 7, false));
    let cases: Vec<(&str, Vec<Statement>, Option<Terminator>, bool)> = vec![
        (
            "`&h.b` handed to a call",
            vec![borrow_slot()],
            helper(Operand::Move(Place::local(4))),
            false,
        ),
        // The review's rc12: `dup_and_free(h); *h.b`.
        ("`h` itself handed to a call", vec![], helper(Operand::Copy(Place::local(1))), false),
        (
            "`&*h` handed to a call",
            vec![assign(
                Place::local(9),
                Rvalue::Ref { mutable: false, place: deref_of(1, vec![]) },
            )],
            helper(Operand::Move(Place::local(9))),
            false,
        ),
        (
            "`h` stored into an aggregate",
            vec![assign(
                Place::local(10),
                Rvalue::Aggregate(
                    trust_types::AggregateKind::Tuple,
                    vec![Operand::Copy(Place::local(1))],
                ),
            )],
            None,
            false,
        ),
        // The box is read through a COPY `_9 = copy _1`; the alias escapes through
        // the ORIGINAL. The walk must keep the path through the copy to see it.
        (
            "the original of a copied reference escapes",
            vec![borrow_slot()],
            helper(Operand::Move(Place::local(4))),
            true,
        ),
    ];
    for (what, pre, term, copy_ref) in cases {
        let (f, read) = ref_struct_box_deref(pre, term, copy_ref);
        let rows = ref_lane_rows(&f, read);
        assert!(keeps_null_row(&rows), "{what} must keep the deref's rows: {rows:?}");
    }
}

#[test]
fn any_unsafe_operation_in_the_body_keeps_the_reference_lane_rows() {
    // An unsafe operation ANYWHERE in the body, touching nothing this local
    // names — a second parameter aliasing `*h`, or a raw pointer into it, is
    // invisible to any per-local scan, so the lane refuses on the operation.
    let unrelated = |unsafe_sig: bool| {
        Some(call_with(
            "test::something",
            vec![Operand::Constant(ConstValue::Uint(3, 32))],
            7,
            unsafe_sig,
        ))
    };
    let (control, read) = ref_struct_box_deref(vec![], unrelated(false), false);
    assert!(ref_lane_rows(&control, read).is_empty(), "control: the same call, safe");

    let cases: Vec<(&str, Vec<Statement>, Option<Terminator>)> = vec![
        ("an `unsafe`-signature call", vec![], unrelated(true)),
        (
            "a cast that mints a `Box` from bits (a lowered `transmute`)",
            vec![assign(
                Place::local(6),
                Rvalue::Cast(Operand::Constant(ConstValue::Uint(8, 64)), box_of(Ty::u32())),
            )],
            None,
        ),
        (
            "a union field read",
            vec![assign(
                Place::local(11),
                Rvalue::Use(Operand::Copy(Place {
                    local: 10,
                    projections: vec![Projection::Field(1)],
                })),
            )],
            None,
        ),
        (
            "a raw-pointer dereference",
            vec![assign(Place::local(11), Rvalue::Use(Operand::Copy(deref_of(5, vec![]))))],
            None,
        ),
    ];
    for (what, pre, term) in cases {
        let (f, read) = ref_struct_box_deref(pre, term, false);
        let rows = ref_lane_rows(&f, read);
        assert!(keeps_null_row(&rows), "{what} must keep the deref's rows: {rows:?}");
    }
}

/// Trust (2026-09-30): NEGATIVE pins of the 2026-09-29 recursive-enum admission.
/// The reference lane credits a `Downcast` — and the `Field` right after it — on a
/// by-name `Ty::Datatype`, because MIR downcasts only enums and coroutines and a
/// RECURSIVE enum lowers to that marker (`rhs_const` in
/// tests/false_refutation_shapes_realmir.rs is the positive side). Two spellings of
/// the same marker are NOT a recursive enum, and nothing else pinned that they stay
/// refused:
///  * `__trust_compacted_aggregate`, which `compact_oversized_field` gives an
///    oversized NON-ADT (a coroutine among them);
///  * a BARE `Field` on a `Ty::Datatype` (no `Downcast` before it): the marker can
///    stand for a compacted UNION, whose field read is an unsafe operation.
///
/// Mutants that accept the compaction marker in `is_recursive_enum_datatype`, or drop
/// the "previous step is a `Downcast`" guard from `ReferenceLaneFacts::touch_place`,
/// turn this red.
#[test]
fn the_recursive_enum_admission_refuses_the_compaction_marker_and_a_bare_field() {
    use super::{
        ReceivedBoxFence, ReferenceLaneFacts, access_path_is_validity_preserving,
        is_recursive_enum_datatype,
    };
    let recursive = Ty::Datatype { name: "Expr".to_string(), variants: vec![] };
    let marker = Ty::Datatype { name: "__trust_compacted_aggregate".to_string(), variants: vec![] };
    assert!(is_recursive_enum_datatype(&recursive), "control: a recursive enum is admitted");
    assert!(!is_recursive_enum_datatype(&marker), "the compaction marker is not an enum");

    // `_1: &D` and one statement `_2 = copy <path>` reading through it.
    let body = |pointee: Ty, path: Vec<Projection>| {
        func(
            "c2_negative_pin",
            vec![
                local(0, Ty::Unit),
                local(1, Ty::Ref { mutable: false, inner: Box::new(pointee) }),
                local(2, Ty::u32()),
            ],
            1,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![assign(
                    Place::local(2),
                    Rvalue::Use(Operand::Copy(Place { local: 1, projections: path })),
                )],
                terminator: Terminator::Return,
            }],
        )
    };
    let variant_field = vec![Projection::Deref, Projection::Downcast(1), Projection::Field(2)];
    let bare_field = vec![Projection::Deref, Projection::Field(2)];
    let fence = ReceivedBoxFence::default();

    // The access path the box root walks.
    let admitted = body(recursive.clone(), variant_field.clone());
    assert!(
        access_path_is_validity_preserving(&admitted, &fence, 1, &variant_field, 0),
        "control: `((*e) as Bin).2` on a recursive enum is a validity-preserving path"
    );
    assert!(
        !access_path_is_validity_preserving(
            &body(marker.clone(), variant_field.clone()),
            &fence,
            1,
            &variant_field,
            0
        ),
        "a `Downcast` of the compaction marker is refused"
    );
    assert!(
        !access_path_is_validity_preserving(
            &body(recursive.clone(), bare_field.clone()),
            &fence,
            1,
            &bare_field,
            0
        ),
        "a bare `Field` on a `Ty::Datatype` is refused (it may be a compacted union's)"
    );

    // The reference lane's unsafe-operation scan of the same reads.
    assert!(
        !ReferenceLaneFacts::build(&admitted).unsafe_operation,
        "control: a variant-field read of a recursive enum is not an unsafe operation"
    );
    assert!(
        ReferenceLaneFacts::build(&body(recursive, bare_field)).unsafe_operation,
        "a bare `Field` on a `Ty::Datatype` cannot be typed and fails the lane closed"
    );
}

// ── the recursive-enum `Ty::Datatype` admission (B2 (c2), 2026-09-29) ────────────
//
// A RECURSIVE enum lowers to a by-name `Ty::Datatype`, and B2 let the reference
// lane credit a `Downcast` (and the `Field` right after it) on one: MIR downcasts
// only enums and coroutines. Three things must stay refused, and until 2026-09-30
// no test caught a mutant that admitted any of them (the real-MIR pins in
// `tests/false_refutation_shapes_realmir.rs` hold no marker and no bare field):
//  * the generic compaction marker `__trust_compacted_aggregate`, which
//    `compact_oversized_field` gives an oversized NON-ADT (a coroutine among them);
//  * a bare `Field` (no `Downcast`) on a `Ty::Datatype` — the same spelling can
//    stand for a compacted UNION, whose field bytes carry no validity guarantee;
//  * anywhere in the body, a READ of a bare `Field` of a multi-variant
//    `Ty::Datatype`, whose type the reference lane's walk cannot follow (the
//    `touch_place` early return is for a `Field` right after a `Downcast` only).

/// `enum Expr { Num(u32), Neg(Box<u32>) }` spelled the way the extractor spells a
/// RECURSIVE enum: a by-name `Ty::Datatype` with its variants.
fn datatype_enum_with_box(name: &str) -> Ty {
    Ty::Datatype {
        name: name.into(),
        variants: vec![
            ("Num".into(), vec![("0".into(), Ty::u32())]),
            ("Neg".into(), vec![("0".into(), box_of(Ty::u32()))]),
        ],
    }
}

/// `match_binding_box_deref` with the binding's projections below `(*e)` given,
/// and `extra` statements ahead of it.
fn binding_box_deref(
    scrutinee: Ty,
    below_deref: Vec<Projection>,
    extra: Vec<Statement>,
) -> (VerifiableFunction, usize) {
    let binding = Rvalue::Ref { mutable: false, place: deref_of(1, below_deref) };
    let mut stmts = extra;
    stmts.extend([
        assign(Place::local(5), binding),
        assign(Place::local(2), Rvalue::CopyForDeref(deref_of(5, vec![]))),
        box_temp(3, 2, Ty::u32()),
        read_through(0, 3),
    ]);
    let read = stmts.len() - 1;
    let f = func(
        "binding_box_deref",
        vec![
            local(0, Ty::u32()),
            local(1, shared_ref(scrutinee)),
            local(2, box_of(Ty::u32())),
            local(3, raw(Ty::u32())),
            local(4, Ty::u32()),
            local(5, shared_ref(box_of(Ty::u32()))),
        ],
        1,
        vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
    );
    (f, read)
}

fn variant_field(variant: usize, field: usize) -> Vec<Projection> {
    vec![Projection::Downcast(variant), Projection::Field(field)]
}

#[test]
fn a_match_binding_on_a_recursive_enum_datatype_reaches_the_parameter_root() {
    // CONTROL for the three refusals below: the admission itself.
    let (f, read) =
        binding_box_deref(datatype_enum_with_box("test::Expr"), variant_field(1, 0), vec![]);
    let control = messages(&rows_at_installed(&f, &FxHashSet::default(), 0, read));
    assert!(keeps_null_row(&control), "control: uncredited, the deref is charged: {control:?}");
    let rooted = rows_at_installed(&f, &ops(&[(0, read)]), 0, read);
    assert!(
        rooted.is_empty(),
        "`**a` for `Expr::Neg(a)` bound out of `e: &Expr`, `Expr` recursive: {:?}",
        messages(&rooted)
    );
    // D100: the recursive `eval(e: &Expr)` shape roots through `e` only under the
    // premise, which the gate installs.
    let bare = messages(&rows_at(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&bare), "no premise, no root through `e`: {bare:?}");
    assert_eq!(d100_gate(&f, &ops(&[(0, read)])), vec![1], "the premise is installed for `e`");
}

// ── a store's destination is charged whatever its source is (2026-10-01) ────
//
// `interpret_assign` used to match the RVALUE first: the raw-read, pointer
// arithmetic, cast and address-of arms all preceded the raw-WRITE arm, so a store
// through a raw pointer whose source matched one of them minted no destination
// row (`unsafe { *p = x as u32 }` kept no `[unsafe:sep:*]` row on the stage-1
// `trustc` of main). And those arms bound the DESTINATION's local as if the whole
// local were assigned, re-binding a pointer stored THROUGH.

fn seven() -> Operand {
    Operand::Constant(ConstValue::Uint(7, 32))
}

/// `fn f(p: *mut u32, x: u64, q: *const u32) { (*_1) = <rvalue> }`.
fn raw_store_of(rvalue: Rvalue) -> VerifiableFunction {
    func(
        "raw_store_of",
        vec![
            local(0, Ty::Unit),
            local(1, Ty::RawPtr { mutable: true, pointee: Box::new(Ty::u32()) }),
            local(2, Ty::u64()),
            local(3, raw(Ty::u32())),
        ],
        3,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![assign(deref_of(1, vec![]), rvalue)],
            terminator: Terminator::Return,
        }],
    )
}

#[test]
fn a_raw_store_keeps_its_write_rows_whatever_its_source() {
    let cases: Vec<(&str, Rvalue)> = vec![
        ("a constant (the control)", Rvalue::Use(seven())),
        ("a cast", Rvalue::Cast(Operand::Copy(Place::local(2)), Ty::u32())),
        (
            "an `Add`",
            Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Copy(Place::local(2)),
                Operand::Constant(ConstValue::Uint(7, 64)),
            ),
        ),
        ("a raw read", Rvalue::Use(Operand::Copy(deref_of(3, vec![])))),
        ("an address-of", Rvalue::AddressOf(false, Place::local(2))),
    ];
    for (what, rvalue) in cases {
        let rows = messages(&rows_at(&raw_store_of(rvalue), &FxHashSet::default(), 0, 0));
        assert!(
            rows.iter().any(|m| m.starts_with("[unsafe:sep:write] write permission for *_1")),
            "a raw store of {what} must keep its write row: {rows:?}"
        );
    }
    // The SOURCE's rows are kept beside the destination's: the raw read of `*_3`.
    let rows = messages(&rows_at(
        &raw_store_of(Rvalue::Use(Operand::Copy(deref_of(3, vec![])))),
        &FxHashSet::default(),
        0,
        0,
    ));
    assert!(
        rows.iter().any(|m| m.starts_with("[unsafe:sep:deref] null check for *_3")),
        "the raw read's own rows stay: {rows:?}"
    );
}

#[test]
fn the_compaction_marker_is_not_a_recursive_enum() {
    assert!(super::is_recursive_enum_datatype(&datatype_enum_with_box("test::Expr")));
    assert!(!super::is_recursive_enum_datatype(&datatype_enum_with_box(
        "__trust_compacted_aggregate"
    )));
    assert!(!super::is_recursive_enum_datatype(&Ty::Datatype {
        name: "__trust_compacted_aggregate".into(),
        variants: vec![],
    }));
    // End to end: the same credited body over the marker keeps its rows.
    let (f, read) = binding_box_deref(
        datatype_enum_with_box("__trust_compacted_aggregate"),
        variant_field(1, 0),
        vec![],
    );
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&rows), "a downcast of the compaction marker is not credited: {rows:?}");
}

#[test]
fn a_bare_field_of_a_datatype_on_the_box_path_keeps_its_rows() {
    // A single-variant `Ty::Datatype` whose field IS typeable by the walk (variant 0),
    // reached with no `Downcast`: the spelling of a compacted union or struct.
    let one_variant = Ty::Datatype {
        name: "test::Compacted".into(),
        variants: vec![("U".into(), vec![("0".into(), box_of(Ty::u32()))])],
    };
    let (f, read) = binding_box_deref(one_variant, vec![Projection::Field(0)], vec![]);
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(keeps_null_row(&rows), "a bare `Field` on a `Ty::Datatype` is not credited: {rows:?}");
}

#[test]
fn a_bare_field_read_of_a_datatype_anywhere_keeps_the_reference_lane_rows() {
    // The credited control body, plus `_4 = copy (*e).0` — a bare `Field` of the
    // two-variant `Ty::Datatype`, which the lane's walk cannot type.
    let bare_read = assign(
        Place::local(4),
        Rvalue::Use(Operand::Copy(deref_of(1, vec![Projection::Field(0)]))),
    );
    let (f, read) = binding_box_deref(
        datatype_enum_with_box("test::Expr"),
        variant_field(1, 0),
        vec![bare_read],
    );
    let rows = messages(&rows_at_installed(&f, &ops(&[(0, read)]), 0, read));
    assert!(
        keeps_null_row(&rows),
        "an untypeable bare `Field` read in the body refuses the reference lane: {rows:?}"
    );
}

#[test]
fn a_store_through_a_local_does_not_rebind_that_local() {
    // `(*_2) = copy _4 as *const u32` through a `Box::new` root's temp: the cast
    // arm used to bind `_2` to `_4`'s allocation, and the box-deref crediting
    // reads `_2`'s binding for its freed-check. CONTROL: the same cast into the
    // WHOLE local `_5` does bind it.
    use super::SepEngine;
    let ptr_ty = raw(Ty::u32());
    let tys = vec![
        Ty::Unit,
        box_of(ptr_ty.clone()),
        raw(ptr_ty.clone()),
        Ty::u32(),
        ptr_ty.clone(),
        ptr_ty.clone(),
        shared_ref(shared_ref(Ty::u32())),
        shared_ref(Ty::u32()),
    ];
    let mut engine = SepEngine::new("rebind").with_local_tys(tys);
    engine.enter_block(0, true);
    engine.interpret_terminator(&call_into(BOX_NEW, 1, 1, false, false));
    engine.enter_block(1, true);
    for stmt in [
        box_temp(2, 1, ptr_ty.clone()),
        assign(Place::local(4), Rvalue::AddressOf(false, Place::local(3))),
        assign(deref_of(2, vec![]), Rvalue::Cast(Operand::Copy(Place::local(4)), ptr_ty.clone())),
        assign(Place::local(5), Rvalue::Cast(Operand::Copy(Place::local(4)), ptr_ty.clone())),
    ] {
        engine.interpret_statement(&stmt, &span());
    }
    let box_name = engine.local_to_ptr.get(&1).cloned();
    assert!(box_name.is_some(), "the `Box::new` result is tracked");
    assert_eq!(engine.local_to_ptr.get(&2).cloned(), box_name, "the temp still names the box");
    assert_eq!(
        engine.local_to_ptr.get(&5),
        engine.local_to_ptr.get(&4),
        "control: a whole-local cast inherits the source's binding"
    );
    // The `Ref` arm, which runs AFTER the store half: `(*_6) = &_3` stores a
    // reference through the reference `_6` (no raw deref, so no store row), and
    // `interpret_ref` binds its destination's local. CONTROL: `_7 = &_3` does.
    for stmt in [
        assign(deref_of(6, vec![]), Rvalue::Ref { mutable: false, place: Place::local(3) }),
        assign(Place::local(7), Rvalue::Ref { mutable: false, place: Place::local(3) }),
    ] {
        engine.interpret_statement(&stmt, &span());
    }
    assert_eq!(engine.local_to_ptr.get(&6), None, "a `&_3` stored through `_6` binds no `_6`");
    assert!(engine.local_to_ptr.contains_key(&7), "control: a whole-local `&_3` binds `_7`");
}

// ── D14: a `Box` behind a reference ARGUMENT (REFERENCE_ARG_BOX_VALID) ────

/// `fn f(b: &Box<u32>) -> u32 { **b }` after `ElaborateBoxDerefs`: `bb0` copies
/// the box out of the argument's pointee (`_2 = copy (*_1)`), mints the temp
/// and reads through it at statement 2. `extra` statements go first; `param` is
/// `_1`'s type and `pointee_path` the projection below `(*_1)` the box sits at.
fn ref_box_deref_with(
    param: Ty,
    pointee_path: Vec<Projection>,
    extra_locals: Vec<LocalDecl>,
    extra: Vec<Statement>,
    terminator: Terminator,
) -> VerifiableFunction {
    let mut stmts = extra;
    let mut src = vec![Projection::Deref];
    src.extend(pointee_path);
    stmts.push(Statement::Assign {
        place: Place::local(2),
        rvalue: Rvalue::CopyForDeref(Place { local: 1, projections: src }),
        span: span(),
    });
    stmts.push(box_temp(3, 2, Ty::u32()));
    stmts.push(read_through(0, 3));
    let mut locals = vec![
        local(0, Ty::u32()),
        local(1, param),
        local(2, box_of(Ty::u32())),
        local(3, raw(Ty::u32())),
    ];
    locals.extend(extra_locals);
    func(
        "ref_box_deref",
        locals,
        1,
        vec![
            BasicBlock { id: BlockId(0), stmts, terminator },
            BasicBlock { id: BlockId(1), stmts: vec![], terminator: Terminator::Return },
        ],
    )
}

fn ref_box_deref(extra_locals: Vec<LocalDecl>, extra: Vec<Statement>) -> VerifiableFunction {
    ref_box_deref_with(
        shared_ref(box_of(Ty::u32())),
        vec![],
        extra_locals,
        extra,
        Terminator::Goto(BlockId(1)),
    )
}

/// The statement index of the `*temp` read: the last statement of `bb0`.
fn ref_deref_index(f: &VerifiableFunction) -> usize {
    f.body.blocks[0].stmts.len() - 1
}

/// The deref rows of `f`'s nominated `*temp` read with the D14 premise
/// installed for `params` (no context at all when `None`).
fn ref_rows(f: &VerifiableFunction, params: Option<&[usize]>) -> Vec<String> {
    let at = ref_deref_index(f);
    let set = ops(&[(0, at)]);
    let run = || messages(&rows_at(f, &set, 0, at));
    match params {
        Some(params) => {
            let context = crate::VcgenContext::for_function(f.def_path.clone())
                .with_reference_box_root_params(params.to_vec());
            crate::with_vcgen_context(&context, run)
        }
        None => run(),
    }
}

fn would_fire(f: &VerifiableFunction) -> Vec<usize> {
    let at = ref_deref_index(f);
    super::reference_box_root_would_fire(f, &ops(&[(0, at)]), &[1])
}

#[test]
fn a_box_behind_a_reference_argument_roots_only_under_the_installed_premise() {
    let f = ref_box_deref(vec![], vec![]);
    // D100 (2026-10-14; stale merge expectation corrected). The merge of 2026-10-14
    // pinned here that main's 13c reference lane roots this plain `**b` on its own,
    // with no premise, so the gate did not fire and the body kept `KernelCertified`
    // rows resting on an undisclosed premise. That expectation was wrong by
    // R1 (one premise, one grade): a box 13c roots THROUGH a reference
    // argument rests on REFERENCE_ARG_BOX_VALID, so it roots only where the premise
    // is installed, and the gate fires for it (the pre-merge expectation, restored).
    for params in [None, Some(&[][..]), Some(&[0usize][..])] {
        let rows = ref_rows(&f, params);
        assert!(keeps_deref_rows(&rows), "no premise for `_1` ({params:?}): {rows:?}");
    }
    let rows = ref_rows(&f, Some(&[1]));
    assert!(rows.is_empty(), "the installed premise roots the box: {rows:?}");
    assert_eq!(would_fire(&f), vec![1], "so the gate installs, demotes and discloses it");
}

#[test]
fn a_box_behind_a_mut_reference_argument_roots_too() {
    let f = ref_box_deref_with(
        Ty::Ref { mutable: true, inner: Box::new(box_of(Ty::u32())) },
        vec![],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    assert!(ref_rows(&f, Some(&[1])).is_empty());
    // D100 (stale merge expectation corrected, see the test above): main's 13c lane
    // roots a `&mut Box` argument too, and that root needs the premise as well.
    assert!(keeps_deref_rows(&ref_rows(&f, None)));
    assert_eq!(would_fire(&f), vec![1]);
}

/// Each mutant keeps its rows WITH the premise installed, and the install gate
/// does not fire for it.
fn assert_refused(f: &VerifiableFunction, what: &str) {
    let rows = ref_rows(f, Some(&[1]));
    assert!(keeps_deref_rows(&rows), "{what}: must keep the deref rows: {rows:?}");
    assert!(would_fire(f).is_empty(), "{what}: the install gate must not fire");
}

/// `evil(copy _arg)` returning into `_0`, continuing at `bb1`.
fn evil_call(arg: usize) -> Terminator {
    Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "evil".to_string(),
        args: vec![Operand::Copy(Place::local(arg))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: span(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: super::tests::fixture_key("evil"),
    }
}

#[test]
fn a_shared_hand_out_of_the_box_slot_is_refused() {
    // `evil(b)`: `_4 = &(*_1)` reaches a callee that can `ptr::read` a duplicate
    // of the box and drop it — a use-after-free with no write to `*b`.
    let reborrow = || {
        ref_box_deref_with(
            shared_ref(box_of(Ty::u32())),
            vec![],
            vec![local(4, shared_ref(box_of(Ty::u32())))],
            vec![assign(
                Place::local(4),
                Rvalue::Ref { mutable: false, place: deref_of(1, vec![]) },
            )],
            evil_call(4),
        )
    };
    assert_refused(&reborrow(), "shared `&(*_1)` passed to a call");
    // Trust (2026-10-11, sweep c67): a shared reborrow of the slot that is used
    // only the confined way (here not at all) hands nothing out, and is admitted
    // like the argument itself (`shared_pointee_alias_is_confined`).
    let mut unused = reborrow();
    unused.body.blocks[0].terminator = Terminator::Goto(BlockId(1));
    assert!(ref_rows(&unused, Some(&[1])).is_empty(), "an unused reborrow hands nothing out");
}

#[test]
fn the_reference_itself_passed_to_a_call_is_refused() {
    let mut f = ref_box_deref(vec![], vec![]);
    f.body.blocks[0].terminator = Terminator::Call {
        unwind: UnwindEdge::Unreachable,
        func: "evil".to_string(),
        args: vec![Operand::Copy(Place::local(1))],
        dest: Place::local(0),
        target: Some(BlockId(1)),
        span: span(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: super::tests::fixture_key("evil"),
    };
    assert_refused(&f, "`copy _1` as a call argument");
}

#[test]
fn a_copy_or_cast_of_the_reference_is_refused() {
    let copy = ref_box_deref(
        vec![local(4, shared_ref(box_of(Ty::u32())))],
        vec![assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(1))))],
    );
    // D100 (stale merge expectation corrected): D14 still refuses a bare `copy _1`
    // (R-e), but main's 13c lane credits a copy of the reference that is never read
    // (`alias_is_inert`: it can hand nothing out). That root is THROUGH the argument
    // `_1`, so it needs the premise, and the gate installs it.
    assert!(ref_rows(&copy, Some(&[1])).is_empty(), "the 13c lane credits an inert copy");
    assert!(keeps_deref_rows(&ref_rows(&copy, None)), "but only under the premise");
    assert_eq!(would_fire(&copy), vec![1], "`_4 = copy _1`: the gate installs the premise");
    // The same copy handed to a call is refused by both lanes.
    let mut passed = copy.clone();
    passed.body.blocks[0].terminator = evil_call(4);
    assert_refused(&passed, "`_4 = copy _1` passed to a call");
    let cast = ref_box_deref(
        vec![local(4, raw(box_of(Ty::u32())))],
        vec![assign(
            Place::local(4),
            Rvalue::Cast(Operand::Copy(Place::local(1)), raw(box_of(Ty::u32()))),
        )],
    );
    assert_refused(&cast, "`Cast(copy _1)`");
}

#[test]
fn a_raw_borrow_or_a_store_through_the_reference_is_refused() {
    let raw_borrow = ref_box_deref(
        vec![local(4, raw(box_of(Ty::u32())))],
        vec![assign(Place::local(4), Rvalue::AddressOf(false, deref_of(1, vec![])))],
    );
    assert_refused(&raw_borrow, "`&raw const (*_1)`");
    let store = ref_box_deref_with(
        Ty::Ref { mutable: true, inner: Box::new(box_of(Ty::u32())) },
        vec![],
        vec![],
        vec![assign(deref_of(1, vec![]), Rvalue::Use(Operand::Copy(Place::local(2))))],
        Terminator::Goto(BlockId(1)),
    );
    assert_refused(&store, "`(*_1) = …`");
}

#[test]
fn a_raw_pointer_or_double_reference_argument_is_refused() {
    let raw_param = ref_box_deref_with(
        raw(box_of(Ty::u32())),
        vec![],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    assert_refused(&raw_param, "`*const Box` argument");
    let double = ref_box_deref_with(
        shared_ref(shared_ref(box_of(Ty::u32()))),
        vec![Projection::Deref],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    // D100 (stale merge expectation corrected): D14 still refuses two derefs
    // (R-c/d), but main's 13c lane admits a reference `Deref` at any depth. The
    // `&&Box` read is a root through the argument `_1`, so it is credited only
    // under the premise, and the gate installs it.
    assert!(ref_rows(&double, Some(&[1])).is_empty(), "the 13c lane credits `**&&Box`");
    assert!(keeps_deref_rows(&ref_rows(&double, None)), "but only under the premise");
    assert_eq!(would_fire(&double), vec![1], "`&&Box` (two derefs): the gate installs it");
}

#[test]
fn a_non_parameter_reference_is_refused() {
    let mut f = ref_box_deref(vec![], vec![]);
    f.body.arg_count = 0;
    assert_refused(&f, "a `&Box` local that is not an argument");
}

#[test]
fn dropping_or_moving_a_copy_of_the_box_is_refused() {
    let mut dropped = ref_box_deref(vec![], vec![]);
    dropped.body.blocks[0].terminator = drop_then(2, 1);
    assert_refused(&dropped, "`Drop` of the hop copy");
    // A SECOND copy of the box, dropped: the walk's own hop is clean, but the
    // confinement of `_1` refuses every copy of the box path that is not
    // deref-only.
    let mut second = ref_box_deref(
        vec![local(4, box_of(Ty::u32()))],
        vec![assign(Place::local(4), Rvalue::CopyForDeref(deref_of(1, vec![])))],
    );
    second.body.blocks[0].terminator = drop_then(4, 1);
    assert_refused(&second, "a dropped second copy");
    // (Block order is irrelevant to the whole-body walk, so the move sits in
    // `extra`, keeping the `*temp` read the last statement.)
    let moved = ref_box_deref(
        vec![local(4, box_of(Ty::u32()))],
        vec![assign(Place::local(4), Rvalue::Use(Operand::Move(Place::local(2))))],
    );
    assert_refused(&moved, "a move of the hop copy");
}

fn pair_of_u32_and_box() -> Ty {
    Ty::Tuple(vec![Ty::u32(), box_of(Ty::u32())])
}

#[test]
fn a_disjoint_sibling_read_or_borrow_stays_admitted_an_overlapping_one_does_not() {
    let pair_then = |extra_locals, extra, terminator| {
        ref_box_deref_with(
            shared_ref(pair_of_u32_and_box()),
            vec![Projection::Field(1)],
            extra_locals,
            extra,
            terminator,
        )
    };
    let pair = |extra_locals, extra| pair_then(extra_locals, extra, Terminator::Goto(BlockId(1)));
    let plain = pair(vec![], vec![]);
    assert!(ref_rows(&plain, Some(&[1])).is_empty(), "the box at `(*_1).1` roots");
    let read = pair(
        vec![local(4, Ty::u32())],
        vec![assign(
            Place::local(4),
            Rvalue::Use(Operand::Copy(deref_of(1, vec![Projection::Field(0)]))),
        )],
    );
    assert!(ref_rows(&read, Some(&[1])).is_empty(), "a sibling read is confined");
    let borrow_sibling = pair(
        vec![local(4, shared_ref(Ty::u32()))],
        vec![assign(
            Place::local(4),
            Rvalue::Ref { mutable: false, place: deref_of(1, vec![Projection::Field(0)]) },
        )],
    );
    assert!(ref_rows(&borrow_sibling, Some(&[1])).is_empty(), "a disjoint borrow is confined");
    // An overlapping borrow is refused once it can reach a callee (sweep c67 admits
    // one whose every use is confined).
    let borrow_box = pair_then(
        vec![local(4, shared_ref(box_of(Ty::u32())))],
        vec![assign(
            Place::local(4),
            Rvalue::Ref { mutable: false, place: deref_of(1, vec![Projection::Field(1)]) },
        )],
        evil_call(4),
    );
    assert_refused(&borrow_box, "`&(*_1).1` hands out the box slot");
    let borrow_whole = pair_then(
        vec![local(4, shared_ref(pair_of_u32_and_box()))],
        vec![assign(Place::local(4), Rvalue::Ref { mutable: false, place: deref_of(1, vec![]) })],
        evil_call(4),
    );
    assert_refused(&borrow_whole, "`&(*_1)` contains the box slot");
}

#[test]
fn a_box_in_a_union_field_behind_a_reference_is_refused() {
    let mut union = Ty::adt("test::U", vec![("0".to_string(), box_of(Ty::u32()))]);
    if let Ty::Adt { adt_kind, .. } = &mut union {
        *adt_kind = Some(AdtKind::Union);
    }
    let f = ref_box_deref_with(
        shared_ref(union),
        vec![Projection::Field(0)],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    assert_refused(&f, "a union field");
}

#[test]
fn a_box_inside_an_unsafe_cell_behind_a_reference_is_refused() {
    // CONTROL: the same shape through an ordinary struct roots.
    let plain = ref_box_deref_with(
        shared_ref(sysroot_struct("test::Plain", box_of(Ty::u32()))),
        vec![Projection::Field(0)],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    assert!(ref_rows(&plain, Some(&[1])).is_empty(), "control: a struct field roots");
    let cell = ref_box_deref_with(
        shared_ref(sysroot_struct("core::cell::UnsafeCell", box_of(Ty::u32()))),
        vec![Projection::Field(0)],
        vec![],
        vec![],
        Terminator::Goto(BlockId(1)),
    );
    assert_refused(&cell, "a box inside an `UnsafeCell`");
}

// ── review round 85: every synthesized box-pointer temp is fenced ──────

/// `param_box_deref` (owned `b`, deref temp `_2`) plus a SECOND synthesized
/// box-pointer temp `_4 = copy ((_1.0).0) as *const u32` (another `*b` of the
/// same box) and `extra` uses of it, with spare locals `_5: ty5`, `_6: ty6`;
/// when `call_arg` is set, `bb1` passes `move _5` to a call before returning.
/// The deref under test is the ORIGINAL temp's read.
fn owned_box_with_temp_uses(
    extra: Vec<Statement>,
    ty5: Ty,
    ty6: Ty,
    call_arg: bool,
) -> (VerifiableFunction, usize) {
    owned_box_with_temp_call(extra, ty5, ty6, call_arg.then_some(("user::take", Ty::u32())))
}

/// [`owned_box_with_temp_uses`] with the call's callee path and result type.
fn owned_box_with_temp_call(
    extra: Vec<Statement>,
    ty5: Ty,
    ty6: Ty,
    call: Option<(&str, Ty)>,
) -> (VerifiableFunction, usize) {
    let mut stmts = vec![box_temp(4, 1, Ty::u32())];
    stmts.extend(extra);
    let n = stmts.len();
    let mut f = param_box_deref(stmts);
    f.body.locals.push(local(4, raw(Ty::u32())));
    f.body.locals.push(local(5, ty5));
    f.body.locals.push(local(6, ty6));
    if let Some((callee, result_ty)) = call {
        f.body.locals.push(local(7, result_ty));
        f.body.blocks[1].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: callee.to_string(),
            args: vec![Operand::Move(Place::local(5))],
            dest: Place::local(7),
            target: Some(BlockId(2)),
            span: span(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: super::tests::fixture_key(callee),
        };
        f.body.blocks.push(BasicBlock {
            id: BlockId(2),
            stmts: vec![],
            terminator: Terminator::Return,
        });
    }
    (f, n + 1)
}

fn temp_rows(f: &VerifiableFunction, at: usize) -> Vec<String> {
    messages(&rows_at(f, &ops(&[(0, at)]), 0, at))
}

fn deref_of_second_temp() -> Place {
    Place { local: 4, projections: vec![Projection::Deref] }
}

#[test]
fn a_second_unused_box_pointer_temp_is_harmless() {
    let (f, at) = owned_box_with_temp_uses(vec![], Ty::u32(), Ty::u32(), false);
    assert!(temp_rows(&f, at).is_empty(), "control: a second deref temp fences nothing");
}

#[test]
fn a_raw_pointer_to_the_box_allocation_reaching_anything_but_ptr_metadata_keeps_the_rows() {
    // `sink(addr_of!(*b)); *b`: the raw pointer carries the box's own tag, so
    // the callee may `Box::from_raw` it and free the allocation the LATER deref
    // (a different temp) reads.
    let raw_u32 = raw(Ty::u32());
    let (escaped, at) = owned_box_with_temp_uses(
        vec![
            assign(Place::local(5), Rvalue::AddressOf(false, deref_of_second_temp())),
            assign(Place::local(6), Rvalue::Use(Operand::Copy(Place::local(5)))),
        ],
        raw_u32.clone(),
        raw_u32.clone(),
        false,
    );
    assert!(keeps_deref_rows(&temp_rows(&escaped, at)), "an escaping `&raw (*_t)` keeps the rows");
    let (passed, at) = owned_box_with_temp_uses(
        vec![assign(Place::local(5), Rvalue::AddressOf(false, deref_of_second_temp()))],
        raw_u32.clone(),
        Ty::u32(),
        true,
    );
    assert!(keeps_deref_rows(&temp_rows(&passed, at)), "`sink(addr_of!(*b))` keeps the rows");
    // CONTROL: the compiler's fake borrow for a length, read only by PtrMetadata.
    let (metadata, at) = owned_box_with_temp_uses(
        vec![
            assign(Place::local(5), Rvalue::AddressOf(false, deref_of_second_temp())),
            assign(
                Place::local(6),
                Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, Operand::Move(Place::local(5))),
            ),
        ],
        raw_u32,
        Ty::usize(),
        false,
    );
    assert!(temp_rows(&metadata, at).is_empty(), "a PtrMetadata-only raw borrow roots");
    // The extracted spelling of that fake borrow: `PtrMetadata(copy _t)`.
    let (folded, at) = owned_box_with_temp_uses(
        vec![assign(
            Place::local(6),
            Rvalue::UnaryOp(trust_types::UnOp::PtrMetadata, Operand::Copy(Place::local(4))),
        )],
        Ty::u32(),
        Ty::usize(),
        false,
    );
    assert!(temp_rows(&folded, at).is_empty(), "`PtrMetadata(copy _t)` roots");
}

#[test]
fn a_copy_of_a_box_pointer_temp_keeps_the_rows() {
    let (f, at) = owned_box_with_temp_uses(
        vec![assign(Place::local(5), Rvalue::Use(Operand::Copy(Place::local(4))))],
        raw(Ty::u32()),
        Ty::u32(),
        false,
    );
    assert!(keeps_deref_rows(&temp_rows(&f, at)), "`_5 = copy _t` keeps the rows");
}

#[test]
fn a_box_pointer_cast_into_a_projection_keeps_the_rows() {
    let mut f = param_box_deref(vec![Statement::Assign {
        place: Place { local: 5, projections: vec![Projection::Field(0)] },
        rvalue: Rvalue::Cast(
            Operand::Copy(Place {
                local: 1,
                projections: vec![Projection::Field(0), Projection::Field(0)],
            }),
            raw(Ty::u32()),
        ),
        span: span(),
    }]);
    f.body.locals.push(local(4, Ty::u32()));
    f.body.locals.push(local(5, Ty::Tuple(vec![raw(Ty::u32())])));
    assert!(keeps_deref_rows(&temp_rows(&f, 2)), "a box pointer stored in a field keeps the rows");
}

#[test]
fn a_shared_reborrow_of_a_cell_free_pointee_roots_a_mutable_one_only_when_contained() {
    let shared_u32 = shared_ref(Ty::u32());
    let (shared, at) = owned_box_with_temp_uses(
        vec![
            assign(Place::local(5), Rvalue::Ref { mutable: false, place: deref_of_second_temp() }),
            assign(Place::local(6), Rvalue::Use(Operand::Copy(Place::local(5)))),
        ],
        shared_u32.clone(),
        shared_u32,
        false,
    );
    assert!(temp_rows(&shared, at).is_empty(), "a shared reborrow of a `u32` is read-only");
    let mut_u32 = Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) };
    let reborrow =
        || assign(Place::local(5), Rvalue::Ref { mutable: true, place: deref_of_second_temp() });
    // Review round 86: a protected call argument is NOT contained — the callee
    // can return or stash a pointer derived from it (`NonNull::from(&mut *b)`).
    let (user, at) = owned_box_with_temp_call(
        vec![reborrow()],
        mut_u32.clone(),
        Ty::u32(),
        Some(("user::take", Ty::u32())),
    );
    assert!(
        keeps_deref_rows(&temp_rows(&user, at)),
        "a `&mut (*_t)` passed to a user callee keeps the rows"
    );
    let nonnull = sysroot_struct("core::ptr::non_null::NonNull", raw(Ty::u32()));
    let (returned, at) = owned_box_with_temp_call(
        vec![reborrow()],
        mut_u32.clone(),
        Ty::u32(),
        Some(("core::ptr::NonNull::<u32>::from", nonnull)),
    );
    assert!(
        keeps_deref_rows(&temp_rows(&returned, at)),
        "a sysroot callee whose result carries a pointer keeps the rows"
    );
    let (stored, at) = owned_box_with_temp_uses(
        vec![reborrow(), assign(Place::local(6), Rvalue::Use(Operand::Move(Place::local(5))))],
        mut_u32.clone(),
        mut_u32.clone(),
        false,
    );
    assert!(
        temp_rows(&stored, at).is_empty(),
        "a copy of a contained `&mut` used nowhere else is contained"
    );
    let (raw_cast, at) = owned_box_with_temp_uses(
        vec![
            reborrow(),
            assign(Place::local(6), Rvalue::Cast(Operand::Copy(Place::local(5)), raw(Ty::u32()))),
        ],
        mut_u32.clone(),
        raw(Ty::u32()),
        false,
    );
    assert!(keeps_deref_rows(&temp_rows(&raw_cast, at)), "`&mut *b as *mut _` keeps the rows");
    // CONTROLS: `mem::replace(&mut *b, 0)` (sysroot, scalar result, scalar
    // argument) and a local `&mut` used only for a store through it.
    let (mut replace, at) = owned_box_with_temp_call(
        vec![reborrow()],
        mut_u32.clone(),
        Ty::u32(),
        Some(("core::mem::replace::<u32>", Ty::u32())),
    );
    // The display path alone is not enough: the compiler-resolved key must say
    // real sysroot.
    assert!(
        keeps_deref_rows(&temp_rows(&replace, at)),
        "a sysroot-SPELLED callee without a real-sysroot key keeps the rows"
    );
    if let Terminator::Call { callee_key, .. } = &mut replace.body.blocks[1].terminator {
        *callee_key = Some(real_sysroot_key());
    }
    assert!(temp_rows(&replace, at).is_empty(), "a pointer-free sysroot call is contained");
    // A user ADT pointee: a generic sysroot routine could hand the `&mut` to a
    // user impl (`Clone::clone_from`, `clone_from_slice`).
    let mut user_adt = replace.clone();
    let s_ty = sysroot_struct("user::S", Ty::u32());
    for decl in &mut user_adt.body.locals {
        if decl.index == 5 {
            decl.ty = Ty::Ref { mutable: true, inner: Box::new(s_ty.clone()) };
        }
    }
    assert!(
        keeps_deref_rows(&temp_rows(&user_adt, at)),
        "a `&mut` to a user ADT passed to a sysroot callee keeps the rows"
    );
    let (local_store, at) = owned_box_with_temp_uses(
        vec![
            reborrow(),
            assign(
                Place { local: 5, projections: vec![Projection::Deref] },
                Rvalue::Use(Operand::Constant(ConstValue::Uint(5, 32))),
            ),
        ],
        mut_u32,
        Ty::u32(),
        false,
    );
    assert!(
        temp_rows(&local_store, at).is_empty(),
        "a `&mut` used only to store through is contained"
    );
}

#[test]
fn a_store_of_a_non_constant_value_through_a_box_pointer_is_admitted() {
    let (f, at) = owned_box_with_temp_uses(
        vec![assign(
            Place { local: 4, projections: vec![Projection::Deref] },
            Rvalue::Use(Operand::Copy(Place::local(6))),
        )],
        Ty::u32(),
        Ty::u32(),
        false,
    );
    assert!(temp_rows(&f, at).is_empty(), "`*b = y` frees nothing");
}

#[test]
fn the_debug_ub_check_address_comparison_roots_but_an_address_passed_on_does_not() {
    // `_5 = _t as *const (); _6 = _5 as u64; _7 = _6 & 3; _8 = _7 == 0` — the
    // measured shape of rustc's alignment check on a `*box`.
    let unit_ptr = raw(Ty::Unit);
    let check = |tail: Vec<Statement>| {
        let mut stmts = vec![
            assign(Place::local(5), Rvalue::Cast(Operand::Copy(Place::local(4)), unit_ptr.clone())),
            assign(Place::local(6), Rvalue::Cast(Operand::Copy(Place::local(5)), Ty::u64())),
            assign(
                Place::local(7),
                Rvalue::BinaryOp(
                    trust_types::BinOp::BitAnd,
                    Operand::Copy(Place::local(6)),
                    Operand::Constant(ConstValue::Uint(3, 64)),
                ),
            ),
        ];
        stmts.extend(tail);
        let (mut f, at) = owned_box_with_temp_uses(stmts, unit_ptr.clone(), Ty::u64(), false);
        f.body.locals.push(local(7, Ty::u64()));
        f.body.locals.push(local(8, Ty::Bool));
        (f, at)
    };
    let (compared, at) = check(vec![assign(
        Place::local(8),
        Rvalue::BinaryOp(
            trust_types::BinOp::Eq,
            Operand::Copy(Place::local(7)),
            Operand::Constant(ConstValue::Uint(0, 64)),
        ),
    )]);
    assert!(temp_rows(&compared, at).is_empty(), "an address only compared roots");
    let (passed, at) = check(vec![assign(
        Place::local(8),
        Rvalue::Cast(Operand::Copy(Place::local(6)), raw(Ty::u32())),
    )]);
    assert!(
        keeps_deref_rows(&temp_rows(&passed, at)),
        "an address cast back to a pointer keeps the rows"
    );
}

fn real_sysroot_key() -> trust_types::CalleeKey {
    trust_types::CalleeKey {
        sysroot_item: None,
        krate_is_real_sysroot: true,
        krate_name_is_ambiguous: false,
        stable_crate_id: 1,
        krate_name: "core".to_string(),
        foreign_block_leaf: None,
        upstream_foreign_link_symbol: None,
        diverging_entry: None,
    }
}

// ── review round 87 ───────────────────────────────────────────────────────

#[test]
fn a_compound_assignment_through_a_box_pointer_is_a_value_read() {
    // `*b += 1` on the second temp: `(*_4) = Add(copy (*_4), 1)`.
    let deref4 = Place { local: 4, projections: vec![Projection::Deref] };
    let (f, at) = owned_box_with_temp_uses(
        vec![assign(
            deref4.clone(),
            Rvalue::BinaryOp(
                trust_types::BinOp::Add,
                Operand::Copy(deref4),
                Operand::Constant(ConstValue::Uint(1, 32)),
            ),
        )],
        Ty::u32(),
        Ty::u32(),
        false,
    );
    assert!(temp_rows(&f, at).is_empty(), "`*b += 1` reads a value; it frees nothing");
}

#[test]
fn an_opaque_scalar_operand_anywhere_roots_nothing() {
    // The extractor folds `addr_of_mut!(*b) as usize` (an expose) into an opaque
    // constant and drops the `&raw`, so no fence could see it.
    let (f, at) = owned_box_with_temp_uses(
        vec![assign(
            Place::local(6),
            Rvalue::Use(Operand::Constant(ConstValue::OpaqueScalar {
                width: 64,
                signed: false,
                origin: Default::default(),
            })),
        )],
        Ty::u32(),
        Ty::u64(),
        false,
    );
    assert!(keeps_deref_rows(&temp_rows(&f, at)), "an opaque scalar in the body keeps the rows");
}

#[test]
fn a_reference_result_of_a_sysroot_call_is_held_to_the_containment_rule() {
    // `let s = <[u32]>::get_mut-like(&mut *b)` returning `&mut u32`: the result is
    // contained when used only through `*s`, refused when it escapes as raw.
    let mut_u32 = Ty::Ref { mutable: true, inner: Box::new(Ty::u32()) };
    let reborrow =
        || assign(Place::local(5), Rvalue::Ref { mutable: true, place: deref_of_second_temp() });
    let build = |tail: Statement| {
        let (mut f, at) = owned_box_with_temp_call(
            vec![reborrow()],
            mut_u32.clone(),
            raw(Ty::u32()),
            Some(("core::convert::identity::<&mut u32>", mut_u32.clone())),
        );
        if let Terminator::Call { callee_key, .. } = &mut f.body.blocks[1].terminator {
            *callee_key = Some(real_sysroot_key());
        }
        f.body.blocks[2].stmts.push(tail);
        (f, at)
    };
    let (contained, at) = build(assign(
        Place { local: 7, projections: vec![Projection::Deref] },
        Rvalue::Use(Operand::Constant(ConstValue::Uint(3, 32))),
    ));
    assert!(
        temp_rows(&contained, at).is_empty(),
        "a returned `&mut` used only through `*r` is contained"
    );
    let (escaped, at) = build(assign(
        Place::local(6),
        Rvalue::Cast(Operand::Copy(Place::local(7)), raw(Ty::u32())),
    ));
    assert!(
        keeps_deref_rows(&temp_rows(&escaped, at)),
        "a returned `&mut` cast to raw keeps the rows"
    );
}

// ----- D14 through a SHARED local reborrow chain (sweep c67, 2026-10-11) -----
//
// `pub fn second(n: &Node) -> Option<u32> { match &n.next { Some(b) => Some(b.val),
// None => None } }` with `struct Node { val: u32, next: Option<Box<Node>> }`, the
// real extracted MIR (`-Ztrust-dump=mir`): `_2 = &(*_1).1; _4 = &((*_2) as Some).0;
// _6 = copy (*_4); _7 = (_6.0.0) as *const Node; .. _5 = copy (*_7).0` (bb6[0]).
// `Node` is recursive, so `(*_1)` types as a bare `Datatype` marker that only the
// body's definition table resolves.

fn c67() -> VerifiableFunction {
    let path =
        format!("{}/tests/fixtures/d14_reborrow/c67_second.json", env!("CARGO_MANIFEST_DIR"));
    serde_json::from_str(&std::fs::read_to_string(path).expect("fixture")).expect("MIR")
}

fn c67_rows(f: &VerifiableFunction, params: &[usize]) -> Vec<String> {
    let set = ops(&[(6, 0)]);
    let context = crate::VcgenContext::for_function(f.def_path.clone())
        .with_reference_box_root_params(params.to_vec());
    crate::with_vcgen_context(&context, || messages(&rows_at(f, &set, 6, 0)))
}

fn c67_would_fire(f: &VerifiableFunction) -> Vec<usize> {
    super::reference_box_root_would_fire(f, &ops(&[(6, 0)]), &[1])
}

/// A spare local `_19` of type `ty` for a mutant statement.
fn c67_with_local(ty: Ty) -> VerifiableFunction {
    let mut f = c67();
    f.body.locals.push(LocalDecl { index: 19, ty, name: None });
    f
}

fn c67_refused(f: &VerifiableFunction, what: &str) {
    assert!(keeps_deref_rows(&c67_rows(f, &[1])), "{what}: must keep the deref rows");
    assert!(c67_would_fire(f).is_empty(), "{what}: the install gate must not fire");
}

#[test]
fn a_box_reached_through_a_shared_reborrow_chain_of_a_reference_argument_roots() {
    let f = c67();
    assert!(keeps_deref_rows(&c67_rows(&f, &[])), "without the premise the rows stay");
    let rows = c67_rows(&f, &[1]);
    assert!(rows.is_empty(), "the premise roots the box behind `&n.next`: {rows:?}");
    assert_eq!(c67_would_fire(&f), vec![1]);
    // A shared borrow of a DISJOINT part through the argument keeps it.
    let mut disjoint = c67_with_local(Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) });
    disjoint.body.blocks[3].stmts.insert(
        0,
        assign(
            Place::local(19),
            Rvalue::Ref { mutable: false, place: deref_of(1, vec![Projection::Field(0)]) },
        ),
    );
    assert_eq!(c67_would_fire(&disjoint), vec![1], "`&n.val` is disjoint from the box");
}

#[test]
fn a_shared_reborrow_chain_that_escapes_is_refused() {
    let call = |arg: usize| {
        let mut f = c67();
        f.body.blocks[3].terminator = Terminator::Call {
            unwind: UnwindEdge::Unreachable,
            func: "evil".to_string(),
            args: vec![Operand::Copy(Place::local(arg))],
            dest: Place::local(19),
            target: Some(BlockId(5)),
            span: span(),
            atomic: None,
            is_foreign: false,
            is_unsafe_sig: false,
            callee_identity: None,
            callee_key: super::tests::fixture_key("evil"),
        };
        f.body.locals.push(LocalDecl { index: 19, ty: Ty::Unit, name: None });
        f
    };
    // `evil(b)` / `evil(&n.next)`: a callee holding a path to the box slot can
    // `ptr::read` a duplicate and drop it.
    c67_refused(&call(4), "the inner reborrow `_4` as a call argument");
    c67_refused(&call(2), "the outer reborrow `_2` as a call argument");
    // A copy of the reborrow itself.
    let mut copy = c67_with_local(Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) });
    copy.body.blocks[3]
        .stmts
        .insert(2, assign(Place::local(19), Rvalue::Use(Operand::Copy(Place::local(4)))));
    c67_refused(&copy, "`_19 = copy _4`");
    // A raw borrow through the outer reborrow.
    let mut raw_borrow = c67_with_local(raw(Ty::u32()));
    raw_borrow.body.blocks[3]
        .stmts
        .insert(2, assign(Place::local(19), Rvalue::AddressOf(false, deref_of(2, vec![]))));
    c67_refused(&raw_borrow, "`&raw const (*_2)`");
    // A shared reborrow of the box slot that is itself handed to a call.
    let mut hand_out = call(19);
    hand_out.body.locals[19].ty = Ty::Ref { mutable: false, inner: Box::new(Ty::u32()) };
    hand_out.body.blocks[3].stmts.insert(
        2,
        assign(Place::local(19), Rvalue::Ref { mutable: false, place: deref_of(4, vec![]) }),
    );
    c67_refused(&hand_out, "`_19 = &(*_4)` passed to a call");
}

#[test]
fn a_reborrow_with_a_second_value_is_refused() {
    // `_4` written twice: it is no longer one known part of the argument.
    let mut f = c67();
    let again = f.body.blocks[3].stmts[0].clone();
    f.body.blocks[3].stmts.insert(1, again);
    c67_refused(&f, "`_4` assigned twice");
    let mut g = c67();
    let again = g.body.blocks[0].stmts[0].clone();
    g.body.blocks[3].stmts.insert(0, again);
    c67_refused(&g, "`_2` assigned twice");
}

// ── D100 (2026-10-14): one premise, one grade ─────────────────────────────
//
// Main's 13c reference lane and D14 rest on the same language fact (a valid `&T`
// points to a valid `T`, whose `Box` is valid and live). After the merge of
// 2026-10-14 13c rooted boxes through reference ARGUMENTS with no install, no
// demotion and no disclosure, so such a body could read `KernelCertified` on a
// verdict resting on an undisclosed premise. D100 (by R1): a box 13c
// roots through a reference argument is a root of REFERENCE_ARG_BOX_VALID. The
// root walk admits it only for an installed argument
// (`crosses_an_argument_reference`), and the compiler's gate re-runs that walk, so it
// fires for every such shape. 13c's other roots keep no premise.

/// `Option<Box<u32>>` as the extractor spells it (see [`enum_with_box`]).
fn option_of_box() -> Ty {
    let mut ty = Ty::adt_enum(
        "core::option::Option<alloc::boxed::Box<u32>>",
        vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), box_of(Ty::u32()))],
            },
        ],
    );
    if let Ty::Adt { adt_kind, fields, .. } = &mut ty {
        *adt_kind = Some(AdtKind::Enum);
        *fields = vec![
            ("__tag".to_string(), Ty::Int { width: 64, signed: true }),
            ("__v1_0".to_string(), box_of(Ty::u32())),
        ]
        .into();
    }
    ty
}

/// D100 end to end inside vcgen, the way the compiler drives it: the install gate
/// over the body's reference arguments, then generation under EXACTLY what it
/// installed. Returns (installed arguments, the read's rows).
fn d100_pipeline(f: &VerifiableFunction, block: usize, stmt: usize) -> (Vec<usize>, Vec<String>) {
    let set = ops(&[(block, stmt)]);
    let installed = d100_gate(f, &set);
    let context = crate::VcgenContext::for_function(f.def_path.clone())
        .with_reference_box_root_params(installed.clone());
    let rows = crate::with_vcgen_context(&context, || messages(&rows_at(f, &set, block, stmt)));
    (installed, rows)
}

#[test]
fn every_13c_root_through_a_reference_argument_is_graded_under_the_premise() {
    let mut_box = Ty::Ref { mutable: true, inner: Box::new(box_of(Ty::u32())) };
    let goto = || Terminator::Goto(BlockId(1));
    let inert_copy = ref_box_deref(
        vec![local(4, shared_ref(box_of(Ty::u32())))],
        vec![assign(Place::local(4), Rvalue::Use(Operand::Copy(Place::local(1))))],
    );
    let (struct_field, struct_read) = ref_struct_box_deref(vec![], None, false);
    let (option, option_read) = match_binding_box_deref(option_of_box(), false);
    let (expr, expr_read) = match_binding_box_deref(enum_with_box(AdtKind::Enum), false);
    let (recursive, recursive_read) =
        binding_box_deref(datatype_enum_with_box("test::Expr"), variant_field(1, 0), vec![]);
    let at_end = |f: &VerifiableFunction| (0, ref_deref_index(f));
    let cases: Vec<(&str, VerifiableFunction, (usize, usize))> = vec![
        ("`&Box`", ref_box_deref(vec![], vec![]), (0, 2)),
        ("`&mut Box`", ref_box_deref_with(mut_box, vec![], vec![], vec![], goto()), (0, 2)),
        ("`&S.b`", struct_field, (1, struct_read)),
        ("`&Option<Box>` (match binding)", option, (0, option_read)),
        (
            "`&&Box`",
            ref_box_deref_with(
                shared_ref(shared_ref(box_of(Ty::u32()))),
                vec![Projection::Deref],
                vec![],
                vec![],
                goto(),
            ),
            (0, 2),
        ),
        ("`eval(e: &Expr)` (match binding)", expr, (0, expr_read)),
        ("`&Expr`, `Expr` recursive (`Ty::Datatype`)", recursive, (0, recursive_read)),
        ("an inert copy of the `&Box` argument", inert_copy.clone(), at_end(&inert_copy)),
    ];
    for (what, f, (block, stmt)) in cases {
        let bare = messages(&rows_at(&f, &ops(&[(block, stmt)]), block, stmt));
        assert!(keeps_deref_rows(&bare), "{what}: no premise, no root through `_1`: {bare:?}");
        let (installed, rows) = d100_pipeline(&f, block, stmt);
        assert_eq!(installed, vec![1], "{what}: the gate installs (demotes, discloses) `_1`");
        assert!(rows.is_empty(), "{what}: under the installed premise the box roots: {rows:?}");
    }
}

#[test]
fn roots_not_through_a_reference_argument_install_nothing() {
    // A by-value `Box` parameter (D8's root).
    let by_value = param_box_deref(vec![]);
    // An in-body `Box::new` (statement 1 of `bb1`).
    let box_new = called_box_deref(BOX_NEW, false, false);
    for (what, f, (block, stmt)) in [
        ("a by-value `Box` parameter", by_value, (0, 1)),
        ("an in-body `Box::new`", box_new, (1, 1)),
    ] {
        let set = ops(&[(block, stmt)]);
        let bare = messages(&rows_at(&f, &set, block, stmt));
        assert!(bare.is_empty(), "{what}: rooted with no premise, as before D100: {bare:?}");
        // Even offered `_1` as a candidate, the premise would change nothing.
        assert!(
            super::reference_box_root_would_fire(&f, &set, &[1]).is_empty(),
            "{what}: the gate must not fire"
        );
        let (installed, rows) = d100_pipeline(&f, block, stmt);
        assert!(installed.is_empty() && rows.is_empty(), "{what}: {installed:?} {rows:?}");
    }
    // A `&Box` that is not an argument: no root with or without the premise, and the
    // gate never fires for it (only an ARGUMENT can carry REFERENCE_ARG_BOX_VALID).
    let mut local_ref = ref_box_deref(vec![], vec![]);
    local_ref.body.arg_count = 0;
    let set = ops(&[(0, 2)]);
    let forced = crate::VcgenContext::for_function(local_ref.def_path.clone())
        .with_reference_box_root_params(vec![1]);
    let rows = crate::with_vcgen_context(&forced, || messages(&rows_at(&local_ref, &set, 0, 2)));
    assert!(keeps_deref_rows(&rows), "a non-argument `&Box` roots nothing: {rows:?}");
    assert!(super::reference_box_root_would_fire(&local_ref, &set, &[1]).is_empty());
}

#[test]
fn reference_root_queries_preserve_each_candidate_and_do_not_reuse_another_body() {
    let f = func(
        "two_reference_box_arguments",
        vec![
            local(0, Ty::u32()),
            local(1, shared_ref(box_of(Ty::u32()))),
            local(2, shared_ref(box_of(Ty::u32()))),
            local(3, box_of(Ty::u32())),
            local(4, raw(Ty::u32())),
            local(5, box_of(Ty::u32())),
            local(6, raw(Ty::u32())),
        ],
        2,
        vec![BasicBlock {
            id: BlockId(0),
            stmts: vec![
                assign(Place::local(3), Rvalue::CopyForDeref(deref_of(1, vec![]))),
                box_temp(4, 3, Ty::u32()),
                read_through(0, 4),
                assign(Place::local(5), Rvalue::CopyForDeref(deref_of(2, vec![]))),
                box_temp(6, 5, Ty::u32()),
                read_through(0, 6),
            ],
            terminator: Terminator::Return,
        }],
    );
    let set = ops(&[(0, 2), (0, 5)]);
    let mut unsafe_body = f.clone();
    unsafe_body.body.locals.push(local(7, Ty::Unit));
    unsafe_body.body.blocks[0].terminator = call_into("test::unrelated_unsafe", 7, 1, false, true);
    unsafe_body.body.blocks.push(BasicBlock {
        id: BlockId(1),
        stmts: vec![],
        terminator: Terminator::Return,
    });

    // Interleave distinct immutable bodies with the same definition path: the
    // unsafe body's refusal must neither inherit nor poison the safe body's facts.
    for (body, safe) in [(&f, true), (&unsafe_body, false), (&f, true)] {
        for (candidates, expected) in [
            (vec![], vec![]),
            (vec![1], vec![1]),
            (vec![2], vec![2]),
            (vec![2, 1], vec![2, 1]),
            (vec![2, 2, 1], vec![2, 2, 1]),
        ] {
            let expected = if safe { expected } else { vec![] };
            assert_eq!(super::reference_box_root_would_fire(body, &set, &candidates), expected);
        }
        for roots in [vec![], vec![1], vec![2], vec![1, 2]] {
            let context = crate::VcgenContext::for_function(body.def_path.clone())
                .with_reference_box_root_params(roots.clone());
            let rooted = crate::with_vcgen_context(&context, || {
                super::validity_rooted_box_deref_ops(body, &set)
            });
            assert_eq!(
                rooted.get(&(BlockId(0), 2)),
                (safe && roots.contains(&1)).then(|| vec![4]).as_ref()
            );
            assert_eq!(
                rooted.get(&(BlockId(0), 5)),
                (safe && roots.contains(&2)).then(|| vec![6]).as_ref()
            );
            assert_eq!(rooted.len(), if safe { roots.len() } else { 0 });
        }
    }
}

/// A box reached through a reference stored INSIDE a by-value argument rests on the
/// same premise as one behind a reference argument (a valid `&T` points to a valid
/// `T`), so D100 grades it the same way: 13c roots it only under the installed
/// REFERENCE_ARG_BOX_VALID, and the gate installs it for that argument. Review of
/// D100 (2026-10-15): the first version asked only for a LEADING `Deref`, so
/// `w: W { h: &Box<u32> }` read as `**w.h`, and `o: Option<&Box<u32>>` matched as
/// `Some(b) => **b`, kept rooting with no install, no demotion and no disclosure.
#[test]
fn a_reference_inside_a_by_value_argument_is_graded_under_the_premise() {
    let by_value_holder = |name: &str, holder: Ty, path: Vec<Projection>| {
        func(
            name,
            vec![
                local(0, Ty::u32()),
                local(1, holder),
                local(2, box_of(Ty::u32())),
                local(3, raw(Ty::u32())),
            ],
            1,
            vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(
                        Place::local(2),
                        Rvalue::CopyForDeref(Place { local: 1, projections: path }),
                    ),
                    box_temp(3, 2, Ty::u32()),
                    read_through(0, 3),
                ],
                terminator: Terminator::Return,
            }],
        )
    };
    // `w: W { h: &Box<u32> }`, read as `**w.h`: the path `(*(_1.0))`.
    let struct_holder = by_value_holder(
        "by_value_ref_holder",
        struct_of("test::W", vec![("h", shared_ref(box_of(Ty::u32())))]),
        vec![Projection::Field(0), Projection::Deref],
    );
    // `o: Option<&Box<u32>>`, matched as `Some(b) => **b`: the path
    // `(*((_1 as Some).0))`.
    let mut option_ref_box = Ty::adt_enum(
        "core::option::Option<&alloc::boxed::Box<u32>>",
        vec![
            trust_types::VariantDef { name: "None".into(), discriminant: 0, fields: vec![] },
            trust_types::VariantDef {
                name: "Some".into(),
                discriminant: 1,
                fields: vec![("0".into(), shared_ref(box_of(Ty::u32())))],
            },
        ],
    );
    if let Ty::Adt { adt_kind, fields, .. } = &mut option_ref_box {
        *adt_kind = Some(AdtKind::Enum);
        *fields = vec![
            ("__tag".to_string(), Ty::Int { width: 64, signed: true }),
            ("__v1_0".to_string(), shared_ref(box_of(Ty::u32()))),
        ]
        .into();
    }
    let mut option_path = variant_field(1, 0);
    option_path.push(Projection::Deref);
    let option_holder = by_value_holder("by_value_option_ref", option_ref_box, option_path);
    for (what, f) in
        [("`w: W { h: &Box<u32> }`", struct_holder), ("`o: Option<&Box<u32>>`", option_holder)]
    {
        let bare = messages(&rows_at(&f, &ops(&[(0, 2)]), 0, 2));
        assert!(keeps_deref_rows(&bare), "{what}: no premise, no root through `_1`: {bare:?}");
        let (installed, rows) = d100_pipeline(&f, 0, 2);
        assert_eq!(installed, vec![1], "{what}: the gate installs (demotes, discloses) `_1`");
        assert!(rows.is_empty(), "{what}: under the installed premise the box roots: {rows:?}");
    }
}
