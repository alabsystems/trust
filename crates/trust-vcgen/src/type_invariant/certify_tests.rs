//! TINV step 7.7: Houdini end to end with the REAL mint, on hand-built bodies.
//!
//! `certify` is `trust_certify::certify_vc` followed by `trust_certify::replay_vc_evidence`
//! (a `CleanCic` term the clean kernel re-checks against the row's whole identity), and
//! the oracle is the in-process ay router. Since step 7.7 the kernel kind gate admits
//! `VcKind::TypeInvariant`, so these are the first runs in which a TINV certificate can
//! exist at all. They exist only here: no compiler producer calls `houdini` until step 9
//! and nothing consumes a certificate until step 10.
//!
//! WHAT CERTIFIES (every row minted and replayed):
//! * P1, the json `Parser` (`i <= len(b)`): the constructor `Parser { b, i: 0 }` and
//!   `bump` in BOTH the tail-Return and the shared-Return (join, two edge parts) lowering;
//! * `P { i: 0, n, k: 0 }` from an integer parameter (`i <= n`), situated by the
//!   parameter's type range (the `TypeInvariant` type-range battery class);
//! * P5 reduced to `feed`/`down` (`row <= rows`): a pass-through C point, the inventory U
//!   discharge and the post-call fact.
//!
//! WHAT IS DROPPED, MEASURED (each fail-closed; recovery is producer work, never a gate):
//! * P2's product `len(v) == c * r`: its entry assumption is stripped (unmodeled machine
//!   arithmetic), so its first row is unsituated (`Situatedness`); it never reaches the
//!   mint, where 0(b) says it would not certify either;
//! * P5 through `F { s: S }`: the C point on the field-chain root has no entry fact in v1;
//!
//! RAILS (design §5 "Must-stay-refuted rails") covered here, reduced to hand-built MIR:
//! 1 (a foreign call that may unwind inside the window), 2 (the `Continue` edge), 7 (an
//! `S` reached through another type: RootShape), 8 (a user `Drop` owner of a dirty `S`),
//! 10 (a terminator-destination write), 14 (the defaulted, `Unreachable`, unwind edge
//! still owes U), 16 (the dirty move `*self = p`), plus an unguarded increment and a
//! write through a field reborrow after the guard. Rail 9 needs a `Vec::extend` model and
//! rail 23 is a use-site (step 10) property; every other rail needs the compiler (census,
//! attributes, visibility, other crates, coroutines, real std models) and is a step-9
//! UI test.
//!
//! MUTATION (run 2026-10-05): with `VcKind::TypeInvariant` moved back to the REFUSED arm
//! of `kind_authority_refusal`, the P1, P5 and P2-control tests fail (every row drops as
//! `NotCertified`); the rails and the measured drops still pass, as they must.

use std::collections::BTreeSet;

use trust_types::UnOp;

use super::*;

// ---------------------------------------------------------------------------------------
// The real mint
// ---------------------------------------------------------------------------------------

fn run_certified(
    types: &[TinvType],
    bodies: &[TinvBody<'_>],
) -> TinvOutcome<impl Sized + std::fmt::Debug + use<>> {
    let certify = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
    };
    let out = houdini(types, bodies, &NoExactModels, &|_| true, &Ay, &certify, BUDGET);
    // Every published row passes the row gate, and its evidence replays against it.
    let dropped: BTreeSet<(String, u32)> =
        out.dropped.iter().map(|d| (d.ty.clone(), d.conjunct)).collect();
    for (ty, cert) in &out.certificates {
        assert!(!out.refused.iter().any(|(r, _)| r == ty), "a refused type certified: {ty}");
        let ids: BTreeSet<u32> = cert.conjuncts().iter().map(|c| c.id).collect();
        for row in cert.rows() {
            assert!(ids.contains(&row.key().conjunct));
            assert!(!dropped.contains(&(ty.clone(), row.key().conjunct)), "a dropped row");
            assert_eq!(row.vc().kernel_authority_refusal(), None, "{:?}", row.key());
            assert!(
                trust_certify::replay_vc_evidence(row.vc(), row.evidence()),
                "published evidence does not replay: {:?}",
                row.key()
            );
        }
        for id in &ids {
            assert!(
                cert.rows()
                    .iter()
                    .any(|r| r.key().conjunct == *id
                        && r.key().point == TypeInvariantPoint::Establish),
                "conjunct {id} of {ty} has no E row"
            );
        }
    }
    out
}

fn drops<E>(out: &TinvOutcome<E>) -> Vec<(u32, DropCause, TypeInvariantPoint, &str)> {
    out.dropped.iter().map(|d| (d.conjunct, d.cause, d.point, d.function.as_str())).collect()
}

fn certified_ids<E>(out: &TinvOutcome<E>, ty: &str) -> Vec<u32> {
    out.certificates.get(ty).map_or_else(Vec::new, |c| c.conjuncts().iter().map(|c| c.id).collect())
}

/// The (function, point, edge) of every published row of `ty`.
fn published<E>(out: &TinvOutcome<E>, ty: &str) -> BTreeSet<(String, &'static str, Option<usize>)> {
    out.certificates[ty]
        .rows()
        .iter()
        .map(|r| (r.function().to_string(), r.key().point.as_tag(), r.key().edge))
        .collect()
}

// ---------------------------------------------------------------------------------------
// More bodies on `c::P { i: u64, n: u64, k: u64 }`
// ---------------------------------------------------------------------------------------

fn adt(name: &str, fields: Vec<(String, Ty)>) -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: name.into(),
        fields: fields.into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn agg(name: &str, ops: Vec<Operand>) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt { name: name.into(), variant: 0, active_field: None, args: None },
        ops,
    )
}

/// `fn new(n: u64) -> P { P { i: 0, n, k: 0 } }`: the constructor that establishes P1.
fn new_p() -> VerifiableFunction {
    func(
        "new",
        vec![(p_ty(), None), (u64_ty(), Some("n"))],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                agg("c::P", vec![konst(0), Operand::Copy(Place::local(1)), konst(0)]),
            )],
            Terminator::Return,
        )],
    )
}

fn call_term(
    callee: &str,
    args: Vec<Operand>,
    dest: Place,
    target: usize,
    id: Option<CalleeIdentity>,
    unwind: UnwindEdge,
) -> Terminator {
    Terminator::Call {
        func: callee.into(),
        args,
        dest,
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind,
        callee_identity: id,
        callee_key: None,
    }
}

fn renamed(mut f: VerifiableFunction, name: &str) -> VerifiableFunction {
    f.name = name.into();
    f.def_path = format!("c::{name}");
    f
}

/// Rail 2 / rail 14: `fn poke(&mut self, j: bool) { self.k = self.n + 1; assert!(j); self.k = 0 }`.
/// The window is open at the assert, whose unwind edge is `unwind` (`Continue` for rail 2,
/// the serde default `Unreachable` for rail 14). The Return holds; only U can fail.
fn poke(unwind: UnwindEdge) -> VerifiableFunction {
    let name = if unwind == UnwindEdge::Continue { "poke" } else { "poke_default_edge" };
    func(
        name,
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (Ty::Bool, Some("j"))],
        2,
        vec![
            blk(
                0,
                vec![assign(
                    self_field(1, 2),
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(self_field(1, 1)), konst(1)),
                )],
                Terminator::Assert {
                    cond: Operand::Copy(Place::local(2)),
                    expected: true,
                    msg: AssertMessage::Custom("j".into()),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind,
                },
            ),
            blk(1, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], Terminator::Return),
        ],
    )
}

/// Rail 1 (reduced): `fn resize(&mut self) { self.k = self.n + 1; reflow(); self.k = 0 }`
/// with `reflow` outside the inventory: the call may unwind with the window open.
fn resize_reduced() -> VerifiableFunction {
    func(
        "resize",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (Ty::Unit, None)],
        1,
        vec![
            blk(
                0,
                vec![assign(
                    self_field(1, 2),
                    Rvalue::BinaryOp(BinOp::Add, Operand::Copy(self_field(1, 1)), konst(1)),
                )],
                call_term("c::reflow", Vec::new(), Place::local(2), 1, None, UnwindEdge::Continue),
            ),
            blk(1, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], Terminator::Return),
        ],
    )
}

/// Rail 10: `fn seek(&mut self) { self.i = compute() }`, `compute` outside the inventory:
/// a terminator destination writes the field.
fn seek() -> VerifiableFunction {
    func(
        "seek",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self"))],
        1,
        vec![
            blk(
                0,
                vec![],
                call_term(
                    "c::compute",
                    Vec::new(),
                    self_field(1, 0),
                    1,
                    None,
                    UnwindEdge::Continue,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

/// Rail 16: `fn rewind(&mut self, k: u64) { let mut p = *self; p.i = k; *self = p; }`.
fn rewind() -> VerifiableFunction {
    func(
        "rewind",
        vec![
            (Ty::Unit, None),
            (mut_ref(p_ty()), Some("self")),
            (u64_ty(), Some("k")),
            (p_ty(), Some("p")),
        ],
        2,
        vec![blk(
            0,
            vec![
                assign(
                    Place::local(3),
                    Rvalue::Use(Operand::Copy(Place {
                        local: 1,
                        projections: vec![Projection::Deref],
                    })),
                ),
                assign(field(3, 0), Rvalue::Use(Operand::Copy(Place::local(2)))),
                assign(
                    Place { local: 1, projections: vec![Projection::Deref] },
                    Rvalue::Use(Operand::Move(Place::local(3))),
                ),
            ],
            Terminator::Return,
        )],
    )
}

/// A write through a FIELD reborrow after the guard:
/// `fn skip(&mut self) { if self.i < self.n { let r = &mut self.i; *r = self.n + 1 } }`.
fn reborrow_write() -> VerifiableFunction {
    let mut f = bump(true);
    f = renamed(f, "skip");
    // `_5: &mut u64` replaces the checked-add tuple; bb1 takes the borrow and writes
    // through it, bb2 returns.
    f.body.locals[5] = LocalDecl { index: 5, ty: mut_ref(u64_ty()), name: Some("r".into()) };
    f.body.blocks[1] = blk(
        1,
        vec![
            assign(Place::local(5), Rvalue::Ref { mutable: true, place: self_field(1, 0) }),
            assign(
                Place { local: 5, projections: vec![Projection::Deref] },
                Rvalue::BinaryOp(BinOp::Add, Operand::Copy(self_field(1, 1)), konst(1)),
            ),
        ],
        Terminator::Goto(BlockId(2)),
    );
    f.body.blocks[2] = blk(2, vec![], Terminator::Return);
    f
}

/// Rail 8: `struct Owner(P)` with a user `Drop`.
fn owner_ty() -> Ty {
    adt("c::Owner", vec![("0".to_string(), p_ty())])
}

/// Rail 7: `fn shrink(m: &Mutex<P>) { lock(m) }`: `P` reached through another type.
fn shrink() -> VerifiableFunction {
    let mutex = adt("std::sync::Mutex<c::P>", vec![("data".to_string(), p_ty())]);
    func(
        "shrink",
        vec![(Ty::Unit, None), (shared_ref(mutex), Some("m")), (Ty::Unit, None)],
        1,
        vec![
            blk(
                0,
                vec![],
                call_term(
                    "std::sync::Mutex::lock",
                    vec![Operand::Copy(Place::local(1))],
                    Place::local(2),
                    1,
                    None,
                    UnwindEdge::Continue,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

// ---------------------------------------------------------------------------------------
// The json `Parser` itself: `c::Parser<'a> { b: &'a [u8], i: usize }`, `I = i <= len(b)`
// ---------------------------------------------------------------------------------------

fn slice_ty() -> Ty {
    shared_ref(Ty::Slice { elem: Box::new(Ty::Int { width: 8, signed: false }) })
}

fn parser_fields() -> Vec<(String, Ty)> {
    vec![("b".to_string(), slice_ty()), ("i".to_string(), u64_ty())]
}

fn parser_ty() -> Ty {
    adt("c::Parser", parser_fields())
}

/// `i <= len(b)`.
fn parser(conjuncts: Vec<CandidateConjunct>) -> TinvType {
    TinvType { def_path: "c::Parser".into(), fields: parser_fields(), conjuncts }
}

fn i_le_len_b() -> CandidateConjunct {
    CandidateConjunct {
        id: 0,
        formula: Formula::Le(
            Box::new(field_var(FieldTerm::Value(1))),
            Box::new(field_var(FieldTerm::Len(0))),
        ),
    }
}

/// `fn new(b: &[u8]) -> Parser { Parser { b, i: 0 } }`.
fn parser_new() -> VerifiableFunction {
    func(
        "parser_new",
        vec![(parser_ty(), None), (slice_ty(), Some("b"))],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                agg("c::Parser", vec![Operand::Copy(Place::local(1)), konst(0)]),
            )],
            Terminator::Return,
        )],
    )
}

/// `fn bump(&mut self) { if self.i < self.b.len() { self.i += 1 } }`, debug MIR: the
/// guard reads `PtrMetadata(copy (*self).b)`; `join` routes the write block to a shared
/// Return (rustc's join lowering) instead of returning from it (tail duplication).
fn parser_bump(join: bool) -> VerifiableFunction {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(parser_ty()), Some("self")),
        (u64_ty(), None),
        (u64_ty(), None),
        (Ty::Bool, None),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
        (slice_ty(), None),
    ];
    let entry = blk(
        0,
        vec![
            assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
            assign(Place::local(6), Rvalue::Use(Operand::Copy(self_field(1, 0)))),
            assign(
                Place::local(3),
                Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(6))),
            ),
            assign(
                Place::local(4),
                Rvalue::BinaryOp(
                    BinOp::Lt,
                    Operand::Move(Place::local(2)),
                    Operand::Move(Place::local(3)),
                ),
            ),
        ],
        Terminator::SwitchInt {
            discr: Operand::Move(Place::local(4)),
            targets: vec![(0, BlockId(3))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    );
    let add = blk(
        1,
        vec![assign(
            Place::local(5),
            Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(self_field(1, 1)), konst(1)),
        )],
        Terminator::Assert {
            cond: Operand::Move(field(5, 1)),
            expected: false,
            msg: AssertMessage::Overflow(BinOp::Add),
            target: BlockId(2),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Continue,
        },
    );
    let write = blk(
        2,
        vec![assign(self_field(1, 1), Rvalue::Use(Operand::Move(field(5, 0))))],
        if join { Terminator::Goto(BlockId(3)) } else { Terminator::Return },
    );
    let ret = blk(3, vec![], Terminator::Return);
    let name = if join { "parser_bump_join" } else { "parser_bump" };
    func(name, locals, 1, vec![entry, add, write, ret])
}

// ---------------------------------------------------------------------------------------
// P1: json `Parser`, `i <= n`
// ---------------------------------------------------------------------------------------

// ---------------------------------------------------------------------------------------
// P1: json `Parser`, `i <= len(b)`
// ---------------------------------------------------------------------------------------

/// P1 certifies: the constructor `Parser { b, i: 0 }` (E, bound by the `0 <= len` fact)
/// and `bump` in BOTH lowerings — the tail-duplicated Return (one R row) and rustc's
/// shared Return (one R point split into two edge parts, TINV-9(a)) — every row minted
/// by `certify_vc` and replayed by the kernel.
#[test]
fn p1_parser_linear_invariant_is_kernel_certified_in_both_return_lowerings() {
    let funcs = [parser_new(), parser_bump(false), parser_bump(true)];
    let out = run_certified(&[parser(vec![i_le_len_b()])], &run_bodies(&funcs));
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.dropped.is_empty(), "{:?}", drops(&out));
    assert_eq!(certified_ids(&out, "c::Parser"), vec![0]);
    let rows = published(&out, "c::Parser");
    let expected: BTreeSet<(String, &str, Option<usize>)> = [
        ("c::parser_new".to_string(), "establish", None),
        ("c::parser_bump".to_string(), "return", None),
        ("c::parser_bump_join".to_string(), "return", Some(0)),
        ("c::parser_bump_join".to_string(), "return", Some(2)),
    ]
    .into_iter()
    .collect();
    assert_eq!(rows, expected);
    assert_eq!(out.certificates["c::Parser"].rows().len(), 4);
}

/// Control: the same run with the UNGUARDED increment added drops the conjunct (Refuted
/// at its Return) and publishes nothing, though every other row certifies.
#[test]
fn p1_with_an_unguarded_increment_certifies_nothing() {
    let mut unguarded = parser_bump(false);
    unguarded.body.blocks[0] = blk(0, vec![], Terminator::Goto(BlockId(1)));
    let unguarded = renamed(unguarded, "parser_bump_unguarded");
    let funcs = [parser_new(), parser_bump(false), unguarded];
    let out = run_certified(&[parser(vec![i_le_len_b()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(
        drops(&out),
        vec![(0, DropCause::Refuted, TypeInvariantPoint::Return, "c::parser_bump_unguarded")]
    );
}

/// An E row whose aggregate operands are an INTEGER parameter and constants
/// (`P { i: 0, n, k: 0 }`) is situated by the parameter's TYPE range (`0 <= n <=
/// u64::MAX`, a recorded battery fact of the `TypeInvariant` class) and certifies, with
/// the guarded `bump` preserving it: every row minted by `certify_vc` and replayed.
///
/// Until 2026-10-06 this was the MEASURED precision gap: a TINV row took only the
/// `Other` type-range class (`0 <= len`), no hypothesis bound `n`, and the conjunct
/// dropped as `Situatedness` at the constructor.
#[test]
fn an_integer_parameter_constructor_certifies_with_a_preserving_method() {
    let funcs = [new_p(), bump(true)];
    let out = run_certified(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.dropped.is_empty(), "{:?}", drops(&out));
    assert_eq!(certified_ids(&out, "c::P"), vec![0]);
    let expected: BTreeSet<(String, &str, Option<usize>)> =
        [("c::new".to_string(), "establish", None), ("c::bump".to_string(), "return", None)]
            .into_iter()
            .collect();
    assert_eq!(published(&out, "c::P"), expected);
}

/// Control: `fn bad(n: u64) -> P { P { i: n, n: 0, k: 0 } }` violates `i <= n` for every
/// `n > 0`; the parameter range must not hide it. The conjunct drops as `Refuted` at the
/// constructor and nothing certifies.
#[test]
fn an_integer_parameter_constructor_that_violates_is_refuted() {
    let mut bad = renamed(new_p(), "bad");
    bad.body.blocks[0].stmts[0] = assign(
        Place::local(0),
        agg("c::P", vec![Operand::Copy(Place::local(1)), konst(0), konst(0)]),
    );
    let funcs = [bad, bump(true)];
    let out = run_certified(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(drops(&out), vec![(0, DropCause::Refuted, TypeInvariantPoint::Establish, "c::bad")]);
}

// ---------------------------------------------------------------------------------------
// P5: the `Folder` field chain, `S { row, rows }` with `row <= rows` inside `F { s: S }`
// ---------------------------------------------------------------------------------------

fn s_fields() -> Vec<(String, Ty)> {
    vec![("row".to_string(), u64_ty()), ("rows".to_string(), u64_ty())]
}

fn s_ty() -> Ty {
    adt("c::S", s_fields())
}

fn f_ty() -> Ty {
    adt("c::F", vec![("s".to_string(), s_ty())])
}

/// `row <= rows`: a LINEAR, subtraction-free conjunct between two integer fields.
fn s_type() -> TinvType {
    TinvType {
        def_path: "c::S".into(),
        fields: s_fields(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Le(
                Box::new(field_var(FieldTerm::Value(0))),
                Box::new(field_var(FieldTerm::Value(1))),
            ),
        }],
    }
}

/// `fn s_new(b: &[u8]) -> S { S { row: 0, rows: b.len() } }`.
fn s_new() -> VerifiableFunction {
    func(
        "s_new",
        vec![(s_ty(), None), (slice_ty(), Some("b")), (u64_ty(), None)],
        1,
        vec![blk(
            0,
            vec![
                assign(
                    Place::local(2),
                    Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(Place::local(1))),
                ),
                assign(
                    Place::local(0),
                    agg("c::S", vec![konst(0), Operand::Move(Place::local(2))]),
                ),
            ],
            Terminator::Return,
        )],
    )
}

/// `fn down(&mut self) { if self.row < self.rows { self.row += 1 } }`.
fn down() -> VerifiableFunction {
    let mut f = renamed(bump(true), "down");
    f.body.locals[1].ty = mut_ref(s_ty());
    f
}

/// `fn feed(s: &mut S) { s.row = s.rows; down(&mut *s); let r = s.rows; s.rows = r; }`.
/// The first write opens the window, so the call owes C (`rows <= rows`) and U (which the
/// inventory call discharges, TINV-9(f)); `&mut *s` is a pass-through reborrow. The call
/// havocs `*s`, and the write after it re-opens the window, so the Return holds ONLY by
/// `down`'s post-call fact `row <= rows` at bb1.
fn feed(down_id: CalleeIdentity) -> VerifiableFunction {
    let deref = || Place { local: 1, projections: vec![Projection::Deref] };
    func(
        "feed",
        vec![
            (Ty::Unit, None),
            (mut_ref(s_ty()), Some("s")),
            (mut_ref(s_ty()), None),
            (Ty::Unit, None),
            (u64_ty(), Some("r")),
        ],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
                    assign(Place::local(2), Rvalue::Ref { mutable: true, place: deref() }),
                ],
                call_term(
                    "c::down",
                    vec![Operand::Move(Place::local(2))],
                    Place::local(3),
                    1,
                    Some(down_id),
                    UnwindEdge::Continue,
                ),
            ),
            blk(
                1,
                vec![
                    assign(Place::local(4), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
                    assign(self_field(1, 1), Rvalue::Use(Operand::Copy(Place::local(4)))),
                ],
                Terminator::Return,
            ),
        ],
    )
}

/// `fn apply(&mut self) { feed(&mut self.s) }` on `F { s: S }`: the root is the field
/// chain `(*self).s`.
fn apply(feed_id: CalleeIdentity) -> VerifiableFunction {
    func(
        "apply",
        vec![
            (Ty::Unit, None),
            (mut_ref(f_ty()), Some("self")),
            (mut_ref(s_ty()), None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            blk(
                0,
                vec![assign(
                    Place::local(2),
                    Rvalue::Ref { mutable: true, place: self_field(1, 0) },
                )],
                call_term(
                    "c::feed",
                    vec![Operand::Move(Place::local(2))],
                    Place::local(3),
                    1,
                    Some(feed_id),
                    UnwindEdge::Continue,
                ),
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

/// P5 reduced to `feed`/`down` (the design's `F { s: S }` wrapper is measured below):
/// a pass-through C point, the inventory U discharge and the post-call fact, every row
/// kernel-certified.
#[test]
fn p5_pass_through_call_with_a_post_call_fact_is_kernel_certified() {
    // `run_bodies` numbers identities by position: s_new 100, down 101, feed 102.
    let funcs = [s_new(), down(), feed(ident(101))];
    let out = run_certified(&[s_type()], &run_bodies(&funcs));
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.dropped.is_empty(), "{:?}", drops(&out));
    assert_eq!(certified_ids(&out, "c::S"), vec![0]);
    let rows = published(&out, "c::S");
    for row in [
        ("c::s_new".to_string(), "establish", None),
        ("c::down".to_string(), "return", None),
        ("c::feed".to_string(), "call", None),
        ("c::feed".to_string(), "return", None),
    ] {
        assert!(rows.contains(&row), "{row:?} missing from {rows:?}");
    }
    // The inventory call discharged U: `feed` has no certified (or any) Unwind row.
    assert!(!rows.iter().any(|(f, p, _)| f == "c::feed" && *p == "unwind"), "{rows:?}");

    // Control: with `down` OUTSIDE the run the call is foreign: it neither discharges U
    // nor yields a post-call fact, and the conjunct is dropped in `feed`.
    let funcs = [s_new(), down(), feed(ident(999))];
    let out = run_certified(&[s_type()], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert!(matches!(drops(&out).as_slice(), [(0, _, _, "c::feed")]), "{:?}", drops(&out));
}

/// MEASURED (fail-closed, v1 scope): the design's full P5 adds `F { s: S }` and
/// `fn apply(&mut self) { feed(&mut self.s) }`. The C point in `apply` is owed on the
/// FIELD-CHAIN root `(*self).s`, and v1's entry assumption covers only direct `S`/`&S`/
/// `&mut S` parameter roots (TINV-9(d)), so that row has no hypothesis and the row gate
/// drops the conjunct (`Situatedness`). Recovery is D3's type walk (an entry fact for an
/// `S` reached through a private field of a parameter), not a gate change.
#[test]
fn p5_through_a_wrapper_field_is_unsituated_in_v1() {
    let funcs = [s_new(), down(), feed(ident(101)), apply(ident(102))];
    let out = run_certified(&[s_type()], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(
        drops(&out),
        vec![(0, DropCause::Situatedness, TypeInvariantPoint::Call, "c::apply")]
    );
}

// ---------------------------------------------------------------------------------------
// P2: `len(v) == c * r`
// ---------------------------------------------------------------------------------------

fn g_fields() -> Vec<(String, Ty)> {
    vec![
        (
            "v".to_string(),
            Ty::Seq { elem: Box::new(Ty::Int { width: 8, signed: false }), drop_auth: None },
        ),
        ("c".to_string(), u64_ty()),
        ("r".to_string(), u64_ty()),
        ("k".to_string(), u64_ty()),
    ]
}

fn g_ty() -> Ty {
    adt("c::G", g_fields())
}

/// `len(v) == c * r`, the Screen grid-length product conjunct.
fn g_type() -> TinvType {
    TinvType {
        def_path: "c::G".into(),
        fields: g_fields(),
        conjuncts: vec![CandidateConjunct {
            id: 0,
            formula: Formula::Eq(
                Box::new(field_var(FieldTerm::Len(0))),
                Box::new(Formula::Mul(
                    Box::new(field_var(FieldTerm::Value(1))),
                    Box::new(field_var(FieldTerm::Value(2))),
                )),
            ),
        }],
    }
}

/// `fn dup(g: &G) -> G { G { v: g.v, c: g.c, r: g.r, k: g.k } }`.
fn g_dup() -> VerifiableFunction {
    func(
        "dup",
        vec![(g_ty(), None), (shared_ref(g_ty()), Some("g"))],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                agg("c::G", (0..4).map(|f| Operand::Copy(self_field(1, f))).collect()),
            )],
            Terminator::Return,
        )],
    )
}

/// `fn touch(&mut self) { self.k = 0 }`: the product's fields are not written.
fn g_touch() -> VerifiableFunction {
    func(
        "touch",
        vec![(Ty::Unit, None), (mut_ref(g_ty()), Some("self"))],
        1,
        vec![blk(0, vec![assign(self_field(1, 3), Rvalue::Use(konst(0)))], Terminator::Return)],
    )
}

/// `fn recommit(&mut self) { let c = self.c; self.c = c; }`: compute-then-commit of a
/// product field, which keeps its value but gives it a new version.
fn g_recommit() -> VerifiableFunction {
    func(
        "recommit",
        vec![(Ty::Unit, None), (mut_ref(g_ty()), Some("self")), (u64_ty(), Some("c"))],
        1,
        vec![blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
                assign(self_field(1, 1), Rvalue::Use(Operand::Copy(Place::local(2)))),
            ],
            Terminator::Return,
        )],
    )
}

/// P2's product conjunct `len(v) == c * r` certifies nowhere. MEASURED: it does not even
/// reach the mint. The entry channel strips an assumption with unmodeled machine
/// arithmetic (a `u64` product; `conjoin_preconditions_versioned_at_point_recorded`), so
/// at the copy constructor `dup` the E row is the bare negated core and the row gate drops
/// the conjunct (`Situatedness`) in round 1, with or without a mutator. Were it to reach
/// the mint, 0(b) says the kernel would still not certify its preservation (product
/// congruence) — TINV-2 keeps it unminted either way. The NotCertified path itself is
/// pinned with a scripted certify in `houdini_tests.rs`.
#[test]
fn p2_product_conjunct_is_dropped_and_no_certificate_contains_it() {
    for funcs in [vec![g_dup()], vec![g_dup(), g_touch()], vec![g_dup(), g_recommit()]] {
        let out = run_certified(&[g_type()], &run_bodies(&funcs));
        assert!(out.certificates.is_empty(), "{:?}", certified_ids(&out, "c::G"));
        assert!(out.refused.is_empty(), "{:?}", out.refused);
        assert_eq!(
            drops(&out),
            vec![(0, DropCause::Situatedness, TypeInvariantPoint::Establish, "c::dup")]
        );
    }
    // Control: the LINEAR `r <= c` over the same type and bodies certifies, so the drop is
    // the product, not the shape of `dup`/`touch`/`recommit`.
    let mut linear = g_type();
    linear.conjuncts[0].formula = Formula::Le(
        Box::new(field_var(FieldTerm::Value(2))),
        Box::new(field_var(FieldTerm::Value(1))),
    );
    let out = run_certified(&[linear], &run_bodies(&[g_dup(), g_touch(), g_recommit()]));
    assert_eq!(certified_ids(&out, "c::G"), vec![0], "{:?}", drops(&out));
}

// ---------------------------------------------------------------------------------------
// Rails
// ---------------------------------------------------------------------------------------

/// Rail 8 with the owned value arriving by parameter (so its own E is not the drop):
/// `fn own(p: P) { let mut o = Owner(p); o.0.i = o.0.n + 1; }`.
fn own_param() -> VerifiableFunction {
    func(
        "own",
        vec![(Ty::Unit, None), (p_ty(), Some("p")), (owner_ty(), Some("o"))],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(Place::local(2), agg("c::Owner", vec![Operand::Move(Place::local(1))])),
                    assign(
                        Place {
                            local: 2,
                            projections: vec![Projection::Field(0), Projection::Field(0)],
                        },
                        Rvalue::BinaryOp(
                            BinOp::Add,
                            Operand::Copy(Place {
                                local: 2,
                                projections: vec![Projection::Field(0), Projection::Field(1)],
                            }),
                            konst(1),
                        ),
                    ),
                ],
                Terminator::Drop {
                    place: Place::local(2),
                    target: BlockId(1),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            ),
            blk(1, vec![], Terminator::Return),
        ],
    )
}

/// Every rail runs beside `copy_of` (an E row situated by the entry assumption, which
/// certifies on its own), so the drop below is the rail's own row. No rail publishes a
/// row. The causes are MEASURED: a rail whose violating state is a fresh symbol no
/// hypothesis binds (a whole-root store) fails the row gate before the oracle is asked,
/// which is the fail-closed outcome; since the TINV type-range battery (2026-10-06) a
/// fresh INTEGER field (a call destination, a value moved into an owner) is bound by its
/// type range, and those rails are refuted by the oracle instead.
#[test]
fn rails_stay_dropped_or_refused_with_the_real_mint() {
    use DropCause::{Refuted, Situatedness};
    use TypeInvariantPoint::{Return, Unwind};
    let cases: Vec<(
        VerifiableFunction,
        CandidateConjunct,
        Option<(DropCause, TypeInvariantPoint)>,
    )> = vec![
        // An unguarded increment.
        (bump(false), c0(), Some((Refuted, Return))),
        // A write through a field reborrow after the guard.
        (reborrow_write(), c0(), Some((Refuted, Return))),
        // Rail 2: the `Continue` edge of an assert inside the window.
        (poke(UnwindEdge::Continue), c1(), Some((Refuted, Unwind))),
        // Rail 14: the same edge left at the serde default (`Unreachable`) still owes U.
        (poke(UnwindEdge::Unreachable), c1(), Some((Refuted, Unwind))),
        // Rail 1 (reduced): a foreign call that may unwind inside the window.
        (resize_reduced(), c1(), Some((Refuted, Unwind))),
        // Rail 10: a terminator-destination write. Since 2026-10-06 the written field's
        // `u64` type range (the TINV battery) situates the row, and the oracle REFUTES
        // it (`compute()` may return any `u64`): dropped as before, now with a witness
        // instead of at the row gate.
        (seek(), c0(), Some((Refuted, Return))),
        // Rail 16: the dirty move `*self = p`.
        (rewind(), c0(), Some((Situatedness, Return))),
        // Rail 8: a user-`Drop` owner of a dirty `P` (the Drop terminator's unwind edge).
        // Since 2026-10-06 situated by the TINV battery's field ranges and REFUTED, as
        // rail 10.
        (own_param(), c0(), Some((Refuted, Unwind))),
        // Rail 7: `P` reached through another type refuses the type (RootShape).
        (shrink(), c0(), None),
    ];
    for (body, conjunct, expected) in cases {
        let name = body.def_path.clone();
        let funcs = [copy_of(), body];
        let out = run_certified(&[p(vec![conjunct.clone()])], &run_bodies(&funcs));
        assert!(out.certificates.is_empty(), "{name}: a rail published a certificate");
        match expected {
            Some((cause, point)) => {
                assert!(out.refused.is_empty(), "{name}: {:?}", out.refused);
                assert_eq!(drops(&out), vec![(conjunct.id, cause, point, name.as_str())], "{name}");
            }
            None => {
                assert!(out.dropped.is_empty(), "{name}: {:?}", drops(&out));
                assert!(
                    matches!(
                        out.refused.as_slice(),
                        [(ty, TinvObligationRefusal::RootShape { .. })] if ty == "c::P"
                    ),
                    "{name}: {:?}",
                    out.refused
                );
            }
        }
    }
}
