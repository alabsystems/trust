use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::build_immutable_read_value_tie_facts;

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}
fn usize_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}
fn shared_arr() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Array { elem: Box::new(u32_ty()), len: 3 }) }
}
fn elem_read(base: usize, idx: usize) -> Operand {
    Operand::Copy(Place {
        local: base,
        projections: vec![Projection::Deref, Projection::Index(idx)],
    })
}
fn assign(local: usize, rvalue: Rvalue) -> Statement {
    Statement::Assign { place: Place::local(local), rvalue, span: SourceSpan::default() }
}

/// `fn f(ps: &[u32;3], i: usize)` with two element reads through distinct
/// single-write index temps (`_5 = i; _3 = (*ps)[_5]; _6 = i; _4 = (*ps)[_6]`)
/// — the exact MIR shape of the guard-read / use-read pair.
fn two_read_func() -> VerifiableFunction {
    VerifiableFunction {
        name: "two_reads".to_string(),
        def_path: "test::two_reads".to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: Some("ret".into()) },
                LocalDecl { index: 1, ty: shared_arr(), name: Some("ps".into()) },
                LocalDecl { index: 2, ty: usize_ty(), name: Some("i".into()) },
                LocalDecl { index: 3, ty: u32_ty(), name: None },
                LocalDecl { index: 4, ty: u32_ty(), name: None },
                LocalDecl { index: 5, ty: usize_ty(), name: None },
                LocalDecl { index: 6, ty: usize_ty(), name: None },
            ],
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![
                    assign(5, Rvalue::Use(Operand::Copy(Place::local(2)))),
                    assign(3, Rvalue::Use(elem_read(1, 5))),
                    assign(6, Rvalue::Use(Operand::Copy(Place::local(2)))),
                    assign(4, Rvalue::Use(elem_read(1, 6))),
                ],
                terminator: Terminator::Return,
            }],
            arg_count: 2,
            return_ty: Ty::Unit,
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
    }
}

/// Base case: a shared-ref array base emits exactly ONE congruence fact
/// `Or(idx_a != idx_b, read_a == read_b)` — the index tie is a HYPOTHESIS.
#[test]
fn shared_ref_two_reads_emit_congruence() {
    let func = two_read_func();
    let facts = build_immutable_read_value_tie_facts(&func);
    assert_eq!(facts.len(), 1, "expected exactly one pair fact; got {facts:?}");
    match &facts[0] {
        Formula::Or(djs) => {
            assert_eq!(djs.len(), 2, "hypothesis + tie; got {djs:?}");
            assert!(
                matches!(&djs[0], Formula::Not(inner) if matches!(&**inner, Formula::Eq(..))),
                "first disjunct must be the index-disequality hypothesis; got {:?}",
                djs[0]
            );
            assert!(
                matches!(&djs[1], Formula::Eq(..)),
                "second disjunct must be the read-value tie; got {:?}",
                djs[1]
            );
        }
        other => panic!("expected Or(..); got {other:?}"),
    }
}

/// N1 (fact level): a `&mut` base must emit NOTHING — the element can be
/// written between the reads, so the congruence would be a false-PROVE vector.
#[test]
fn mut_ref_base_declines() {
    let mut func = two_read_func();
    func.body.locals[1].ty = Ty::Ref {
        mutable: true,
        inner: Box::new(Ty::Array { elem: Box::new(u32_ty()), len: 3 }),
    };
    assert!(build_immutable_read_value_tie_facts(&func).is_empty());
}

/// A RESEATED base param (`ps = other;` between the reads) must emit NOTHING:
/// the two reads may see two DIFFERENT arrays. This is the hole neither
/// `whole_local_def_count` (param entry def invisible) nor
/// `is_single_static_assignment` (a once-reassigned param counts 1) catches.
#[test]
fn reseated_param_base_declines() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl { index: 7, ty: shared_arr(), name: None });
    // Insert `ps = copy _7` BETWEEN the two reads.
    func.body.blocks[0].stmts.insert(2, assign(1, Rvalue::Use(Operand::Copy(Place::local(7)))));
    assert!(
        build_immutable_read_value_tie_facts(&func).is_empty(),
        "a reseated base must fail closed"
    );
}

/// A `&mut`-borrowed root (the ref itself aliased mutably) must emit NOTHING.
#[test]
fn mut_borrowed_root_declines() {
    let mut func = two_read_func();
    func.body.locals.push(LocalDecl {
        index: 7,
        ty: Ty::Ref { mutable: true, inner: Box::new(shared_arr()) },
        name: None,
    });
    func.body.blocks[0]
        .stmts
        .insert(2, assign(7, Rvalue::Ref { mutable: true, place: Place::local(1) }));
    assert!(
        build_immutable_read_value_tie_facts(&func).is_empty(),
        "a mut-borrowed root must fail closed"
    );
}

/// Reads of DIFFERENT fields (`(*ps)[_5].0` vs `(*ps)[_6].1`) must NOT group:
/// different shapes are different elements-projections — no tie.
#[test]
fn different_field_shapes_do_not_group() {
    let mut func = two_read_func();
    // Retype the array element to a 2-tuple and re-project the reads.
    func.body.locals[1].ty = Ty::Ref {
        mutable: false,
        inner: Box::new(Ty::Array {
            elem: Box::new(Ty::Tuple(vec![u32_ty(), u32_ty()])),
            len: 3,
        }),
    };
    let read_a = Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(5), Projection::Field(0)],
    });
    let read_b = Operand::Copy(Place {
        local: 1,
        projections: vec![Projection::Deref, Projection::Index(6), Projection::Field(1)],
    });
    func.body.blocks[0].stmts[1] = assign(3, Rvalue::Use(read_a));
    func.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(read_b));
    assert!(
        build_immutable_read_value_tie_facts(&func).is_empty(),
        "different field projections must not tie"
    );
}

/// A `Downcast` projection (variant-relative read) bails the whole operand.
#[test]
fn downcast_projection_declines() {
    let mut func = two_read_func();
    let read_a = Operand::Copy(Place {
        local: 1,
        projections: vec![
            Projection::Deref,
            Projection::Index(5),
            Projection::Downcast(0),
            Projection::Field(0),
        ],
    });
    func.body.blocks[0].stmts[1] = assign(3, Rvalue::Use(read_a.clone()));
    func.body.blocks[0].stmts[3] = assign(4, Rvalue::Use(read_a));
    assert!(build_immutable_read_value_tie_facts(&func).is_empty());
}
