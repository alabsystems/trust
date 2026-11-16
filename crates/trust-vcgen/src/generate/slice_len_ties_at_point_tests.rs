//! `v2_live_slice_len_ties_at_point`: the same-block slice-length ties the
//! load/store index lane conjoins at a row's use point (slices matched through a
//! tuple, 2026-10-02). The real-MIR pins are
//! `tests/slice_tuple_pattern_len_realmir.rs`; these pin the helper's rules on a
//! synthetic one-block body:
//!
//!   stmt0: _3 = copy _1              (the copy tie `_3__slice_len == a__slice_len`)
//!   [reseat]                         (optional: `_1 = copy _2` or `_3 = copy _2`)
//!   use:   _4 = &(*_3)[0 of 1]       (the row's use point)

use trust_types::{
    BasicBlock, BlockId, Formula, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::v2_live_slice_len_ties_at_point;

fn slice_ref() -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(Ty::Slice { elem: Box::new(Ty::u8()) }) }
}

fn copy(dest: usize, src: usize) -> Statement {
    Statement::Assign {
        place: Place::local(dest),
        rvalue: Rvalue::Use(Operand::Copy(Place::local(src))),
        span: SourceSpan::default(),
    }
}

#[derive(Clone, Copy)]
enum Reseat {
    None,
    /// `_1 = copy _2` between the tie and the use: the tie's SOURCE changes.
    Source,
    /// `_3 = copy _2` between the tie and the use: the tie's SUBJECT changes.
    Dest,
}

/// The body, and the index of the use statement.
fn body(reseat: Reseat) -> (VerifiableFunction, usize) {
    let mut stmts = vec![copy(3, 1)];
    match reseat {
        Reseat::None => {}
        Reseat::Source => stmts.push(copy(1, 2)),
        Reseat::Dest => stmts.push(copy(3, 2)),
    }
    let use_point = stmts.len();
    stmts.push(Statement::Assign {
        place: Place::local(4),
        rvalue: Rvalue::Ref {
            mutable: false,
            place: Place {
                local: 3,
                projections: vec![
                    Projection::Deref,
                    Projection::ConstantIndex { offset: 0, min_length: 1, from_end: false },
                ],
            },
        },
        span: SourceSpan::default(),
    });
    let func = VerifiableFunction {
        name: "tie".into(),
        def_path: "test::tie".into(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals: vec![
                LocalDecl { index: 0, ty: Ty::Unit, name: None },
                LocalDecl { index: 1, ty: slice_ref(), name: Some("a".into()) },
                LocalDecl { index: 2, ty: slice_ref(), name: Some("c".into()) },
                LocalDecl { index: 3, ty: slice_ref(), name: None },
                LocalDecl {
                    index: 4,
                    ty: Ty::Ref { mutable: false, inner: Box::new(Ty::u8()) },
                    name: None,
                },
            ],
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count: 2,
            return_ty: Ty::Unit,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    };
    (func, use_point)
}

/// The row body the index lane builds for `(*_3)[0 of 1]`.
fn row_body() -> Formula {
    let len = || Formula::Var("_3__slice_len".into(), trust_types::Sort::Int);
    Formula::Or(vec![
        Formula::Le(Box::new(len()), Box::new(Formula::Int(0))),
        Formula::Lt(Box::new(len()), Box::new(Formula::Int(1))),
    ])
}

fn ties(reseat: Reseat) -> Vec<String> {
    let (func, point) = body(reseat);
    v2_live_slice_len_ties_at_point(&func, &func.body.blocks[0], point, &row_body())
        .iter()
        .map(|f| format!("{f:?}"))
        .collect()
}

fn ties_a_to_the_row(ties: &[String]) -> bool {
    ties.iter().any(|t| t.contains("\"_3__slice_len") && t.contains("\"a__slice_len"))
}

#[test]
fn the_copy_tie_before_the_use_is_conjoined() {
    let ties = ties(Reseat::None);
    assert!(
        ties_a_to_the_row(&ties),
        "the row's length `_3__slice_len` must be tied to `a__slice_len`: {ties:?}"
    );
}

/// `a` is reseated between the tie and the use. The tie is still TRUE — `_3`
/// holds the OLD `a` — provided it names `a`'s length at the tie, not at the
/// use. It must therefore name a VERSIONED `a__slice_len` (the entry token),
/// never a bare one the whole-row rename at the use point would move onto the
/// post-reseat value (`c`'s length).
#[test]
fn a_tie_whose_source_is_reseated_before_the_use_names_the_old_value() {
    let ties = ties(Reseat::Source);
    let tie = ties
        .iter()
        .find(|t| t.contains("\"_3__slice_len"))
        .unwrap_or_else(|| panic!("the row's own copy tie is live: {ties:?}"));
    assert!(
        tie.contains("\"a__slice_len#") && !tie.contains("\"a__slice_len\""),
        "the tie must pin `a`'s pre-reseat length by version: {tie}"
    );
    let (func, point) = body(Reseat::Source);
    let sv = super::stmt_versions_for(&func);
    let at_use = super::version_rename_at(
        &Formula::Var("a__slice_len".into(), trust_types::Sort::Int),
        &sv,
        &func,
        BlockId(0),
        point,
    );
    assert!(
        !tie.contains(&format!("{at_use:?}")),
        "the tie must not name `a`'s post-reseat length {at_use:?}: {tie}"
    );
}

/// The row reads the NEW `_3` (`= copy c`): the old tie to `a` is about a value
/// the row does not read and must not reach it; the new tie to `c` does.
#[test]
fn a_tie_whose_subject_is_reseated_before_the_use_is_not_the_rows() {
    let ties = ties(Reseat::Dest);
    assert!(!ties_a_to_the_row(&ties), "the stale tie to `a` must not reach the row: {ties:?}");
    assert!(
        ties.iter().any(|t| t.contains("\"_3__slice_len") && t.contains("\"c__slice_len")),
        "the live tie to `c` is the row's: {ties:?}"
    );
}

#[test]
fn a_row_at_the_first_statement_has_no_same_block_ties() {
    let (func, _) = body(Reseat::None);
    assert!(
        v2_live_slice_len_ties_at_point(&func, &func.body.blocks[0], 0, &row_body()).is_empty()
    );
}
