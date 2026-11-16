// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! E9-ODT-FACE-SELF-CALL-1 against TG11's real mint: a cited `ensures` over a
//! by-value struct's flattened field rows is graded against the NOMINAL ODT
//! import through the face constructor, and each drift the kernel cannot see
//! is refused before a goal is built.
//!
//! The order matches production: `trust_open_island_session` checks the
//! islands, the walk runs, and `trust_mint_program_admissions` mints the ODT
//! imports after it. The clause mode is the sweep's
//! (`ProofClauseInputs::proof_lift` with the resolved `u64` return type).

use trust_odt::{Entry, Field, RustDecl, Scalar, Shape, TypeKey};
use trust_spec_elab::{Carrier, FacetTable, FnFacets, ProofClauseInputs};
use trust_types::{
    BasicBlock, BlockId, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement,
    Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{CitationVerdict, CleanIslandSession};
use crate::odt_e6::FaceInput;

const ISLAND: &str = "\
theorem degree_le_self : forall (d : UInt64) (k : UInt64),\n\
    Nat.le (UInt64.toNat d) (UInt64.toNat d) :=\n\
    fun d k => Nat.le.refl (UInt64.toNat d)\n\
theorem first_refl : forall (x : UInt64) (y : UInt64), x = x := fun x y => rfl\n\
theorem third_of_four : forall (a0 : UInt64) (a1 : UInt64) (b0 : UInt64) (b1 : UInt64),\n\
    b0 = b0 := fun a0 a1 b0 b1 => rfl\n\
theorem third_of_three : forall (n : UInt64) (d : UInt64) (k : UInt64), k = k :=\n\
    fun n d k => rfl\n";
const CST_ROWS: [(&str, &str); 2] = [("c.degree", "u64"), ("c.coeff", "u64")];

fn cst() -> Ty {
    Ty::adt("test::Cst", vec![("degree".into(), Ty::u64()), ("coeff".into(), Ty::u64())])
}

fn cst_face() -> FaceInput {
    let declaration = RustDecl {
        key: TypeKey { stable_crate_id: 33, local_def_path_hash: 44 },
        shape: Shape::ScalarStruct {
            fields: vec![
                Field { name: "degree".into(), scalar: Scalar::U64 },
                Field { name: "coeff".into(), scalar: Scalar::U64 },
            ],
        },
    };
    let transport = Entry::generate(declaration.clone()).unwrap().encode().unwrap();
    FaceInput { rust_path: "test::Cst".into(), declaration, transport }
}

/// `fn <name>(<params>) -> u64 { <params[param]>.<field #field> }`.
fn reads_field(
    name: &str,
    params: &[(&str, Ty)],
    param: usize,
    field: usize,
) -> VerifiableFunction {
    let mut locals = vec![LocalDecl { index: 0, ty: Ty::u64(), name: None }];
    for (i, (p, ty)) in params.iter().enumerate() {
        locals.push(LocalDecl { index: i + 1, ty: ty.clone(), name: Some((*p).into()) });
    }
    VerifiableFunction {
        name: name.into(),
        def_path: format!("test::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: Ty::u64(),
            locals,
            arg_count: params.len(),
            blocks: vec![BasicBlock {
                id: BlockId(0),
                stmts: vec![Statement::Assign {
                    place: Place::local(0),
                    rvalue: Rvalue::Use(Operand::Copy(Place {
                        local: param + 1,
                        projections: vec![Projection::Field(field)],
                    })),
                    span: SourceSpan::default(),
                }],
                terminator: Terminator::Return,
            }],
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

/// Check the island, then mint TG11's ODT imports into the same session and
/// key each under its def-path and every spec spelling, as the session mint
/// does.
fn minted(funcs: &[VerifiableFunction]) -> (CleanIslandSession, FacetTable) {
    let mut table = FacetTable::new();
    for f in funcs {
        table.insert(
            &f.def_path,
            FnFacets::from_structural_certificates(true, true, true, true, "ODT self-call test"),
        );
    }
    let mut session = CleanIslandSession::new();
    let outcome = session.check(ISLAND);
    assert!(!outcome.is_rejected(), "{outcome:?}");
    let admitted = session.admit_odt_program_functions(&[cst_face()], funcs, &table).unwrap();
    assert_eq!(admitted.len(), funcs.len(), "{admitted:?}");
    for (path, admission) in admitted {
        // The shape this lane bridges: nominal, unflattened, unnamed.
        assert!(admission.param_names.is_none(), "{admission:?}");
        let carriers = admission.carriers.as_ref().expect("TG11 records the declared carriers");
        assert!(carriers.params.iter().any(|k| matches!(k, Carrier::RegisteredAdt(_))));
        for spelling in trust_spec_elab::spec_spellings(&path) {
            table.admit(spelling, admission.clone());
        }
        table.admit(path, admission);
    }
    (session, table)
}

fn discharge(
    s: &CleanIslandSession,
    t: &FacetTable,
    thm: &str,
    clause: &str,
    rows: &[(&str, &str)],
    f: &str,
) -> CitationVerdict {
    s.check_ensures_discharge_in(
        thm,
        clause,
        rows,
        f,
        t,
        &ProofClauseInputs::proof_lift(Some("u64")),
    )
}

fn refusal(verdict: CitationVerdict) -> String {
    let CitationVerdict::ClauseOutsideFragment { reason } = verdict else {
        panic!("this flattening must not reach the kernel: {verdict:?}")
    };
    reason
}

#[test]
fn a_cited_clause_over_flattened_rows_discharges_against_the_nominal_import() {
    let (s, t) = minted(&[
        reads_field("degree_bound", &[("c", cst())], 0, 0),
        reads_field("second_degree", &[("a", cst()), ("b", cst())], 1, 0),
        reads_field("mixed", &[("n", Ty::u64()), ("c", cst())], 1, 1),
    ]);
    let v =
        discharge(&s, &t, "degree_le_self", "result <= c.degree", &CST_ROWS, "test::degree_bound");
    assert!(matches!(v, CitationVerdict::KernelStatementMatchCertified), "{v:?}");
    let four = [("a.degree", "u64"), ("a.coeff", "u64"), ("b.degree", "u64"), ("b.coeff", "u64")];
    let v = discharge(&s, &t, "third_of_four", "result == b.degree", &four, "test::second_degree");
    assert!(matches!(v, CitationVerdict::KernelStatementMatchCertified), "{v:?}");
    let three = [("n", "u64"), ("c.degree", "u64"), ("c.coeff", "u64")];
    let v = discharge(&s, &t, "third_of_three", "result == c.coeff", &three, "test::mixed");
    assert!(matches!(v, CitationVerdict::KernelStatementMatchCertified), "{v:?}");
}

/// An order-only rebuild would build `f (K.mk c.coeff c.degree) = c.coeff` and
/// let `first_refl` "prove" `result == c.coeff` about a body returning
/// `c.degree`.
#[test]
fn a_swapped_row_order_is_refused_by_name() {
    let (s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 0)]);
    let swapped = [("c.coeff", "u64"), ("c.degree", "u64")];
    let reason = refusal(discharge(
        &s,
        &t,
        "first_refl",
        "result == c.coeff",
        &swapped,
        "test::degree_bound",
    ));
    assert!(reason.contains("does not fill field slot 0"), "{reason}");
}

#[test]
fn a_missing_or_extra_row_is_refused() {
    let (s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 0)]);
    let one = [("c.degree", "u64")];
    let reason = refusal(discharge(
        &s,
        &t,
        "degree_le_self",
        "result <= c.degree",
        &one,
        "test::degree_bound",
    ));
    assert!(reason.contains("needs 2 field row(s)"), "{reason}");
    let extra = [("c.degree", "u64"), ("c.coeff", "u64"), ("x", "u64")];
    let reason =
        refusal(discharge(&s, &t, "degree_le_self", "result <= x", &extra, "test::degree_bound"));
    assert!(reason.contains("left over"), "{reason}");
}

#[test]
fn a_row_at_another_carrier_is_refused() {
    let (s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 0)]);
    let rows = [("c.degree", "u32"), ("c.coeff", "u64")];
    let reason = refusal(discharge(
        &s,
        &t,
        "degree_le_self",
        "result <= c.coeff",
        &rows,
        "test::degree_bound",
    ));
    assert!(reason.contains("is bound at `u32`"), "{reason}");
}

#[test]
fn the_bridge_never_proves_a_body_that_reads_the_other_field() {
    let (s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 1)]);
    let v =
        discharge(&s, &t, "degree_le_self", "result <= c.degree", &CST_ROWS, "test::degree_bound");
    assert!(matches!(v, CitationVerdict::StatementOrCertificationRejected { .. }), "{v:?}");
}

#[test]
fn an_author_written_flattened_call_of_another_function_keeps_the_arity_refusal() {
    let (_s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 0)]);
    let err = trust_spec_elab::elaborate_ensures(
        "test::degree_bound(c.degree, c.coeff) <= c.degree",
        &CST_ROWS,
        "test::other",
        &t,
    )
    .expect_err("only the contracted function's own call is rebuilt");
    assert!(err.contains("has arity 1 but is applied to 2"), "{err}");
}

/// The conditional (under-`requires`) rungs install no self key, so they do not
/// reach the rebuild and keep the arity refusal: fail-closed, and disclosed in
/// E9-ODT-FACE-SELF-CALL-1. If they gain the rebuild, this pin must become a
/// positive one that keeps every name and count check.
#[test]
fn a_conditional_citation_does_not_reach_the_rebuild() {
    let (s, t) = minted(&[reads_field("degree_bound", &[("c", cst())], 0, 0)]);
    let hyp = trust_spec_elab::HypothesisInput {
        contract_index: 0,
        canonical_text: "c.degree <= c.coeff".into(),
        authored_text: "c.degree <= c.coeff".into(),
        query_bindings: CST_ROWS.iter().map(|(n, k)| ((*n).into(), (*k).into())).collect(),
    };
    let ladder = s.check_ensures_discharge_conditional_in(
        "degree_le_self",
        "result <= c.degree",
        &CST_ROWS,
        "test::degree_bound",
        &t,
        &[hyp],
        &ProofClauseInputs::proof_lift(Some("u64")),
    );
    assert!(ladder.conditional_link().is_none(), "{ladder:#?}");
    let why = format!("{ladder:?}");
    assert!(why.contains("has arity 1 but is applied to 2"), "{why}");
}
