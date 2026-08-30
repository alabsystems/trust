use trust_certify::{certify_vc, recheck_vc_cleancic};
use trust_ir::ProofEvidence;

mod fixture {
    include!("fixtures/r174_branch_clamp.rs");
}

use fixture::Mutation;

#[test]
fn standalone_branch_clamp_fixture_certifies_and_rechecks() {
    let vc = fixture::vc(Mutation::Honest);
    let ProofEvidence::CleanCic { term, context, lineage, .. } =
        certify_vc(&vc).expect("standalone branch-clamp fixture must certify")
    else {
        panic!("expected CleanCic evidence");
    };
    assert!(recheck_vc_cleancic(&term, &context, &lineage, &vc));

    let mut wrong_identity = vc.clone();
    wrong_identity.function = "r174_fixture::other".into();
    assert!(!recheck_vc_cleancic(&term, &context, &lineage, &wrong_identity));

    let mut malformed_term = term.clone();
    malformed_term[0] ^= 1;
    assert!(!recheck_vc_cleancic(&malformed_term, &context, &lineage, &vc));
}

#[test]
fn standalone_fixture_requires_the_precondition_and_result_binding() {
    assert!(certify_vc(&fixture::vc(Mutation::MissingRequires)).is_none());
    assert!(certify_vc(&fixture::vc(Mutation::MissingResultBinding)).is_none());
}

#[test]
fn standalone_fixture_rejects_an_ill_sorted_reification() {
    let vc = fixture::vc(Mutation::MalformedReification);
    assert!(trust_types::smt_logic::check_formula_sort(&vc.formula).is_err());
    assert!(certify_vc(&vc).is_none());
}
