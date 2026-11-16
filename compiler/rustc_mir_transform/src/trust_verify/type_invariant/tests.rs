//! Trust (TINV step 9): unit tests of the mint's pure helpers.

use super::*;

fn adt(auth: Option<trust_types::AdtAuth>) -> trust_types::Ty {
    let mut ty = trust_types::Ty::adt("t::S", vec![]);
    if let trust_types::Ty::Adt { arbitrary_precision, .. } = &mut ty {
        *arbitrary_precision = auth;
    }
    ty
}

#[test]
fn may_run_user_drop_truth_table() {
    use trust_types::{AdtAuth, Ty as T};
    let int = T::Int { width: 64, signed: false };
    assert!(!may_run_user_drop(&int));
    assert!(!may_run_user_drop(&T::Ref { mutable: true, inner: Box::new(adt(None)) }));
    assert!(!may_run_user_drop(&T::Tuple(vec![int.clone(), T::Bool])));
    assert!(may_run_user_drop(&T::Tuple(vec![int.clone(), adt(None)])));
    assert!(may_run_user_drop(&adt(None)));
    assert!(!may_run_user_drop(&adt(Some(AdtAuth::TotalDrop(None)))));
    let map = adt(Some(AdtAuth::TotalStdMap(trust_types::TotalMapKind::OrdGlobal)));
    assert!(may_run_user_drop(&map), "TotalStdMap is key-total, not drop-total");
    assert!(may_run_user_drop(&T::Seq { elem: Box::new(int.clone()), drop_auth: None }));
    assert!(!may_run_user_drop(&T::Seq {
        elem: Box::new(int),
        drop_auth: Some(AdtAuth::TotalDrop(None)),
    }));
}

#[test]
fn promoted_key_is_injective_and_never_an_item_path() {
    assert_ne!(promoted_key("a::f", 1), promoted_key("a::f", 10));
    assert_ne!(promoted_key("a::f", 0), promoted_key("a::g", 0));
    assert_ne!(promoted_key("a::f::{promoted#1}", 0), promoted_key("a::f", 1));
    assert!(promoted_key("a::f", 0).contains("{promoted#0}"));
}

#[test]
fn walk_budget_covers_the_round_bound_and_saturates() {
    // 2·Σc + #types + 2 rounds, one walk per body each.
    assert_eq!(walk_budget(3, 4, 2), 3 * (2 * 4 + 2 + 2));
    assert_eq!(walk_budget(usize::MAX, 1, 1), u32::MAX);
    assert_eq!(walk_budget(1, usize::MAX, 1), u32::MAX);
}

#[test]
fn a_failed_verdict_without_a_model_is_unknown() {
    use trust_types::{Counterexample, Symbol, VerificationResult};
    let failed = |cex| VerificationResult::Failed {
        solver: Symbol::intern("ay"),
        time_ms: 0,
        counterexample: cex,
    };
    assert_eq!(oracle_verdict(&failed(None)), None);
    assert_eq!(oracle_model(&failed(None)), None);
    assert_eq!(oracle_verdict(&failed(Some(Counterexample::new(vec![])))), Some(false));
    let unknown = VerificationResult::Unknown {
        solver: Symbol::intern("ay"),
        time_ms: 0,
        reason: String::new(),
    };
    assert_eq!(oracle_verdict(&unknown), None);
}
