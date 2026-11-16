//! TINV step 10.2: the use set's constructor and its tag map.

use std::collections::{BTreeMap, BTreeSet, HashSet};

use trust_types::{CalleeIdentity, Formula, Ty, type_invariant_assume_tag};

use super::*;
use crate::type_invariant::houdini::{TinvOutcome, TypeInvariantCertificate};
use crate::type_invariant::{CandidateConjunct, FieldTerm, field_var};

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn ty(def_path: &str, ids: &[u32]) -> TinvType {
    TinvType {
        def_path: def_path.into(),
        fields: vec![("i".into(), u64_ty()), ("n".into(), u64_ty())],
        conjuncts: ids
            .iter()
            .map(|&id| CandidateConjunct {
                id,
                formula: Formula::Le(
                    Box::new(field_var(FieldTerm::Value(0))),
                    Box::new(field_var(FieldTerm::Value(1))),
                ),
            })
            .collect(),
    }
}

const ID: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 1, def_index: 9, substs_digest: [0, 0] };

fn outcome(types: &[TinvType]) -> TinvOutcome<()> {
    TinvOutcome {
        certificates: types
            .iter()
            .map(|t| (t.def_path.clone(), TypeInvariantCertificate::for_test(t)))
            .collect::<BTreeMap<_, _>>(),
        inventory: [ID].into_iter().collect(),
        checked_bodies: ["c::f".to_string(), "c::g".to_string()].into_iter().collect(),
        ..TinvOutcome::default()
    }
}

#[test]
fn the_set_carries_the_published_types_and_the_runs_induction() {
    let out = outcome(&[ty("c::P", &[0, 2]), ty("c::Q", &[1])]);
    let set = TinvUseSet::from_outcome(&out, |p| p != "c::Q").expect("a use set");
    assert!(!set.is_empty());
    assert_eq!(set.types().keys().collect::<Vec<_>>(), vec!["c::P"], "only the published type");
    assert_eq!(set.types()["c::P"], ty("c::P", &[0, 2]), "fields and conjuncts as certified");
    assert_eq!(set.inventory(), &[ID].into_iter().collect::<HashSet<_>>());
    assert_eq!(set.checked_bodies(), &out.checked_bodies);
    // The tag map round-trips, names only published conjuncts, and is the trust-types spelling.
    assert_eq!(set.tags().len(), 2);
    for id in [0, 2] {
        let tag = set.tag_for("c::P", id).expect("a published conjunct has a tag");
        assert_eq!(tag, type_invariant_assume_tag("c::P", id));
        assert_eq!(set.decode_tag(tag), Some(("c::P", id)));
    }
    assert_eq!(set.tag_for("c::P", 1), None);
    assert_eq!(set.tag_for("c::Q", 1), None, "an unpublished type has no tag");
    assert_eq!(set.decode_tag(&type_invariant_assume_tag("c::Q", 1)), None);
    assert_eq!(set.decode_tag("$tinv_assume_0000000000000000"), None);
}

#[test]
fn nothing_published_is_an_empty_set() {
    let set = TinvUseSet::from_outcome(&outcome(&[ty("c::P", &[0])]), |_| false).expect("empty");
    assert!(set.is_empty() && set.tags().is_empty());
    let set = TinvUseSet::from_outcome(&TinvOutcome::<()>::default(), |_| true).expect("empty");
    assert!(set.is_empty());
}

/// A tag collision refuses the WHOLE set, not just the second conjunct.
#[test]
fn a_tag_collision_refuses_the_set() {
    let out = outcome(&[ty("c::P", &[0]), ty("c::Q", &[0])]);
    let got = TinvUseSet::build(&out, |_| true, |_, _| "$tinv_assume_collide".to_string());
    assert_eq!(
        got,
        Err(TinvUseSetRefusal::TagCollision {
            tag: "$tinv_assume_collide".into(),
            first: ("c::P".into(), 0),
            second: ("c::Q".into(), 0),
        })
    );
    // Within one type too.
    let out = outcome(&[ty("c::P", &[0, 1])]);
    let got = TinvUseSet::build(&out, |_| true, |p, _| format!("$tinv_assume_{}", p.len()));
    assert!(matches!(got, Err(TinvUseSetRefusal::TagCollision { .. })), "{got:?}");
    // The same outcome with the real spelling builds.
    assert!(TinvUseSet::from_outcome(&out, |_| true).is_ok());
}

#[test]
fn an_inconsistent_outcome_refuses_the_set() {
    // Published certificates but no checked body.
    let mut out = outcome(&[ty("c::P", &[0])]);
    out.checked_bodies = BTreeSet::new();
    assert_eq!(TinvUseSet::from_outcome(&out, |_| true), Err(TinvUseSetRefusal::NoCheckedBodies));
    // ...which is fine when nothing is published.
    assert!(TinvUseSet::from_outcome(&out, |_| false).is_ok());
    // A certificate filed under another type's key.
    let mut out = outcome(&[ty("c::P", &[0])]);
    let cert = out.certificates.remove("c::P").expect("cert");
    out.certificates.insert("c::Q".into(), cert);
    assert_eq!(
        TinvUseSet::from_outcome(&out, |_| true),
        Err(TinvUseSetRefusal::MalformedCertificate("c::Q".into()))
    );
    // No conjunct, or no field.
    let out = outcome(&[ty("c::P", &[])]);
    assert!(matches!(
        TinvUseSet::from_outcome(&out, |_| true),
        Err(TinvUseSetRefusal::MalformedCertificate(_))
    ));
    let mut fieldless = ty("c::P", &[0]);
    fieldless.fields.clear();
    let out = outcome(&[fieldless]);
    assert!(matches!(
        TinvUseSet::from_outcome(&out, |_| true),
        Err(TinvUseSetRefusal::MalformedCertificate(_))
    ));
}
