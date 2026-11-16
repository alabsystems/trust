//! TINV step 10.1: the type-invariant assumption tag, its scan, and the kernel refusal
//! of every VC that carries one (TINV-23).
//!
//! The kernel entries themselves (`trust_certify::certify_vc`, the native-planning and
//! replay entries, `trust_clean`'s certificate and pipeline entries) are pinned in their
//! own crates; this file pins the predicate they all call.

use std::collections::BTreeSet;

use trust_types::{
    Formula, ObligationRecord, ObligationWrapper, PathGuardTerm, Sort, SourceSpan,
    TINV_ASSUME_TAG_HEX_DIGITS, TINV_ASSUME_TAG_PREFIX, TINV_TAG_SCAN_MAX_NODES, TinvTagScan,
    TypeInvariantPoint, TypeInvariantSite, VcKind, VerificationCondition,
    is_type_invariant_assume_tag, type_invariant_assume_tag,
};

fn int(name: &str) -> Formula {
    Formula::Var(name.to_string(), Sort::Int)
}

fn tag_var(def_path: &str, id: u32) -> Formula {
    Formula::Var(type_invariant_assume_tag(def_path, id), Sort::Bool)
}

/// `i < n ∧ ¬(i < n)`: UNSAT, so a kernel would certify it but for the gate.
fn violation() -> Formula {
    let lt = Formula::Lt(Box::new(int("i")), Box::new(int("n")));
    Formula::And(vec![lt.clone(), Formula::Not(Box::new(lt))])
}

/// The use-site fact shape: `And([tag, I])`.
fn tagged_fact(def_path: &str, id: u32) -> Formula {
    Formula::And(vec![tag_var(def_path, id), Formula::Le(Box::new(int("i")), Box::new(int("n")))])
}

fn vc(
    kind: VcKind,
    formula: Formula,
    obligation: Option<ObligationRecord>,
) -> VerificationCondition {
    VerificationCondition {
        kind,
        function: "c::f".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation,
    }
}

fn bounds(formula: Formula) -> VerificationCondition {
    vc(VcKind::IndexOutOfBounds, formula, None)
}

fn tinv_kind() -> VcKind {
    VcKind::TypeInvariant {
        ty: "c::P".into(),
        point: TypeInvariantPoint::Return,
        site: TypeInvariantSite { block: 1, statement_index: 0 },
        conjunct: 0,
        ordinal: 0,
        edge: None,
    }
}

fn tags(names: &[String]) -> TinvTagScan {
    TinvTagScan::Tags(names.iter().cloned().collect::<BTreeSet<_>>())
}

// ---------------------------------------------------------------------------------------
// The spelling
// ---------------------------------------------------------------------------------------

#[test]
fn the_tag_is_the_prefix_and_sixteen_lowercase_hex_digits() {
    for (path, id) in [("c::P", 0), ("c::P", 1), ("a::b::Screen", u32::MAX), ("", 0)] {
        let tag = type_invariant_assume_tag(path, id);
        let digits = tag.strip_prefix(TINV_ASSUME_TAG_PREFIX).expect("prefix");
        assert_eq!(digits.len(), TINV_ASSUME_TAG_HEX_DIGITS, "{tag}");
        assert!(digits.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)), "{tag}");
        assert!(is_type_invariant_assume_tag(&tag));
        assert_eq!(tag, type_invariant_assume_tag(path, id), "deterministic");
    }
    // Known vectors pin the input encoding (`def_path ‖ 0x00 ‖ id as u32 BE`, sha256,
    // first 8 bytes), computed independently with Python's `hashlib`: a change re-spells
    // every tag and must be deliberate.
    assert_eq!(type_invariant_assume_tag("c::P", 0), "$tinv_assume_be986673103757f8");
    assert_eq!(type_invariant_assume_tag("a::b::Screen", 7), "$tinv_assume_1eb235d44b854b36");
    assert_ne!(type_invariant_assume_tag("c::P", 0), type_invariant_assume_tag("c::P", 1));
    assert_ne!(type_invariant_assume_tag("c::P", 0), type_invariant_assume_tag("c::Q", 0));
}

/// The separator byte makes `(path, id)` unambiguous: no two inputs that only re-split
/// the same bytes between the path and the id share a preimage.
#[test]
fn the_digest_input_is_unambiguous() {
    let mut seen = BTreeSet::new();
    for path in ["", "c", "c::", "c::P", "c::P\u{0}", "c::P\u{0}\u{0}"] {
        for id in [0u32, 1, 256, 0x0000_00ff, 0x00ff_0000] {
            assert!(seen.insert(type_invariant_assume_tag(path, id)), "{path:?} {id}");
        }
    }
}

/// The characters the vcgen version and place grammar splits on never occur in a tag:
/// `#` (version tokens, `#e` sentinels), `:` (paths), `.` (field projections), `*`
/// (derefs), and nothing outside `[$_a-z0-9]`.
#[test]
fn no_tag_contains_a_version_or_place_separator() {
    let paths =
        ["c::P", "a::b::C", "x#e", "y.0", "z*", "w:v", "#", "::", "", "c::P#3", "a\u{0}b", "Ü"];
    for path in paths {
        for id in [0u32, 1, 7, 42, 1 << 16, u32::MAX] {
            let tag = type_invariant_assume_tag(path, id);
            for bad in ['#', ':', '.', '*', ' ', '[', ']', '(', ')'] {
                assert!(!tag.contains(bad), "{tag} contains {bad:?}");
            }
            assert!(
                tag.chars()
                    .all(|c| c == '$' || c == '_' || c.is_ascii_lowercase() || c.is_ascii_digit()),
                "{tag}"
            );
        }
    }
}

// ---------------------------------------------------------------------------------------
// The scan
// ---------------------------------------------------------------------------------------

#[test]
fn the_scan_finds_a_tag_in_every_formula_position_of_a_vc() {
    let t0 = type_invariant_assume_tag("c::P", 0);
    let t1 = type_invariant_assume_tag("c::P", 1);
    let untagged = violation();
    assert_eq!(bounds(untagged.clone()).type_invariant_tags(), TinvTagScan::None);

    // In the formula.
    let f = Formula::And(vec![tagged_fact("c::P", 0), untagged.clone()]);
    assert_eq!(bounds(f).type_invariant_tags(), tags(&[t0.clone()]));
    // Two tags, under a negation and an implication.
    let f = Formula::And(vec![
        Formula::Not(Box::new(Formula::Not(Box::new(tag_var("c::P", 1))))),
        Formula::Implies(Box::new(tag_var("c::P", 0)), Box::new(untagged.clone())),
    ]);
    assert_eq!(bounds(f).type_invariant_tags(), tags(&[t0.clone(), t1.clone()]));
    // As a SymVar, a binder and a predicate symbol.
    let sym = Formula::SymVar(t0.as_str().into(), Sort::Bool);
    assert_eq!(bounds(sym).type_invariant_tags(), tags(&[t0.clone()]));
    let bound = Formula::Forall(vec![(t1.as_str().into(), Sort::Bool)], Box::new(untagged.clone()));
    assert_eq!(bounds(bound).type_invariant_tags(), tags(&[t1.clone()]));
    let exists =
        Formula::Exists(vec![(t1.as_str().into(), Sort::Bool)], Box::new(untagged.clone()));
    assert_eq!(bounds(exists).type_invariant_tags(), tags(&[t1.clone()]));
    let pred = Formula::Pred(t0.as_str().into(), vec![int("i")]);
    assert_eq!(bounds(pred).type_invariant_tags(), tags(&[t0.clone()]));
    // A forged spelling under the prefix is a tag too (the prefix alone decides).
    let forged = format!("{TINV_ASSUME_TAG_PREFIX}not_hex#e");
    let f = Formula::Var(forged.clone(), Sort::Bool);
    assert_eq!(bounds(f).type_invariant_tags(), tags(&[forged]));

    // In the obligation record only: body, subject, a fact, a path guard.
    let record = |body: Formula, wrappers: Vec<ObligationWrapper>, subject: Option<Formula>| {
        Some(ObligationRecord { body, wrappers, subject, width: None })
    };
    let only_in = [
        record(tagged_fact("c::P", 0), vec![], None),
        record(untagged.clone(), vec![], Some(tag_var("c::P", 0))),
        record(
            untagged.clone(),
            vec![ObligationWrapper::ConjoinFactsLast { facts: vec![tagged_fact("c::P", 0)] }],
            None,
        ),
        record(
            untagged.clone(),
            vec![ObligationWrapper::PathGuardOr {
                paths: vec![
                    PathGuardTerm::Raw,
                    PathGuardTerm::Guarded { guards: vec![tag_var("c::P", 0)] },
                ],
            }],
            None,
        ),
    ];
    for obligation in only_in {
        let v = vc(VcKind::IndexOutOfBounds, untagged.clone(), obligation.clone());
        assert_eq!(v.type_invariant_tags(), tags(&[t0.clone()]), "{obligation:?}");
        assert!(v.kernel_authority_refusal().is_some(), "{obligation:?}");
    }
}

#[test]
fn a_scan_past_the_node_bound_is_unbounded() {
    // `And` of exactly the bound minus one leaves: the root plus every leaf is the bound.
    let wide = |leaves: usize| Formula::And(vec![Formula::Bool(true); leaves]);
    let at_bound = bounds(wide(TINV_TAG_SCAN_MAX_NODES - 1));
    assert_eq!(at_bound.type_invariant_tags(), TinvTagScan::None);
    let past = bounds(wide(TINV_TAG_SCAN_MAX_NODES));
    assert_eq!(past.type_invariant_tags(), TinvTagScan::Unbounded);
    assert!(past.kernel_authority_refusal().is_some());
    // The bound is over every formula of the VC together, record included.
    let split = vc(
        VcKind::IndexOutOfBounds,
        wide(TINV_TAG_SCAN_MAX_NODES / 2),
        Some(ObligationRecord {
            body: wide(TINV_TAG_SCAN_MAX_NODES / 2),
            wrappers: vec![],
            subject: None,
            width: None,
        }),
    );
    assert_eq!(split.type_invariant_tags(), TinvTagScan::Unbounded);
    assert!(split.kernel_authority_refusal().is_some());
}

// ---------------------------------------------------------------------------------------
// The kernel refusal
// ---------------------------------------------------------------------------------------

#[test]
fn a_tagged_vc_is_refused_kernel_authority_and_its_untagged_twin_is_not() {
    for kind in [
        VcKind::IndexOutOfBounds,
        VcKind::DivisionByZero,
        VcKind::Assertion { message: "a".into() },
        VcKind::Unreachable,
    ] {
        let twin = vc(kind.clone(), violation(), None);
        assert_eq!(twin.kernel_authority_refusal(), None, "{kind:?}: the untagged control");
        let tagged =
            vc(kind.clone(), Formula::And(vec![tagged_fact("c::P", 3), violation()]), None);
        let why = tagged.kernel_authority_refusal().expect("a tagged VC is refused");
        assert!(why.contains("$tinv_assume_"), "{kind:?}: {why}");
    }
}

/// A type-invariant row with a tag is refused even when it is otherwise situated: the
/// tag refusal comes before the row gate, and nothing about a row exempts it.
#[test]
fn a_tagged_type_invariant_row_is_refused_though_situated() {
    let hyp = Formula::Le(Box::new(int("i")), Box::new(int("n")));
    let core = Formula::Not(Box::new(hyp.clone()));
    let body = Formula::And(vec![hyp.clone(), core.clone()]);
    let situated = vc(
        tinv_kind(),
        body.clone(),
        Some(ObligationRecord { body: body.clone(), wrappers: vec![], subject: None, width: None }),
    );
    assert_eq!(situated.type_invariant_situatedness_refusal(), None);
    assert_eq!(situated.kernel_authority_refusal(), None, "the untagged control");

    let facts = vec![tagged_fact("c::P", 0)];
    let formula = Formula::And(facts.iter().cloned().chain([body.clone()]).collect());
    let tagged = vc(
        tinv_kind(),
        formula,
        Some(ObligationRecord {
            body,
            wrappers: vec![ObligationWrapper::ConjoinFactsLast { facts }],
            subject: None,
            width: None,
        }),
    );
    assert_eq!(tagged.type_invariant_situatedness_refusal(), None, "still situated");
    let why = tagged.kernel_authority_refusal().expect("a tagged TINV row is refused");
    assert!(why.contains("TINV-23"), "{why}");
}

/// A name that merely contains the prefix, or a near-miss spelling, is not a tag.
#[test]
fn only_the_prefix_makes_a_tag() {
    for name in
        ["tinv_assume_00", "x$tinv_assume_00", "$tinv_assum_00", "$TINV_ASSUME_00", "$tinv_v0"]
    {
        assert!(!is_type_invariant_assume_tag(name), "{name}");
        let f = Formula::And(vec![Formula::Var(name.into(), Sort::Bool), violation()]);
        assert_eq!(bounds(f.clone()).type_invariant_tags(), TinvTagScan::None, "{name}");
        assert_eq!(bounds(f).kernel_authority_refusal(), None, "{name}");
    }
}
