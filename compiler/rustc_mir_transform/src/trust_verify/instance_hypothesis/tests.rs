//! OD-1 phase 1: the admission predicate's pure core and the row shapes.

use super::*;

fn r(mutable: bool, pointee: Shape) -> Shape {
    Shape::Ref { mutable, pointee: Box::new(pointee) }
}

fn cell(inner: Shape) -> Shape {
    Shape::UnsafeCell(Box::new(inner))
}

fn owned(inner: Shape) -> Shape {
    Shape::Owned(Box::new(inner))
}

fn refused(decision: ArgDecision) -> bool {
    matches!(decision, ArgDecision::Refuse(_))
}

#[test]
fn raw_pointer_arguments_are_refused() {
    assert!(refused(decide_arg(&Shape::RawPtr)));
    // ... wherever they sit: in a by-value aggregate, behind `&`, behind `&mut`.
    assert!(refused(decide_arg(&Shape::Fields(vec![Shape::Plain, Shape::RawPtr]))));
    assert!(refused(decide_arg(&r(false, Shape::Fields(vec![Shape::RawPtr])))));
    assert!(refused(decide_arg(&r(true, Shape::Fields(vec![Shape::RawPtr])))));
}

#[test]
fn mut_refs_are_havocked_only_when_one_level_covers_them() {
    assert_eq!(decide_arg(&r(true, Shape::Plain)), ArgDecision::Havoc);
    assert_eq!(decide_arg(&r(true, Shape::Generic)), ArgDecision::Havoc);
    assert_eq!(
        decide_arg(&r(true, Shape::Fields(vec![Shape::Plain, cell(Shape::Plain)]))),
        ArgDecision::Havoc
    );
    // A pointee holding a reference or pointer of its own: a write through it is not
    // covered by storing a fresh pointee.
    assert!(refused(decide_arg(&r(true, r(true, Shape::Plain)))));
    assert!(refused(decide_arg(&r(true, r(false, Shape::Plain)))));
    assert!(refused(decide_arg(&r(true, owned(Shape::Plain)))));
    // Unsized or opaque pointees cannot be stored.
    assert!(refused(decide_arg(&r(true, Shape::Str))));
    assert!(refused(decide_arg(&r(true, Shape::Slice(Box::new(Shape::Plain))))));
    assert!(refused(decide_arg(&r(true, Shape::Opaque))));
}

#[test]
fn shared_refs_are_inert_unless_interior_mutable() {
    assert_eq!(decide_arg(&r(false, Shape::Plain)), ArgDecision::Inert);
    assert_eq!(decide_arg(&r(false, Shape::Str)), ArgDecision::Inert);
    assert_eq!(decide_arg(&r(false, Shape::Generic)), ArgDecision::Inert);
    // `&Vec<u8>`: owned contents behind a shared reference are immutable.
    assert_eq!(decide_arg(&r(false, owned(Shape::Plain))), ArgDecision::Inert);
    // `&&mut u32` is read-only.
    assert_eq!(decide_arg(&r(false, r(true, Shape::Plain))), ArgDecision::Inert);
    // `&Cell<u32>`: the callee may write it; one level covers it.
    assert_eq!(decide_arg(&r(false, cell(Shape::Plain))), ArgDecision::Havoc);
    // `&&Cell<u32>`, `&Box<Cell<u32>>`: the cell is behind a pointer the havoc
    // cannot reach.
    assert!(refused(decide_arg(&r(false, r(false, cell(Shape::Plain))))));
    assert!(refused(decide_arg(&r(false, owned(cell(Shape::Plain))))));
    // Interior mutability in an unsized pointee cannot be stored.
    assert!(refused(decide_arg(&r(false, Shape::Slice(Box::new(cell(Shape::Plain)))))));
}

#[test]
fn by_value_arguments_are_judged_by_what_they_borrow() {
    assert_eq!(decide_arg(&Shape::Plain), ArgDecision::Inert);
    assert_eq!(decide_arg(&Shape::Generic), ArgDecision::Inert);
    // Owned contents move with the value.
    assert_eq!(decide_arg(&owned(cell(Shape::Plain))), ArgDecision::Inert);
    assert_eq!(decide_arg(&Shape::Fields(vec![r(false, Shape::Plain)])), ArgDecision::Inert);
    // A borrowed `&mut` or a shared borrow of interior mutability is observable after.
    assert!(refused(decide_arg(&Shape::Fields(vec![r(true, Shape::Plain)]))));
    assert!(refused(decide_arg(&Shape::Fields(vec![r(false, cell(Shape::Plain))]))));
    // A `Vec<&mut u32>` element type sits in `PhantomData`, read as owned.
    assert!(refused(decide_arg(&Shape::Fields(vec![
        owned(Shape::Plain),
        Shape::Fields(vec![r(true, Shape::Plain)])
    ]))));
    assert!(refused(decide_arg(&Shape::Opaque)));
}

#[test]
fn body_conjuncts_refuse_unsafe_and_polymorphic_recursion() {
    assert_eq!(body_admits(true, false, false), Ok(()));
    assert_eq!(body_admits(false, false, false), Err(BodyRefusal::NotAFunction));
    assert_eq!(body_admits(true, true, false), Err(BodyRefusal::UnsafeOperation));
    assert_eq!(body_admits(true, false, true), Err(BodyRefusal::PolymorphicRecursion));
}

#[test]
fn site_conjuncts_are_all_required() {
    let inert = [ArgDecision::Inert, ArgDecision::Havoc, ArgDecision::Inert];
    assert_eq!(site_admits(true, true, false, &inert), Ok(vec![1]));
    assert!(site_admits(false, true, false, &inert).is_err());
    assert!(site_admits(true, false, false, &inert).is_err());
    assert!(site_admits(true, true, true, &inert).is_err());
    assert!(
        site_admits(true, true, false, &[ArgDecision::Inert, ArgDecision::Refuse("raw")]).is_err()
    );
}

fn record(kind: SiteKind) -> SiteRecord {
    SiteRecord {
        block: 0,
        callee: rustc_span::def_id::CRATE_DEF_ID.to_def_id(),
        kind,
        span: rustc_span::DUMMY_SP,
        call_key: "<T as c::Tr>::m".to_string(),
        accounted_key: Some("<T as c::Tr>::m".to_string()),
    }
}

/// The definition row is an exact `assumption:instance-hypothesis` row: skipped, the
/// pinned solver, no typed kind, no proof evidence, marker-free, and never read as
/// an absent-callee row.
#[test]
fn hypothesis_rows_have_the_exact_assumption_shape() {
    for row in [
        hypothesis_row("c::f", &record(SiteKind::Direct), None, None),
        hypothesis_row("c::g", &record(SiteKind::Direct), Some("<U as c::Tr>::m"), None),
        inventory_row(),
    ] {
        assert!(transport_row_is_instance_hypothesis_assumption(&row), "{row:?}");
        assert!(trust_types::assumption::strict_policy_publishes_assumption_row(
            &row.kind,
            &row.solver,
            &row.description
        ));
        assert_eq!(row.outcome, Outcome::Skipped);
        assert!(row.description.starts_with("unverified assumption: "));
        assert!(
            !row.description.contains(trust_types::assumption::ABSENT_CALLEE_ASSUMPTION_PREFIX)
        );
        let kind = trust_types::VcKind::Assertion { message: row.description.clone() };
        assert_eq!(trust_types::l0_refutation::absent_callee_name(&kind), None);
        for text in [&row.kind, &row.description, row.reason.as_ref().unwrap(), &row.solver] {
            let lower = text.to_ascii_lowercase();
            for marker in
                ["native full verifier", "full verifier", "full-verifier", "fullverification::"]
            {
                assert!(!lower.contains(marker), "`{text}` carries `{marker}`");
            }
        }
    }
}

/// A discharge row is never an assumption row, and the strict table never admits it.
#[test]
fn discharge_rows_are_verdicts_not_assumptions() {
    for outcome in [Outcome::Proved, Outcome::Failed, Outcome::Unknown] {
        let row = discharge_row("d".to_string(), None, outcome, "r".to_string());
        assert!(is_instance_hypothesis_discharge_row(&row.kind, &row.solver));
        assert!(!transport_row_is_instance_hypothesis_assumption(&row));
        assert!(!trust_types::assumption::strict_policy_publishes_assumption_row(
            &row.kind,
            &row.solver,
            &row.description
        ));
    }
}

/// Pre-existing rows claiming this module's kinds are stripped (staleness and
/// forgery defence); every other row is kept in order; nothing to do is `None`.
#[test]
fn rows_with_instance_hypotheses_strips_stale_rows_and_appends_the_charge() {
    let other = discharge_row("x".to_string(), None, Outcome::Proved, "r".to_string());
    let mut plain = other.clone();
    plain.kind = "assert".to_string();
    plain.solver = "trust-full-verifier".to_string();
    assert!(rows_with_instance_hypotheses(&[plain.clone()], None).is_none());
    let forged = {
        let mut row = inventory_row();
        row.outcome = Outcome::Proved;
        row
    };
    let charge = InstanceHypothesisCharge {
        rows: vec![hypothesis_row("c::f", &record(SiteKind::Direct), None, None)],
    };
    let out =
        rows_with_instance_hypotheses(&[plain.clone(), forged, other], Some(&charge)).unwrap();
    assert_eq!(out.len(), 2);
    assert_eq!(out[0], plain);
    assert!(transport_row_is_instance_hypothesis_assumption(&out[1]));
    assert!(charge.has_hypotheses());
}

/// Review 2026-10-04 (D2): an alias that survived normalization is inert
/// (`Generic`) only while it is still rooted in a parameter; an alias that mentions
/// no parameter yet did not normalize, and every opaque `impl Trait`, is `Opaque`
/// and refuses the argument wherever it sits.
#[test]
fn only_parameter_rooted_aliases_are_generic() {
    assert_eq!(alias_shape(true, false), Shape::Generic);
    assert_eq!(alias_shape(false, false), Shape::Opaque);
    assert_eq!(alias_shape(true, true), Shape::Opaque);
    assert_eq!(alias_shape(false, true), Shape::Opaque);
    for shape in [alias_shape(false, false), alias_shape(true, true)] {
        assert!(refused(decide_arg(&shape.clone())));
        assert!(refused(decide_arg(&Shape::Fields(vec![Shape::Plain, shape.clone()]))));
        assert!(refused(decide_arg(&r(false, shape.clone()))));
        assert!(refused(decide_arg(&r(true, shape))));
    }
}

/// Review 2026-10-04 (dead exact-shape check): the zero-obligation transport
/// exemption reads `hypotheses_are_exact`, which a charge with no hypothesis row, or
/// with one whose shape was tampered with, never satisfies.
#[test]
fn hypotheses_are_exact_requires_the_exact_compiler_shape() {
    let exact = InstanceHypothesisCharge {
        rows: vec![hypothesis_row("c::f", &record(SiteKind::Direct), None, None)],
    };
    assert!(exact.hypotheses_are_exact());
    let only_discharge = InstanceHypothesisCharge {
        rows: vec![discharge_row("d".to_string(), None, Outcome::Proved, "r".to_string())],
    };
    assert!(!only_discharge.hypotheses_are_exact());
    for tamper in [
        |row: &mut TransportObligationResult| row.outcome = Outcome::Proved,
        |row: &mut TransportObligationResult| row.design_mandate = true,
        |row: &mut TransportObligationResult| {
            row.typed_kind =
                Some(Box::new(trust_types::VcKind::Assertion { message: "x".to_string() }))
        },
    ] {
        let mut row = hypothesis_row("c::f", &record(SiteKind::Direct), None, None);
        tamper(&mut row);
        let charge = InstanceHypothesisCharge { rows: vec![row] };
        assert!(!charge.hypotheses_are_exact());
    }
}
