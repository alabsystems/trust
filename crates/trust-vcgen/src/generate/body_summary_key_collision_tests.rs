//! SUMMARY-NAME-COLLIDE-1 (2026-10-05): a BODY-DERIVED callee summary (not the
//! postcondition-injection lane `summary_key_collision_tests.rs` pins) is keyed
//! by the callee's rendered `def_path`, and a call site finds it by its own
//! rendered callee name. Two bodies can render one key — rustc keeps
//! `impl Tr for W<for<'a> fn(&'a u8) -> &'static u8>` and
//! `impl Tr for W<for<'a> fn(&'a u8) -> &'a u8>` as two impls (rust#56105), and
//! the extractor canonicalizes both methods to
//! `<k::W<for<'_> fn(&'_ u8) -> &'_ u8> as k::Tr>::get`. Every lane used to keep
//! whichever body came LAST, so a call through the other impl was handed its
//! facts. A shared key now summarizes nothing, in every lane, whichever order
//! the bodies arrive in (`summary_candidates`), and the compiler's crate-wide
//! half of the rule is `summary_key_collisions`.

use trust_types::{
    BasicBlock, BlockId, ConstValue, LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan,
    Statement, Terminator, Ty, VerifiableBody, VerifiableFunction,
};

use super::{
    compute_return_bool_pred_summaries, compute_return_bound_summaries,
    compute_return_const_set_summaries, compute_return_disc_summaries,
    compute_return_field_summaries, compute_return_lower_bound_summaries,
    compute_trivial_setter_summaries, summary_key_collisions,
};

/// The key both impls' methods render to (the measured HRTB pair).
const SHARED: &str = "<k::W<for<'_> fn(&'_ u8) -> &'_ u8> as k::Tr>::get";
/// A key only one body has.
const UNIQUE: &str = "k::five";

fn u32_ty() -> Ty {
    Ty::Int { width: 32, signed: false }
}

fn func(
    def_path: &str,
    locals: Vec<LocalDecl>,
    stmts: Vec<Statement>,
    arg_count: usize,
) -> VerifiableFunction {
    let return_ty = locals[0].ty.clone();
    VerifiableFunction {
        name: def_path.rsplit("::").next().unwrap_or(def_path).to_string(),
        def_path: def_path.to_string(),
        span: SourceSpan::default(),
        body: VerifiableBody {
            locals,
            blocks: vec![BasicBlock { id: BlockId(0), stmts, terminator: Terminator::Return }],
            arg_count,
            return_ty,
            datatype_defs: Default::default(),
        },
        contracts: vec![],
        preconditions: vec![],
        postconditions: vec![],
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

/// `fn get(_x: u32) -> u32 { c }` — every return a constant: const-set `{c}`,
/// upper and lower bound `c`.
fn const_get(def_path: &str, c: u128) -> VerifiableFunction {
    func(
        def_path,
        vec![
            LocalDecl { index: 0, ty: u32_ty(), name: None },
            LocalDecl { index: 1, ty: u32_ty(), name: Some("x".into()) },
        ],
        vec![assign(Place::local(0), Rvalue::Use(Operand::Constant(ConstValue::Uint(c, 32))))],
        1,
    )
}

/// `fn get(x: u32) -> u32 { x }` — no constant return, so no summary of its own.
fn identity_get(def_path: &str) -> VerifiableFunction {
    func(
        def_path,
        vec![
            LocalDecl { index: 0, ty: u32_ty(), name: None },
            LocalDecl { index: 1, ty: u32_ty(), name: Some("x".into()) },
        ],
        vec![assign(Place::local(0), Rvalue::Use(Operand::Copy(Place::local(1))))],
        1,
    )
}

/// `fn set(p: &mut u32, v: u32) { *p = <src>; }` — a trivial setter.
fn setter(def_path: &str, src: Operand) -> VerifiableFunction {
    func(
        def_path,
        vec![
            LocalDecl { index: 0, ty: Ty::Unit, name: None },
            LocalDecl {
                index: 1,
                ty: Ty::Ref { mutable: true, inner: Box::new(u32_ty()) },
                name: Some("p".into()),
            },
            LocalDecl { index: 2, ty: u32_ty(), name: Some("v".into()) },
        ],
        vec![assign(Place { local: 1, projections: vec![Projection::Deref] }, Rvalue::Use(src))],
        2,
    )
}

/// Every body-derived lane's entry for `key` over `funcs`, as debug strings
/// (`None` = no entry), in a fixed lane order.
fn lane_entries(funcs: &[VerifiableFunction], key: &str) -> Vec<(&'static str, Option<String>)> {
    vec![
        ("upper", compute_return_bound_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("lower", compute_return_lower_bound_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("const_set", compute_return_const_set_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("disc", compute_return_disc_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("setter", compute_trivial_setter_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("bool_pred", compute_return_bool_pred_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
        ("field", compute_return_field_summaries(funcs).get(key).map(|v| format!("{v:?}"))),
    ]
}

fn no_entry(entries: &[(&'static str, Option<String>)]) -> bool {
    entries.iter().all(|(_, entry)| entry.is_none())
}

#[test]
fn the_const_body_alone_is_summarized_in_three_lanes() {
    // Control: the fixtures below DO produce summaries on their own, so an
    // absent entry later is the collision rule, not a fixture that never
    // summarized.
    let entries = lane_entries(&[const_get(SHARED, 1)], SHARED);
    assert_eq!(entries[0], ("upper", Some("1".to_string())), "{entries:?}");
    assert_eq!(entries[1], ("lower", Some("1".to_string())), "{entries:?}");
    assert_eq!(entries[2], ("const_set", Some("[1]".to_string())), "{entries:?}");
    assert!(no_entry(&lane_entries(&[identity_get(SHARED)], SHARED)));
}

#[test]
fn a_key_two_bodies_share_is_summarized_by_no_lane_in_either_order() {
    // The measured shape: the impl a call RUNS returns `x`, its sibling returns
    // `1`. Before the fix the const-set `{1}`, upper bound 1 and lower bound 1
    // were recorded under the shared key when the const body came last (and the
    // const body's alone when it came first, since the identity body records
    // nothing); a call through the identity impl was then handed `y == 1`.
    for funcs in [
        vec![identity_get(SHARED), const_get(SHARED, 1)],
        vec![const_get(SHARED, 1), identity_get(SHARED)],
        vec![const_get(SHARED, 1), const_get(SHARED, 100)],
    ] {
        let entries = lane_entries(&funcs, SHARED);
        assert!(no_entry(&entries), "a shared key must summarize nothing: {entries:?}");
    }
}

#[test]
fn the_rule_is_per_key_not_per_crate() {
    // A unique key beside a shared one keeps its summary: the rule refuses the
    // key two bodies share, not every summary in a crate that has one.
    let funcs = vec![identity_get(SHARED), const_get(UNIQUE, 5), const_get(SHARED, 1)];
    assert!(no_entry(&lane_entries(&funcs, SHARED)));
    let unique = lane_entries(&funcs, UNIQUE);
    assert_eq!(unique[2], ("const_set", Some("[5]".to_string())), "{unique:?}");
}

#[test]
fn a_setter_key_two_bodies_share_records_no_effect() {
    // Two trivial setters under one key: `*p = v` and `*p = 7`. Each alone is
    // recorded; together, neither — the caller's `assert!(a == v)` must not be
    // discharged from a body the call may not run.
    let by_param = setter(SHARED, Operand::Copy(Place::local(2)));
    let by_const = setter(SHARED, Operand::Constant(ConstValue::Uint(7, 32)));
    assert!(compute_trivial_setter_summaries(std::slice::from_ref(&by_param)).contains_key(SHARED));
    assert!(compute_trivial_setter_summaries(std::slice::from_ref(&by_const)).contains_key(SHARED));
    for funcs in [vec![by_param.clone(), by_const.clone()], vec![by_const, by_param]] {
        assert!(
            !compute_trivial_setter_summaries(&funcs).contains_key(SHARED),
            "a shared setter key must record no effect"
        );
    }
}

#[test]
fn summary_key_collisions_names_exactly_the_keys_two_owners_share() {
    // Owner identities stand in for `DefId`s. The same (key, owner) pair given
    // twice — the compiler feeds an extracted body from two inventories — is
    // one owner, not a collision.
    let owners = [
        (SHARED, 10u32),
        (UNIQUE, 11),
        (SHARED, 12),
        (UNIQUE, 11),
        ("k::g", 13),
        ("k::h", 14),
        ("k::h", 15),
        ("k::h", 14),
    ];
    let mut keys: Vec<String> = summary_key_collisions(owners).into_iter().collect();
    keys.sort();
    assert_eq!(keys, vec!["<k::W<for<'_> fn(&'_ u8) -> &'_ u8> as k::Tr>::get", "k::h"]);
    assert!(summary_key_collisions(std::iter::empty::<(&str, u32)>()).is_empty());
}
