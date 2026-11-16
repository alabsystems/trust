//! TINV step 10.2: the use-site facts, on hand-built bodies. Nothing is conjoined into a
//! row yet (step 10.3); these tests pin WHICH facts a body gets and their spelling.

use std::rc::Rc;
use std::sync::Arc;

use trust_types::{
    BasicBlock, BlockId, CalleeIdentity, Formula, LocalDecl, Operand, Place, Projection, Rvalue,
    Sort, SourceSpan, Statement, Terminator, Ty, UnwindEdge, VerifiableBody, VerifiableFunction,
};

use super::*;
use crate::generate::tinv_rows::{TinvRowRequest, enter_tinv_rows};
use crate::type_invariant::houdini::{TinvOutcome, TypeInvariantCertificate};
use crate::type_invariant::{CandidateConjunct, FieldTerm, field_var};

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn vec_ty() -> Ty {
    Ty::Seq { elem: Box::new(Ty::Int { width: 8, signed: false }), drop_auth: None }
}

fn s_fields() -> Vec<(String, Ty)> {
    vec![("v".into(), vec_ty()), ("k".into(), u64_ty())]
}

fn s_ty() -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::S".into(),
        fields: s_fields().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

/// `I(S) = k <= len(v)` (conjunct 0) and `k <= k + 1`-free `0 <= k` (conjunct 3).
fn s_tinv() -> TinvType {
    TinvType {
        def_path: "c::S".into(),
        fields: s_fields(),
        conjuncts: vec![
            CandidateConjunct {
                id: 0,
                formula: Formula::Le(
                    Box::new(field_var(FieldTerm::Value(1))),
                    Box::new(field_var(FieldTerm::Len(0))),
                ),
            },
            CandidateConjunct {
                id: 3,
                formula: Formula::Le(
                    Box::new(Formula::Int(0)),
                    Box::new(field_var(FieldTerm::Value(1))),
                ),
            },
        ],
    }
}

const INV: CalleeIdentity =
    CalleeIdentity { stable_crate_id: 1, def_index: 7, substs_digest: [0, 0] };

fn use_set(checked: &[&str]) -> TinvUseSet {
    let t = s_tinv();
    let out = TinvOutcome::<()> {
        certificates: [(t.def_path.clone(), TypeInvariantCertificate::for_test(&t))]
            .into_iter()
            .collect(),
        inventory: [INV].into_iter().collect(),
        checked_bodies: checked.iter().map(|s| s.to_string()).collect(),
        ..TinvOutcome::default()
    };
    TinvUseSet::from_outcome(&out, |_| true).expect("use set")
}

fn func(
    name: &str,
    locals: Vec<(Ty, Option<&str>)>,
    arg_count: usize,
    blocks: Vec<BasicBlock>,
) -> VerifiableFunction {
    VerifiableFunction {
        name: name.into(),
        def_path: format!("c::{name}"),
        span: SourceSpan::default(),
        body: VerifiableBody {
            return_ty: locals[0].0.clone(),
            locals: locals
                .into_iter()
                .enumerate()
                .map(|(index, (ty, name))| LocalDecl { index, ty, name: name.map(Into::into) })
                .collect(),
            blocks,
            arg_count,
            datatype_defs: Default::default(),
        },
        contracts: Vec::new(),
        preconditions: Vec::new(),
        postconditions: Vec::new(),
        spec: Default::default(),
        tuple_layouts: Default::default(),
    }
}

fn blk(id: usize, stmts: Vec<Statement>, terminator: Terminator) -> BasicBlock {
    BasicBlock { id: BlockId(id), stmts, terminator }
}

fn ret() -> Terminator {
    Terminator::Return
}

/// `fn name(s: <param>) {}`.
fn one_param(name: &str, param: Ty) -> VerifiableFunction {
    func(name, vec![(Ty::Unit, None), (param, Some("s"))], 1, vec![blk(0, vec![], ret())])
}

fn deref(l: usize) -> Place {
    Place { local: l, projections: vec![Projection::Deref] }
}

/// The entry instances the MINT assumes at `root` (`type_invariant_check_vcs`), tagged.
fn mint_instances(
    f: &VerifiableFunction,
    set: &TinvUseSet,
    root: &Place,
) -> Vec<(String, Formula)> {
    let t = s_tinv();
    let sigma = sigma_of_root(f, &t, root);
    t.conjuncts
        .iter()
        .map(|c| {
            let tag = set.tag_for("c::S", c.id).expect("tag").to_owned();
            let inst = instantiate(c, &sigma).expect("instantiable");
            (tag.clone(), Formula::And(vec![Formula::Var(tag, Sort::Bool), inst]))
        })
        .collect()
}

#[test]
fn a_shared_ref_and_a_by_value_parameter_get_exactly_the_mints_entry_facts() {
    for (name, param, root) in [
        ("get", Ty::Ref { mutable: false, inner: Box::new(s_ty()) }, deref(1)),
        ("take", s_ty(), Place::local(1)),
    ] {
        let f = one_param(name, param);
        let set = use_set(&[&f.def_path]);
        let facts = tinv_use_facts_with(&f, &set).expect("entry facts");
        assert_eq!(facts.entry, mint_instances(&f, &set, &root), "{name}");
        assert!(facts.post_calls.is_empty());
        for (tag, fact) in &facts.entry {
            let (ty, _) = set.decode_tag(tag).expect("every tag decodes");
            assert_eq!(ty, "c::S");
            let Formula::And(parts) = fact else { panic!("{fact:?}") };
            assert_eq!(parts[0], Formula::Var(tag.clone(), Sort::Bool), "the tag is first");
            // Entry facts are BARE: no version token anywhere.
            let mut versioned = false;
            fact.visit(&mut |n| {
                if let Formula::Var(v, _) = n {
                    versioned |= v.contains('#');
                }
            });
            assert!(!versioned, "{fact:?}");
        }
        // The `Fact::entry` view carries the same formulas.
        let as_facts = facts.entry_facts();
        assert_eq!(as_facts.len(), facts.entry.len());
    }
}

/// Step 10.6 (TINV-31): an `&mut S` pointee gets the entry fact now that the gate is on
/// (the mint assumes at the same root); with the gate overridden off it gets none. A
/// `Box<S>` parameter never gets one (no `Box<S>` root in v1).
#[test]
fn a_mut_ref_gets_the_entry_fact_only_with_the_gate_and_a_boxed_parameter_never() {
    assert!(TINV_MUT_ENTRY_FACTS, "step 10.6: `&mut` entry facts are on");
    let f = one_param("mutr", Ty::Ref { mutable: true, inner: Box::new(s_ty()) });
    assert_eq!(param_roots(&f, "c::S"), vec![deref(1)], "the mint DOES assume here");
    assert_eq!(entry_roots(&f, "c::S"), vec![deref(1)]);
    let set = use_set(&[&f.def_path]);
    let facts = tinv_use_facts_with(&f, &set).expect("the `&mut` entry fact");
    assert_eq!(facts.entry, mint_instances(&f, &set, &deref(1)));
    {
        let _off = super::override_mut_entry_facts(false);
        assert!(entry_roots(&f, "c::S").is_empty());
        assert_eq!(tinv_use_facts_with(&f, &set), None);
    }

    let boxed = Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "alloc::boxed::Box<c::S>".into(),
        fields: vec![("0".to_string(), s_ty())].into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    };
    let f = one_param("boxed", boxed);
    assert_eq!(tinv_use_facts_with(&f, &use_set(&[&f.def_path])), None);
}

#[test]
fn no_fact_outside_the_checked_bodies_under_a_request_or_with_a_tail_call() {
    let f = one_param("get", Ty::Ref { mutable: false, inner: Box::new(s_ty()) });
    // Control.
    assert!(tinv_use_facts_with(&f, &use_set(&[&f.def_path])).is_some());
    // The induction never walked this body.
    assert_eq!(tinv_use_facts_with(&f, &use_set(&["c::other"])), None);
    // Nothing published.
    let empty = TinvUseSet::from_outcome(&TinvOutcome::<()>::default(), |_| true).expect("empty");
    assert_eq!(tinv_use_facts_with(&f, &empty), None);
    // A TINV row request for this body is active: the mint's own walk assumes nothing here.
    {
        let _g = enter_tinv_rows(Rc::new(TinvRowRequest::new(
            f.def_path.clone(),
            Vec::new(),
            Vec::new(),
        )));
        assert_eq!(tinv_use_facts_with(&f, &use_set(&[&f.def_path])), None);
    }
    // ...but a request for ANOTHER body does not stop it.
    {
        let _g = enter_tinv_rows(Rc::new(TinvRowRequest::new(
            "c::other".into(),
            Vec::new(),
            Vec::new(),
        )));
        assert!(tinv_use_facts_with(&f, &use_set(&[&f.def_path])).is_some());
    }
    // A tail call (D5).
    let mut tail = f.clone();
    tail.body.blocks[0].terminator = Terminator::TailCall {
        func: "c::g".into(),
        args: Vec::new(),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
    };
    assert_eq!(tinv_use_facts_with(&tail, &use_set(&[&tail.def_path])), None);
}

#[test]
fn the_context_read_fails_closed_and_sees_an_installed_set() {
    let f = one_param("get", Ty::Ref { mutable: false, inner: Box::new(s_ty()) });
    assert!(tinv_use_facts(&f).is_none(), "no context, no facts");
    {
        let _g = crate::enter_test_callee_summaries(crate::CalleeSummaryContext::default());
        assert!(tinv_use_facts(&f).is_none(), "a context without a use set");
    }
    let set = Arc::new(use_set(&[&f.def_path]));
    let context =
        crate::CalleeSummaryContext::default().with_type_invariants(Some(Arc::clone(&set)));
    assert!(!context.is_empty(), "a use set is a crate-derived fact");
    let _g = crate::enter_test_callee_summaries(context);
    // Installed, but no recording scope for this body: no fact (step 10.3).
    assert!(tinv_use_facts(&f).is_none(), "no recording scope, no facts");
    let (facts, record) =
        crate::type_invariant::with_tinv_assumed_rows_scope(&f, || tinv_use_facts(&f));
    assert_eq!(facts, tinv_use_facts_with(&f, &set));
    assert!(facts.is_some());
    assert!(record.rows.is_empty(), "reading the facts records nothing");
    assert!(record.use_set.as_ref().is_some_and(|s| Arc::ptr_eq(s, &set)), "the set is named");
    assert!(!record.conflicting_sets);
    // A scope for ANOTHER body admits nothing for this one.
    let other = one_param("other", Ty::Ref { mutable: false, inner: Box::new(s_ty()) });
    let (facts, _) =
        crate::type_invariant::with_tinv_assumed_rows_scope(&other, || tinv_use_facts(&f));
    assert!(facts.is_none(), "a scope for another body admitted facts");
}

/// `fn m(self: &mut S) { self.k = 0; g(&mut *self); self.k = 1 }` with `g` the inventory
/// callee `id`: bb0 writes and calls, bb1 is the call's single-predecessor target.
fn after_call(id: Option<CalleeIdentity>) -> VerifiableFunction {
    let k = Place { local: 1, projections: vec![Projection::Deref, Projection::Field(1)] };
    let assign = |place: Place, rvalue: Rvalue| Statement::Assign {
        place,
        rvalue,
        span: SourceSpan::default(),
    };
    let konst = |v: u128| Operand::Constant(trust_types::ConstValue::Uint(v, 64));
    func(
        "m",
        vec![
            (Ty::Unit, None),
            (Ty::Ref { mutable: true, inner: Box::new(s_ty()) }, Some("self")),
            (Ty::Ref { mutable: true, inner: Box::new(s_ty()) }, None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(k.clone(), Rvalue::Use(konst(0))),
                    assign(Place::local(2), Rvalue::Ref { mutable: true, place: deref(1) }),
                ],
                Terminator::Call {
                    func: "c::g".into(),
                    args: vec![Operand::Move(Place::local(2))],
                    dest: Place::local(3),
                    target: Some(BlockId(1)),
                    span: SourceSpan::default(),
                    atomic: None,
                    is_foreign: false,
                    is_unsafe_sig: false,
                    unwind: UnwindEdge::Continue,
                    callee_identity: id,
                    callee_key: None,
                },
            ),
            blk(1, vec![assign(k, Rvalue::Use(konst(1)))], ret()),
        ],
    )
}

#[test]
fn an_inventory_call_gives_sealed_post_call_facts_with_the_tag_intact() {
    let f = after_call(Some(INV));
    let set = use_set(&[&f.def_path]);
    // Step 10.6 turned the `&mut` entry channel on; this test pins the POST-CALL channel
    // alone, so it is overridden off here (the entry channel has its own tests).
    let _off = super::override_mut_entry_facts(false);
    let facts = tinv_use_facts_with(&f, &set).expect("post-call facts");
    assert!(facts.entry.is_empty(), "no `&mut` entry fact (overridden off)");
    assert_eq!(facts.post_calls.len(), 1);
    let (target, at) = &facts.post_calls[0];
    assert_eq!(*target, BlockId(1));
    assert_eq!(at, &mint_instances(&f, &set, &deref(1)));

    let sv = super::super::stmt_versions_for(&f);
    // At bb1[0], before the write: both facts are kept, sealed at `(bb1, 0)`, tags intact.
    let sealed = facts.post_call_facts_at(&f, &sv, BlockId(1), 0);
    assert_eq!(sealed.len(), 2, "{sealed:?}");
    for ((tag, fact), (want_tag, _)) in sealed.iter().zip(at) {
        assert_eq!(tag, want_tag);
        assert_eq!(fact.sealed_point(), Some((BlockId(1), 0)));
        let Formula::And(parts) = fact.formula() else { panic!("{fact:?}") };
        assert_eq!(parts[0], Formula::Var(tag.clone(), Sort::Bool), "the tag is unchanged");
    }
    // At bb0 (the call's own block, not dominated by its target): nothing.
    assert!(facts.post_call_facts_at(&f, &sv, BlockId(0), 0).is_empty());
    // After `self.k = 1` in bb1 the sealed facts still name the POST-CALL version of `k`
    // (sealed names carry their token, so the row's rename leaves them alone), while the
    // row itself reads the post-write version: the fact cannot bind the new value.
    let after = facts.post_call_facts_at(&f, &sv, BlockId(1), 1);
    assert_eq!(
        after.iter().map(|(t, f)| (t, f.formula())).collect::<Vec<_>>(),
        sealed.iter().map(|(t, f)| (t, f.formula())).collect::<Vec<_>>()
    );
    let k_at = |point: usize| {
        crate::generate::version_rename_at(
            &Formula::Var("self*.1".into(), Sort::Int),
            &sv,
            &f,
            BlockId(1),
            point,
        )
    };
    let mentions = |f: &Formula, needle: &Formula| {
        let mut hit = false;
        f.visit(&mut |n| hit |= n == needle);
        hit
    };
    assert!(mentions(sealed[0].1.formula(), &k_at(0)), "{:?} {:?}", sealed[0].1, k_at(0));
    assert_ne!(k_at(0), k_at(1), "the write re-versions `k`");
    assert!(!after.iter().any(|(_, f)| mentions(f.formula(), &k_at(1))), "{after:?}");

    // Outside the inventory, or with no identity: no post-call point at all.
    let set = use_set(&["c::m"]);
    let other = CalleeIdentity { def_index: 8, ..INV };
    assert_eq!(tinv_use_facts_with(&after_call(Some(other)), &set), None);
    assert_eq!(tinv_use_facts_with(&after_call(None), &set), None);
}
