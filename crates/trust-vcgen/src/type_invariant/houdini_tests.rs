//! TINV step 7.6: the Houdini fixpoint and mint loop, on hand-built bodies.
//!
//! Rows come from the real walk (`type_invariant_check_vcs`); the oracle is the
//! in-process ay router, optionally overridden by a script, and `certify` is scripted, so
//! these tests pin the loop itself. `certify_tests.rs` runs the same loop with
//! the real `trust_certify::certify_vc` (step 7.7).

use std::cell::Cell;
use std::collections::BTreeSet;

use trust_types::{
    AggregateKind, AssertMessage, BasicBlock, BinOp, BlockId, CalleeIdentity, ConstValue, Formula,
    LocalDecl, Operand, Place, Projection, Rvalue, SourceSpan, Statement, Terminator, Ty,
    TypeInvariantPoint, TypeInvariantSite, UnwindEdge, VcKind, VerifiableBody, VerifiableFunction,
    VerificationCondition, VerificationResult,
};

use super::*;
use crate::type_invariant::unwind::NoExactModels;
use crate::type_invariant::{CandidateConjunct, FieldTerm, TinvType, field_var};

// ---------------------------------------------------------------------------------------
// Bodies: `c::P { i: u64, n: u64, k: u64 }`
// ---------------------------------------------------------------------------------------

fn u64_ty() -> Ty {
    Ty::Int { width: 64, signed: false }
}

fn p_fields() -> Vec<(String, Ty)> {
    ["i", "n", "k"].into_iter().map(|n| (n.to_string(), u64_ty())).collect()
}

fn p_ty() -> Ty {
    Ty::Adt {
        adt_kind: Some(trust_types::AdtKind::Struct),
        layout: None,
        variants: Vec::new().into(),
        name: "c::P".into(),
        fields: p_fields().into(),
        disc_index_safe: false,
        faithful_enum_repr: None,
        enum_layout: None,
        arbitrary_precision: None,
        validity_wrapper: None,
    }
}

fn v(i: usize) -> Box<Formula> {
    Box::new(field_var(FieldTerm::Value(i)))
}

/// c0: `i <= n`.
fn c0() -> CandidateConjunct {
    CandidateConjunct { id: 0, formula: Formula::Le(v(0), v(1)) }
}

/// c1: `k <= n`.
fn c1() -> CandidateConjunct {
    CandidateConjunct { id: 1, formula: Formula::Le(v(2), v(1)) }
}

/// c2: `n < i`, inconsistent with c0.
fn c2() -> CandidateConjunct {
    CandidateConjunct { id: 2, formula: Formula::Lt(v(1), v(0)) }
}

/// c3: `i <= len(i)`: `i` is an integer, so the generator has no Len term for it.
fn c3() -> CandidateConjunct {
    CandidateConjunct { id: 3, formula: Formula::Le(v(0), Box::new(field_var(FieldTerm::Len(0)))) }
}

fn p(conjuncts: Vec<CandidateConjunct>) -> TinvType {
    TinvType { def_path: "c::P".into(), fields: p_fields(), conjuncts }
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

fn assign(place: Place, rvalue: Rvalue) -> Statement {
    Statement::Assign { place, rvalue, span: SourceSpan::default() }
}

fn konst(v: i128) -> Operand {
    Operand::Constant(ConstValue::Uint(v as u128, 64))
}

/// `(*_l).f`.
fn self_field(l: usize, f: usize) -> Place {
    Place { local: l, projections: vec![Projection::Deref, Projection::Field(f)] }
}

fn field(l: usize, f: usize) -> Place {
    Place { local: l, projections: vec![Projection::Field(f)] }
}

fn mut_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: true, inner: Box::new(t) }
}

fn shared_ref(t: Ty) -> Ty {
    Ty::Ref { mutable: false, inner: Box::new(t) }
}

/// `fn copy_of(p: &P) -> P { P { i: p.i, n: p.n, k: p.k } }`: the E point, situated by
/// the entry assumption on `*p`.
fn copy_of() -> VerifiableFunction {
    func(
        "copy_of",
        vec![(p_ty(), None), (shared_ref(p_ty()), Some("p"))],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "c::P".into(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    (0..3).map(|f| Operand::Copy(self_field(1, f))).collect(),
                ),
            )],
            Terminator::Return,
        )],
    )
}

/// `fn bump(&mut self) { if self.i < self.n { self.i += 1 } }` (`guarded`, the
/// tail-duplicated Return) or `fn bump_unguarded(&mut self) { self.i += 1 }`.
fn bump(guarded: bool) -> VerifiableFunction {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(p_ty()), Some("self")),
        (u64_ty(), None),
        (u64_ty(), None),
        (Ty::Bool, None),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    let add = blk(
        1,
        vec![assign(
            Place::local(5),
            Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(self_field(1, 0)), konst(1)),
        )],
        Terminator::Assert {
            cond: Operand::Move(field(5, 1)),
            expected: false,
            msg: AssertMessage::Overflow(BinOp::Add),
            target: BlockId(2),
            span: SourceSpan::default(),
            unwind: UnwindEdge::Continue,
        },
    );
    let write = blk(2, vec![assign(self_field(1, 0), Rvalue::Use(Operand::Move(field(5, 0))))], {
        if guarded { Terminator::Return } else { Terminator::Goto(BlockId(3)) }
    });
    let ret = blk(3, vec![], Terminator::Return);
    let entry = if guarded {
        blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 0)))),
                assign(Place::local(3), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
                assign(
                    Place::local(4),
                    Rvalue::BinaryOp(
                        BinOp::Lt,
                        Operand::Move(Place::local(2)),
                        Operand::Move(Place::local(3)),
                    ),
                ),
            ],
            Terminator::SwitchInt {
                discr: Operand::Move(Place::local(4)),
                targets: vec![(0, BlockId(3))],
                otherwise: BlockId(1),
                exhaustive_enum_unreachable: false,
                span: SourceSpan::default(),
            },
        )
    } else {
        blk(0, vec![], Terminator::Goto(BlockId(1)))
    };
    let name = if guarded { "bump" } else { "bump_unguarded" };
    func(name, locals, 1, vec![entry, add, write, ret])
}

/// `fn set_k(&mut self) { self.k = self.i }`: preserves `k <= n` only given `i <= n`.
fn set_k() -> VerifiableFunction {
    func(
        "set_k",
        vec![(Ty::Unit, None), (mut_ref(p_ty()), Some("self")), (u64_ty(), None)],
        1,
        vec![blk(
            0,
            vec![
                assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 0)))),
                assign(self_field(1, 2), Rvalue::Use(Operand::Move(Place::local(2)))),
            ],
            Terminator::Return,
        )],
    )
}

/// `fn twice(&mut self) { self.k = 0; g(&mut *self); self.k = 0; }`, `g` named by `id`.
/// The call havocs `*self`: the Return is provable only from `g`'s post-call fact, which
/// exists only when `g`'s body is in the run.
fn twice(id: CalleeIdentity) -> VerifiableFunction {
    func(
        "twice",
        vec![
            (Ty::Unit, None),
            (mut_ref(p_ty()), Some("self")),
            (mut_ref(p_ty()), None),
            (Ty::Unit, None),
        ],
        1,
        vec![
            blk(
                0,
                vec![
                    assign(self_field(1, 2), Rvalue::Use(konst(0))),
                    assign(
                        Place::local(2),
                        Rvalue::Ref {
                            mutable: true,
                            place: Place { local: 1, projections: vec![Projection::Deref] },
                        },
                    ),
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
                    callee_identity: Some(id),
                    callee_key: None,
                },
            ),
            blk(1, vec![assign(self_field(1, 2), Rvalue::Use(konst(0)))], Terminator::Return),
        ],
    )
}

fn ident(def_index: u32) -> CalleeIdentity {
    CalleeIdentity { stable_crate_id: 1, def_index, substs_digest: [0, 0] }
}

/// The bodies of a run, each with a distinct identity (its position + 100).
fn run_bodies(funcs: &[VerifiableFunction]) -> Vec<TinvBody<'_>> {
    funcs
        .iter()
        .enumerate()
        .map(|(i, f)| TinvBody { identity: Some(ident(100 + i as u32)), func: f, facts: None })
        .collect()
}

// ---------------------------------------------------------------------------------------
// Oracles and certifiers
// ---------------------------------------------------------------------------------------

/// The in-process ay router, on a thread with room for generation-sized formulas.
fn ay_solve(vc: &VerificationCondition) -> VerificationResult {
    let vc = VerificationCondition {
        kind: VcKind::Assertion { message: "tinv houdini oracle".into() },
        function: "tinv".into(),
        location: SourceSpan::default(),
        formula: vc.formula.clone(),
        contract_metadata: None,
        obligation: None,
    };
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let router = crate::test_router::deterministic_test_router();
            router.verify_all(std::slice::from_ref(&vc)).into_iter().next().expect("one verdict").1
        })
        .expect("spawn solver thread")
        .join()
        .expect("solver thread must not panic")
}

fn verdict(r: &VerificationResult) -> Option<bool> {
    match r {
        VerificationResult::Proved { .. } => Some(true),
        VerificationResult::Failed { .. } => Some(false),
        _ => None,
    }
}

/// ay's verdict on `vc`.
fn ay(vc: &VerificationCondition) -> Option<bool> {
    verdict(&ay_solve(vc))
}

/// The counterexample model of a refuted result, restricted to the values a
/// [`TinvModel`] carries (an `Int` or a `Bool`); any other binding is left out, so a
/// probe reading it is not confirmed.
fn model_of(r: &VerificationResult) -> Option<TinvModel> {
    let VerificationResult::Failed { counterexample: Some(cex), .. } = r else { return None };
    Some(
        cex.assignments
            .iter()
            .filter_map(|(name, v)| {
                let v = match v {
                    trust_types::CounterexampleValue::Int(i) => TinvModelValue::Int(*i),
                    trust_types::CounterexampleValue::Bool(b) => TinvModelValue::Bool(*b),
                    _ => return None,
                };
                Some((name.clone(), v))
            })
            .collect(),
    )
}

/// ay's model of `vc`'s violation formula, if it refutes it with one.
fn ay_model(vc: &VerificationCondition) -> Option<TinvModel> {
    model_of(&ay_solve(vc))
}

/// The in-process ay router as the oracle: verdicts and models both from ay.
struct Ay;

impl TinvOracle for Ay {
    fn proves(&self, vc: &VerificationCondition) -> Option<bool> {
        ay(vc)
    }
    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel> {
        ay_model(vc)
    }
}

/// An oracle from a closure. Probes are told apart by carrying no record. A probe's
/// MODEL comes from the script too: when the closure answers `Some(false)`
/// ("satisfiable") for a probe, the model is ay's, so a scripted SAT claim keeps a row
/// only if a real model exists and the ground evaluator confirms it.
struct Script<F: Fn(&VerificationCondition) -> Option<bool>>(F);

impl<F: Fn(&VerificationCondition) -> Option<bool>> TinvOracle for Script<F> {
    fn proves(&self, vc: &VerificationCondition) -> Option<bool> {
        (self.0)(vc)
    }
    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel> {
        if (self.0)(vc) == Some(false) { ay_model(vc) } else { None }
    }
}

/// An oracle that must never be asked.
struct Never;

impl TinvOracle for Never {
    fn proves(&self, vc: &VerificationCondition) -> Option<bool> {
        panic!("the oracle must not be asked: {:?}", vc.kind)
    }
    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel> {
        panic!("the oracle must not be asked for a model: {:?}", vc.kind)
    }
}

fn is_probe(vc: &VerificationCondition) -> bool {
    vc.obligation.is_none()
}

/// A certifier that numbers the rows it certifies, in call order.
fn numbering() -> (Cell<u32>, impl Fn(&Cell<u32>, &VerificationCondition) -> Option<u32>) {
    (Cell::new(0), |n: &Cell<u32>, _vc: &VerificationCondition| {
        n.set(n.get() + 1);
        Some(n.get())
    })
}

const BUDGET: TinvBudget = TinvBudget { steps_per_walk: u64::MAX, total_walks: 1_000 };

fn run(
    types: &[TinvType],
    bodies: &[TinvBody<'_>],
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<u32>,
    budget: TinvBudget,
) -> TinvOutcome<u32> {
    let out = houdini(types, bodies, &NoExactModels, &|_| true, oracle, certify, budget);
    check_publication(&out);
    out
}

fn run_ay(types: &[TinvType], bodies: &[TinvBody<'_>]) -> TinvOutcome<u32> {
    let (n, certify) = numbering();
    run(types, bodies, &Ay, &|vc| certify(&n, vc), BUDGET)
}

/// TINV-8(e) and the mint discipline, for every outcome a test produces: a certificate
/// publishes exactly the rows of its surviving conjuncts, each with evidence; no dropped
/// conjunct and no refused type has a row or a certificate.
fn check_publication(out: &TinvOutcome<u32>) {
    let dropped: BTreeSet<(String, u32)> =
        out.dropped.iter().map(|d| (d.ty.clone(), d.conjunct)).collect();
    for (ty, cert) in &out.certificates {
        assert_eq!(ty, cert.def_path());
        assert!(!out.refused.iter().any(|(r, _)| r == ty), "a refused type certified: {ty}");
        assert!(!cert.conjuncts().is_empty(), "a certificate with no conjunct: {ty}");
        let ids: BTreeSet<u32> = cert.conjuncts().iter().map(|c| c.id).collect();
        assert!(cert.conjuncts().windows(2).all(|w| w[0].id < w[1].id), "conjuncts sorted");
        for row in cert.rows() {
            assert_eq!(&row.key().ty, ty);
            assert!(ids.contains(&row.key().conjunct), "a row of a conjunct not certified");
            assert!(!dropped.contains(&(ty.clone(), row.key().conjunct)), "a dropped row");
            assert!(matches!(row.vc().kind, VcKind::TypeInvariant { .. }));
            assert_eq!(row.vc().type_invariant_situatedness_refusal(), None);
            assert!(*row.evidence() > 0);
        }
        for id in &ids {
            assert!(!dropped.contains(&(ty.clone(), *id)));
            assert!(
                cert.rows()
                    .iter()
                    .any(|r| r.key().conjunct == *id
                        && r.key().point == TypeInvariantPoint::Establish),
                "conjunct {id} of {ty} has no E row"
            );
        }
    }
}

fn dropped_ids(out: &TinvOutcome<u32>) -> Vec<(u32, DropCause, &str)> {
    out.dropped.iter().map(|d| (d.conjunct, d.cause, d.function.as_str())).collect()
}

fn cert_ids(out: &TinvOutcome<u32>, ty: &str) -> Vec<u32> {
    out.certificates[ty].conjuncts().iter().map(|c| c.id).collect()
}

/// The negated core of a row (its record body's last conjunct).
fn core_of(vc: &VerificationCondition) -> &Formula {
    match &vc.obligation.as_ref().expect("record").body {
        Formula::Not(c) => c,
        Formula::And(parts) => match parts.last() {
            Some(Formula::Not(c)) => c,
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    }
}

fn mentions(f: &Formula, needle: &str) -> bool {
    let mut hit = false;
    f.visit(&mut |n| {
        if let Formula::Var(name, _) = n
            && name.contains(needle)
        {
            hit = true;
        }
    });
    hit
}

// ---------------------------------------------------------------------------------------
// The fixpoint
// ---------------------------------------------------------------------------------------

#[test]
fn the_fixpoint_drops_a_conjunct_refuted_in_one_body_and_keeps_the_others() {
    let funcs = [copy_of(), bump(true), bump(false)];
    let out = run_ay(&[p(vec![c0(), c1()])], &run_bodies(&funcs));
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::Refuted, "c::bump_unguarded")]);
    assert_eq!(out.dropped[0].point, TypeInvariantPoint::Return);
    assert_eq!(out.dropped[0].round, 1);
    assert_eq!(cert_ids(&out, "c::P"), vec![1]);
    let cert = &out.certificates["c::P"];
    // c1's rows in all three bodies are published, and only c1's.
    let fns: BTreeSet<&str> = cert.rows().iter().map(|r| r.function()).collect();
    assert_eq!(fns, ["c::bump", "c::bump_unguarded", "c::copy_of"].into_iter().collect());
    assert!(cert.rows().iter().all(|r| r.key().conjunct == 1));
    // One oracle round, one more round after the drop, then the mint pass.
    assert_eq!(out.rounds, 3);
    assert!(out.notes.iter().any(|n| n.text.contains("conjunct #0 dropped (Refuted)")));
}

#[test]
fn dropping_one_conjunct_drops_a_conjunct_whose_preservation_assumed_it() {
    // Control: without the refuting body both survive, so c1's survival in `set_k`
    // rested on c0 at entry.
    let funcs = [copy_of(), set_k()];
    let out = run_ay(&[p(vec![c0(), c1()])], &run_bodies(&funcs));
    assert!(out.dropped.is_empty(), "{:?}", out.dropped);
    assert_eq!(cert_ids(&out, "c::P"), vec![0, 1]);

    let funcs = [copy_of(), set_k(), bump(false)];
    let out = run_ay(&[p(vec![c0(), c1()])], &run_bodies(&funcs));
    assert_eq!(
        dropped_ids(&out),
        vec![(0, DropCause::Refuted, "c::bump_unguarded"), (1, DropCause::Refuted, "c::set_k")]
    );
    assert_eq!(
        out.dropped.iter().map(|d| d.round).collect::<Vec<_>>(),
        vec![1, 2],
        "c1 is dropped only in the round after c0"
    );
    assert!(out.certificates.is_empty());
    assert!(out.refused.is_empty());
    assert!(out.notes.iter().any(|n| n.text.contains("no candidate conjunct survives")));
    // Termination: at most one round per conjunct plus the final one.
    assert!(out.rounds <= 3, "{}", out.rounds);
}

#[test]
fn an_unknown_answer_drops_the_conjunct() {
    let funcs = [copy_of(), bump(true)];
    let oracle = Script(|vc: &VerificationCondition| {
        let in_bump = matches!(&vc.kind, VcKind::TypeInvariant { point, .. }
            if *point == TypeInvariantPoint::Return);
        if !is_probe(vc) && in_bump && mentions(core_of(vc), ".0") { None } else { ay(vc) }
    });
    let (n, certify) = numbering();
    let out =
        run(&[p(vec![c0(), c1()])], &run_bodies(&funcs), &oracle, &|vc| certify(&n, vc), BUDGET);
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::Unknown, "c::bump")]);
    assert_eq!(cert_ids(&out, "c::P"), vec![1]);
}

// ---------------------------------------------------------------------------------------
// The vacuity probe
// ---------------------------------------------------------------------------------------

#[test]
fn the_vacuity_probe_drops_an_inconsistent_conjunct_set() {
    // `i <= n` and `n < i` together: every row's entry hypotheses are UNSAT, so every row
    // "holds" and the structural gate passes them all. The probe catches it.
    let funcs = [copy_of(), bump(true)];
    let out = run_ay(&[p(vec![c0(), c2()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(
        dropped_ids(&out),
        vec![(0, DropCause::Vacuous, "c::bump"), (2, DropCause::Vacuous, "c::bump")]
    );
}

/// A probe answered "unsat" or "unknown" yields no model and drops; a "sat" answer keeps
/// the row only through ay's real model, which the ground evaluator confirms.
#[test]
fn a_probe_that_is_proved_or_unknown_drops_and_only_a_sat_probe_keeps() {
    let funcs = [copy_of(), bump(true)];
    for (probe, keeps) in [(Some(true), false), (None, false), (Some(false), true)] {
        let oracle =
            Script(move |vc: &VerificationCondition| if is_probe(vc) { probe } else { Some(true) });
        let (n, certify) = numbering();
        let out =
            run(&[p(vec![c0()])], &run_bodies(&funcs), &oracle, &|vc| certify(&n, vc), BUDGET);
        assert_eq!(out.certificates.contains_key("c::P"), keeps, "{probe:?}");
        if !keeps {
            assert_eq!(dropped_ids(&out), vec![(0, DropCause::Vacuous, "c::bump")]);
        }
    }
}

/// TINV-21: a `Vacuous` verdict is deferred while the same round drops anything else. The
/// script refutes every row of `c1` (`k <= n`) and answers a vacuity probe "unsat" (no
/// model) exactly while `c1`'s instances are among its hypotheses (a name of field 2). So
/// `c0`'s probes are vacuous in round 1 only BECAUSE of the false `c1`: `c0` must survive
/// to round 2 and certify, and only `c1` drops. Before the deferral both dropped in round 1.
#[test]
fn a_vacuous_row_is_rejudged_after_the_rounds_other_drops() {
    let funcs = [copy_of(), bump(true)];
    let oracle = Script(|vc: &VerificationCondition| {
        if is_probe(vc) {
            return if mentions(&vc.formula, ".2") { Some(true) } else { Some(false) };
        }
        match vc.kind {
            VcKind::TypeInvariant { conjunct: 1, .. } => Some(false),
            _ => Some(true),
        }
    });
    let (n, certify) = numbering();
    let out =
        run(&[p(vec![c0(), c1()])], &run_bodies(&funcs), &oracle, &|vc| certify(&n, vc), BUDGET);
    assert_eq!(cert_ids(&out, "c::P"), vec![0], "{:?}", out.dropped);
    assert_eq!(out.dropped.len(), 1, "{:?}", out.dropped);
    assert_eq!((out.dropped[0].conjunct, out.dropped[0].cause), (1, DropCause::Refuted));

    // A round whose ONLY drops are vacuous applies them (the loop still ends).
    let all_vacuous =
        Script(|vc: &VerificationCondition| if is_probe(vc) { Some(true) } else { Some(true) });
    let (n, certify) = numbering();
    let out = run(
        &[p(vec![c0(), c1()])],
        &run_bodies(&funcs),
        &all_vacuous,
        &|vc| certify(&n, vc),
        BUDGET,
    );
    assert!(out.certificates.is_empty());
    assert!(
        out.dropped.iter().all(|d| d.cause == DropCause::Vacuous && d.round == 1),
        "{:?}",
        out.dropped
    );
}

/// An oracle that proves every row and answers every probe with the model `lie` makes
/// from ay's real one. Records each probe with the model it returned.
struct Lying<L: Fn(TinvModel) -> TinvModel> {
    lie: L,
    seen: std::cell::RefCell<Vec<(VerificationCondition, TinvModel)>>,
}

impl<L: Fn(TinvModel) -> TinvModel> TinvOracle for Lying<L> {
    fn proves(&self, vc: &VerificationCondition) -> Option<bool> {
        assert!(!is_probe(vc), "a probe is asked for a model, never a verdict");
        Some(true)
    }
    fn model(&self, vc: &VerificationCondition) -> Option<TinvModel> {
        let real = ay_model(vc).expect("the honest probe of c0 in bump is satisfiable");
        let lie = (self.lie)(real);
        self.seen.borrow_mut().push((vc.clone(), lie.clone()));
        Some(lie)
    }
}

/// 2026-10-05 (review of step 7.7): the oracle CLAIMS the probe is satisfiable and hands
/// back a model, but the model does not satisfy the hypotheses. The conjunct drops as
/// Vacuous: a bare SAT answer never keeps a row. Three lies: every integer set to -1 (the
/// ground evaluator evaluates the probe to `false`, asserted), an empty model (a missing
/// variable), and every integer re-sorted to a bool (an ill-sorted binding).
#[test]
fn a_sat_claim_whose_model_fails_the_ground_check_drops_the_conjunct() {
    let funcs = [copy_of(), bump(true)];
    let negative = |m: TinvModel| {
        m.into_iter()
            .map(|(k, v)| match v {
                TinvModelValue::Int(_) => (k, TinvModelValue::Int(-1)),
                b => (k, b),
            })
            .collect()
    };
    let empty = |_: TinvModel| TinvModel::new();
    let resorted = |m: TinvModel| {
        m.into_iter()
            .map(|(k, v)| match v {
                TinvModelValue::Int(_) => (k, TinvModelValue::Bool(true)),
                b => (k, b),
            })
            .collect()
    };
    type Lie<'a> = &'a dyn Fn(TinvModel) -> TinvModel;
    let lies: [(&str, Lie<'_>, Option<bool>); 3] = [
        ("negative", &negative, Some(false)),
        ("empty", &empty, None),
        ("resorted", &resorted, None),
    ];
    for (what, lie, evaluates) in lies {
        let oracle = Lying { lie, seen: Default::default() };
        let (n, certify) = numbering();
        let out =
            run(&[p(vec![c0()])], &run_bodies(&funcs), &oracle, &|vc| certify(&n, vc), BUDGET);
        assert!(out.certificates.is_empty(), "{what}");
        assert_eq!(dropped_ids(&out).len(), 1, "{what}: {:?}", out.dropped);
        assert_eq!(out.dropped[0].cause, DropCause::Vacuous, "{what}");
        assert_eq!(n.get(), 0, "{what}: nothing reached the mint");
        let seen = oracle.seen.into_inner();
        assert_eq!(seen.len(), 1, "{what}: the first probe drops the conjunct");
        let (probe, model) = &seen[0];
        assert_eq!(ground_eval(&probe.formula, model), evaluates, "{what}: {model:?}");
    }

    // Control: the same oracle telling the truth (ay's model unchanged) keeps the
    // conjunct, so the drops above are the ground check and not the oracle's shape.
    let honest = Lying { lie: |m: TinvModel| m, seen: Default::default() };
    let (n, certify) = numbering();
    let out = run(&[p(vec![c0()])], &run_bodies(&funcs), &honest, &|vc| certify(&n, vc), BUDGET);
    assert_eq!(cert_ids(&out, "c::P"), vec![0], "{:?}", out.dropped);
    for (probe, model) in honest.seen.into_inner() {
        assert_eq!(ground_eval(&probe.formula, &model), Some(true));
    }
}

/// The ground evaluator is total over its fragment and `None` everywhere else.
#[test]
fn ground_eval_is_total_on_its_fragment_and_none_outside_it() {
    use trust_types::Sort;
    let int = |n: &str| Formula::Var(n.into(), Sort::Int);
    let b = |n: &str| Formula::Var(n.into(), Sort::Bool);
    let bx = Box::new;
    let m: TinvModel = [
        ("x".to_string(), TinvModelValue::Int(3)),
        ("y".to_string(), TinvModelValue::Int(-4)),
        ("p".to_string(), TinvModelValue::Bool(true)),
    ]
    .into_iter()
    .collect();
    // x + y * 2 - (-x) == -2 ∧ (p → x < 4) ∧ ite(p, x, y) >= 3 ∧ ¬(y > 0 ∨ ¬p)
    let f = Formula::And(vec![
        Formula::Eq(
            bx(Formula::Sub(
                bx(Formula::Add(bx(int("x")), bx(Formula::Mul(bx(int("y")), bx(Formula::Int(2)))))),
                bx(Formula::Neg(bx(int("x")))),
            )),
            bx(Formula::Int(-2)),
        ),
        Formula::Implies(bx(b("p")), bx(Formula::Lt(bx(int("x")), bx(Formula::Int(4))))),
        Formula::Ge(bx(Formula::Ite(bx(b("p")), bx(int("x")), bx(int("y")))), bx(Formula::Int(3))),
        Formula::Not(bx(Formula::Or(vec![
            Formula::Gt(bx(int("y")), bx(Formula::Int(0))),
            Formula::Not(bx(b("p"))),
        ]))),
        Formula::Le(bx(int("y")), bx(int("x"))),
        Formula::Eq(bx(b("p")), bx(Formula::Bool(true))),
    ]);
    assert_eq!(ground_eval(&f, &m), Some(true));
    assert_eq!(ground_eval(&Formula::Lt(bx(int("x")), bx(int("y"))), &m), Some(false));
    // A missing variable, even under a `false` conjunct (no short circuit).
    let missing = Formula::And(vec![Formula::Bool(false), Formula::Gt(bx(int("z")), bx(int("x")))]);
    assert_eq!(ground_eval(&missing, &m), None);
    let missing = Formula::Or(vec![Formula::Bool(true), b("q")]);
    assert_eq!(ground_eval(&missing, &m), None);
    // Ill-sorted: an Int var bound to a Bool, a Bool var read as an Int, a mixed Eq.
    assert_eq!(ground_eval(&Formula::Eq(bx(b("x")), bx(Formula::Bool(true))), &m), None);
    assert_eq!(ground_eval(&Formula::Lt(bx(int("p")), bx(Formula::Int(1))), &m), None);
    assert_eq!(ground_eval(&Formula::Eq(bx(int("x")), bx(b("p"))), &m), None);
    // A bare integer is not a truth value.
    assert_eq!(ground_eval(&int("x"), &m), None);
    // i128 overflow.
    let big =
        Formula::Gt(bx(Formula::Add(bx(Formula::Int(i128::MAX)), bx(int("x")))), bx(int("x")));
    assert_eq!(ground_eval(&big, &m), None);
    // Outside the fragment: Div, Rem, a bit-vector variable.
    let div = Formula::Eq(bx(Formula::Div(bx(int("x")), bx(Formula::Int(1)))), bx(int("x")));
    assert_eq!(ground_eval(&div, &m), None);
    let rem = Formula::Eq(bx(Formula::Rem(bx(int("x")), bx(Formula::Int(2)))), bx(Formula::Int(1)));
    assert_eq!(ground_eval(&rem, &m), None);
    let bv = Formula::Eq(bx(Formula::Var("x".into(), Sort::BitVec(64))), bx(int("x")));
    assert_eq!(ground_eval(&bv, &m), None);
    // Past the depth bound.
    let mut deep = Formula::Bool(true);
    for _ in 0..600 {
        deep = Formula::Not(bx(Formula::Not(bx(deep))));
    }
    assert_eq!(ground_eval(&deep, &m), None);
}

#[test]
fn the_probe_is_the_row_with_its_core_replaced_by_true_and_no_record() {
    let funcs = [copy_of(), bump(true)];
    let seen: std::cell::RefCell<Vec<(VerificationCondition, bool)>> = Default::default();
    let oracle = Script(|vc: &VerificationCondition| {
        seen.borrow_mut().push((vc.clone(), is_probe(vc)));
        ay(vc)
    });
    let (n, certify) = numbering();
    let _ = run(&[p(vec![c0()])], &run_bodies(&funcs), &oracle, &|vc| certify(&n, vc), BUDGET);
    let seen = seen.into_inner();
    let rows: Vec<_> = seen.iter().filter(|(_, p)| !p).map(|(vc, _)| vc).collect();
    let probes: Vec<_> = seen.iter().filter(|(_, p)| *p).map(|(vc, _)| vc).collect();
    assert!(!rows.is_empty());
    assert_eq!(rows.len(), probes.len(), "every proved row is probed once");
    for (row, probe) in rows.iter().zip(&probes) {
        let expected = hypotheses_only(row).expect("probe");
        assert_eq!(probe.formula, expected.formula);
        assert_eq!(probe.kind, row.kind);
        assert!(probe.obligation.is_none());
        assert_ne!(probe.formula, row.formula);
        // The core is gone: the probe is the row's formula with `Not(core)` -> `true`.
        let core = core_of(row);
        let mut has_core = false;
        probe.formula.visit(&mut |f| {
            if let Formula::Not(c) = f
                && c.as_ref() == core
            {
                has_core = true;
            }
        });
        assert!(!has_core, "{:?}", probe.formula);
    }
    // A record-less row has no probe.
    let mut bare = rows[0].clone();
    bare.obligation = None;
    assert!(hypotheses_only(&bare).is_none());
}

#[test]
fn an_unsituated_row_drops_before_the_oracle_is_asked() {
    let vc = VerificationCondition {
        kind: VcKind::TypeInvariant {
            ty: "c::P".into(),
            point: TypeInvariantPoint::Return,
            site: TypeInvariantSite { block: 0, statement_index: 0 },
            conjunct: 0,
            ordinal: 0,
            edge: None,
        },
        function: "c::f".into(),
        location: SourceSpan::default(),
        formula: Formula::Not(Box::new(Formula::Bool(true))),
        contract_metadata: None,
        obligation: None,
    };
    assert_eq!(judge(&vc, &Never), Some(DropCause::Situatedness));
}

// ---------------------------------------------------------------------------------------
// The mint loop
// ---------------------------------------------------------------------------------------

#[test]
fn a_certify_failure_on_one_row_withholds_the_types_certificate() {
    let funcs = [copy_of(), bump(true)];
    let is_return = |vc: &VerificationCondition| matches!(&vc.kind, VcKind::TypeInvariant { point, .. } if *point == TypeInvariantPoint::Return);
    // One conjunct: its Return row in `bump` does not certify -> no certificate at all.
    let n = Cell::new(0);
    let certify = |vc: &VerificationCondition| {
        n.set(n.get() + 1);
        (!is_return(vc)).then_some(n.get())
    };
    let out = run(&[p(vec![c0()])], &run_bodies(&funcs), &Ay, &certify, BUDGET);
    assert!(out.certificates.is_empty());
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::NotCertified, "c::bump")]);
    assert_eq!(out.dropped[0].point, TypeInvariantPoint::Return);
    assert!(out.refused.is_empty());

    // Two conjuncts: only c0's rows fail to certify. c0 is dropped, the loop re-runs
    // (its rows assumed c0 at entry), and c1 is minted from the re-run's rows only.
    let n = Cell::new(0);
    let certify = |vc: &VerificationCondition| {
        n.set(n.get() + 1);
        (!(is_return(vc) && mentions(core_of(vc), ".0"))).then_some(n.get())
    };
    let out = run(&[p(vec![c0(), c1()])], &run_bodies(&funcs), &Ay, &certify, BUDGET);
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::NotCertified, "c::bump")]);
    assert_eq!(cert_ids(&out, "c::P"), vec![1]);
    // round 1 filter, round 2 mint (fails), round 3 filter, round 4 mint.
    assert_eq!(out.rounds, 4);
    // Every published row is a c1 row of the re-run.
    for row in out.certificates["c::P"].rows() {
        assert!(!mentions(core_of(row.vc()), ".0"));
    }
}

#[test]
fn a_type_with_no_establish_row_is_refused() {
    let funcs = [bump(true)];
    let out = run_ay(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(out.refused, vec![("c::P".to_string(), TinvObligationRefusal::NoEstablishPoint)]);
    assert!(out.notes.iter().any(|n| n.ty == "c::P" && n.text.contains("NoEstablishPoint")));
}

#[test]
fn an_uninstantiable_conjunct_is_dropped_and_the_others_kept() {
    let funcs = [copy_of(), bump(true)];
    let out = run_ay(&[p(vec![c0(), c3()])], &run_bodies(&funcs));
    assert_eq!(dropped_ids(&out), vec![(3, DropCause::Uninstantiable, "c::bump")]);
    assert_eq!(cert_ids(&out, "c::P"), vec![0]);
}

// ---------------------------------------------------------------------------------------
// The derived inventory
// ---------------------------------------------------------------------------------------

#[test]
fn the_inventory_is_derived_from_the_bodies() {
    // `twice` calls the body with identity 7. In the run, that call kills the window and
    // its post-call fact proves the Return; out of it, the call is foreign, owes U with
    // `*self` havocked, and the conjunct cannot survive.
    let g = ident(7);
    let callee = bump(true);
    let caller = twice(g);
    let ctor = copy_of();
    let with = [
        TinvBody { identity: Some(g), func: &callee, facts: None },
        TinvBody { identity: Some(ident(8)), func: &caller, facts: None },
        TinvBody { identity: Some(ident(9)), func: &ctor, facts: None },
    ];
    let out = run_ay(&[p(vec![c0()])], &with);
    assert!(out.dropped.is_empty(), "{:?}", out.dropped);
    assert_eq!(cert_ids(&out, "c::P"), vec![0]);
    assert!(
        !out.certificates["c::P"]
            .rows()
            .iter()
            .any(|r| r.function() == "c::twice" && r.key().point == TypeInvariantPoint::Unwind)
    );

    let without = [with[1], with[2]];
    let out = run_ay(&[p(vec![c0()])], &without);
    assert!(out.certificates.is_empty());
    assert_eq!(out.dropped.len(), 1);
    assert_eq!(out.dropped[0].function, "c::twice");
}

// ---------------------------------------------------------------------------------------
// Refusals
// ---------------------------------------------------------------------------------------

fn q() -> TinvType {
    TinvType { def_path: "c::Q".into(), fields: p_fields(), conjuncts: vec![c0()] }
}

/// `fn bad(p: &P) -> P { P { i: p.i, n: p.k, k: p.k } }`: an E point (situated by the
/// entry assumption on `*p`) that violates c0 and keeps c1.
fn bad_ctor() -> VerifiableFunction {
    func(
        "bad",
        vec![(p_ty(), None), (shared_ref(p_ty()), Some("p"))],
        1,
        vec![blk(
            0,
            vec![assign(
                Place::local(0),
                Rvalue::Aggregate(
                    AggregateKind::Adt {
                        name: "c::P".into(),
                        variant: 0,
                        active_field: None,
                        args: None,
                    },
                    [0, 2, 2].into_iter().map(|f| Operand::Copy(self_field(1, f))).collect(),
                ),
            )],
            Terminator::Return,
        )],
    )
}

#[test]
fn a_body_with_no_identity_is_checked() {
    // Increment A: a body no call can name (identity `None`) is still walked, and its
    // refuted E row drops the conjunct like any other body's.
    let funcs = [copy_of(), bad_ctor()];
    let mut bodies = run_bodies(&funcs);
    bodies[1].identity = None;
    let out = run_ay(&[p(vec![c0(), c1()])], &bodies);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::Refuted, "c::bad")]);
    assert_eq!(out.dropped[0].point, TypeInvariantPoint::Establish);
    assert_eq!(cert_ids(&out, "c::P"), vec![1]);
    // Its surviving rows are published with the others.
    assert!(out.certificates["c::P"].rows().iter().any(|r| r.function() == "c::bad"));
}

#[test]
fn a_call_to_a_body_with_no_identity_is_never_an_inventory_kill() {
    // The callee's body is in the run but has no identity, so the inventory is empty
    // of it: `twice`'s call (stamped with `g`, or with the identity the callee would
    // have had) is foreign, havocs `*self`, and the conjunct cannot survive, exactly as
    // when the callee is not in the run at all.
    let g = ident(7);
    let callee = bump(true);
    let caller = twice(g);
    let ctor = copy_of();
    let bodies = [
        TinvBody { identity: None, func: &callee, facts: None },
        TinvBody { identity: Some(ident(8)), func: &caller, facts: None },
        TinvBody { identity: Some(ident(9)), func: &ctor, facts: None },
    ];
    let out = run_ay(&[p(vec![c0()])], &bodies);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.certificates.is_empty(), "the post-call fact was assumed");
    assert_eq!(out.dropped.len(), 1, "{:?}", out.dropped);
    assert_eq!(out.dropped[0].function, "c::twice");
    // The callee's own rows were walked: with every identity `None` the outcome is the
    // same, and no identity is a duplicate.
    let none: Vec<TinvBody<'_>> =
        bodies.iter().map(|b| TinvBody { identity: None, ..*b }).collect();
    let again = run_ay(&[p(vec![c0()])], &none);
    assert!(again.refused.is_empty(), "{:?}", again.refused);
    assert_eq!(again.dropped.len(), 1, "{:?}", again.dropped);
    assert_eq!(again.dropped[0].function, "c::twice");
}

#[test]
fn duplicate_detection_ignores_bodies_with_no_identity() {
    let funcs = [copy_of(), bump(true), set_k()];
    let never = |_: &VerificationCondition| -> Option<u32> { panic!("nothing may certify") };

    // Two `None` bodies (and a third) are not a DuplicateIdentity: the run proceeds.
    let mut bodies = run_bodies(&funcs);
    bodies[0].identity = None;
    bodies[1].identity = None;
    let out = run_ay(&[p(vec![c0(), c1()])], &bodies);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    assert!(out.rounds > 0);
    assert_eq!(cert_ids(&out, "c::P"), vec![0, 1]);

    // A `None` beside two equal `Some` identities still refuses every type.
    let mut bodies = run_bodies(&funcs);
    bodies[0].identity = None;
    bodies[2].identity = bodies[1].identity;
    let out = run(&[p(vec![c0()]), q()], &bodies, &Never, &never, BUDGET);
    assert!(out.certificates.is_empty());
    assert_eq!(out.rounds, 0);
    let why = TinvObligationRefusal::DuplicateIdentity(ident(101));
    assert_eq!(out.refused, vec![("c::P".to_string(), why.clone()), ("c::Q".to_string(), why)]);
}

#[test]
fn a_duplicate_identity_or_def_path_refuses_every_type() {
    let funcs = [copy_of(), bump(true)];
    let never = |_: &VerificationCondition| -> Option<u32> { panic!("nothing may certify") };
    let refused_all = |out: &TinvOutcome<u32>, why: TinvObligationRefusal| {
        assert!(out.certificates.is_empty());
        assert_eq!(out.rounds, 0);
        assert_eq!(out.refused, vec![("c::P".to_string(), why.clone()), ("c::Q".to_string(), why)]);
    };
    let types = [p(vec![c0()]), q()];

    // Two bodies, one identity.
    let mut bodies = run_bodies(&funcs);
    bodies[1].identity = bodies[0].identity;
    let out = run(&types, &bodies, &Never, &never, BUDGET);
    refused_all(&out, TinvObligationRefusal::DuplicateIdentity(ident(100)));

    // Two bodies, one def_path.
    let twin = copy_of();
    let mut bodies = run_bodies(&funcs);
    bodies.push(TinvBody { identity: Some(ident(55)), func: &twin, facts: None });
    let out = run(&types, &bodies, &Never, &never, BUDGET);
    refused_all(&out, TinvObligationRefusal::DuplicateDefPath("c::copy_of".into()));

    // Two types, one def_path.
    let out = run(&[p(vec![c0()]), q(), q()], &run_bodies(&funcs), &Never, &never, BUDGET);
    refused_all(&out, TinvObligationRefusal::DuplicateDefPath("c::Q".into()));

    // Two conjuncts of one type, one id.
    let mut dup = p(vec![c0(), c1()]);
    dup.conjuncts[1].id = 0;
    let out = run(&[dup, q()], &run_bodies(&funcs), &Never, &never, BUDGET);
    refused_all(&out, TinvObligationRefusal::DuplicateDefPath("c::P#0".into()));
}

#[test]
fn a_type_refused_in_one_body_is_reported_and_never_certified() {
    let mut tail = bump(true);
    tail.name = "tail".into();
    tail.def_path = "c::tail".into();
    tail.body.blocks[3].terminator = Terminator::TailCall {
        func: "c::g".into(),
        args: Vec::new(),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        callee_identity: None,
        callee_key: None,
    };
    let funcs = [copy_of(), bump(true), tail];
    let out = run_ay(&[p(vec![c0(), c1()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(out.refused.len(), 1);
    assert_eq!(out.refused[0].0, "c::P");
    assert!(matches!(out.refused[0].1, TinvObligationRefusal::U(_)), "{:?}", out.refused);
    assert!(out.dropped.is_empty(), "a refusal is not a drop: {:?}", out.dropped);
}

#[test]
fn budget_exhaustion_refuses_and_certifies_nothing() {
    let funcs = [copy_of(), bump(true), bump(false)];
    let types = [p(vec![c0(), c1()])];
    let (n, certify) = numbering();
    // The run needs 3 walks per round over at least two rounds; give it 4.
    let out = run(
        &types,
        &run_bodies(&funcs),
        &Ay,
        &|vc| certify(&n, vc),
        TinvBudget { steps_per_walk: u64::MAX, total_walks: 4 },
    );
    assert!(out.certificates.is_empty());
    assert_eq!(out.refused, vec![("c::P".to_string(), TinvObligationRefusal::Budget)]);
    assert_eq!(n.get(), 0, "nothing was certified");

    // A per-walk step budget trip refuses the walk's types.
    let (n, certify) = numbering();
    let out = run(
        &types,
        &run_bodies(&funcs),
        &Ay,
        &|vc| certify(&n, vc),
        TinvBudget { steps_per_walk: 1, total_walks: 1_000 },
    );
    assert!(out.certificates.is_empty());
    assert_eq!(out.refused.len(), 1);
    assert!(
        matches!(
            out.refused[0].1,
            TinvObligationRefusal::Truncated | TinvObligationRefusal::Budget
        ),
        "{:?}",
        out.refused
    );
}

// ---------------------------------------------------------------------------------------
// Determinism
// ---------------------------------------------------------------------------------------

fn fingerprint(out: &TinvOutcome<u32>) -> String {
    let certs: Vec<_> = out
        .certificates
        .values()
        .map(|c| {
            let rows: Vec<_> = c
                .rows()
                .iter()
                .map(|r| {
                    format!(
                        "{:?} {} {:?} {:?}",
                        r.key(),
                        r.function(),
                        r.vc().formula,
                        r.evidence()
                    )
                })
                .collect();
            format!("{} {:?} {rows:?}", c.def_path(), c.conjuncts())
        })
        .collect();
    let mut inventory: Vec<String> = out.inventory.iter().map(|i| format!("{i:?}")).collect();
    inventory.sort();
    let fields: Vec<_> = out.certificates.values().map(|c| c.fields().to_vec()).collect();
    format!(
        "{certs:?} {:?} {:?} {:?} {} {inventory:?} {:?} {fields:?}",
        out.dropped, out.refused, out.notes, out.rounds, out.checked_bodies
    )
}

#[test]
fn the_outcome_is_deterministic_under_input_permutations() {
    let funcs = [copy_of(), bump(true), bump(false)];
    let bodies = run_bodies(&funcs);
    let reference_out = run_ay(&[p(vec![c0(), c1()])], &bodies);
    assert_eq!(cert_ids(&reference_out, "c::P"), vec![1]);
    let reference = fingerprint(&reference_out);
    let orders: [[usize; 3]; 5] = [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
    for (k, order) in orders.iter().enumerate() {
        let shuffled: Vec<TinvBody<'_>> = order.iter().map(|&i| bodies[i]).collect();
        // The conjuncts in reverse order as well, every other permutation.
        let conjuncts = if k % 2 == 0 { vec![c1(), c0()] } else { vec![c0(), c1()] };
        assert_eq!(fingerprint(&run_ay(&[p(conjuncts)], &shuffled)), reference, "{order:?}");
    }
    // Two types, in both orders.
    let a = fingerprint(&run_ay(&[p(vec![c0()]), q()], &bodies));
    let b = fingerprint(&run_ay(&[q(), p(vec![c0()])], &[bodies[2], bodies[0], bodies[1]]));
    assert_eq!(a, b);
}

// ---------------------------------------------------------------------------------------
// TINV-9(a): edge parts of an R point at a join
// ---------------------------------------------------------------------------------------

/// `bump(true)` in rustc's join lowering: the write block bb2 jumps to the shared Return
/// bb3, which the else edge of bb0 also reaches. `guarded: false` routes bb0 on a bool
/// parameter `c` unrelated to `i < n` (`fn bump_any(&mut self, c: bool)`).
fn bump_join(guarded: bool) -> VerifiableFunction {
    let mut f = bump(true);
    f.body.blocks[2].terminator = Terminator::Goto(BlockId(3));
    if guarded {
        f.name = "bump_join".into();
    } else {
        // `_2` becomes the parameter `c: bool`; bb0 routes on it directly.
        f.name = "bump_any".into();
        f.body.arg_count = 2;
        f.body.locals[2] = LocalDecl { index: 2, ty: Ty::Bool, name: Some("c".into()) };
        f.body.blocks[0].stmts.clear();
        f.body.blocks[0].terminator = Terminator::SwitchInt {
            discr: Operand::Copy(Place::local(2)),
            targets: vec![(0, BlockId(3))],
            otherwise: BlockId(1),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        };
    }
    f.def_path = format!("c::{}", f.name);
    f
}

#[test]
fn a_join_point_is_certified_only_with_every_edge_part() {
    let funcs = [copy_of(), bump_join(true)];
    let out = run_ay(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(
        out.refused.is_empty() && out.dropped.is_empty(),
        "{:?} {:?}",
        out.refused,
        out.dropped
    );
    assert_eq!(cert_ids(&out, "c::P"), vec![0]);
    let parts: Vec<Option<usize>> = out.certificates["c::P"]
        .rows()
        .iter()
        .filter(|r| r.function() == "c::bump_join" && r.key().point == TypeInvariantPoint::Return)
        .map(|r| r.key().edge)
        .collect();
    assert_eq!(parts, vec![Some(0), Some(2)], "both parts are published rows");
}

#[test]
fn one_failing_edge_part_drops_the_conjunct_though_the_other_part_holds() {
    let funcs = [copy_of(), bump_join(false)];
    let out = run_ay(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert_eq!(dropped_ids(&out), vec![(0, DropCause::Refuted, "c::bump_any")]);
    assert_eq!(out.dropped[0].point, TypeInvariantPoint::Return);
    assert_eq!(out.dropped[0].edge, Some(2), "the write edge's part refutes");
    assert!(out.notes.iter().any(|n| n.text.contains("via edge bb2")), "{:?}", out.notes);
}

#[test]
fn an_incomplete_or_mixed_part_set_refuses_the_type() {
    let f = bump_join(true);
    let key = |edge: Option<usize>| TinvRowKey {
        ty: "c::P".into(),
        conjunct: 0,
        point: TypeInvariantPoint::Return,
        site: TypeInvariantSite { block: 3, statement_index: 0 },
        ordinal: 0,
        edge,
    };
    assert_eq!(incomplete_join_parts(&f, &[key(Some(0)), key(Some(2))]), Vec::new());
    assert_eq!(incomplete_join_parts(&f, &[key(Some(2)), key(Some(0))]), Vec::new());
    assert_eq!(incomplete_join_parts(&f, &[key(None)]), Vec::new());
    for bad in [
        vec![key(Some(0))],
        vec![key(Some(0)), key(Some(1))],
        vec![key(Some(0)), key(Some(2)), key(Some(1))],
        vec![key(Some(0)), key(Some(0)), key(Some(2))],
        vec![key(None), key(Some(0)), key(Some(2))],
        vec![key(None), key(None)],
    ] {
        let got = incomplete_join_parts(&f, &bad);
        assert!(matches!(got.as_slice(), [(ty, _)] if ty == "c::P"), "{bad:?}: {got:?}");
    }
}

/// Every offending type is reported, not only the first point's: two types whose part
/// sets are both incomplete are BOTH refused, and a complete third type is not.
#[test]
fn every_type_with_an_incomplete_part_set_is_refused() {
    let f = bump_join(true);
    let key = |ty: &str, edge: Option<usize>| TinvRowKey {
        ty: ty.into(),
        conjunct: 0,
        point: TypeInvariantPoint::Return,
        site: TypeInvariantSite { block: 3, statement_index: 0 },
        ordinal: 0,
        edge,
    };
    let keys = [
        key("c::A", Some(0)),
        key("c::B", Some(0)),
        key("c::B", Some(2)),
        key("c::C", Some(2)),
        key("c::C", None),
    ];
    let got = incomplete_join_parts(&f, &keys);
    assert_eq!(
        got.iter().map(|(ty, _)| ty.as_str()).collect::<Vec<_>>(),
        vec!["c::A", "c::C"],
        "{got:?}"
    );
    assert!(got[0].1.contains("not exactly its predecessors"), "{got:?}");
    assert!(got[1].1.contains("mixes a whole row"), "{got:?}");
}

// ---------------------------------------------------------------------------------------
// Step 10.0: what a use site reads off the outcome
// ---------------------------------------------------------------------------------------

/// A certifying run reports the inventory its rows assumed (the `Some` identities only),
/// every body of the final round (an identity-less body included: it is walked and
/// checked, it is only not callable), and each certificate's field list.
#[test]
fn a_certifying_run_reports_its_inventory_checked_bodies_and_fields() {
    let funcs = [copy_of(), bump(true)];
    let anonymous = bump_join(true);
    let mut bodies = run_bodies(&funcs);
    bodies.push(TinvBody { identity: None, func: &anonymous, facts: None });
    let out = run_ay(&[p(vec![c0()])], &bodies);
    assert_eq!(cert_ids(&out, "c::P"), vec![0], "{:?} {:?}", out.refused, out.dropped);
    assert_eq!(out.inventory, [ident(100), ident(101)].into_iter().collect());
    assert_eq!(
        out.checked_bodies,
        ["c::bump", "c::bump_join", "c::copy_of"].into_iter().map(String::from).collect()
    );
    let cert = &out.certificates["c::P"];
    assert_eq!(cert.fields(), p_fields().as_slice());
    assert_eq!(cert.field_count(), 3);
}

/// No certificate, no body set: a run whose only conjunct drops keeps its inventory (a
/// note) but reports no checked body, and a run refused at its inputs reports neither.
#[test]
fn a_run_without_a_certificate_reports_no_checked_body() {
    let funcs = [copy_of(), bump_join(false)];
    let out = run_ay(&[p(vec![c0()])], &run_bodies(&funcs));
    assert!(out.certificates.is_empty());
    assert!(out.checked_bodies.is_empty(), "{:?}", out.checked_bodies);
    assert_eq!(out.inventory, [ident(100), ident(101)].into_iter().collect());

    let funcs = [copy_of(), bump(true)];
    let dup: Vec<TinvBody<'_>> =
        funcs.iter().map(|f| TinvBody { identity: Some(ident(7)), func: f, facts: None }).collect();
    let out = run(&[p(vec![c0()])], &dup, &Never, &|_| panic!("no mint"), BUDGET);
    assert!(out.certificates.is_empty() && !out.refused.is_empty());
    assert!(out.inventory.is_empty() && out.checked_bodies.is_empty());
}

/// Step 10.0 (circularity backstop): Houdini refuses EVERY type, at runtime, when a TINV
/// use set is visible in the active generation context, and asks neither the oracle nor
/// the mint. The same run with no set visible certifies (the control).
#[test]
fn houdini_refuses_every_type_when_a_use_set_is_visible() {
    let funcs = [copy_of(), bump(true)];
    let control = run_ay(&[p(vec![c0()])], &run_bodies(&funcs));
    assert_eq!(cert_ids(&control, "c::P"), vec![0], "control: {:?}", control.refused);
    let set = super::super::TinvUseSet::from_outcome(&control, |_| true).expect("use set");
    let _guard = crate::enter_test_callee_summaries(
        crate::CalleeSummaryContext::default().with_type_invariants(Some(std::sync::Arc::new(set))),
    );
    let out = run(&[p(vec![c0()])], &run_bodies(&funcs), &Never, &|_| panic!("no mint"), BUDGET);
    assert!(out.certificates.is_empty());
    assert_eq!(out.refused, vec![("c::P".to_string(), TinvObligationRefusal::UseSetVisible)]);
    assert!(out.checked_bodies.is_empty() && out.inventory.is_empty());
}

// ---------------------------------------------------------------------------------------
// Step 7.7: the same loop with the real mint
// ---------------------------------------------------------------------------------------

#[path = "certify_tests.rs"]
mod certify_tests;

#[path = "alias_write_realmir_tests.rs"]
mod alias_write_realmir_tests;

#[path = "p1_realmir_tests.rs"]
mod p1_realmir_tests;

#[path = "arm_lemma_tests.rs"]
mod arm_lemma_tests;
