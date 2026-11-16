//! TINV design §5 P1 (the json `Parser`, `i <= len(b)`) on the compiler's OWN MIR.
//!
//! FIXTURE. `tests/fixtures/tinv_p1_json_parser_fx.rs` (the UI test
//! `tests/ui/trust/tinv/tinv_p1_json_parser.rs` without its annotations), compiled by the
//! stage 1 of `42ef871e33` + this change as, and REGENERATED on the 1.101
//! toolchain (2026-10-18, `migrate/rust-1.101-20261016`) by the same command:
//! the residual of `?` on `Option` is now `Option<!>` (was
//! `Option<Infallible>`), and `peek`'s `copied` call carries the
//! extraction-minted `OptionCopied` tag. The `!` spelling first broke this
//! corpus (every conjunct dropped in round 1) until
//! `path_defs::ty_is_pure_frozen_value` admitted `Ty::Never` as a frozen
//! leaf. Regenerate from:
//!
//! ```text
//! TRUST_TINV=1 rustc -Ztrust-verify=on -Ztrust-policy=advisory -Ztrust-dump=mir:<dir> \
//!       --edition 2021 --crate-type lib --crate-name tinvp1 tinv_p1_json_parser_fx.rs
//! ```
//!
//! `tests/fixtures/tinv_p1_json_parser_fx.json` is `<dir>/tinv-inventory.json`, verbatim:
//! the EXACT bodies the step-9 mint walks (`mir_drops_elaborated_and_const_checked`,
//! promoted bodies re-keyed) with the identities it computed, written by
//! `trust_verify::type_invariant::dump_inventory`. (The per-function `-Ztrust-dump=mir`
//! files are the later TrustVerify input: different blocks, no storage markers, a
//! `from_residual` argument folded to an opaque constant that synthesis refuses.)
//!
//! WHAT WAS WRONG ON THIS MIR, AND WHAT CHANGED (2026-10-06):
//! * every call with a pointer-free or read-only argument havocked `*self`: the
//!   `Option<u8>` into `Try::branch`/`from_residual` on `bump`'s `?` path, the `&[u8]`
//!   into `<[u8]>::len`, the `&&[u8]` into `PartialEq::eq` in `literal`. Each Return
//!   edge part then read fresh `self*.1#e_s{b}_t`/`self*.0__slice_len#.._t` the entry
//!   assumption does not bind, and was refuted. Fixed in the havoc list
//!   (`path_defs::arg_grants_no_write`), UNDONE by the TINV-18 correction's coarse
//!   rule (2026-10-06, CALL-HAVOC-ESCAPE-1: the dest-only arm exempted only a `&mut`
//!   PARAMETER whose pointee holds no pointer of any kind, and `P` holds `b: &[u8]`),
//!   and RECOVERED by the P1 precision widening of that rule (2026-10-06): the pointee
//!   may hold SHARED references to pointer-free `Freeze` data
//!   (`path_defs::ty_is_protected_plain_pointee`), so `*self`'s OWN bytes (`i`, `b`'s
//!   length) survive those calls (the bytes behind `b` are still havocked);
//! * `literal`'s guard `self.b.len() >= self.i + w.len()` read `_4 = len(&*_27)`,
//!   `_27 = copy (*self).0`, and no fact tied `_4` to `self*.0__slice_len` (the global
//!   `_len == coll_len` tie declines an unstable base). Fixed by the call-point tie
//!   `dest == recv__slice_len` for std `<[T]>::len` (`semantic_guard`);
//! * `parse`'s C row before `p.bump()` read `p.1#s0_3`/`p.0__slice_len#s0_3`, which
//!   nothing bound: the ordinary walk drops an aggregate's field defs for a local that
//!   is `&mut`-borrowed anywhere (hunt-7). Fixed by TINV construction facts
//!   (`tinv_rows::Construction`), gated to the construction's own block with no
//!   untracked write in between;
//! * `bump`'s Return edge part from `bb7` (`self.i += 1` after `self.peek()?`) needs
//!   `peek()` to have returned `Some` only if `i < len(b)`. Before TINV-21 nothing said so:
//!   the `get`-`Some` fact was minted NOWHERE, not even inside `peek`, because `get`'s
//!   direct target is the `copied` call, not a switch (the recognizer's hop helpers also
//!   refused the storage markers rustc puts in every hop block). TINV-21 (design §6 item 2,
//!   2026-10-06) adds the authenticated `copied` hop, the storage-marker tolerance and the
//!   kernel-certified `Some`-arm lemma of `peek` (`arm_lemma`), consumed in `bump` sealed
//!   at the call target `bb1` inside the `Continue` region `bb4`; with the rule-(b)
//!   widening above, `Try::branch` in `bb1` keeps `*self`'s own bytes, so the sealed
//!   lemma binds the names the core reads. The fixture predates
//!   `SysrootItem::OptionCopied`, so `inventory()` adds that one tag to `peek`'s `copied`
//!   call, as a re-extraction mints it (`arm_lemma_tests::with_copied_tag`);
//! * `literal`'s Return edge part from `bb14` (the untouched `false` path) was UNKNOWN:
//!   ay answered `unknown (incomplete self-check-rejected)` on a formula that is UNSAT by
//!   two contradictory literals. That ay defect is fixed at the ay pin `630e4d62` (ledger
//!   2026-10-06 (p)); the three-atom reproduction below pins the Proved verdict.
//!
//! OUTCOME (MEASURED 2026-10-06 on this tree: rule-(b) widening + stored-ref havoc +
//! TINV-21 + ay `630e4d62`): `i <= len(b)` CERTIFIES end to end. Houdini (4 rounds) drops
//! the three sibling conjuncts (`len(b) == i * i` Refuted at `bump`'s C row in round 1;
//! `i <= 0` at `bump`'s `bb7` part and `i <= 1` at `literal`'s `bb11` part, both Refuted in
//! round 2) and returns one certificate for `tinvp1::P` holding `i <= len(b)` alone: eight
//! rows, every one kernel-certified and replayed, the `bb7` row assuming BOTH of `peek`'s
//! carried `Some`-arm lemmas (`i < len(b)`, `i <= len(b)`, parameter `_1`), whose use at
//! the caller is a trusted composition (the `arm lemma` note), not a kernel re-check of the
//! composition. Pinned in `p1_realmir_houdini_certifies_i_le_len_b`.

use std::collections::BTreeMap;

use trust_types::{Sort, TypeInvariantPoint};

use super::*;
use crate::type_invariant::candidate;
use crate::type_invariant::obligations::{
    BodyTinvPlan, type_invariant_check_vcs, type_invariant_check_vcs_with_lemmas,
};

const FIXTURE: &str = include_str!("../../tests/fixtures/tinv_p1_json_parser_fx.json");
const P: &str = "tinvp1::P";
const BUMP: &str = "tinvp1::P::<'_>::bump";
const PEEK: &str = "tinvp1::P::<'_>::peek";
const LITERAL: &str = "tinvp1::P::<'_>::literal";
const PARSE: &str = "tinvp1::parse";

#[derive(serde::Deserialize)]
struct InventoryRow {
    identity: Option<CalleeIdentity>,
    func: VerifiableFunction,
}

/// The fixture with the `SysrootItem::OptionCopied` tag a re-extraction mints on `peek`'s
/// `copied` call (TINV-21; see `arm_lemma_tests::with_copied_tag`).
fn inventory() -> Vec<InventoryRow> {
    let rows: Vec<InventoryRow> =
        serde_json::from_str(FIXTURE).expect("fixture bundle must deserialize");
    rows.into_iter()
        .map(|r| InventoryRow {
            identity: r.identity,
            func: super::arm_lemma_tests::with_copied_tag(r.func),
        })
        .collect()
}

fn fixtures() -> Vec<VerifiableFunction> {
    inventory().into_iter().map(|r| r.func).collect()
}

/// Each body's identity, exactly as the compiler's mint computed it (TINV-11).
fn identities() -> BTreeMap<String, CalleeIdentity> {
    inventory().into_iter().filter_map(|r| Some((r.func.def_path, r.identity?))).collect()
}

/// The UNTRUSTED synthesis over the fixture, as step 9 runs it.
fn p_type(all: &[VerifiableFunction]) -> TinvType {
    candidate::synthesize(P, all).expect("P1 synthesizes on the inventory bodies").ty
}

/// The id of `i <= len(b)` among the synthesized conjuncts.
fn i_le_len_b(ty: &TinvType) -> u32 {
    let want = Formula::Le(
        Box::new(field_var(FieldTerm::Value(1))),
        Box::new(field_var(FieldTerm::Len(0))),
    );
    ty.conjuncts.iter().find(|c| c.formula == want).expect("`i <= len(b)` is proposed").id
}

/// `(function, point, edge) -> (situated, ay verdict, Houdini's judge)` for every row of
/// conjunct `id`; the judge is `None` when Houdini keeps the row (situated, proved AND a
/// ground-checked vacuity model), else its drop cause.
type Verdicts =
    BTreeMap<(String, &'static str, usize, Option<usize>), (bool, Option<bool>, Option<DropCause>)>;

/// The TINV-21 lemmas exactly as Houdini mints them before its fixpoint (real kernel mint).
fn minted_lemmas(
    all: &[VerifiableFunction],
    ty: &TinvType,
) -> crate::type_invariant::arm_lemma::ArmLemmas {
    let ids = identities();
    let bodies: Vec<TinvBody<'_>> = all
        .iter()
        .map(|f| TinvBody { identity: ids.get(&f.def_path).copied(), func: f, facts: None })
        .collect();
    let inventory: HashSet<CalleeIdentity> = bodies.iter().filter_map(|b| b.identity).collect();
    let env = crate::type_invariant::arm_lemma::LemmaEnv {
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    crate::type_invariant::arm_lemma::mint_arm_lemmas(
        &[ty],
        &bodies,
        &env,
        &Ay,
        &|vc: &VerificationCondition| {
            let evidence = trust_certify::certify_vc(vc)?;
            trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
        },
        u64::MAX,
    )
    .0
}

/// Every row of conjunct `id`, walked with `lemmas`. `alone`: only `id` is alive (the
/// entry and post-call assumptions are `I = {id}`), else every synthesized conjunct is.
fn row_verdicts(
    id: u32,
    lemmas: &crate::type_invariant::arm_lemma::ArmLemmas,
    alone: bool,
) -> Verdicts {
    let all = fixtures();
    let mut ty = p_type(&all);
    if alone {
        ty.conjuncts.retain(|c| c.id == id);
    }
    let inventory: HashSet<CalleeIdentity> = identities().values().copied().collect();
    let types = [ty];
    let mut out = BTreeMap::new();
    for f in &all {
        let plan = BodyTinvPlan {
            types: &types,
            facts: None,
            inventory: &inventory,
            models: &NoExactModels,
            may_run_user_drop: &|_| true,
            step_budget: u64::MAX,
        };
        let got = type_invariant_check_vcs_with_lemmas(f, &plan, lemmas)
            .expect("every P1 body is walked");
        assert!(got.refused.is_empty(), "{}: {:?}", f.def_path, got.refused);
        assert!(got.uninstantiable.is_empty(), "{}: {:?}", f.def_path, got.uninstantiable);
        for (k, vc) in got.rows.iter().filter(|(k, _)| k.conjunct == id) {
            let situated = vc.type_invariant_situatedness_refusal().is_none();
            out.insert(
                (f.def_path.clone(), k.point.as_tag(), k.site.block, k.edge),
                (situated, ay(vc), crate::type_invariant::houdini::judge(vc, &Ay)),
            );
        }
    }
    out
}

#[test]
fn p1_realmir_rows_of_i_le_len_b() {
    let all = fixtures();
    let ty = p_type(&all);
    let id = i_le_len_b(&ty);
    let lemmas = minted_lemmas(&all, &ty);
    // TINV-21: exactly `peek`'s two lemmas, `i < len(b)` and `i <= len(b)`.
    let minted: Vec<(&str, &Formula)> = lemmas.iter().map(|l| (l.function(), l.phi())).collect();
    let (i, len) = (field_var(FieldTerm::Value(1)), field_var(FieldTerm::Len(0)));
    assert_eq!(
        minted,
        vec![
            (PEEK, &Formula::Lt(Box::new(i.clone()), Box::new(len.clone()))),
            (PEEK, &Formula::Le(Box::new(i), Box::new(len))),
        ]
    );
    let key = |f: &str, p: &'static str, b: usize, e: Option<usize>| (f.to_string(), p, b, e);
    let proved = (true, Some(true), None);
    let expected = |bb7: (bool, Option<bool>, Option<DropCause>)| -> Verdicts {
        [
            // `bump`: the C row at `self.peek()` (entry assumption on `*self`).
            (key(BUMP, "call", 0, None), proved),
            // The `?` path: no write; `branch`/`from_residual` keep `*self`'s own bytes
            // (rule (b) of the call havoc admits `P`'s shared `&[u8]` field).
            (key(BUMP, "return", 8, Some(6)), proved),
            // `self.i += 1` after `peek()?` (below).
            (key(BUMP, "return", 8, Some(7)), bb7),
            // `literal`'s write path and untouched path: the `len`/`eq` calls keep `*self`'s
            // own bytes (rule (b)), and ay at `630e4d62` proves the `bb14` part it once
            // answered Unknown on (the ay defect pinned below).
            (key(LITERAL, "return", 15, Some(11)), proved),
            (key(LITERAL, "return", 15, Some(14)), proved),
            (key(PARSE, "establish", 0, None), proved),
            // The C row before `p.bump()`: situated by the construction facts.
            (key(PARSE, "call", 0, None), proved),
            // The C row before `p.literal(..)`: the post-call fact of `bump`.
            (key(PARSE, "call", 1, None), proved),
        ]
        .into_iter()
        .collect()
    };
    let none = crate::type_invariant::arm_lemma::ArmLemmas::default();
    // Without the lemmas (as before TINV-21) the `bb7` part is REFUTED (counterexample
    // `len(b) = 0, i = 0`: nothing says `peek()` returned `Some` only if `i < len(b)`),
    // with every conjunct alive and with `i <= len(b)` alone. MEASURED 2026-10-06.
    let refuted = (true, Some(false), Some(DropCause::Refuted));
    assert_eq!(row_verdicts(id, &none, false), expected(refuted));
    assert_eq!(row_verdicts(id, &none, true), expected(refuted));
    // With the lemmas and ONLY `i <= len(b)` alive (the question Houdini's last round
    // asks): every row is PROVED and kept by Houdini's judge, the `bb7` part included and
    // non-vacuous. The arm fact is sealed at the call target `bb1` (region `bb4` dominates
    // the hook block `bb7`), and `Try::branch` in `bb1` no longer havocs `*self`'s own
    // bytes, so the names the core reads are the ones the sealed fact binds. MEASURED
    // 2026-10-06.
    assert_eq!(row_verdicts(id, &lemmas, true), expected(proved));
    // With every synthesized conjunct alive, ay PROVES the `bb7` part, but VACUOUSLY: the
    // post-call `i <= 0` and `len(b) == i * i` contradict the lemma's `i < len(b)`, so the
    // hypotheses have no model and Houdini's judge drops it (`Vacuous`). Not a proof; the
    // TINV-21 vacuity deferral lets Houdini drop those siblings first (next test).
    assert_eq!(
        row_verdicts(id, &lemmas, false),
        expected((true, Some(true), Some(DropCause::Vacuous)))
    );
}

/// End to end with the real kernel mint (MEASURED 2026-10-06): `i <= len(b)` CERTIFIES.
/// Houdini mints `peek`'s two `Some`-arm lemmas before its fixpoint and runs four rounds:
/// `len(b) == i * i` drops Refuted at `bump`'s C row (round 1), `i <= 0` at `bump`'s `bb7`
/// part and `i <= 1` at `literal`'s `bb11` part (round 2, both Refuted); the one
/// certificate for `P` holds `i <= len(b)` alone, over eight kernel-certified rows, and
/// replays. Only the `bb7` row assumes arm facts: both carried lemmas of `peek`
/// (`i < len(b)` and `i <= len(b)`, parameter `_1`); their use at the caller is a trusted
/// composition, not a kernel re-check of it.
///
/// Without `bump` (a reduction of the crate, not a claim about it) nothing certifies:
/// `i <= len(b)` drops at `parse`'s C row before `p.literal(..)` (`Situatedness`, round
/// 1), whose `p` facts came from `bump`'s post-call fact, which an uninventoried callee
/// does not give.
#[test]
fn p1_realmir_houdini_certifies_i_le_len_b() {
    let all = fixtures();
    let ids = identities();
    let ty = p_type(&all);
    let id = i_le_len_b(&ty);
    let cid =
        |want: &Formula| ty.conjuncts.iter().find(|c| &c.formula == want).expect("proposed").id;
    let (i, len) = (field_var(FieldTerm::Value(1)), field_var(FieldTerm::Len(0)));
    let i_le_0 = cid(&Formula::Le(Box::new(i.clone()), Box::new(Formula::Int(0))));
    let i_le_1 = cid(&Formula::Le(Box::new(i.clone()), Box::new(Formula::Int(1))));
    let len_sq = cid(&Formula::Eq(
        Box::new(len.clone()),
        Box::new(Formula::Mul(Box::new(i.clone()), Box::new(i.clone()))),
    ));
    assert_eq!(ty.conjuncts.len(), 4);
    let mint = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
    };
    let run = |gone: &[&str]| {
        let bodies: Vec<TinvBody<'_>> = all
            .iter()
            .filter(|f| !gone.contains(&f.def_path.as_str()))
            .map(|f| TinvBody { identity: ids.get(&f.def_path).copied(), func: f, facts: None })
            .collect();
        houdini(std::slice::from_ref(&ty), &bodies, &NoExactModels, &|_| true, &Ay, &mint, BUDGET)
    };
    let drops = |out: &TinvOutcome<_>| -> Vec<_> {
        out.dropped
            .iter()
            .map(|d| (d.conjunct, d.cause, d.point, d.function.clone(), d.edge, d.round))
            .collect()
    };
    use TypeInvariantPoint::{Call, Return};

    let out = run(&[]);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    let minted: Vec<&str> = out.arm_lemmas.iter().map(|l| l.function()).collect();
    assert_eq!(minted, vec![PEEK, PEEK]);
    assert_eq!(out.rounds, 4);
    assert_eq!(
        drops(&out),
        vec![
            (len_sq, DropCause::Refuted, Call, BUMP.to_string(), None, 1),
            (i_le_0, DropCause::Refuted, Return, BUMP.to_string(), Some(7), 2),
            (i_le_1, DropCause::Refuted, Return, LITERAL.to_string(), Some(11), 2),
        ]
    );
    assert_eq!(out.certificates.keys().collect::<Vec<_>>(), vec![P]);
    let cert = &out.certificates[P];
    assert_eq!(cert.conjuncts().iter().map(|c| c.id).collect::<Vec<_>>(), vec![id]);
    assert!(cert.replay(&|vc, e| trust_certify::replay_vc_evidence(vc, e)));
    assert_eq!(cert.lemmas().len(), 2);
    let rows: Vec<_> = cert
        .rows()
        .iter()
        .map(|r| {
            let k = r.key();
            assert_eq!(k.conjunct, id);
            let uses: Vec<Formula> = r.lemma_uses().iter().map(|u| u.lemma.phi.clone()).collect();
            (r.function().to_string(), k.point, k.site.block, k.edge, uses)
        })
        .collect();
    let lt = Formula::Lt(Box::new(i.clone()), Box::new(len.clone()));
    let le = Formula::Le(Box::new(i), Box::new(len));
    let row = |f: &str, p, b, e, u: Vec<Formula>| (f.to_string(), p, b, e, u);
    assert_eq!(
        rows,
        vec![
            row(BUMP, Call, 0, None, vec![]),
            row(BUMP, Return, 8, Some(6), vec![]),
            row(BUMP, Return, 8, Some(7), vec![lt, le]),
            row(LITERAL, Return, 15, Some(11), vec![]),
            row(LITERAL, Return, 15, Some(14), vec![]),
            row(PARSE, TypeInvariantPoint::Establish, 0, None, vec![]),
            row(PARSE, Call, 0, None, vec![]),
            row(PARSE, Call, 1, None, vec![]),
        ]
    );

    let out = run(&[BUMP]);
    assert!(out.certificates.is_empty());
    assert_eq!(
        out.dropped.iter().find(|d| d.conjunct == id).map(|d| (
            d.cause,
            d.point,
            d.function.clone(),
            d.site.block,
            d.round
        )),
        Some((DropCause::Situatedness, Call, PARSE.to_string(), 1, 1))
    );
}

/// The ay defect that once made `literal`'s `bb14` part Unknown, on three atoms: `a <= b`
/// and its negation under one `Or` arm, with a `true` conjunct (an unguarded edge's guard
/// slot) beside the negation. ay up to `cb87694a` answered `unknown (incomplete
/// self-check-rejected)`; the ay pin `630e4d62` (ay `ba4e7b5d1`, ledger 2026-10-06 (p))
/// proves it, as it proves the same formula without the `Or` or without the `true`. With
/// the fix the `bb14` part itself is PROVED (`p1_realmir_rows_of_i_le_len_b`).
#[test]
fn ay_proves_a_true_conjunct_under_an_or() {
    let l = || {
        Formula::Le(
            Box::new(Formula::var_owned("a".into(), Sort::Int)),
            Box::new(Formula::var_owned("b".into(), Sort::Int)),
        )
    };
    let n = || Formula::Not(Box::new(l()));
    let t = || Formula::Bool(true);
    let vc = |formula: Formula| VerificationCondition {
        kind: VcKind::Assertion { message: "tinv ay defect".into() },
        function: "tinv".into(),
        location: SourceSpan::default(),
        formula,
        contract_metadata: None,
        obligation: None,
    };
    use Formula::{And, Or};
    assert_eq!(ay(&vc(Or(vec![And(vec![l(), n()])]))), Some(true));
    assert_eq!(ay(&vc(And(vec![l(), And(vec![t(), n()])]))), Some(true));
    let result = ay_solve(&vc(Or(vec![And(vec![l(), And(vec![t(), n()])])])));
    assert!(
        matches!(&result, VerificationResult::Proved { .. }),
        "the true-under-or formula is UNSAT and the pinned ay proves it: {result:?}"
    );
}

// ---------------------------------------------------------------------------------------
// Construction facts (`tinv_rows::Construction`), on hand-built bodies over `c::P`
// ---------------------------------------------------------------------------------------

/// `fn g(n: u64) { let mut p = P { i: 0, n, k: 0 }; [mid..] c::take(move r) }` with
/// `r = &mut p`, the construction in `bb0` and the call in `bb{call_block}`.
fn construct_then_call(mid: Vec<Statement>, call_block: usize) -> VerifiableFunction {
    let agg = Rvalue::Aggregate(
        AggregateKind::Adt { name: "c::P".into(), variant: 0, active_field: None, args: None },
        vec![konst(0), Operand::Copy(Place::local(1)), konst(0)],
    );
    let mut first = vec![assign(Place::local(2), agg)];
    first.push(assign(Place::local(3), Rvalue::Ref { mutable: true, place: Place::local(2) }));
    first.extend(mid);
    let call = Terminator::Call {
        func: "c::take".into(),
        args: vec![Operand::Move(Place::local(3))],
        dest: Place::local(0),
        target: Some(BlockId(call_block + 1)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: None,
        callee_key: None,
    };
    let mut blocks = Vec::new();
    if call_block == 0 {
        blocks.push(blk(0, first, call));
    } else {
        blocks.push(blk(0, first, Terminator::Goto(BlockId(1))));
        blocks.push(blk(1, vec![], call));
    }
    blocks.push(blk(call_block + 1, vec![], Terminator::Return));
    func(
        "g",
        vec![(Ty::Unit, None), (u64_ty(), Some("n")), (p_ty(), Some("p")), (mut_ref(p_ty()), None)],
        1,
        blocks,
    )
}

/// The C row of `c::take(r)` for `i <= n`: (situated, ay verdict).
fn call_row(f: &VerifiableFunction) -> (bool, Option<bool>) {
    let types = [p(vec![c0()])];
    let inventory = HashSet::new();
    let plan = BodyTinvPlan {
        types: &types,
        facts: None,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
        step_budget: u64::MAX,
    };
    let rows = type_invariant_check_vcs(f, &plan).expect("walked").rows;
    let calls: Vec<_> = rows.iter().filter(|(k, _)| k.point == TypeInvariantPoint::Call).collect();
    assert_eq!(calls.len(), 1, "{rows:#?}");
    let vc = &calls[0].1;
    (vc.type_invariant_situatedness_refusal().is_none(), ay(vc))
}

#[test]
fn a_construction_situates_the_call_row_in_its_own_block() {
    assert_eq!(call_row(&construct_then_call(vec![], 0)), (true, Some(true)));
}

#[test]
fn a_write_through_a_pointer_after_the_construction_withholds_the_facts() {
    // `(*r).0 = n + 1` before the call. A construction fact `p.0 == 0` read after it
    // would be STALE and prove a false C row. Two guards keep it out: the gap gate
    // (`untracked_write_free`: a `Deref` write refuses) and, for this canonical alias,
    // the version oracle, which re-versions `p.0` at the write (MEASURED: with the gap
    // gate disabled the row is still refuted). A write through an alias the oracle
    // cannot canonicalize (a reseated `&mut`, a raw pointer) is refused earlier, by the
    // TINV root analysis (`UnresolvedRoot`/`RootShape`), so the gap gate is the
    // fail-closed backstop, not the only line.
    let write = assign(
        Place { local: 3, projections: vec![Projection::Deref, Projection::Field(0)] },
        Rvalue::BinaryOp(BinOp::Add, Operand::Copy(Place::local(1)), konst(1)),
    );
    let (situated, verdict) = call_row(&construct_then_call(vec![write], 0));
    assert!(!(situated && verdict == Some(true)), "FALSE PROOF: the stale construction fact");
}

#[test]
fn a_construction_in_another_block_gives_no_facts() {
    // v1 scope: the facts reach rows of the construction's own block only.
    let (situated, verdict) = call_row(&construct_then_call(vec![], 1));
    assert!(!(situated && verdict == Some(true)), "({situated}, {verdict:?})");
}
