//! TINV-21 (2026-10-06): the `Some`-arm lemma (`arm_lemma`), the `copied` hop and the
//! storage-marker tolerance it rests on (`guards::slice_get_some_index_bound_definitions`),
//! and the caller-side arm facts (`obligations::arm_fact_sites`, `tinv_rows::ArmFact`).
//!
//! On the REAL `peek`/`bump` of the P1 fixture (`tinv_p1_json_parser_fx.json`, see
//! `p1_realmir_tests.rs`) and on hand-built `c::P { i, n, k }` bodies. The oracle is the
//! in-process ay router and `certify` is the real kernel mint and replay, so a lemma
//! here is exactly what Houdini would admit.
//!
//! THE FIXTURE'S `copied` TAG. The fixture was extracted before `SysrootItem::OptionCopied`
//! existed, so its `Option::<&u8>::copied` call carries `sysroot_item: None`. The
//! extractor mints the tag from the `DECLS` row `(core, Inherent(Option), copied)`
//! (`trust_types::callee_key`), and that call's key is `krate_is_real_sysroot: true`,
//! `krate_name: core`; [`with_copied_tag`] adds exactly that one field to exactly that
//! call. Every rail that removes it or forges its residency is pinned below.

use std::collections::{BTreeMap, HashSet};

use super::*;
use crate::generate::tinv_rows::{
    RequestRow, RequestType, RowArmUse, TinvRowRequest, tinv_check_rows,
};
use crate::type_invariant::arm_lemma::{
    ArmLemma, ArmLemmaDep, ArmLemmas, LEMMA_CONJUNCT_BASE, LemmaEnv, lemma_atoms, lemma_probe,
    strip_versions,
};
use crate::type_invariant::obligations::{
    ArmSite, BodyTinvPlan, SigmaSource, TinvInputs, TinvPointRow, TinvStateSpec, arm_fact_sites,
    sigma_of_root, type_invariant_check_vcs_with_lemmas,
};
use crate::type_invariant::{Sigma, candidate};

const FIXTURE: &str = include_str!("../../tests/fixtures/tinv_p1_json_parser_fx.json");
const PEEK: &str = "tinvp1::P::<'_>::peek";
const BUMP: &str = "tinvp1::P::<'_>::bump";
const P1: &str = "tinvp1::P";

#[derive(serde::Deserialize)]
struct InventoryRow {
    identity: Option<CalleeIdentity>,
    func: VerifiableFunction,
}

/// `arm_lemma::mint_body` over `f` alone (inventory `{id}`, no exact models, no facts),
/// evidence dropped: the lemma-shape rails below read the lemmas only.
fn mint_body<E>(
    f: &VerifiableFunction,
    id: CalleeIdentity,
    types: &[&TinvType],
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    budget: u64,
) -> Vec<ArmLemma> {
    let inventory: HashSet<CalleeIdentity> = [id].into_iter().collect();
    let env =
        LemmaEnv { inventory: &inventory, models: &NoExactModels, may_run_user_drop: &|_| true };
    crate::type_invariant::arm_lemma::mint_body(f, None, id, types, &env, oracle, certify, budget)
        .into_iter()
        .map(|(l, _)| l)
        .collect()
}

/// `arm_lemma::mint_arm_lemmas` with the bodies' own identities as the inventory, the
/// evidence dropped.
fn mint_arm_lemmas<E>(
    types: &[&TinvType],
    bodies: &[TinvBody<'_>],
    oracle: &dyn TinvOracle,
    certify: &dyn Fn(&VerificationCondition) -> Option<E>,
    budget: u64,
) -> (ArmLemmas, Vec<TinvNote>) {
    let inventory: HashSet<CalleeIdentity> = bodies.iter().filter_map(|b| b.identity).collect();
    let env =
        LemmaEnv { inventory: &inventory, models: &NoExactModels, may_run_user_drop: &|_| true };
    let (lemmas, evidence, notes) = crate::type_invariant::arm_lemma::mint_arm_lemmas(
        types, bodies, &env, oracle, certify, budget,
    );
    assert_eq!(lemmas.len(), evidence.len(), "one evidence per lemma");
    (lemmas, notes)
}

/// `f` re-serialized, edited as JSON, and read back: every mutation below is a field
/// edit of the extracted body, never a re-construction.
fn mutate(f: &VerifiableFunction, edit: impl FnOnce(&mut serde_json::Value)) -> VerifiableFunction {
    let mut v = serde_json::to_value(f).expect("serialize");
    edit(&mut v);
    serde_json::from_value(v).expect("the edited body deserializes")
}

/// The fixture's `copied` call(s) with the tag a re-extraction mints (module doc).
pub(super) fn with_copied_tag(f: VerifiableFunction) -> VerifiableFunction {
    mutate(&f, |v| {
        for b in v["body"]["blocks"].as_array_mut().expect("blocks") {
            let Some(call) = b["terminator"].get_mut("Call") else { continue };
            let is_copied = call["func"].as_str().is_some_and(|s| {
                s.starts_with("core::option::Option::<") && s.ends_with(">::copied")
            });
            let key = &mut call["callee_key"];
            if is_copied && key["krate_is_real_sysroot"] == true && key["krate_name"] == "core" {
                key["sysroot_item"] = serde_json::json!("OptionCopied");
            }
        }
    })
}

fn inventory() -> Vec<(Option<CalleeIdentity>, VerifiableFunction)> {
    let rows: Vec<InventoryRow> = serde_json::from_str(FIXTURE).expect("fixture bundle");
    rows.into_iter().map(|r| (r.identity, with_copied_tag(r.func))).collect()
}

fn fx(name: &str) -> (CalleeIdentity, VerifiableFunction) {
    let (id, f) = inventory().into_iter().find(|(_, f)| f.def_path == name).expect("in fixture");
    (id.expect("an inventory identity"), f)
}

fn p1_type() -> TinvType {
    let all: Vec<VerifiableFunction> = inventory().into_iter().map(|(_, f)| f).collect();
    candidate::synthesize(P1, &all).expect("P synthesizes").ty
}

/// The real kernel mint and replay (the compiler's `certify`, minus its evidence-kind
/// check, which `certify_vc` only ever answers with `CleanCic` for a TINV row).
fn kernel(vc: &VerificationCondition) -> Option<impl std::fmt::Debug + use<>> {
    let evidence = trust_certify::certify_vc(vc)?;
    trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
}

fn int(name: &str) -> Formula {
    Formula::var_owned(name.into(), trust_types::Sort::Int)
}

fn lt(a: Formula, b: Formula) -> Formula {
    Formula::Lt(Box::new(a), Box::new(b))
}

fn le(a: Formula, b: Formula) -> Formula {
    Formula::Le(Box::new(a), Box::new(b))
}

fn fv(t: FieldTerm) -> Formula {
    field_var(t)
}

// ---------------------------------------------------------------------------------------
// The probe: the tag is read off `_0`'s type
// ---------------------------------------------------------------------------------------

#[test]
fn the_probe_switches_on_the_some_tag_read_off_the_return_type() {
    let (_, f) = fx(PEEK);
    let (probe, shape) = lemma_probe(&f).expect("peek is eligible");
    assert_eq!(
        (shape.r, shape.a, shape.n, shape.j, shape.tag),
        (BlockId(2), BlockId(3), BlockId(4), BlockId(5), 1)
    );
    let r = &probe.body.blocks[2];
    let d = f.body.locals.len();
    assert!(matches!(r.stmts.last(), Some(Statement::Assign {
            place, rvalue: Rvalue::Discriminant(src), .. })
        if *place == Place::local(d) && *src == Place::local(0)));
    assert!(matches!(&r.terminator, Terminator::SwitchInt { targets, otherwise, .. }
        if targets == &vec![(1, BlockId(3))] && *otherwise == BlockId(4)));
    assert!(probe.preconditions.is_empty() && probe.postconditions.is_empty());

    // A core `Option` whose `Some` is DECLARED 0: the probe follows the declaration.
    let swapped = mutate(&f, |v| {
        let vs = &mut v["body"]["locals"][0]["ty"]["Adt"]["variants"];
        vs[0]["discriminant"] = serde_json::json!(1);
        vs[1]["discriminant"] = serde_json::json!(0);
    });
    assert_eq!(lemma_probe(&swapped).map(|(_, s)| s.tag), Some(0));

    // A crate-local `enum Option { Some(u8), None }` (`Some` = 0): not the modeled std
    // `Option`, so no probe and no lemma, never a `None`-arm fact under the `Some` label.
    let local = mutate(&f, |v| {
        v["body"]["locals"][0]["ty"]["Adt"]["name"] = serde_json::json!("tinvp1::Option");
        let vs = &mut v["body"]["locals"][0]["ty"]["Adt"]["variants"];
        vs[0]["discriminant"] = serde_json::json!(1);
        vs[1]["discriminant"] = serde_json::json!(0);
    });
    assert!(lemma_probe(&local).is_none());
    let ty = p1_type();
    let (id, _) = fx(PEEK);
    assert!(mint_body(&local, id, &[&ty], &Ay, &kernel, u64::MAX).is_empty());

    // Two `Return` blocks: no probe.
    let two = mutate(&f, |v| {
        let b2 = v["body"]["blocks"][2].clone();
        let mut b3 = b2.clone();
        b3["id"] = serde_json::json!(3);
        v["body"]["blocks"].as_array_mut().unwrap().push(b3);
    });
    assert!(lemma_probe(&two).is_none());
}

// ---------------------------------------------------------------------------------------
// The `copied` hop and the storage-marker tolerance (guards)
// ---------------------------------------------------------------------------------------

/// The `get`-`Some` facts the recognizer seeds at the probe's `Some` arm of `f`.
fn seeded_at_some_arm(f: &VerifiableFunction) -> Vec<Formula> {
    let Some((probe, shape)) = lemma_probe(f) else { return Vec::new() };
    crate::guards::slice_get_some_index_bound_definitions(&probe)
        .remove(&shape.a)
        .unwrap_or_default()
}

#[test]
fn the_copied_hop_seeds_the_get_some_fact_at_the_probes_some_arm() {
    let (_, f) = fx(PEEK);
    // The real body: `get` -> `copied` -> `Return`. No switch, so no fact anywhere
    // (diagnosis M2: the fact is minted nowhere in `peek` itself).
    assert!(crate::guards::slice_get_some_index_bound_definitions(&f).is_empty());
    // The probe: `get` -> `copied` (markers `StorageDead(_4)`, `StorageDead(_3)`) ->
    // the switch on `_0` (marker `StorageDead(_2)`) -> `A`.
    let facts = seeded_at_some_arm(&f);
    assert_eq!(
        facts,
        vec![lt(int("_4"), int("_3__slice_len")), lt(int("self*.1"), int("_3__slice_len"))]
    );
}

#[test]
fn storage_markers_on_a_hop_local_and_every_other_statement_refuse_the_hop() {
    let (_, f) = fx(PEEK);
    let push_stmt = |block: usize, stmt: serde_json::Value| {
        mutate(&f, |v| {
            v["body"]["blocks"][block]["stmts"].as_array_mut().unwrap().insert(0, stmt);
        })
    };
    let place = |l: usize| serde_json::json!({ "local": l, "projections": [] });
    // Tolerated: a marker of a local no hop reads, and a `Nop`.
    for ok in [
        push_stmt(1, serde_json::json!({ "StorageDead": 5 })),
        push_stmt(1, serde_json::json!("Nop")),
        push_stmt(2, serde_json::json!({ "StorageLive": 4 })),
    ] {
        assert_eq!(seeded_at_some_arm(&ok).len(), 2);
    }
    // Refused: a marker naming `copied`'s argument (`_2`) or destination (`_0`) in the
    // `copied` block, or the switched local (`_0`) in the switch block; and any
    // non-marker statement in a hop block.
    for bad in [
        push_stmt(1, serde_json::json!({ "StorageDead": 2 })),
        push_stmt(1, serde_json::json!({ "StorageLive": 2 })),
        push_stmt(1, serde_json::json!({ "StorageLive": 0 })),
        push_stmt(2, serde_json::json!({ "StorageDead": 0 })),
        push_stmt(2, serde_json::json!({ "StorageLive": 0 })),
        push_stmt(1, serde_json::json!({ "PlaceMention": place(2) })),
        push_stmt(1, serde_json::json!({ "Retag": { "place": place(2) } })),
        push_stmt(2, serde_json::json!({ "Retag": { "place": place(0) } })),
        push_stmt(2, serde_json::json!({ "Deinit": { "place": place(5) } })),
    ] {
        assert!(seeded_at_some_arm(&bad).is_empty(), "{:?}", bad.body.blocks[1..3].to_vec());
    }
    // The probe's own discriminant temp: a marker on it in the switch block refuses.
    let (mut probe, shape) = lemma_probe(&f).unwrap();
    let d = f.body.locals.len();
    probe.body.blocks[shape.r.0].stmts.push(Statement::StorageDead(d));
    assert!(crate::guards::slice_get_some_index_bound_definitions(&probe).get(&shape.a).is_none());
}

#[test]
fn copied_is_a_hop_only_as_the_authenticated_sysroot_item() {
    let (_, f) = fx(PEEK);
    let key_edit = |edit: fn(&mut serde_json::Value)| {
        mutate(&f, |v| edit(&mut v["body"]["blocks"][1]["terminator"]["Call"]))
    };
    for bad in [
        // The untagged spelling (the fixture as extracted): never a hop by name.
        key_edit(|c| {
            c["callee_key"].as_object_mut().unwrap().remove("sysroot_item");
        }),
        // The tag on a crate that is not the real sysroot (a `--crate-name core` rebuild).
        key_edit(|c| c["callee_key"]["krate_is_real_sysroot"] = serde_json::json!(false)),
        // `cloned`: runs a user `Clone`; undeclared, so untagged.
        key_edit(|c| {
            c["func"] = serde_json::json!("core::option::Option::<&u8>::cloned");
            c["callee_key"].as_object_mut().unwrap().remove("sysroot_item");
        }),
        // A user `fn copied(o: Option<&u8>) -> Option<u8> { Some(0) }`.
        key_edit(|c| {
            c["func"] = serde_json::json!("tinvp1::copied");
            c["callee_key"] = serde_json::json!({
                "krate_is_real_sysroot": false, "krate_name_is_ambiguous": false,
                "stable_crate_id": 12082752112893045721u64, "krate_name": "tinvp1" });
        }),
        // Not a move of `get`'s destination.
        key_edit(|c| {
            c["args"][0] = serde_json::json!({ "Copy": { "local": 2, "projections": [] } })
        }),
    ] {
        assert!(seeded_at_some_arm(&bad).is_empty());
    }
    // The `get` itself must still be core's: a user `get` is not the contract.
    let user_get = mutate(&f, |v| {
        v["body"]["blocks"][0]["terminator"]["Call"]["func"] = serde_json::json!("tinvp1::get");
    });
    assert!(seeded_at_some_arm(&user_get).is_empty());
    // A second predecessor of the `copied` block: not a hop (the 2026-10-04 join gate).
    let joined = mutate(&f, |v| {
        let blocks = v["body"]["blocks"].as_array_mut().unwrap();
        blocks.push(serde_json::json!({ "id": 3, "stmts": [], "terminator": { "Goto": 1 } }));
    });
    assert!(lemma_probe(&joined).is_some());
    assert!(seeded_at_some_arm(&joined).is_empty());
}

// ---------------------------------------------------------------------------------------
// The lemma on the real `peek`
// ---------------------------------------------------------------------------------------

#[test]
fn peek_mints_i_lt_len_b_and_i_le_len_b_and_nothing_else() {
    let (id, f) = fx(PEEK);
    let ty = p1_type();
    let lemmas = mint_body(&f, id, &[&ty], &Ay, &kernel, u64::MAX);
    let (v1, l0) = (fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0)));
    let got: Vec<&Formula> = lemmas.iter().map(|l| l.phi()).collect();
    assert_eq!(got, vec![&lt(v1.clone(), l0.clone()), &le(v1, l0)], "{lemmas:#?}");
    for l in &lemmas {
        assert_eq!((l.callee(), l.function(), l.ty(), l.param()), (id, PEEK, P1, 1));
        let vc = l.vc().expect("a minted lemma carries its row");
        assert_eq!(vc.kernel_authority_refusal(), None);
        assert!(matches!(vc.kind, VcKind::TypeInvariant { edge: Some(3), conjunct, .. }
            if conjunct >= LEMMA_CONJUNCT_BASE));
    }
    // Without the `copied` tag nothing proves. The 1.101 re-extraction mints
    // the tag itself, so the untagged control strips it back off.
    let (_, untagged) = inventory_untagged(PEEK);
    assert!(mint_body(&untagged, id, &[&ty], &Ay, &kernel, u64::MAX).is_empty());
}

fn inventory_untagged(name: &str) -> (CalleeIdentity, VerifiableFunction) {
    let rows: Vec<InventoryRow> = serde_json::from_str(FIXTURE).expect("fixture bundle");
    let r = rows.into_iter().find(|r| r.func.def_path == name).expect("in fixture");
    let id = r.identity.expect("identity");
    // Inverse of `with_copied_tag`: the 1.101 fixture's extraction already
    // mints the tag, so remove it wherever a `copied` call carries one.
    let f = mutate(&r.func, |v| {
        for b in v["body"]["blocks"].as_array_mut().expect("blocks") {
            let Some(call) = b["terminator"].get_mut("Call") else { continue };
            if call["callee_key"]["sysroot_item"] == "OptionCopied" {
                call["callee_key"]
                    .as_object_mut()
                    .expect("callee_key object")
                    .remove("sysroot_item");
            }
        }
    });
    (id, f)
}

/// The probe's hand-built R rows for `cores`, walked; `(edge, ay verdict)` per row.
fn probe_rows(
    f: &VerifiableFunction,
    ty: &TinvType,
    cores: &[Formula],
) -> Vec<(Option<usize>, Option<bool>)> {
    let (probe, shape) = lemma_probe(f).expect("eligible");
    let root = Place { local: 1, projections: vec![Projection::Deref] };
    let sigma = sigma_of_root(&probe, ty, &root);
    let site = TypeInvariantSite { block: shape.j.0, statement_index: 0 };
    let rows = cores
        .iter()
        .enumerate()
        .map(|(i, core)| RequestRow {
            key: TinvRowKey {
                ty: ty.def_path.clone(),
                conjunct: LEMMA_CONJUNCT_BASE + i as u32,
                point: TypeInvariantPoint::Return,
                site,
                ordinal: 0,
                edge: None,
            },
            ty: 0,
            point: TinvPointRow {
                point: TypeInvariantPoint::Return,
                site,
                row_point: usize::MAX,
                root: root.clone(),
                sigma_src: SigmaSource::Root,
                state: TinvStateSpec::At,
                failure: None,
            },
            sigma: sigma.clone(),
            core: core.clone(),
            edge_guard: None,
        })
        .collect();
    let request = TinvRowRequest::new(
        probe.def_path.clone(),
        vec![RequestType {
            def_path: ty.def_path.clone(),
            post_calls: Vec::new(),
            constructions: Vec::new(),
            arm_facts: Vec::new(),
        }],
        rows,
    );
    tinv_check_rows(&probe, request)
        .expect("walked")
        .iter()
        .map(|(k, vc)| (k.edge, ay(vc)))
        .collect()
}

#[test]
fn the_wrong_phi_is_refuted_and_the_none_part_is_refuted() {
    let (_, f) = fx(PEEK);
    let ty = p1_type();
    let (i, len) = (int("self*.1"), int("self*.0__slice_len"));
    let plus1 = Formula::Add(Box::new(i.clone()), Box::new(Formula::Int(1)));
    let got = probe_rows(&f, &ty, &[lt(i, len.clone()), lt(plus1, len)]);
    assert_eq!(
        got,
        vec![
            // `i < len(b)`: the `Some` part proves, the `None` part (never admitted) does not.
            (Some(3), Some(true)),
            (Some(4), Some(false)),
            // `i + 1 < len(b)`: refuted on the `Some` part too.
            (Some(3), Some(false)),
            (Some(4), Some(false)),
        ]
    );
}

// ---------------------------------------------------------------------------------------
// Hand-built getters over `c::P { i, n, k }`
// ---------------------------------------------------------------------------------------

/// core `Option<u64>`, spelled as the extractor spells `Option<u8>` in the fixture.
fn opt_u64() -> Ty {
    serde_json::from_value(serde_json::json!({ "Adt": {
        "name": "core::option::Option",
        "fields": [["__tag", { "Int": { "width": 64, "signed": true } }],
                   ["__v1_0", { "Int": { "width": 64, "signed": false } }]],
        "variants": [{ "name": "None", "discriminant": 0, "fields": [] },
                     { "name": "Some", "discriminant": 1,
                       "fields": [["0", { "Int": { "width": 64, "signed": false } }]] }],
        "disc_index_safe": true, "faithful_enum_repr": null, "layout": null,
        "enum_layout": null, "adt_kind": "Enum" } }))
    .expect("Option<u64>")
}

fn some(v: i128) -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant: 1,
            active_field: None,
            args: None,
        },
        vec![konst(v)],
    )
}

fn none() -> Rvalue {
    Rvalue::Aggregate(
        AggregateKind::Adt {
            name: "core::option::Option".into(),
            variant: 0,
            active_field: None,
            args: None,
        },
        Vec::new(),
    )
}

fn call(
    f: &str,
    args: Vec<Operand>,
    dest: usize,
    target: usize,
    id: Option<CalleeIdentity>,
) -> Terminator {
    Terminator::Call {
        func: f.into(),
        args,
        dest: Place::local(dest),
        target: Some(BlockId(target)),
        span: SourceSpan::default(),
        atomic: None,
        is_foreign: false,
        is_unsafe_sig: false,
        unwind: UnwindEdge::Continue,
        callee_identity: id,
        callee_key: None,
    }
}

/// `fn lt(&self) -> Option<u64> { if self.i < self.n { Some(0) } else { None } }`, with
/// `extra` statements in the join (the original `Return` block).
fn lt_getter(extra: Vec<Statement>) -> VerifiableFunction {
    let mut f = func(
        "lt",
        vec![
            (opt_u64(), None),
            (shared_ref(p_ty()), Some("self")),
            (u64_ty(), None),
            (u64_ty(), None),
            (Ty::Bool, None),
            (u64_ty(), None),
        ],
        1,
        vec![
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
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(1, vec![assign(Place::local(0), some(0))], Terminator::Goto(BlockId(3))),
            blk(2, vec![assign(Place::local(0), none())], Terminator::Goto(BlockId(3))),
            blk(3, extra, Terminator::Return),
        ],
    );
    f.def_path = "c::lt".into();
    f
}

/// `fn rec(&self) -> Option<u64> { if self.k != 0 { callee(self) } else { None } }`.
fn recursive_getter(name: &str, callee: &str, callee_id: CalleeIdentity) -> VerifiableFunction {
    func(
        name,
        vec![(opt_u64(), None), (shared_ref(p_ty()), Some("self")), (u64_ty(), None)],
        1,
        vec![
            blk(
                0,
                vec![assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 2))))],
                Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(2)),
                    targets: vec![(0, BlockId(2))],
                    otherwise: BlockId(1),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                1,
                vec![],
                call(callee, vec![Operand::Copy(Place::local(1))], 0, 3, Some(callee_id)),
            ),
            blk(2, vec![assign(Place::local(0), none())], Terminator::Goto(BlockId(3))),
            blk(3, vec![], Terminator::Return),
        ],
    )
}

/// `fn some0(&self) -> Option<u64> { [self.other();] Some(0) }`.
fn some0(call_other: Option<CalleeIdentity>) -> VerifiableFunction {
    let mut blocks = Vec::new();
    if let Some(id) = call_other {
        blocks.push(blk(
            0,
            vec![assign(
                Place::local(2),
                Rvalue::Ref {
                    mutable: false,
                    place: Place { local: 1, projections: vec![Projection::Deref] },
                },
            )],
            call("c::other", vec![Operand::Move(Place::local(2))], 3, 1, Some(id)),
        ));
        blocks.push(blk(1, vec![assign(Place::local(0), some(0))], Terminator::Return));
    } else {
        blocks.push(blk(0, vec![assign(Place::local(0), some(0))], Terminator::Return));
    }
    func(
        "some0",
        vec![
            (opt_u64(), None),
            (shared_ref(p_ty()), Some("self")),
            (shared_ref(p_ty()), None),
            (Ty::Unit, None),
        ],
        1,
        blocks,
    )
}

/// `fn other(&self) {}`.
fn other() -> VerifiableFunction {
    func(
        "other",
        vec![(Ty::Unit, None), (shared_ref(p_ty()), Some("self"))],
        1,
        vec![blk(0, vec![], Terminator::Return)],
    )
}

fn phis(lemmas: &[crate::type_invariant::arm_lemma::ArmLemma]) -> Vec<Formula> {
    lemmas.iter().map(|l| l.phi().clone()).collect()
}

/// THE VARIANT ROUTE (MATCH-ARM-CALL-CHAIN, re-measured 2026-10-07). A getter of the
/// shape `if self.i < self.n { Some(0) } else { None }` mints `i < n` and `i <= n` when
/// its join (the original `Return` block) holds no statement, and NOTHING when it holds
/// one more.
///
/// The demux still routes nothing (`enum_construction_demux_definitions` routes a
/// constructing block's facts only into an arm that READS a `Downcast` of the enum, and
/// the probe's `A` is an empty `Goto`). The guard reaches `A` through
/// `guards::switch_join_variant_arm_definitions`: the probe's `J` is the getter's join,
/// rewritten to exactly `d = discriminant(_0); switchInt(d)`, which sits on the getter's
/// `if` partition, so `A` (entered only under `Some`'s label) is seeded with the route
/// guard of the arms that may have built `Some` — here `!(_4 == false)`, the `bb1` arm,
/// since `bb2`'s last write to `_0` is a whole `None`. With `_4 == (i < n)` from `bb0`, the
/// `A` part proves both atoms. The lemma is TRUE: the body writes nothing, and it returns
/// `Some` exactly when `i < n`. One more statement in the join fails that recognizer's
/// gate (`J` holds ONLY the discriminant read), so that shape still mints nothing
/// (precision only). Before MATCH-ARM-CALL-CHAIN this getter minted nothing in both
/// shapes (the 2026-10-06 pin, then named `..._mints_nothing_the_demux_routes_only_into_a_downcasting_arm`).
/// Soundness of the route under writes, a loop, a callee and an aliased selector:
/// [`the_variant_route_mints_no_false_lemma`].
#[test]
fn an_if_else_getter_mints_its_guard_through_the_variant_route_only_with_a_bare_join() {
    let ty = p(vec![c0()]);
    let (i, n) = (fv(FieldTerm::Value(0)), fv(FieldTerm::Value(1)));
    let route_guard = Formula::Not(Box::new(Formula::Not(Box::new(Formula::var_owned(
        "_4".into(),
        trust_types::Sort::Bool,
    )))));

    // Bare join: the route seeds `A`, and exactly the two true atoms are minted.
    let f = lt_getter(vec![]);
    let (probe, shape) = lemma_probe(&f).expect("eligible");
    assert!(crate::guards::enum_construction_demux_definitions(&probe).is_empty());
    let route = crate::guards::switch_join_variant_arm_definitions(&probe);
    assert_eq!(route.len(), 1, "{route:?}");
    assert_eq!(route.get(&shape.a), Some(&vec![route_guard]), "{route:?}");
    let got = phis(&mint_body(&f, ident(7), &[&ty], &Ay, &kernel, u64::MAX));
    assert_eq!(got, vec![lt(i, n.clone()), le(fv(FieldTerm::Value(0)), n)]);

    // One more join statement: no route, no demux, no lemma.
    let f = lt_getter(vec![assign(Place::local(5), Rvalue::Use(konst(0)))]);
    let (probe, _) = lemma_probe(&f).expect("eligible");
    assert!(crate::guards::enum_construction_demux_definitions(&probe).is_empty());
    assert!(crate::guards::switch_join_variant_arm_definitions(&probe).is_empty());
    assert!(mint_body(&f, ident(7), &[&ty], &Ay, &kernel, u64::MAX).is_empty());
}

/// `fn(&mut self) -> Option<u64>` over `c::P { i, n, k }` with locals
/// `_2 = i, _3 = n, _4 = _2 < _3, _5, _6: u64, _7: &mut bool, _8: &mut P, _9: ()`.
fn route_getter(name: &str, blocks: Vec<BasicBlock>) -> VerifiableFunction {
    let mut f = func(
        name,
        vec![
            (opt_u64(), None),
            (mut_ref(p_ty()), Some("self")),
            (u64_ty(), None),
            (u64_ty(), None),
            (Ty::Bool, None),
            (u64_ty(), None),
            (u64_ty(), None),
            (mut_ref(Ty::Bool), None),
            (mut_ref(p_ty()), None),
            (Ty::Unit, None),
        ],
        1,
        blocks,
    );
    f.def_path = format!("c::{name}");
    f
}

/// THE VARIANT ROUTE MINTS NO FALSE LEMMA (adversarial review of MATCH-ARM-CALL-CHAIN's
/// route into the lemma probe, 2026-10-07). The route seeds only the merge SELECTOR's
/// guard (`_4 != false`) at the probe's `Some` arm; whether that becomes a field atom is
/// the walk's ordinary business. Each getter below reaches `Return` with `Some` in a
/// state where `i < n` is FALSE (and, where marked, `n <= i` / `n < i` too), and each
/// leaves the `i < n` guard's selector intact so the route is (or is not) seeded as
/// pinned. MEASURED 2026-10-07: every case mints nothing; the assertions are the
/// soundness property (no false atom), plus the route's own reach, so a later precision
/// gain (e.g. the true `i <= n` of the arm-write case) stays allowed.
#[test]
fn the_variant_route_mints_no_false_lemma() {
    let ty = p(vec![c0()]);
    let (i, n) = (fv(FieldTerm::Value(0)), fv(FieldTerm::Value(1)));
    let sw = |discr: usize, zero: usize, other: usize| Terminator::SwitchInt {
        discr: Operand::Copy(Place::local(discr)),
        targets: vec![(0, BlockId(zero))],
        otherwise: BlockId(other),
        exhaustive_enum_unreachable: false,
        span: SourceSpan::default(),
    };
    let reads = vec![
        assign(Place::local(2), Rvalue::Use(Operand::Copy(self_field(1, 0)))),
        assign(Place::local(3), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
        assign(
            Place::local(4),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(2)),
                Operand::Copy(Place::local(3)),
            ),
        ),
    ];
    // `self.i = self.n`.
    let i_eq_n = vec![
        assign(Place::local(5), Rvalue::Use(Operand::Copy(self_field(1, 1)))),
        assign(self_field(1, 0), Rvalue::Use(Operand::Copy(Place::local(5)))),
    ];
    let some_to_j = |id: usize, mut stmts: Vec<Statement>| {
        stmts.push(assign(Place::local(0), some(0)));
        blk(id, stmts, Terminator::Goto(BlockId(3)))
    };
    let none_to_j = || blk(2, vec![assign(Place::local(0), none())], Terminator::Goto(BlockId(3)));
    let ret = || blk(3, vec![], Terminator::Return);
    let reborrow_self = assign(
        Place::local(8),
        Rvalue::Ref {
            mutable: true,
            place: Place { local: 1, projections: vec![Projection::Deref] },
        },
    );
    let mut alias_b0 = reads.clone();
    alias_b0.push(assign(Place::local(7), Rvalue::Ref { mutable: true, place: Place::local(4) }));
    let deref7 = Place { local: 7, projections: vec![Projection::Deref] };

    // (name, getter, the route reaches `A`, atoms FALSE on some `Some` return)
    let cases: Vec<(&str, VerifiableFunction, bool, Vec<Formula>)> = vec![
        // `if i < n { i = n; Some(0) } else { None }`: Some returns with `i == n`.
        (
            "arm_write",
            route_getter(
                "arm_write",
                vec![
                    blk(0, reads.clone(), sw(4, 2, 1)),
                    some_to_j(1, i_eq_n.clone()),
                    none_to_j(),
                    ret(),
                ],
            ),
            true,
            vec![lt(i.clone(), n.clone()), lt(n.clone(), i.clone())],
        ),
        // `let c = i < n; i = n; if c { Some(0) } else { None }`: the write is in the
        // switch block, after the read the selector was computed from.
        (
            "write_after_read",
            route_getter(
                "write_after_read",
                vec![
                    blk(0, [reads.clone(), i_eq_n.clone()].concat(), sw(4, 2, 1)),
                    some_to_j(1, vec![]),
                    none_to_j(),
                    ret(),
                ],
            ),
            true,
            vec![lt(i.clone(), n.clone()), lt(n.clone(), i.clone())],
        ),
        // `let c = i < n; while k == 0 { i = n; k = 1 } if c { Some(0) } else { None }`:
        // the selector is stale after one iteration (Some with `i == n`).
        (
            "loop_stale_selector",
            route_getter(
                "loop_stale_selector",
                vec![
                    blk(0, reads.clone(), Terminator::Goto(BlockId(4))),
                    some_to_j(1, vec![]),
                    none_to_j(),
                    ret(),
                    blk(
                        4,
                        vec![assign(Place::local(6), Rvalue::Use(Operand::Copy(self_field(1, 2))))],
                        sw(6, 5, 6),
                    ),
                    blk(
                        5,
                        [i_eq_n.clone(), vec![assign(self_field(1, 2), Rvalue::Use(konst(1)))]]
                            .concat(),
                        Terminator::Goto(BlockId(4)),
                    ),
                    blk(6, vec![], sw(4, 2, 1)),
                ],
            ),
            true,
            vec![lt(i.clone(), n.clone()), lt(n.clone(), i.clone()), le(n.clone(), i.clone())],
        ),
        // `if i < n { reset(&mut *self); Some(0) } else { None }`: a `Call` hop (the
        // route admits it: `_4` is a bare, never mutably borrowed local); `reset` may
        // leave any `i`, `n`.
        (
            "call_hop_unknown_callee",
            route_getter(
                "call_hop_unknown_callee",
                vec![
                    blk(0, reads.clone(), sw(4, 2, 1)),
                    blk(
                        1,
                        vec![reborrow_self.clone()],
                        call("c::reset", vec![Operand::Move(Place::local(8))], 9, 4, None),
                    ),
                    none_to_j(),
                    ret(),
                    some_to_j(4, vec![]),
                ],
            ),
            true,
            vec![
                lt(i.clone(), n.clone()),
                le(i.clone(), n.clone()),
                lt(n.clone(), i.clone()),
                le(n.clone(), i.clone()),
            ],
        ),
        (
            "call_hop_identified_callee",
            route_getter(
                "call_hop_identified_callee",
                vec![
                    blk(0, reads.clone(), sw(4, 2, 1)),
                    blk(
                        1,
                        vec![reborrow_self],
                        call(
                            "c::reset",
                            vec![Operand::Move(Place::local(8))],
                            9,
                            4,
                            Some(ident(40)),
                        ),
                    ),
                    none_to_j(),
                    ret(),
                    some_to_j(4, vec![]),
                ],
            ),
            true,
            vec![
                lt(i.clone(), n.clone()),
                le(i.clone(), n.clone()),
                lt(n.clone(), i.clone()),
                le(n.clone(), i.clone()),
            ],
        ),
        // `let r = &mut c; if c { *r = false; i = n; Some(0) } else { None }`: the
        // selector rewritten through an alias inside the arm. The partition's write
        // check declines it (no route).
        (
            "aliased_selector_rewrite",
            route_getter(
                "aliased_selector_rewrite",
                vec![
                    blk(0, alias_b0, sw(4, 2, 1)),
                    some_to_j(
                        1,
                        [
                            vec![assign(
                                deref7,
                                Rvalue::Use(Operand::Constant(ConstValue::Bool(false))),
                            )],
                            i_eq_n,
                        ]
                        .concat(),
                    ),
                    none_to_j(),
                    ret(),
                ],
            ),
            false,
            vec![lt(i.clone(), n.clone()), lt(n, i)],
        ),
    ];
    for (name, f, routed, false_atoms) in cases {
        let (probe, shape) = lemma_probe(&f).expect("eligible");
        let route = crate::guards::switch_join_variant_arm_definitions(&probe);
        assert_eq!(route.contains_key(&shape.a), routed, "{name}: {route:?}");
        let got = phis(&mint_body(&f, ident(7), &[&ty], &Ay, &kernel, u64::MAX));
        for bad in &false_atoms {
            assert!(!got.contains(bad), "{name}: minted the FALSE lemma {bad:?} ({got:?})");
        }
    }
}

#[test]
fn a_lemma_is_hypothesis_free() {
    let ty = p(vec![c0()]);
    let (i, n) = (fv(FieldTerm::Value(0)), fv(FieldTerm::Value(1)));
    // No entry assumption: `i <= n` (the candidate conjunct) is NOT a lemma of a getter
    // that never tests it, although every row of that getter may assume it.
    let got = phis(&mint_body(&some0(None), ident(8), &[&ty], &Ay, &kernel, u64::MAX));
    assert!(got.is_empty(), "{got:?}");
    // No post-call fact: calling an inventory method that would give `I(*self)` after it
    // does not make `i <= n` a lemma either.
    let got = phis(&mint_body(&some0(Some(ident(9))), ident(8), &[&ty], &Ay, &kernel, u64::MAX));
    assert!(!got.contains(&le(i, n)), "{got:?}");

    // End to end: Houdini, whose rows of `some0` assume `I` at entry and after the
    // call, mints no lemma of it.
    let funcs = [copy_of(), some0(Some(ident(103))), other()];
    let bodies = run_bodies(&funcs);
    let out = houdini(
        std::slice::from_ref(&ty),
        &bodies,
        &NoExactModels,
        &|_| true,
        &Ay,
        &kernel,
        BUDGET,
    );
    assert!(out.arm_lemmas.is_empty(), "{:?}", out.arm_lemmas);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
}

#[test]
fn recursion_and_mutual_recursion_mint_nothing() {
    let ty = p(vec![c0()]);
    let me = ident(20);
    let rec = recursive_getter("rec", "c::rec", me);
    assert!(mint_body(&rec, me, &[&ty], &Ay, &kernel, u64::MAX).is_empty());
    let (a, b) = (ident(21), ident(22));
    let fa = recursive_getter("ra", "c::rb", b);
    let fb = recursive_getter("rb", "c::ra", a);
    let bodies = [
        TinvBody { identity: Some(a), func: &fa, facts: None },
        TinvBody { identity: Some(b), func: &fb, facts: None },
    ];
    let (lemmas, _) = mint_arm_lemmas(&[&ty], &bodies, &Ay, &kernel, u64::MAX);
    assert!(lemmas.is_empty(), "{lemmas:?}");
}

#[test]
fn only_a_body_with_an_identity_is_eligible_and_a_duplicate_identity_mints_nothing() {
    let ty = p(vec![c0()]);
    let f = lt_getter(vec![]);
    let g = lt_getter(vec![]);
    let none = [TinvBody { identity: None, func: &f, facts: None }];
    assert!(mint_arm_lemmas(&[&ty], &none, &Ay, &kernel, u64::MAX).0.is_empty());
    let dup = [
        TinvBody { identity: Some(ident(5)), func: &f, facts: None },
        TinvBody { identity: Some(ident(5)), func: &g, facts: None },
    ];
    assert!(mint_arm_lemmas(&[&ty], &dup, &Ay, &kernel, u64::MAX).0.is_empty());
    assert_eq!(
        lemma_atoms(&Sigma { value: vec![Some(int("a")), Some(int("b"))], len: vec![None, None] })
            .map(|a| a.len()),
        Some(4)
    );
}

// ---------------------------------------------------------------------------------------
// The caller: arm facts over `c::P`
// ---------------------------------------------------------------------------------------

const LT: u32 = 101;

/// `fn bump_if(&mut self) { match self.lt() { Some(_) => self.i += 1, None => {} } }`,
/// the call `c::lt` carrying `call_id`. `arm`: which switch value reaches the increment
/// (`1` = `Some`, `0` = `None`). `between`: statements between the call and the switch
/// (in the switch block). `in_arm`: statements at the head of the increment arm.
fn bump_if(
    call_id: CalleeIdentity,
    arm: u128,
    between: Vec<Statement>,
    in_arm: Vec<Statement>,
) -> VerifiableFunction {
    bump_if_over(p_ty(), opt_u64(), "c::lt", 0, call_id, arm, between, in_arm)
}

/// [`bump_if`] over self type `s`, getter result type `opt`, getter `callee`, and the
/// incremented field `i`.
#[allow(clippy::too_many_arguments)]
fn bump_if_over(
    s: Ty,
    opt: Ty,
    callee: &str,
    i: usize,
    call_id: CalleeIdentity,
    arm: u128,
    between: Vec<Statement>,
    in_arm: Vec<Statement>,
) -> VerifiableFunction {
    let locals = vec![
        (Ty::Unit, None),
        (mut_ref(s.clone()), Some("self")),
        (opt, None),
        (shared_ref(s), None),
        (Ty::Int { width: 64, signed: true }, None),
        (Ty::Tuple(vec![u64_ty(), Ty::Bool]), None),
    ];
    let mut switch = between;
    switch.push(assign(Place::local(4), Rvalue::Discriminant(Place::local(2))));
    let mut add = in_arm;
    add.push(assign(
        Place::local(5),
        Rvalue::CheckedBinaryOp(BinOp::Add, Operand::Copy(self_field(1, i)), konst(1)),
    ));
    func(
        "bump_if",
        locals,
        1,
        vec![
            blk(
                0,
                vec![assign(
                    Place::local(3),
                    Rvalue::Ref {
                        mutable: false,
                        place: Place { local: 1, projections: vec![Projection::Deref] },
                    },
                )],
                call(callee, vec![Operand::Move(Place::local(3))], 2, 1, Some(call_id)),
            ),
            blk(
                1,
                switch,
                Terminator::SwitchInt {
                    discr: Operand::Move(Place::local(4)),
                    targets: vec![(arm, BlockId(2))],
                    otherwise: BlockId(4),
                    exhaustive_enum_unreachable: false,
                    span: SourceSpan::default(),
                },
            ),
            blk(
                2,
                add,
                Terminator::Assert {
                    cond: Operand::Move(field(5, 1)),
                    expected: false,
                    msg: AssertMessage::Overflow(BinOp::Add),
                    target: BlockId(3),
                    span: SourceSpan::default(),
                    unwind: UnwindEdge::Continue,
                },
            ),
            blk(
                3,
                vec![assign(self_field(1, i), Rvalue::Use(Operand::Move(field(5, 0))))],
                Terminator::Goto(BlockId(4)),
            ),
            blk(4, vec![], Terminator::Return),
        ],
    )
}

/// `i < n` and `i <= n` as lemmas of the body with identity `ident(LT)`. Built by hand:
/// the caller side does not depend on how a lemma was minted (the mint is pinned on the
/// real `peek` above, and end to end on the P1 type below); `c::lt` mints the same two
/// through the variant route, pinned above.
fn lt_lemmas() -> ArmLemmas {
    let (i, n) = (fv(FieldTerm::Value(0)), fv(FieldTerm::Value(1)));
    ArmLemmas::for_test([
        (ident(LT), "c::lt".into(), "c::P".into(), 1, lt(i.clone(), n.clone())),
        (ident(LT), "c::lt".into(), "c::P".into(), 1, le(i, n)),
    ])
}

fn sites(f: &VerifiableFunction, lemmas: &ArmLemmas) -> Vec<ArmSite> {
    let ty = p(vec![c0()]);
    let inventory: HashSet<CalleeIdentity> = [ident(LT), ident(LT + 1)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    arm_fact_sites(f, &inp, lemmas)
}

/// `(edge, ay verdict)` of every R part of `f` for `i <= n`, with `lemmas`.
fn return_parts(
    f: &VerifiableFunction,
    lemmas: &ArmLemmas,
) -> BTreeMap<Option<usize>, (Option<bool>, VerificationCondition)> {
    let types = [p(vec![c0()])];
    let inventory: HashSet<CalleeIdentity> = [ident(LT), ident(LT + 1)].into_iter().collect();
    let plan = BodyTinvPlan {
        types: &types,
        facts: None,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
        step_budget: u64::MAX,
    };
    let got = type_invariant_check_vcs_with_lemmas(f, &plan, lemmas).expect("walked");
    got.rows
        .into_iter()
        .filter(|(k, _)| k.point == TypeInvariantPoint::Return)
        .map(|(k, vc)| (k.edge, (ay(&vc), vc)))
        .collect()
}

#[test]
fn the_some_arm_fact_proves_the_increment_and_only_in_its_region() {
    let lemmas = lt_lemmas();
    let f = bump_if(ident(LT), 1, vec![], vec![]);
    let s = sites(&f, &lemmas);
    assert_eq!(s.len(), 1, "{s:?}");
    assert_eq!((s[0].call_block, s[0].seal, s[0].region), (BlockId(0), BlockId(1), BlockId(2)));
    assert_eq!(s[0].root, Place { local: 1, projections: vec![Projection::Deref] });
    assert!(s[0].facts.contains(&lt(int("self*.0"), int("self*.1"))), "{:?}", s[0].facts);

    let with = return_parts(&f, &lemmas);
    let without = return_parts(&f, &ArmLemmas::default());
    // The increment path (edge bb3): refuted without the lemma, proved with it.
    assert_eq!(without[&Some(3)].0, Some(false));
    assert_eq!(with[&Some(3)].0, Some(true));
    assert_eq!(with[&Some(3)].1.type_invariant_situatedness_refusal(), None);
    // The `None` path (edge bb1): the region `bb2` does not dominate it, so its VC is
    // byte-identical with and without the lemma (the fact is absent, not merely unused).
    assert_eq!(with[&Some(1)].1.formula, without[&Some(1)].1.formula);
    assert_eq!(with[&Some(1)].0, Some(true));
}

#[test]
fn the_none_arm_a_join_and_a_write_before_the_switch_get_no_arm_fact() {
    let lemmas = lt_lemmas();
    // The increment in the `None` arm: refuted, and no site (the `Some` arm is the
    // shared `Return` block, which has two predecessors).
    let f = bump_if(ident(LT), 0, vec![], vec![]);
    assert!(sites(&f, &lemmas).is_empty());
    assert_eq!(return_parts(&f, &lemmas)[&Some(3)].0, Some(false));
    // `self.i = self.n` between the call and the switch: the switch block is no longer
    // clean, so no site; the increment is refuted.
    let reset = vec![assign(self_field(1, 0), Rvalue::Use(Operand::Copy(self_field(1, 1))))];
    let f = bump_if(ident(LT), 1, reset.clone(), vec![]);
    assert!(sites(&f, &lemmas).is_empty());
    assert_eq!(return_parts(&f, &lemmas)[&Some(3)].0, Some(false));
    // The same write at the head of the `Some` arm: the site stands, the fact is sealed
    // at the call target (the OLD `i`), and the increment of the NEW `i` is refuted.
    let f = bump_if(ident(LT), 1, vec![], reset);
    assert_eq!(sites(&f, &lemmas).len(), 1);
    assert_eq!(return_parts(&f, &lemmas)[&Some(3)].0, Some(false));
    // A storage marker on the call destination in the switch block refuses the site.
    let f = bump_if(ident(LT), 1, vec![Statement::StorageDead(2)], vec![]);
    assert!(sites(&f, &lemmas).is_empty());
}

#[test]
fn a_join_of_two_calls_gets_no_arm_fact() {
    // `let o = if c { self.lt() } else { q.lt() }; match o { Some(_) => self.i += 1, .. }`
    // with both calls targeting the switch block (two predecessors).
    let lemmas = lt_lemmas();
    let mut f = bump_if(ident(LT), 1, vec![], vec![]);
    f.body.locals.push(LocalDecl { index: 6, ty: shared_ref(p_ty()), name: Some("q".into()) });
    f.body.locals.push(LocalDecl { index: 7, ty: Ty::Bool, name: Some("c".into()) });
    f.body.arg_count = 1;
    let n = f.body.blocks.len();
    // bb0 becomes the branch on `c`; the original call moves to a new block, beside a
    // second call on `q`.
    let first_call = f.body.blocks[0].clone();
    f.body.blocks[0] = blk(
        0,
        vec![assign(
            Place::local(7),
            Rvalue::Use(Operand::Constant(trust_types::ConstValue::Bool(true))),
        )],
        Terminator::SwitchInt {
            discr: Operand::Move(Place::local(7)),
            targets: vec![(0, BlockId(n + 1))],
            otherwise: BlockId(n),
            exhaustive_enum_unreachable: false,
            span: SourceSpan::default(),
        },
    );
    f.body.blocks.push(BasicBlock { id: BlockId(n), ..first_call });
    f.body.blocks.push(blk(
        n + 1,
        vec![],
        call("c::lt", vec![Operand::Copy(Place::local(6))], 2, 1, Some(ident(LT))),
    ));
    assert!(sites(&f, &lemmas).is_empty());
}

#[test]
fn an_inexact_identity_gets_no_arm_fact() {
    let lemmas = lt_lemmas();
    // Another body (another `DefId`).
    assert!(sites(&bump_if(ident(LT + 1), 1, vec![], vec![]), &lemmas).is_empty());
    // The same `DefId` at another instantiation (a generic getter at different substs).
    let other_substs = CalleeIdentity { substs_digest: [1, 0], ..ident(LT) };
    let f = bump_if(other_substs, 1, vec![], vec![]);
    assert!(sites(&f, &lemmas).is_empty());
    // A lemma keyed on the exact identity, about ANOTHER type, is not this type's.
    let foreign = ArmLemmas::for_test([(
        ident(LT),
        "c::lt".into(),
        "c::Q".into(),
        1,
        lt(fv(FieldTerm::Value(0)), fv(FieldTerm::Value(1))),
    )]);
    assert!(sites(&bump_if(ident(LT), 1, vec![], vec![]), &foreign).is_empty());
}

// ---------------------------------------------------------------------------------------
// P1 on real MIR: the arm site of `bump` and its region rail
// ---------------------------------------------------------------------------------------

fn p1_lemmas() -> ArmLemmas {
    let ty = p1_type();
    let (id, f) = fx(PEEK);
    let bodies = [TinvBody { identity: Some(id), func: &f, facts: None }];
    mint_arm_lemmas(&[&ty], &bodies, &Ay, &kernel, u64::MAX).0
}

#[test]
fn bumps_arm_site_is_the_continue_arm_of_branch_sealed_at_the_call_target() {
    let lemmas = p1_lemmas();
    let ty = p1_type();
    let (_, bump) = fx(BUMP);
    let inventory: HashSet<CalleeIdentity> =
        inventory().into_iter().filter_map(|(id, _)| id).collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let s = arm_fact_sites(&bump, &inp, &lemmas);
    assert_eq!(
        s,
        vec![ArmSite {
            call_block: BlockId(0),
            seal: BlockId(1),
            region: BlockId(4),
            root: Place { local: 1, projections: vec![Projection::Deref] },
            facts: vec![
                lt(int("self*.1"), int("self*.0__slice_len")),
                le(int("self*.1"), int("self*.0__slice_len")),
            ],
            dep: ArmLemmaDep { ty: P1.into(), callee: fx(PEEK).0, param: 1 },
            uses: [
                (
                    lt(fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0))),
                    lt(int("self*.1"), int("self*.0__slice_len"))
                ),
                (
                    le(fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0))),
                    le(int("self*.1"), int("self*.0__slice_len"))
                ),
            ]
            .into_iter()
            .map(|(phi, fact)| crate::type_invariant::arm_lemma::ArmLemmaUse {
                dep: ArmLemmaDep { ty: P1.into(), callee: fx(PEEK).0, param: 1 },
                phi,
                fact,
            })
            .collect(),
        }]
    );
}

/// END TO END on the P1 type with the REAL lemmas of the real `peek`:
/// `fn peek_if(&mut self) { match self.peek() { Some(_) => self.i += 1, None => {} } }`.
/// No call runs between the call target and the increment, so the coarse call havoc
/// (TINV-18) does not separate the sealed fact from the core: the increment part is
/// REFUTED without the lemma and PROVED, situated, with it. (`bump`'s `?` spelling has
/// `Try::branch` there, which havocs `*self` under the coarse rule; see
/// `p1_realmir_tests`.)
#[test]
fn the_real_peek_lemma_proves_a_direct_match_increment_over_the_p1_type() {
    let lemmas = p1_lemmas();
    assert_eq!(lemmas.len(), 2);
    let ty = p1_type();
    let (peek_id, _) = fx(PEEK);
    let (_, bump) = fx(BUMP);
    let self_ty = match &bump.body.locals[1].ty {
        Ty::Ref { inner, .. } => inner.as_ref().clone(),
        other => panic!("{other:?}"),
    };
    let opt = bump.body.locals[4].ty.clone();
    let f = bump_if_over(self_ty, opt, PEEK, 1, peek_id, 1, vec![], vec![]);
    let id = ty
        .conjuncts
        .iter()
        .find(|c| c.formula == le(fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0))))
        .expect("`i <= len(b)`")
        .id;
    let inventory: HashSet<CalleeIdentity> =
        inventory().into_iter().filter_map(|(id, _)| id).collect();
    let types = [ty.clone()];
    let parts = |lemmas: &ArmLemmas| -> BTreeMap<Option<usize>, (bool, Option<bool>)> {
        let plan = BodyTinvPlan {
            types: &types,
            facts: None,
            inventory: &inventory,
            models: &NoExactModels,
            may_run_user_drop: &|_| true,
            step_budget: u64::MAX,
        };
        type_invariant_check_vcs_with_lemmas(&f, &plan, lemmas)
            .expect("walked")
            .rows
            .into_iter()
            .filter(|(k, _)| k.point == TypeInvariantPoint::Return && k.conjunct == id)
            .map(|(k, vc)| (k.edge, (vc.type_invariant_situatedness_refusal().is_none(), ay(&vc))))
            .collect()
    };
    let without = parts(&ArmLemmas::default());
    let with = parts(&lemmas);
    assert_eq!(without[&Some(3)], (true, Some(false)));
    assert_eq!(with[&Some(3)], (true, Some(true)));
    assert_eq!(with[&Some(1)], without[&Some(1)]);
}

/// Rails 7 and 8 on a `&mut self` `peek`: a write of `self.i` AFTER `get` (in the
/// returning block) and a write BEFORE it (at the head of `bb0`).
///
/// Rail 7 is that the `get`-`Some` fact about the OLD `i` never becomes a lemma about the
/// NEW one: neither `i < len(b)` nor `i <= len(b)` may be minted after `self.i =
/// usize::MAX`. Since the merge of 2026-10-14 the after-write body mints (by elimination)
/// `len(b) <= i`, and it is TRUE: the returning block sets `i = usize::MAX`, and every
/// slice length is at most `usize::MAX` (`len(b) < i` would be true too, since `b:
/// &[u8]` is at most `isize::MAX` long). It proves because `conjoin_slice_len_bounds`
/// now bounds EVERY `__slice_len` symbol above, `usize::MAX` where the element is not
/// known to be non-zero-sized, which is where the parameter-reached `self*.0__slice_len`
/// lands (`len_ceiling`, 520bbad1c2b); before it that symbol had only `>= 0`, so nothing
/// proved and this rail pinned an empty mint. The old `is_empty()` failed on the merged
/// tree (measured); WHICH atom minted was not printed, and the assertions below pin it.
/// The `get` fact cannot reach the after-write probe's `A` part at all: its returning
/// block carries the write, so `guards::clean_variant_switch_target` refuses the
/// `copied` hop's switch.
#[test]
fn a_write_after_get_mints_nothing_and_a_write_before_get_is_measured() {
    let (id, f) = fx(PEEK);
    let ty = p1_type();
    let write = serde_json::json!({ "Assign": {
        "place": { "local": 1, "projections": ["Deref", { "Field": 1 }] },
        "rvalue": { "Use": { "Constant": { "Uint": [18446744073709551615u64, 64] } } },
        "span": { "file": "", "line_start": 0, "col_start": 0, "line_end": 0, "col_end": 0 } } });
    let mut_self = |block: usize| {
        let write = write.clone();
        mutate(&f, move |v| {
            v["body"]["locals"][1]["ty"]["Ref"]["mutable"] = serde_json::json!(true);
            v["body"]["blocks"][block]["stmts"].as_array_mut().unwrap().insert(0, write);
        })
    };
    // After `get`: `let r = self.b.get(self.i).copied(); self.i = usize::MAX; r`.
    let after = mut_self(2);
    let (v1, l0) = (fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0)));
    let got: Vec<Formula> = phis(&mint_body(&after, id, &[&ty], &Ay, &kernel, u64::MAX));
    // The stale `get`-`Some` atoms: FALSE at this `Return` (`i == usize::MAX`).
    for stale in [lt(v1.clone(), l0.clone()), le(v1.clone(), l0.clone())] {
        assert!(!got.contains(&stale), "stale `get` fact minted as {stale:?}: {got:?}");
    }
    // Only the atoms `i == usize::MAX` makes true, and the weaker of them always.
    let true_atoms = [lt(l0.clone(), v1.clone()), le(l0.clone(), v1.clone())];
    assert!(got.iter().all(|phi| true_atoms.contains(phi)), "{got:?}");
    assert!(got.contains(&le(l0, v1)), "{got:?}");
    // Before `get`: `self.i = usize::MAX; self.b.get(self.i).copied()`. The `get`-`Some`
    // fact reads the NEW `i` (no stale fact can be minted), so the lemma is still TRUE.
    // MEASURED 2026-10-06: it does not PROVE, because `&mut self` over a pointer-carrying
    // `P` is havocked at `get`/`copied` by the coarse TINV-18 rule, which separates the
    // `bb0` slice-length ties from the `Return` names. Precision only.
    let before = mut_self(0);
    let got: Vec<Formula> = phis(&mint_body(&before, id, &[&ty], &Ay, &kernel, u64::MAX));
    assert!(got.is_empty(), "{got:?}");
}

// ---------------------------------------------------------------------------------------
// The probe's root and enumeration gates (adversarial review of `fd530b0a54`, 2026-10-06)
// ---------------------------------------------------------------------------------------

/// Real extractions (`crates/trust-vcgen/tests/fixtures/tinv_arm_lemma_probe_gates_fx.json`,
/// by a stage 1 reporting `0c4b132ee`, `--crate-name tinvp1`, over the P1 struct
/// `pub struct P<'a> { pub b: &'a [u8], pub i: usize }`) of
///
/// ```text
/// pub fn plain<'a>(s: &'a P<'a>, _t: &'a P<'a>) -> Option<u8> { s.b.get(s.i).copied() }
/// pub fn reseat<'a>(mut s: &'a P<'a>, t: &'a P<'a>) -> Option<u8> {
///     s = t;
///     s.b.get(s.i).copied()
/// }
/// impl P<'_> { pub fn peek_raw_whole(&mut self) -> Option<u8> {
///     let r = &raw mut *self;
///     let x = self.b.get(self.i).copied();
///     unsafe { (*r).i = usize::MAX; }
///     x
/// } }
/// pub fn moved<'a>(p: &mut P<'a>) -> Option<u8> {   // extracted with -Zmir-opt-level=0
///     let q = p;                                     // (at the default level CopyProp
///     q.i = q.b.len();                               // merges `q` into `p`)
///     Some(0)
/// }
/// ```
/// each with the `copied` tag added as for the P1 fixture ([`with_copied_tag`]).
const GATES: &str = include_str!("../../tests/fixtures/tinv_arm_lemma_probe_gates_fx.json");

fn gate_fx(name: &str) -> VerifiableFunction {
    let all: Vec<VerifiableFunction> = serde_json::from_str(GATES).expect("gates fixture");
    with_copied_tag(all.into_iter().find(|f| f.def_path == name).expect("in the gates fixture"))
}

/// B: `reseat` proves `i < len(b)` of `*t` at `Return`, under `*s`'s name; minted at
/// parameter 1, a caller would assume it of the argument bound to `s`. `s` is written, so
/// its pointee is not a lemma root (`lemma_param_root`, the `canonical` gate) and
/// nothing is minted. `plain` (same body, `s` never written) is the control.
#[test]
fn a_getter_that_reseats_its_parameter_mints_nothing() {
    let ty = p1_type();
    let star = |l: usize| Place { local: l, projections: vec![Projection::Deref] };
    let (v1, l0) = (fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0)));

    let plain = gate_fx("tinvp1::plain");
    assert_eq!(
        crate::type_invariant::obligations::lemma_param_root(&plain, &star(1)),
        Some(star(1))
    );
    let got = mint_body(&plain, ident(40), &[&ty], &Ay, &kernel, u64::MAX);
    assert!(got.iter().all(|l| l.param() == 1), "{got:#?}");
    assert_eq!(phis(&got), vec![lt(v1.clone(), l0.clone()), le(v1, l0)], "{got:#?}");

    let reseat = gate_fx("tinvp1::reseat");
    assert!(
        matches!(&reseat.body.blocks[0].stmts[0], Statement::Assign { place, rvalue: Rvalue::Use(Operand::Copy(src)), .. }
            if *place == Place::local(1) && *src == Place::local(2)),
        "the fixture reseats `s` first"
    );
    assert_eq!(crate::type_invariant::obligations::lemma_param_root(&reseat, &star(1)), None);
    let got = mint_body(&reseat, ident(41), &[&ty], &Ay, &kernel, u64::MAX);
    assert!(got.is_empty(), "{got:#?}");
}

/// B (audit): the hand-built row skips `obligation_points`, and with it the refusal of an
/// unattributable write of `S`. `peek_raw_whole` writes `self.i = usize::MAX` through a
/// raw pointer to `*self` after `get`: the enumeration refuses the body for `P`, so the
/// probe mints nothing for it. MEASURED (2026-10-06): with the enumeration gate disabled
/// this body still mints nothing (the walk itself does not prove `i < len(b)` past the raw
/// store), so this rail pins the refusal, not a false lemma the gate alone prevents: the
/// gate is defense in depth for writes the walk might not see.
#[test]
fn a_getter_the_enumeration_refuses_mints_nothing() {
    let ty = p1_type();
    let f = gate_fx("tinvp1::P::<'_>::peek_raw_whole");
    let inventory: HashSet<CalleeIdentity> = [ident(42)].into_iter().collect();
    let inp = TinvInputs {
        ty: &ty,
        inventory: &inventory,
        models: &NoExactModels,
        may_run_user_drop: &|_| true,
    };
    let refusal = crate::type_invariant::obligations::obligation_points(&f, None, &inp);
    assert!(
        matches!(&refusal, Err(TinvObligationRefusal::Write(why)) if why.contains("raw pointer")),
        "{refusal:?}"
    );
    let got = mint_body(&f, ident(42), &[&ty], &Ay, &kernel, u64::MAX);
    assert!(got.is_empty(), "{got:#?}");
}

// ---------------------------------------------------------------------------------------
// C: a certificate carries the lemmas its rows consumed
// ---------------------------------------------------------------------------------------

/// Real extraction (`tinv_arm_lemma_cert_fx.json`, same stage 1 and struct) of
///
/// ```text
/// impl<'a> P<'a> {
///     pub fn new(b: &'a [u8]) -> P<'a> { P { b, i: 0 } }
///     pub fn peek(&self) -> Option<u8> { self.b.get(self.i).copied() }
///     pub fn peek_if(&mut self) { match self.peek() { Some(_) => self.i += 1, None => {} } }
/// }
/// ```
/// `peek`'s identity is the one `peek_if`'s call names; `new` and `peek_if` have none.
const CERT: &str = include_str!("../../tests/fixtures/tinv_arm_lemma_cert_fx.json");

/// C: `peek_if`'s `Some`-arm increment row proves `i <= len(b)` only under `peek`'s lemma
/// `i < len(b)`, so the published certificate for `P` CARRIES `peek`'s lemmas, each with
/// the `A`-part VC and kernel evidence it was minted on, and [`TypeInvariantCertificate::replay`]
/// re-checks them: a certificate whose lemma evidence is swapped for another VC's fails
/// replay although every row still replays.
#[test]
fn a_certificate_carries_and_replays_the_lemmas_its_rows_consumed() {
    let (v1, l0) = (fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0)));
    let all: Vec<VerifiableFunction> = serde_json::from_str::<Vec<VerifiableFunction>>(CERT)
        .expect("cert fixture")
        .into_iter()
        .map(with_copied_tag)
        .collect();
    let peek_id = all
        .iter()
        .flat_map(|f| &f.body.blocks)
        .find_map(|b| match &b.terminator {
            Terminator::Call { func, callee_identity: Some(id), .. }
                if func == "tinvp1::P::<'_>::peek" =>
            {
                Some(*id)
            }
            _ => None,
        })
        .expect("peek_if calls peek");
    let mut ty = p1_type();
    ty.conjuncts.retain(|c| c.formula == le(v1.clone(), l0.clone()));
    assert_eq!(ty.conjuncts.len(), 1, "{:?}", ty.conjuncts);
    let bodies: Vec<TinvBody<'_>> = all
        .iter()
        .map(|f| TinvBody {
            identity: (f.def_path == "tinvp1::P::<'_>::peek").then_some(peek_id),
            func: f,
            facts: None,
        })
        .collect();
    let certify = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
    };
    let replay = |vc: &VerificationCondition, e: &_| trust_certify::replay_vc_evidence(vc, e);
    let run = |bodies: &[TinvBody<'_>]| {
        houdini(std::slice::from_ref(&ty), bodies, &NoExactModels, &|_| true, &Ay, &certify, BUDGET)
    };
    let out = run(&bodies);
    assert!(out.refused.is_empty(), "{:?}", out.refused);
    let cert = out.certificates.get(P1).unwrap_or_else(|| panic!("P certifies: {:#?}", out.notes));
    assert_eq!(cert.conjuncts().len(), 1);
    let carried: Vec<(CalleeIdentity, usize, Formula)> = cert
        .lemmas()
        .iter()
        .map(|l| (l.lemma().callee(), l.lemma().param(), l.lemma().phi().clone()))
        .collect();
    assert_eq!(
        carried,
        vec![(peek_id, 1, lt(v1.clone(), l0.clone())), (peek_id, 1, le(v1, l0))],
        "{carried:#?}"
    );
    for l in cert.lemmas() {
        let minted = l.lemma().vc().expect("a minted lemma carries its row");
        assert_eq!((&minted.kind, &minted.formula), (&l.vc().kind, &l.vc().formula));
        assert!(replay(l.vc(), l.evidence()));
    }
    assert!(cert.replay(&replay));

    // Tamper: the first lemma's evidence replaced by the second's. Every ROW still
    // replays; the certificate does not.
    let mut forged = cert.clone();
    forged.lemmas[0].evidence = forged.lemmas[1].evidence.clone();
    assert!(forged.rows().iter().all(|r| replay(r.vc(), r.evidence())));
    assert!(!forged.replay(&replay));

    // The consuming rows record exactly which lemmas they assumed, and the sealed
    // hypothesis is the use's fact up to version tokens.
    let used: Vec<&RowArmUse> = cert.rows().iter().flat_map(|r| r.lemma_uses()).collect();
    assert!(!used.is_empty(), "the Some-arm increment row assumed peek's lemmas");
    for u in &used {
        assert_eq!(u.lemma.dep.callee, peek_id);
        assert_eq!(strip_versions(&u.sealed), u.lemma.fact);
    }

    // Swap in a DIFFERENT VALID lemma (another φ, its own VC and evidence, which replay
    // on their own): the slot of `i < len(b)` now holds a second copy of `i <= len(b)`.
    // Every carried lemma and every row still replays in the kernel; the certificate does
    // not, because a row assumed `i < len(b)` and no carried lemma is it.
    let mut swapped = cert.clone();
    swapped.lemmas[0] = swapped.lemmas[1].clone();
    assert!(swapped.lemmas().iter().all(|l| replay(l.vc(), l.evidence()) && l.well_formed()));
    assert!(swapped.rows().iter().all(|r| replay(r.vc(), r.evidence())));
    assert!(!swapped.replay(&replay));

    // Relabel a lemma: keep its VC and evidence (valid) but claim the other φ. Its VC
    // refutes `¬(i <= len(b))`, not `¬(i < len(b))`: not well formed, replay fails.
    let mut relabelled = cert.clone();
    let other_phi = relabelled.lemmas[1].lemma().phi().clone();
    let other_core = relabelled.lemmas[1].lemma().core().cloned();
    relabelled.lemmas[0].lemma.relabel_for_test(None, Some((other_phi, other_core)));
    assert!(replay(relabelled.lemmas[0].vc(), relabelled.lemmas[0].evidence()));
    assert!(!relabelled.lemmas[0].well_formed());
    assert!(!relabelled.replay(&replay));

    // Another callee: the lemma claims to be about a different getter's identity.
    let mut other_callee = cert.clone();
    other_callee.lemmas[0].lemma.relabel_for_test(Some(ident(999)), None);
    assert!(!other_callee.replay(&replay));
}

/// C (control): without `peek` in the run nothing mints, the `Some`-arm increment is not
/// proved, and `P` gets no certificate; so the certificate above DEPENDS on the lemma it
/// carries. And a run whose rows consumed no lemma publishes a certificate with none.
#[test]
fn a_certificate_without_a_consumed_lemma_carries_none() {
    let (v1, l0) = (fv(FieldTerm::Value(1)), fv(FieldTerm::Len(0)));
    let all: Vec<VerifiableFunction> = serde_json::from_str::<Vec<VerifiableFunction>>(CERT)
        .expect("cert fixture")
        .into_iter()
        .map(with_copied_tag)
        .collect();
    let mut ty = p1_type();
    ty.conjuncts.retain(|c| c.formula == le(v1.clone(), l0.clone()));
    let certify = |vc: &VerificationCondition| {
        let evidence = trust_certify::certify_vc(vc)?;
        trust_certify::replay_vc_evidence(vc, &evidence).then_some(evidence)
    };
    let run = |names: &[&str]| {
        let bodies: Vec<TinvBody<'_>> = all
            .iter()
            .filter(|f| names.contains(&f.def_path.as_str()))
            .map(|f| TinvBody { identity: None, func: f, facts: None })
            .collect();
        houdini(
            std::slice::from_ref(&ty),
            &bodies,
            &NoExactModels,
            &|_| true,
            &Ay,
            &certify,
            BUDGET,
        )
    };
    let no_peek = run(&["tinvp1::P::<'_>::new", "tinvp1::P::<'_>::peek_if"]);
    assert!(no_peek.arm_lemmas.is_empty());
    assert!(no_peek.certificates.get(P1).is_none(), "{:#?}", no_peek.notes);
    let new_only = run(&["tinvp1::P::<'_>::new"]);
    let cert = new_only.certificates.get(P1).unwrap_or_else(|| panic!("{:#?}", new_only.notes));
    assert!(cert.lemmas().is_empty());
}

/// VARIANT-ARM-DUP-EDGE-1 (2026-10-06): the `Some` region must be the ONLY one of the
/// switch's edges into its block. With `bump_if`'s switch `[0: bb2, 1: bb2] otherwise
/// bb4` (rustc's lowering when two arms share a block), `None` also runs the increment:
/// the deduplicated predecessor relation read `bb2` as entered only from the switch and
/// made it the `Some` region, so the increment PROVED under `i < n` on the `None` path
/// too. No site now, and the increment part is refuted. Likewise when `bb2` is the `Some`
/// target AND the `otherwise` target.
#[test]
fn an_arm_two_switch_edges_enter_gets_no_arm_fact() {
    let lemmas = lt_lemmas();
    let with_switch = |targets: Vec<(u128, BlockId)>, otherwise: BlockId| {
        let mut f = bump_if(ident(LT), 1, vec![], vec![]);
        let Terminator::SwitchInt { targets: t, otherwise: o, .. } =
            &mut f.body.blocks[1].terminator
        else {
            panic!("bb1 switches on the tag");
        };
        *t = targets;
        *o = otherwise;
        f
    };
    let dup = with_switch(vec![(0, BlockId(2)), (1, BlockId(2))], BlockId(4));
    assert!(sites(&dup, &lemmas).is_empty(), "{:?}", sites(&dup, &lemmas));
    assert_eq!(return_parts(&dup, &lemmas)[&Some(3)].0, Some(false));
    let with_otherwise = with_switch(vec![(1, BlockId(2))], BlockId(2));
    assert!(sites(&with_otherwise, &lemmas).is_empty());
    // Control: the `Some` label alone into bb2 (and `None` to bb4) keeps the site.
    let some_only = with_switch(vec![(0, BlockId(4)), (1, BlockId(2))], BlockId(4));
    assert_eq!(sites(&some_only, &lemmas).len(), 1);
}

/// Backstop (re-review of `bf5f1dc8b5`): a lemma root `*p` also needs the POINTER to stay
/// in place (`local_defs::pointer_is_pinned`, no `local_pointee_may_escape`). `moved`
/// moves `p` into `q` (`_2 = move _1`) and writes `*p` through `q`: `p` escapes, so its
/// pointee is no lemma root and nothing is minted. `plain` still mints (control).
/// The pre-existing identity gate (`canonical`'s
/// `is_single_static_assignment_modulo_pointee_borrows`) ACCEPTS the moved-out `p`: the
/// backstop alone refuses it. MEASURED (2026-10-06): with the backstop disabled the root
/// is admitted and the body still mints nothing (the walk versions `p*` past the store
/// through `q`): defense in depth, not a measured false lemma.
#[test]
fn a_getter_that_moves_its_parameter_mints_nothing() {
    let ty = p1_type();
    let star = |l: usize| Place { local: l, projections: vec![Projection::Deref] };
    let moved = gate_fx("tinvp1::moved");
    assert!(
        matches!(&moved.body.blocks[0].stmts[1], Statement::Assign { place, rvalue: Rvalue::Use(Operand::Move(src)), .. }
            if *place == Place::local(2) && *src == Place::local(1)),
        "the fixture moves `p` into `q`"
    );
    assert_eq!(crate::type_invariant::obligations::lemma_param_root(&moved, &star(1)), None);
    assert!(crate::generate::local_pointee_may_escape(&moved, 1), "the move is an escape");
    // The pre-existing identity gate does NOT see the move: only the backstop refuses.
    assert!(crate::local_defs::is_single_static_assignment_modulo_pointee_borrows(&moved, 1));
    let plain_f = gate_fx("tinvp1::plain");
    assert!(crate::local_defs::pointer_is_pinned(&plain_f, 1));
    assert!(!crate::generate::local_pointee_may_escape(&plain_f, 1));
    let got = mint_body(&moved, ident(43), &[&ty], &Ay, &kernel, u64::MAX);
    assert!(got.is_empty(), "{got:#?}");
    let plain = gate_fx("tinvp1::plain");
    assert!(!mint_body(&plain, ident(40), &[&ty], &Ay, &kernel, u64::MAX).is_empty());
}
