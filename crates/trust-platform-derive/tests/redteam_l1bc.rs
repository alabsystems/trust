//! Red-team attacks on L1b (typed completeness) and L1c (the X2 replay
//! token), kept as regression tests. Every `attack_*` test asserts the SOUND
//! outcome the claims promise; each hole the red team found failed one of
//! them and is closed:
//!
//! * H1 (A6): an atom naming no label got a clean "exhaustive" answer. The
//!   payload now declares its vocabulary and NativeTyEngine refuses an atom
//!   (or a state label) outside it, and a payload without one.
//! * H2 (A8): a duplicate key in the payload's `labels` map was accepted
//!   (last wins). Any duplicate JSON key is now a payload error.
//! * H3 (C5): a token was minted for a trace that refutes nothing (nothing
//!   wanted, or `policy_exec`). A token now wants violation propositions
//!   only, and its final state must be a concrete violation.
//! * H4 (C7a/b/d): `Derived`'s fields were `pub`, so a clone could be edited
//!   and a token minted from it. The fields are now read-only outside the
//!   crate (each edit is a `compile_fail,E0616` doctest on `Derived`), a
//!   horizon stutter that moves is refused, and a token records the program
//!   and environment it replayed on (`ReplayToken::is_of`, C7 below; the
//!   in-crate edits are unit tests in `src/tests.rs`).
//!
//! Claims under attack:
//! 1. `check_refutation_only` (via `classify`) never yields
//!    `NoCounterexample { Exhaustive }` unless ty explored exhaustively the
//!    machine and formula the producer meant.
//! 2. A `ReplayToken` cannot exist unless the trace refutes, every step
//!    re-executed, every environment step cites its RL clause, every std
//!    step cites its row.
//! 3. `proof_strength` stays `None` on every refutation-only path and
//!    nothing enters a proved/certified total.

use trust_platform_derive::derive::{DeriveOptions, Derived, HALT};
use trust_platform_derive::explore::ActionKey;
use trust_platform_derive::fixtures::{self, Fixture};
use trust_platform_derive::program::{EventProgram, StmtKind, StmtRef};
use trust_platform_derive::property::{self, premised};
use trust_platform_derive::trace::{
    RL_CLAUSES, RL_FOREIGN, RL_IMAGE_EXIT, RL_INIT, Replay, ReplayToken, TokenError,
};
use trust_platform_derive::{derive, fd_inherit_formula, non_vacuity_formula};
use trust_router::full_verification::{
    FullVerificationEngine, FullVerificationPolicy, NativeTyEngine, RefutationCompleteness,
    RefutationOnlyVerdict,
};
use trust_types::fx::FxHashMap;
use trust_types::{
    LivenessProperty, SingleWriterEvidence, StateMachineMetadata, TY_TEMPORAL_MODEL_METADATA_KEY,
    TY_TEMPORAL_MODEL_SCHEMA_REFUTATION_ONLY, TY_TEMPORAL_MODEL_SCHEMA_VERSION, TemporalOperator,
    TyTemporalModelPayload, VcKind,
};
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine, VerificationRunStatus,
    VerifierExecutionContext,
};

// ---------------------------------------------------------------- helpers

fn obligation(id: &str, kind: ObligationKind, metadata: Vec<MetadataEntry>) -> TrustObligation {
    TrustObligation {
        obligation_id: format!("vc:redteam::{id}:temporal_safety:0"),
        kind,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("red-team {id}"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata,
    }
}

fn entry(key: &str, value: String) -> MetadataEntry {
    MetadataEntry { key: key.to_string(), value }
}

/// A refutation-only payload whose vocabulary is the mmap model's one atom
/// (`bad`), so each attack below reaches the check it attacks rather than
/// the vocabulary gate.
fn ro_value(kind: &VcKind) -> String {
    ro_value_with(kind, Some(&["bad"]))
}

fn ro_value_with(kind: &VcKind, vocabulary: Option<&[&str]>) -> String {
    let mut p = TyTemporalModelPayload::refutation_only(kind).expect("ty-owned");
    if let Some(atoms) = vocabulary {
        p = p.with_vocabulary(atoms.iter().map(|a| (*a).to_string()));
    }
    p.to_metadata_value().expect("serializes")
}

fn full_value(kind: &VcKind) -> String {
    TyTemporalModelPayload::from_vc_kind(kind).expect("ty-owned").to_metadata_value().expect("ser")
}

fn temporal(property: &str, md: StateMachineMetadata) -> VcKind {
    VcKind::Temporal { property: property.to_string(), machine: Some(md) }
}

fn mmap(single_writer: SingleWriterEvidence) -> StateMachineMetadata {
    StateMachineMetadata::mmap_temporal_model(single_writer)
}

fn bundle_of(id: &str, obligations: Vec<TrustObligation>) -> TrustContractBundle {
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{id}"),
        BundleSubject::Function {
            crate_name: "redteam".to_string(),
            path: format!("redteam::{id}"),
        },
    );
    bundle.obligations = obligations;
    bundle
}

/// The wire evidence of one obligation through NativeTyEngine::verify.
fn wire(o: &TrustObligation) -> Option<trust_verifier_api::ObligationEvidence> {
    NativeTyEngine::new().verify(&bundle_of("wire", vec![o.clone()]), std::slice::from_ref(o)).pop()
}

fn is_exhaustive(v: &RefutationOnlyVerdict) -> bool {
    matches!(
        v,
        RefutationOnlyVerdict::NoCounterexample {
            completeness: RefutationCompleteness::Exhaustive
        }
    )
}

fn derived(f: &Fixture) -> Derived {
    derive(&f.program, &f.env, &DeriveOptions::default())
        .unwrap_or_else(|e| panic!("{}: {e}", f.name))
}

/// ty's typed answer on a derived model, through the derive crate's own
/// vocabulary-vetted payload.
fn ty_on(d: &Derived, formula: &str) -> RefutationOnlyVerdict {
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let o = obligation(
        d.name(),
        ObligationKind::TemporalSafety,
        vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, payload.to_metadata_value().expect("ser"))],
    );
    NativeTyEngine::new().check_refutation_only(&o)
}

fn ty_trace(d: &Derived, formula: &str) -> Vec<usize> {
    match ty_on(d, formula) {
        RefutationOnlyVerdict::Counterexample { trace } => trace,
        v => panic!("{}: `{formula}` must be refuted: {v:?}", d.name()),
    }
}

fn no_strip() -> (Fixture, Derived, Vec<usize>, String) {
    let f = fixtures::spawnfd::no_strip();
    let d = derived(&f);
    let trace = ty_trace(&d, &fd_inherit_formula(&f.premises));
    let want = premised(property::VIOLATION, &f.premises);
    (f, d, trace, want)
}

// ======================================================= claim 1 (L1b)

/// A1. Wrong / near-miss metadata keys: the payload is not transported, so
/// the answer must be Inconclusive.
#[test]
fn attack_a1_wrong_metadata_keys_are_inconclusive() {
    let ok = ro_value(&temporal("AG !bad", mmap(SingleWriterEvidence::Verified)));
    let k = TY_TEMPORAL_MODEL_METADATA_KEY;
    for key in [
        String::new(),
        k.to_uppercase(),
        format!("{k} "),
        format!(" {k}"),
        k[..k.len() - 1].to_string(),
        format!("{k}.v2"),
    ] {
        let o = obligation("a1", ObligationKind::TemporalSafety, vec![entry(&key, ok.clone())]);
        let v = NativeTyEngine::new().check_refutation_only(&o);
        assert!(matches!(v, RefutationOnlyVerdict::Inconclusive { .. }), "key {key:?}: {v:?}");
    }
}

/// A2. Schema spoofs and malformed payload JSON: Inconclusive, never an
/// answer.
#[test]
fn attack_a2_schema_spoofs_and_malformed_json_are_inconclusive() {
    let kind = temporal("AG !bad", mmap(SingleWriterEvidence::Verified));
    let ro = ro_value(&kind);
    let r = TY_TEMPORAL_MODEL_SCHEMA_REFUTATION_ONLY;
    let mut bad: Vec<(String, String)> = vec![
        ("uppercase schema".into(), ro.replace(r, &r.to_uppercase())),
        ("schema + space".into(), ro.replace(r, &format!("{r} "))),
        ("empty schema".into(), ro.replace(r, "")),
        ("truncated json".into(), ro[..ro.len() / 2].to_string()),
        ("not json".into(), "AG !bad".to_string()),
        ("null".into(), "null".to_string()),
        ("empty".into(), String::new()),
    ];
    // A duplicate `schema_version` field (refutation-only + full).
    let dup = ro.replacen(
        "\"schema_version\"",
        &format!("\"schema_version\":\"{TY_TEMPORAL_MODEL_SCHEMA_VERSION}\",\"schema_version\""),
        1,
    );
    bad.push(("duplicate schema_version field".into(), dup));
    for (what, value) in bad {
        let o = obligation(
            "a2",
            ObligationKind::TemporalSafety,
            vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, value)],
        );
        let v = NativeTyEngine::new().check_refutation_only(&o);
        assert!(matches!(v, RefutationOnlyVerdict::Inconclusive { .. }), "{what}: {v:?}");
    }
    // A FULL payload (no refutation-only marker) is never read as a
    // refutation-only answer.
    let o = obligation(
        "a2-full",
        ObligationKind::TemporalSafety,
        vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, full_value(&kind))],
    );
    assert!(matches!(
        NativeTyEngine::new().check_refutation_only(&o),
        RefutationOnlyVerdict::Inconclusive { .. }
    ));
}

/// A3. Duplicate metadata entries in both orders: the typed answer is never
/// `NoCounterexample` unless the FIRST entry is a sound refutation-only one.
#[test]
fn attack_a3_duplicate_entries_typed_answer() {
    let kind = temporal("AG !bad", mmap(SingleWriterEvidence::Verified));
    let k = TY_TEMPORAL_MODEL_METADATA_KEY;
    for (what, md) in [
        ("malformed then ro", vec![entry(k, "{".into()), entry(k, ro_value(&kind))]),
        ("full then ro", vec![entry(k, full_value(&kind)), entry(k, ro_value(&kind))]),
    ] {
        let o = obligation("a3", ObligationKind::TemporalSafety, md);
        let v = NativeTyEngine::new().check_refutation_only(&o);
        assert!(matches!(v, RefutationOnlyVerdict::Inconclusive { .. }), "{what}: {v:?}");
    }
}

/// A4. Every non-CTL / unchecked payload shape and every malformed machine:
/// Inconclusive (in particular: never NoCounterexample).
#[test]
fn attack_a4_unchecked_shapes_and_malformed_machines_are_inconclusive() {
    let live = |operator, consequent: Option<&str>| VcKind::Liveness {
        property: LivenessProperty {
            name: "p".into(),
            operator,
            predicate: "bad".into(),
            consequent: consequent.map(str::to_string),
            fairness: Vec::new(),
        },
        machine: Some(mmap(SingleWriterEvidence::Verified)),
    };
    let mut kinds: Vec<(String, TyTemporalModelPayload)> = Vec::new();
    let ro = |k: &VcKind| {
        TyTemporalModelPayload::refutation_only(k)
            .expect("ty-owned")
            .with_vocabulary(["bad".to_string()])
    };
    for (what, k) in [
        ("liveness eventually", live(TemporalOperator::Eventually, None)),
        ("liveness always", live(TemporalOperator::Always, None)),
        ("liveness always-eventually", live(TemporalOperator::AlwaysEventually, None)),
        ("liveness leads-to", live(TemporalOperator::LeadsTo, Some("bad"))),
        (
            "temporal without machine",
            VcKind::Temporal { property: "AG !bad".into(), machine: None },
        ),
        ("deadlock", VcKind::Deadlock),
        ("dead state", VcKind::DeadState { state: "BadAccess".into() }),
    ] {
        kinds.push((what.to_string(), ro(&k)));
    }
    // A non-temporal kind under the refutation-only marker (struct literal:
    // `refutation_only` refuses it).
    kinds.push((
        "non-temporal kind".into(),
        TyTemporalModelPayload {
            schema_version: TY_TEMPORAL_MODEL_SCHEMA_REFUTATION_ONLY.to_string(),
            vc_kind: VcKind::DivisionByZero,
            vocabulary: Some(["bad".to_string()].into()),
        },
    ));
    // Malformed machines.
    let good = mmap(SingleWriterEvidence::Verified);
    let mut no_init = good.clone();
    no_init.init_states.clear();
    let mut two_inits = good.clone();
    two_inits.init_states = vec![0, 1];
    let mut far_init = good.clone();
    far_init.init_states = vec![99];
    let mut dangling = good.clone();
    dangling.transitions.push((1, "x".into(), 99));
    let mut far_label = good.clone();
    far_label.labels.insert(99, vec!["bad".into()]);
    let empty = StateMachineMetadata {
        states: Vec::new(),
        init_states: Vec::new(),
        transitions: Vec::new(),
        labels: FxHashMap::default(),
    };
    for (what, md) in [
        ("no initial state", no_init),
        ("two initial states", two_inits),
        ("initial out of range", far_init),
        ("dangling transition", dangling),
        ("label out of range", far_label),
        ("empty machine", empty),
    ] {
        kinds.push((what.to_string(), ro(&temporal("AG !bad", md))));
    }
    // Formulas ty cannot check as CTL.
    for f in ["", "AG", "G !bad", "[] !bad", "AG !(bad", "AG !fd-inherit violation", "AG !bad)"] {
        kinds.push((format!("formula {f:?}"), ro(&temporal(f, mmap(SingleWriterEvidence::None)))));
    }
    for (what, payload) in kinds {
        let o = obligation(
            "a4",
            ObligationKind::TemporalSafety,
            vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, payload.to_metadata_value().expect("ser"))],
        );
        let v = NativeTyEngine::new().check_refutation_only(&o);
        assert!(
            !matches!(v, RefutationOnlyVerdict::NoCounterexample { .. }),
            "{what}: answered {v:?}"
        );
        // And the wire never proves.
        if let Some(ev) = wire(&o) {
            assert!(ev.proof_strength.is_none(), "{what}: {ev:#?}");
            assert_ne!(ev.status, EvidenceStatus::Proved, "{what}");
        }
    }
}

/// A5. Obligation kinds ty does not own: Inconclusive even with a perfect
/// payload.
#[test]
fn attack_a5_unowned_obligation_kinds_are_inconclusive() {
    let ok = ro_value(&temporal("AG !bad", mmap(SingleWriterEvidence::Verified)));
    for kind in [
        ObligationKind::Assertion,
        ObligationKind::Invariant,
        ObligationKind::MemorySafety,
        ObligationKind::Termination,
    ] {
        let o =
            obligation("a5", kind.clone(), vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, ok.clone())]);
        let v = NativeTyEngine::new().check_refutation_only(&o);
        assert!(matches!(v, RefutationOnlyVerdict::Inconclusive { .. }), "{kind:?}: {v:?}");
    }
}

/// A6 (H1). An atom that parses but names no label of the machine (a
/// misspelt `bad`): the multi-writer machine HAS a reachable `bad` state, so
/// a "no counterexample, exhaustive" answer here hides a real refutation
/// (and `AG bda` would refute spuriously). L1b's plan: "a malformed atom
/// gives Inconclusive"; FC-7: unknown spellings are hard errors. Before the
/// fix the typed API answered `NoCounterexample { Exhaustive }`.
#[test]
fn attack_a6_atom_naming_no_label_is_not_an_exhaustive_no_counterexample() {
    let typed = |value: String| {
        let o = obligation(
            "a6",
            ObligationKind::TemporalSafety,
            vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, value)],
        );
        (NativeTyEngine::new().check_refutation_only(&o), wire(&o).expect("one evidence"))
    };
    let refutable = || mmap(SingleWriterEvidence::None);
    let (real, _) = typed(ro_value(&temporal("AG !bad", refutable())));
    assert!(matches!(real, RefutationOnlyVerdict::Counterexample { .. }), "{real:?}");
    for (what, value) in [
        ("misspelt atom", ro_value(&temporal("AG !bda", refutable()))),
        ("misspelt atom refuting", ro_value(&temporal("AG bda", refutable()))),
        ("misspelt atom, no vocabulary", ro_value_with(&temporal("AG !bda", refutable()), None)),
        ("real atom, no vocabulary", ro_value_with(&temporal("AG !bad", refutable()), None)),
        (
            "misspelt atom declared, real label undeclared",
            ro_value_with(&temporal("AG !bda", refutable()), Some(&["bda"])),
        ),
    ] {
        let (v, ev) = typed(value);
        assert!(
            matches!(v, RefutationOnlyVerdict::Inconclusive { .. }),
            "{what}: a misspelt atom over a refutable machine answered {v:?}"
        );
        assert_eq!(ev.status, EvidenceStatus::Unknown, "{what}: {ev:#?}");
    }
    // Through the derive crate: `Derived::payload` refuses the misspelling
    // itself, and a payload whose formula is edited afterwards (its fields
    // are public) is refused by the engine against the vocabulary the
    // payload declares.
    let (f, d, _trace, _want) = no_strip();
    let typo = fd_inherit_formula(&f.premises).replace("violation", "violaton");
    assert!(d.payload(&typo).is_err(), "Derived::payload vets atoms");
    let mut edited = d.payload(&fd_inherit_formula(&f.premises)).expect("vetted");
    edited.vc_kind =
        VcKind::Temporal { property: typo.clone(), machine: Some(d.machine().clone()) };
    let (v, ev) = typed(edited.to_metadata_value().expect("ser"));
    assert!(matches!(v, RefutationOnlyVerdict::Inconclusive { .. }), "`{typo}`: {v:?}");
    assert_eq!(ev.status, EvidenceStatus::Unknown);
}

/// A7. Every derived fixture: whatever ty says, an Exhaustive answer only
/// comes with a complete exploration of a machine that has states, and the
/// typed answer agrees with the wire (Failed <=> Counterexample; never a
/// strength).
#[test]
fn attack_a7_fixture_sweep_typed_vs_wire() {
    for f in fixtures::all() {
        let d = derived(&f);
        for formula in [fd_inherit_formula(&f.premises), non_vacuity_formula(&f.premises)] {
            let v = ty_on(&d, &formula);
            let payload = d.payload(&formula).expect("vetted");
            let o = obligation(
                d.name(),
                ObligationKind::TemporalSafety,
                vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, payload.to_metadata_value().unwrap())],
            );
            let ev = wire(&o).expect("one evidence");
            assert!(ev.proof_strength.is_none(), "{}: {ev:#?}", f.name);
            assert_eq!(
                ev.status == EvidenceStatus::Failed,
                matches!(v, RefutationOnlyVerdict::Counterexample { .. }),
                "{} `{formula}`: wire {:?} typed {v:?}",
                f.name,
                ev.status
            );
            if is_exhaustive(&v) {
                assert!(!d.machine().states.is_empty());
            }
        }
    }
}

// ======================================================= claim 3 (FC-2)

/// B1. Through the composite FullVerificationEngine, a bundle of every
/// refutation-only shape (no counterexample, counterexample, inconclusive,
/// unsupported) proves nothing: no strength, no proved / bounded-proved
/// count, run status not Proved.
#[test]
fn attack_b1_composite_run_has_no_proved_total() {
    let k = TY_TEMPORAL_MODEL_METADATA_KEY;
    let obligations = vec![
        obligation(
            "b1-ok",
            ObligationKind::TemporalSafety,
            vec![entry(k, ro_value(&temporal("AG !bad", mmap(SingleWriterEvidence::Verified))))],
        ),
        obligation(
            "b1-ce",
            ObligationKind::TemporalSafety,
            vec![entry(k, ro_value(&temporal("AG !bad", mmap(SingleWriterEvidence::None))))],
        ),
        obligation(
            "b1-ltl",
            ObligationKind::TemporalSafety,
            vec![entry(k, ro_value(&temporal("G !bad", mmap(SingleWriterEvidence::Verified))))],
        ),
        obligation(
            "b1-true",
            ObligationKind::TemporalSafety,
            vec![entry(k, ro_value(&temporal("AG true", mmap(SingleWriterEvidence::Verified))))],
        ),
        obligation(
            "b1-nomachine",
            ObligationKind::TemporalSafety,
            vec![entry(
                k,
                ro_value(&VcKind::Temporal { property: "AG !bad".into(), machine: None }),
            )],
        ),
    ];
    let bundle = bundle_of("b1", obligations);
    for policy in [
        FullVerificationPolicy { require_all_required_engines: false, ..Default::default() },
        FullVerificationPolicy::default(),
    ] {
        let engine = FullVerificationEngine::new(vec![Box::new(NativeTyEngine::new())], policy);
        let r = engine.verify_bundle(&bundle, &VerifierExecutionContext::new("redteam-b1"));
        assert_ne!(r.status, VerificationRunStatus::Proved, "{r:#?}");
        assert_eq!(r.summary.proved, 0, "{r:#?}");
        assert_eq!(r.summary.bounded_proved, 0, "{r:#?}");
        assert!(r.evidence.iter().all(|e| e.proof_strength.is_none()), "{r:#?}");
        assert!(r.evidence.iter().all(|e| e.status != EvidenceStatus::Proved), "{r:#?}");
    }
}

/// B2. An obligation that carries the derived model's REFUTATION-ONLY
/// payload but also, first, a full-schema payload of the same derived
/// machine: the engine takes the first entry, so the derived model is
/// PROVED with a strength. FC-2/OD-8: a derived model never proves; an
/// ambiguous (duplicate-key) transport should fail closed like the
/// ambiguous-initial-state transport does.
#[test]
fn attack_b2_full_payload_shadowing_a_refutation_only_payload_never_proves() {
    let f = fixtures::spawnfd::strip_first_premise();
    let d = derived(&f);
    let formula = fd_inherit_formula(&f.premises);
    let ro = d.payload(&formula).expect("vetted");
    assert!(ro.is_refutation_only());
    let full = TyTemporalModelPayload::from_vc_kind(&ro.vc_kind).expect("ty-owned");
    let k = TY_TEMPORAL_MODEL_METADATA_KEY;
    let o = obligation(
        "b2",
        ObligationKind::TemporalSafety,
        vec![
            entry(k, full.to_metadata_value().unwrap()),
            entry(k, ro.to_metadata_value().unwrap()),
        ],
    );
    let typed = NativeTyEngine::new().check_refutation_only(&o);
    assert!(matches!(typed, RefutationOnlyVerdict::Inconclusive { .. }), "{typed:?}");
    // The public verify boundary validates the bundle (duplicate metadata
    // keys are refused): no evidence at all, or none that proves.
    if let Some(ev) = wire(&o) {
        assert!(
            ev.proof_strength.is_none() && ev.status != EvidenceStatus::Proved,
            "an obligation carrying a refutation-only payload was PROVED: status {:?}, \
             strength {:?}",
            ev.status,
            ev.proof_strength
        );
    } else {
        eprintln!("B2: NativeTyEngine::verify returned no evidence (request validation refused)");
    }
    let engine = FullVerificationEngine::new(
        vec![Box::new(NativeTyEngine::new())],
        FullVerificationPolicy { require_all_required_engines: false, ..Default::default() },
    );
    let r = engine.verify_bundle(&bundle_of("b2", vec![o]), &VerifierExecutionContext::new("b2"));
    eprintln!("B2: composite status {:?}, summary {:?}", r.status, r.summary);
    assert_ne!(r.status, VerificationRunStatus::Proved, "{r:#?}");
    assert_eq!(r.summary.proved, 0, "{r:#?}");
    assert!(r.evidence.iter().all(|e| e.proof_strength.is_none()), "{r:#?}");
}

// ======================================================= claim 2 (L1c)

/// `impls`-style probe: inherent const wins when the bound holds.
macro_rules! implements {
    ($t:ty: $($tr:tt)+) => {{
        struct Probe<T: ?Sized>(std::marker::PhantomData<T>);
        #[allow(dead_code)]
        trait No {
            const YES: bool = false;
        }
        impl<T: ?Sized> No for T {}
        #[allow(dead_code)]
        impl<T: ?Sized + $($tr)+> Probe<T> {
            const YES: bool = true;
        }
        <Probe<$t>>::YES
    }};
}

/// C1. No safe backdoor constructs or duplicates a token: no Clone, Copy,
/// Default, From<Replay>, From<Vec<usize>>. (No serde: the crate has no
/// serde dependency, so no Deserialize impl can exist; a struct literal is
/// the compile_fail doctest, re-run separately with trustc.)
#[test]
fn attack_c1_no_clone_default_or_conversion_backdoor() {
    assert!(implements!(Vec<usize>: Clone), "the probe works");
    assert!(!implements!(ReplayToken: Clone));
    assert!(!implements!(ReplayToken: Copy));
    assert!(!implements!(ReplayToken: Default));
    assert!(!implements!(ReplayToken: From<Replay>));
    assert!(!implements!(ReplayToken: From<Vec<usize>>));
    assert!(!implements!(ReplayToken: std::str::FromStr));
}

/// C2. Empty and degenerate traces mint nothing.
#[test]
fn attack_c2_empty_and_degenerate_traces_mint_nothing() {
    let (_f, d, trace, want) = no_strip();
    let w = [want.as_str()];
    let n = d.machine().states.len();
    for blocks in [
        vec![],
        vec![0],
        vec![1],
        vec![0, 0],
        vec![usize::MAX],
        vec![0, usize::MAX],
        vec![0, n],
        vec![n],
    ] {
        for want in [&w[..], &[][..]] {
            assert!(d.replay_token(&blocks, want).is_err(), "{blocks:?} {want:?} minted a token");
        }
    }
    assert!(d.replay_token(&trace, &w).is_ok(), "the genuine trace mints");
}

/// C3. Mismatched blocks: reversed, rotated, one block substituted, another
/// derivation's trace, the trace with its initial state dropped.
#[test]
fn attack_c3_mismatched_blocks_mint_nothing() {
    let (_f, d, trace, want) = no_strip();
    let w = [want.as_str()];
    let mut variants: Vec<(String, Vec<usize>)> = Vec::new();
    variants.push(("reversed".into(), trace.iter().rev().copied().collect()));
    variants.push(("initial dropped".into(), trace[1..].to_vec()));
    let mut rotated = trace.clone();
    rotated.rotate_left(1);
    variants.push(("rotated".into(), rotated));
    for i in 1..trace.len() {
        for b in 0..d.machine().states.len() {
            if b == trace[i] {
                continue;
            }
            let mut t = trace.clone();
            t[i] = b;
            // A substitution may still be a real path; only the ones that
            // are not must fail. Check against the emitted machine.
            let real = t
                .windows(2)
                .all(|p| d.machine().transitions.iter().any(|(a, _, c)| *a == p[0] && *c == p[1]));
            if !real {
                variants.push((format!("step {i} -> block {b} (no such edge)"), t));
            }
        }
    }
    // Another derivation's refutation, replayed on this one.
    let g = fixtures::spawnfd::strip_first_no_premise();
    let dg = derived(&g);
    let tg = ty_trace(&dg, &fd_inherit_formula(&g.premises));
    if tg != trace {
        variants.push(("strip_first_no_premise's trace".into(), tg));
    }
    for (what, blocks) in variants {
        if let Ok(tok) = d.replay_token(&blocks, &w) {
            // A mismatched trace that nonetheless re-executes is a real
            // refutation of THIS derivation; it must at least re-execute.
            assert_eq!(tok.blocks(), blocks.as_slice());
            panic!("{what}: {blocks:?} minted a token");
        }
    }
}

/// C4. Partial replays: every strict prefix of the refutation, with the
/// refuted proposition wanted, mints nothing.
#[test]
fn attack_c4_partial_replays_with_the_refuted_proposition_mint_nothing() {
    let (_f, d, trace, want) = no_strip();
    for k in 0..trace.len() {
        let prefix = &trace[..k];
        assert!(
            d.replay_token(prefix, &[want.as_str()]).is_err(),
            "prefix of {k}/{} states minted a token",
            trace.len()
        );
    }
}

/// C5. A token is documented as "X2: a replayed REFUTATION" that a
/// refutation diagnostic takes by value ("no error can be built without a
/// replay"). With `want = []` (or a non-violation atom) the token is minted
/// for a trace that refutes nothing: a strict prefix of the refutation, and
/// a path of the FIXED twin (`strip_first_premise`, which the plan requires
/// NOT refuted).
#[test]
fn attack_c5_a_token_always_witnesses_a_refutation() {
    let (_f, d, trace, _want) = no_strip();
    let mut minted = Vec::new();
    for k in 2..trace.len() {
        if let Ok(tok) = d.replay_token(&trace[..k], &[]) {
            let r = tok.replay();
            if r.violations.is_empty() {
                minted.push(format!(
                    "no_strip prefix {k}/{}: violations {:?}",
                    trace.len(),
                    r.violations
                ));
            }
        }
    }
    let fixed = fixtures::spawnfd::strip_first_premise();
    let df = derived(&fixed);
    // Any path of the fixed model: ty's non-vacuity witness (a policy exec).
    let path = ty_trace(&df, &non_vacuity_formula(&fixed.premises));
    for want in [&[][..], &[property::POLICY_EXEC][..]] {
        if let Ok(tok) = df.replay_token(&path, want) {
            minted.push(format!(
                "strip_first_premise (NOT refuted) path, want {want:?}: token with {} steps, \
                 violations {:?}",
                tok.steps().len(),
                tok.replay().violations
            ));
        }
    }
    assert!(minted.is_empty(), "tokens for traces that refute nothing:\n{}", minted.join("\n"));
}

fn action_of<'a>(d: &'a Derived, label: &str) -> Option<&'a ActionKey> {
    d.action_labels().iter().position(|l| l == label).and_then(|i| d.graph().actions.get(i))
}

fn std_row_of(p: &EventProgram, at: StmtRef) -> Option<&'static str> {
    match p.stmt(at).map(|s| &s.kind) {
        Some(StmtKind::Event(ev)) => ev.std_origin.as_ref().map(|o| o.row),
        Some(StmtKind::Fork { std_origin, .. }) => std_origin.as_ref().map(|o| o.row),
        _ => None,
    }
}

/// C6. Every genuine token of every refuted fixture, re-checked
/// INDEPENDENTLY of `check_x2`: the environment/program split of each site
/// follows the ACTION KIND of its step (Init -> RL-INIT, ForeignSquat ->
/// RL-FOREIGN, ImageExit -> RL-IMAGE-EXIT, Event/Child/Nondet -> program
/// positions only); program sites carry their position's Loc and std row,
/// and the event line says `via <row>` exactly when the site cites a row.
#[test]
fn attack_c6_genuine_tokens_cross_checked_against_action_kinds() {
    let mut checked = 0;
    for f in fixtures::all() {
        let d = derived(&f);
        let formula = fd_inherit_formula(&f.premises);
        let RefutationOnlyVerdict::Counterexample { trace } = ty_on(&d, &formula) else {
            continue;
        };
        let want = premised(property::VIOLATION, &f.premises);
        let tok = match d.replay_token(&trace, &[want.as_str()]) {
            Ok(t) => t,
            Err(TokenError::Replay(e)) => panic!("{}: genuine trace did not replay: {e}", f.name),
            Err(e) => panic!("{}: genuine trace minted no token: {e}", f.name),
        };
        assert_eq!(tok.steps().len(), tok.replay().steps.len(), "{}", f.name);
        for (j, (st, r)) in tok.steps().iter().zip(&tok.replay().steps).enumerate() {
            let at = format!("{} step {j} `{}`", f.name, st.info.text);
            if st.info.label == HALT {
                assert!(r.events.is_empty() && r.sites.is_empty(), "{at}");
                assert_eq!(st.from, st.to, "{at}: a halt step moves");
                continue;
            }
            assert_eq!(r.sites.len(), r.events.len(), "{at}");
            assert!(!r.sites.is_empty(), "{at}: nothing re-executed");
            let kind = action_of(&d, &st.info.label).unwrap_or_else(|| panic!("{at}: no action"));
            let env_clause = match kind {
                ActionKey::Init(_) => Some(RL_INIT),
                ActionKey::ForeignSquat { .. } => Some(RL_FOREIGN),
                ActionKey::ImageExit { .. } => Some(RL_IMAGE_EXIT),
                ActionKey::Event { .. } | ActionKey::Child { .. } | ActionKey::Nondet { .. } => {
                    None
                }
            };
            for (site, line) in r.sites.iter().zip(&r.events) {
                match env_clause {
                    Some(c) => {
                        assert!(site.environment, "{at}: {kind:?} fired a program site {site:?}");
                        assert_eq!(site.rl_clause, Some(c), "{at}");
                        assert!(site.at.is_none() && site.std_row.is_none(), "{at}");
                        assert!(RL_CLAUSES.contains(&c));
                    }
                    None => {
                        assert!(!site.environment, "{at}: program action {kind:?} -> {site:?}");
                        let pos = site.at.unwrap_or_else(|| panic!("{at}: no position"));
                        assert_eq!(d.core().prog.loc_at(pos), Some(&site.loc), "{at}");
                        assert_eq!(site.std_row, std_row_of(&d.core().prog, pos), "{at}");
                        assert!(site.rl_clause.is_none(), "{at}");
                        let says_row = line.contains(" via ");
                        assert_eq!(says_row, site.std_row.is_some(), "{at}: `{line}` vs {site:?}");
                        if let Some(row) = site.std_row {
                            assert!(line.contains(&format!(" via {row} step ")), "{at}: {line}");
                        }
                    }
                }
            }
        }
        checked += 1;
    }
    assert!(checked >= 5, "only {checked} refuted fixtures");
}

/// C7 (H4). `Derived`'s fields are read-only outside the crate, so the red
/// team's C7a/b/c/d edits of a cloned derivation (erasing std rows,
/// rewriting Locs, relabelling a step as the horizon stutter) no longer
/// compile: each is a `compile_fail,E0616` doctest on `Derived`, and the
/// same edits made inside the crate are unit tests (`src/tests.rs`). What
/// remains to attack from outside is a token used for the wrong
/// derivation: it records the program and environment it replayed on.
#[test]
fn attack_c7_a_token_is_only_its_own_derivation_s() {
    let (_f, d, trace, want) = no_strip();
    let tok = d.replay_token(&trace, &[want.as_str()]).expect("genuine token");
    assert!(tok.is_of(&d));
    assert!(tok.is_of(&d.clone()), "a clone is the same derivation");
    let mut others = 0;
    for g in fixtures::all() {
        if g.program == fixtures::spawnfd::no_strip().program {
            continue;
        }
        let dg = derived(&g);
        assert!(!tok.is_of(&dg), "no_strip's token passes as {}'s", g.name);
        others += 1;
    }
    assert!(others > 10, "{others}");
    // The same program in another environment is another derivation.
    let f = fixtures::spawnfd::no_strip();
    let other_env = fixtures::all()
        .into_iter()
        .map(|g| g.env)
        .find(|e| *e != f.env)
        .expect("a fixture with another environment");
    if let Ok(de) = derive(&f.program, &other_env, &DeriveOptions::default()) {
        assert!(!tok.is_of(&de), "no_strip's token passes in another environment");
    }
}

/// A8. A malformed payload that serde accepts silently: a DUPLICATE key in
/// the machine's `labels` JSON map (last wins). The refutable multi-writer
/// machine's `bad` label is overwritten by an empty list, so ty explores a
/// machine with no bad state. L1b: "any payload or parse error gives
/// Inconclusive".
#[test]
fn attack_a8_duplicate_label_key_in_payload_json_is_inconclusive() {
    let value = ro_value(&temporal("AG !bad", mmap(SingleWriterEvidence::None)));
    assert!(value.contains("\"3\":[\"bad\"]"), "{value}");
    let dup = value.replacen("\"3\":[\"bad\"]", "\"3\":[\"bad\"],\"3\":[]", 1);
    let o = obligation(
        "a8",
        ObligationKind::TemporalSafety,
        vec![entry(TY_TEMPORAL_MODEL_METADATA_KEY, dup)],
    );
    let v = NativeTyEngine::new().check_refutation_only(&o);
    assert!(
        matches!(v, RefutationOnlyVerdict::Inconclusive { .. }),
        "a payload with a duplicate labels key answered {v:?}"
    );
}
