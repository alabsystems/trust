//! Shared helpers for the census integration tests: load a real trust-ir
//! dump and its identity sidecar, run the census, and take one (root, site)
//! pair through the path the host will take — derive the root's
//! single-site program, check it with NativeTyEngine (the in-process `ty`
//! primary), replay a refutation, and run the per-site non-vacuity check.

#![allow(dead_code)]

use trust_ir::Module;
use trust_platform_census::stub::SidecarContext;
use trust_platform_census::verdict::{
    Completeness, NonVacuity, Outcome, SiteEvidence, derive_finds_violation, refusal_of,
};
use trust_platform_census::{CensusOptions, CensusOutput, RootProgram, run};
use trust_platform_derive::derive::{DeriveOptions, Derived};
use trust_platform_derive::env::EnvSpec;
use trust_platform_derive::trace::{Replay, ReplayToken};
use trust_platform_derive::{derive, fd_inherit_formula, non_vacuity_formula};
use trust_router::full_verification::{
    NativeTyEngine, RefutationCompleteness, RefutationOnlyVerdict,
};
use trust_types::TY_TEMPORAL_MODEL_METADATA_KEY;
use trust_verifier_api::{
    BundleSubject, EvidenceStatus, MetadataEntry, ObligationKind, SourceLocation,
    TrustContractBundle, TrustObligation, VerificationEngine,
};

pub fn path(file: &str) -> String {
    format!("{}/tests/ir/{file}", env!("CARGO_MANIFEST_DIR"))
}

/// A real stage1 dump, parsed by trust-ir's own text parser.
pub fn module(name: &str) -> Module {
    let text = std::fs::read_to_string(path(&format!("{name}.trust_ir")))
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    trust_ir::parser::parse_module(&text).unwrap_or_else(|e| panic!("{name}: {e:?}"))
}

pub fn sidecar(name: &str) -> String {
    std::fs::read_to_string(path(&format!("{name}.identities"))).unwrap_or_default()
}

pub fn census_with(m: &Module, sidecar: &str, o: &CensusOptions) -> CensusOutput {
    let cx = SidecarContext::parse(m, sidecar).unwrap_or_else(|e| panic!("{e}"));
    run(m, &cx, o)
}

pub fn census(m: &Module, name: &str) -> CensusOutput {
    census_with(m, &sidecar(name), &CensusOptions::default())
}

/// The function `name`'s id.
pub fn func(m: &Module, name: &str) -> trust_ir::FuncId {
    let i = m
        .functions
        .iter()
        .position(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    trust_ir::FuncId::new(i as u32)
}

/// The translated root `name` and its index.
pub fn root<'o>(out: &'o CensusOutput, m: &Module, name: &str) -> (usize, &'o RootProgram) {
    let f = func(m, name);
    let i = out.roots.iter().position(|r| r.root == f).unwrap_or_else(|| {
        panic!(
            "`{name}` is not a translated root; its refusals: {:#?}",
            out.root_refusals(f).iter().map(ToString::to_string).collect::<Vec<_>>()
        )
    });
    (i, &out.roots[i])
}

/// The codes of the refusals recorded against root `name`.
pub fn root_codes(out: &CensusOutput, m: &Module, name: &str) -> Vec<&'static str> {
    let mut v: Vec<_> = out.root_refusals(func(m, name)).iter().map(|r| r.code()).collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// The census's library environments (host-independent limits).
pub fn envs() -> Vec<EnvSpec> {
    trust_platform_census::env::library_envs()
}

/// Check `formula` on `d` with NativeTyEngine (refutation-only payload),
/// read through the typed API the host reads (L1b, Critique C-1): a
/// counterexample trace, "no counterexample" with its completeness, or
/// inconclusive — never `EvidenceStatus` or diagnostic text.
pub fn ty(d: &Derived, formula: &str) -> RefutationOnlyVerdict {
    let payload = d.payload(formula).unwrap_or_else(|e| panic!("`{formula}`: {e}"));
    let id: String = d
        .name()
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '_' })
        .collect();
    let obligation = TrustObligation {
        obligation_id: format!("vc:census::{id}:temporal_safety:{}", formula.len()),
        kind: ObligationKind::TemporalSafety,
        contract_id: None,
        proof_item_id: None,
        source: SourceLocation::default(),
        description: format!("census `{formula}`"),
        required_strength: None,
        summary_facts: Vec::new(),
        metadata: vec![MetadataEntry {
            key: TY_TEMPORAL_MODEL_METADATA_KEY.to_string(),
            value: payload.to_metadata_value().expect("serializes"),
        }],
    };
    let engine = NativeTyEngine::new();
    let typed = engine.check_refutation_only(&obligation);
    // The wire evidence of the same obligation agrees and never proves.
    let mut bundle = TrustContractBundle::empty(
        format!("bundle-{id}"),
        BundleSubject::Function { crate_name: "census".to_string(), path: format!("census::{id}") },
    );
    bundle.obligations.push(obligation.clone());
    let ev = engine.verify(&bundle, &[obligation]).remove(0);
    assert!(ev.proof_strength.is_none(), "a derived model never proves: {ev:?}");
    let refuted = matches!(typed, RefutationOnlyVerdict::Counterexample { .. });
    assert_eq!(ev.status == EvidenceStatus::Failed, refuted, "wire {ev:?} vs typed {typed:?}");
    assert!(refuted || ev.status == EvidenceStatus::Unknown, "{ev:?}");
    typed
}

/// The census's completeness of a typed "no counterexample" or
/// inconclusive answer: only an exhaustive exploration is `Exhaustive`
/// (FC-4); truncated and inconclusive both become `PC-INCOMPLETE` in
/// `site_verdict`.
fn completeness(v: &RefutationOnlyVerdict) -> Completeness {
    match v {
        RefutationOnlyVerdict::NoCounterexample {
            completeness: RefutationCompleteness::Exhaustive,
        } => Completeness::Exhaustive,
        RefutationOnlyVerdict::NoCounterexample {
            completeness: RefutationCompleteness::Truncated { states },
        } => Completeness::Truncated { states: usize::try_from(*states).unwrap_or(usize::MAX) },
        RefutationOnlyVerdict::Inconclusive { reason } => {
            Completeness::Inconclusive { reason: reason.clone() }
        }
        RefutationOnlyVerdict::Counterexample { .. } => {
            Completeness::Inconclusive { reason: "a counterexample is not a completeness".into() }
        }
    }
}

pub fn lines(r: &Replay) -> Vec<String> {
    r.steps.iter().flat_map(|s| s.events.clone()).collect()
}

/// The evidence for one (root, program site) pair, summarized over the
/// library environments for assertions: a refuting environment's evidence
/// if one refutes, else one that witnesses the site's exec, else the first;
/// with that environment's replay. Completeness: a `derive` that returns a
/// model explored every state below its budget, and `derive_violation`
/// cross-checks ty's answer against that exploration (C-1's engine
/// agreement); ty's own completeness is the typed field of its answer
/// (`RefutationOnlyVerdict`, L1b), never assumed exhaustive.
pub fn evidence(
    out: &CensusOutput,
    root: usize,
    program_site: usize,
) -> (SiteEvidence, Option<Replay>) {
    let all: Vec<_> = (0..envs().len())
        .map(|env| evidence_with(out, root, program_site, env, &DeriveOptions::default()))
        .collect();
    let pick = all
        .iter()
        .position(|(e, _)| matches!(e.outcome, Outcome::Refuted { .. }))
        .or_else(|| all.iter().position(|(e, _)| e.non_vacuity == NonVacuity::Witnessed))
        .unwrap_or(0);
    all.into_iter().nth(pick).expect("one environment at least")
}

/// The evidence for one (root, program site) pair in environment `env`.
pub fn evidence_with(
    out: &CensusOutput,
    root: usize,
    program_site: usize,
    env: usize,
    opts: &DeriveOptions,
) -> (SiteEvidence, Option<Replay>) {
    let rp = &out.roots[root];
    let prog = rp.site_program(program_site);
    let d = match derive(&prog, &envs()[env], opts) {
        Ok(d) => d,
        Err(e) => {
            return (
                SiteEvidence {
                    root,
                    program_site,
                    env,
                    outcome: Outcome::DeriveFailed { refusal: refusal_of(&e) },
                    non_vacuity: NonVacuity::Missing,
                    derive_violation: false,
                },
                None,
            );
        }
    };
    let derive_violation = derive_finds_violation(&d);
    let mut replay = None;
    let outcome = match ty(&d, &fd_inherit_formula(&[])) {
        // FC-3: a refutation counts only as a replay token (X2, L1c): the
        // trace re-executed, its environment steps cite their RL clauses,
        // its std steps their rows. No token is PC-REPLAY.
        RefutationOnlyVerdict::Counterexample { trace: t } => {
            match d.replay_token(&t, &["fd_inherit_violation"]).map(ReplayToken::into_replay) {
                Ok(r) => {
                    let o = Outcome::Refuted {
                        trace: lines(&r),
                        overapprox: r.overapprox.iter().map(ToString::to_string).collect(),
                    };
                    replay = Some(r);
                    o
                }
                Err(e) => Outcome::ReplayFailed { detail: e.to_string() },
            }
        }
        v => Outcome::NoCounterexample { completeness: completeness(&v) },
    };
    let non_vacuity = match ty(&d, &non_vacuity_formula(&[])) {
        RefutationOnlyVerdict::Counterexample { trace: t } => {
            match d.replay(&t, &["policy_exec"]) {
                Ok(r) if r.overapprox.is_empty() => NonVacuity::Witnessed,
                Ok(_) => NonVacuity::OnlyOverapprox,
                Err(_) => NonVacuity::Missing,
            }
        }
        _ => NonVacuity::Missing,
    };
    println!(
        "{} site {program_site} env {env} ({:?}): {outcome:?}, non-vacuity {non_vacuity:?}",
        rp.name,
        d.stats()
    );
    (SiteEvidence { root, program_site, env, outcome, non_vacuity, derive_violation }, replay)
}

/// Evidence for every (root, program site) pair that reaches census site
/// `site`, in every library environment.
pub fn evidence_for_site(out: &CensusOutput, site: usize) -> Vec<SiteEvidence> {
    let mut v = Vec::new();
    for r in out.roots_reaching(site) {
        if let Some(i) = out.roots.iter().position(|p| p.root == r) {
            for ps in out.roots[i].policy_sites.clone().iter().filter(|p| p.site == site) {
                for env in 0..envs().len() {
                    v.push(
                        evidence_with(out, i, ps.program_site, env, &DeriveOptions::default()).0,
                    );
                }
            }
        }
    }
    v
}

/// The site verdict through the host's path: evidence in every environment,
/// joined.
pub fn verdict_of(out: &CensusOutput, site: usize) -> trust_platform_census::verdict::SiteVerdict {
    trust_platform_census::verdict::site_verdict(out, site, &evidence_for_site(out, site))
}
