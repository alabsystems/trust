// Trust: M4 v0 — the generic gate wiring (design §4.4). ONE function
// replaces what would otherwise be a new ~85-line copy-pasted block per
// family in `trustir_bridge.rs` (the STEPBLOCK/STEPBRANCH/STEPLOOP/DATALOOP
// pattern this module generalizes). Behavior is byte-compatible with that
// hand-written discipline: fixtures load first (`Err` -> whole family
// pinned as `"fixtures: …"`), per-visit load-then-`require_empty_axiom_deps`,
// pin messages `"{visit}: {err[..200]}"`, composed theorem gated on
// all-visits-proved, probe loop with `ForgeryAccepted` on any load success.
//
// PLANNING FAILURE FOR A REGISTERED FAMILY IS A HARD ERROR (design §4.3):
// release evidence must not silently shrink the claimed family set. An
// `EnvelopeError` from `plan_family` becomes
// `BridgeGateError::GeneratedFamilyEnvelopeRefused`, not a pinned/skipped
// entry.

use std::str::FromStr;

use clean_kernel::Environment;
use serde::{Deserialize, Serialize};

use super::emit::emit_family;
use super::envelope::{self, EnvelopeError};
use super::plan::plan_family;
use super::spec::{CfgFamilySpec, ModeSlice};
use crate::trustir_bridge::{
    BridgeGateError, BridgeGateMode, load_bridge_source, require_empty_axiom_deps,
};

/// A static summary of the envelope decision for one family's report —
/// mirrors the "refuse honestly, never truncate silently" discipline even
/// on the SUCCESS path (a family that planned cleanly still records that
/// fact, so the report format doesn't change shape between a refused and an
/// accepted family).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvelopeSummary {
    pub planned: bool,
    pub error: Option<String>,
}

/// Uniform per-family report — `BridgeAgreement::generated_families` grows
/// one `Vec` entry per registered [`CfgFamilySpec`], replacing what would
/// otherwise be 7+ new `BridgeAgreement` fields per family (design §4.4).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GeneratedFamilyReport {
    pub name: String,
    pub visits_bridged: usize,
    pub visits_pinned_list: Vec<String>,
    pub visits_bridged_list: Vec<String>,
    /// 0 = C0 (conjunction, the only level v0 asserts), 1 = C1, 2 = C2.
    pub composed_level: u8,
    pub composed: bool,
    pub fail_closed_controls: usize,
    pub probes_rejected: usize,
    pub unbridged: Vec<String>,
    pub envelope: EnvelopeSummary,
    /// Wall-clock seconds per loaded declaration group, in load order —
    /// `("fixtures", s)`, one `("visit{k}", s)` per visit, `("composed", s)`,
    /// one `("probe: {label}", s)` per probe. The design's §2/§7 cost-model
    /// data (per-visit kernel time), captured mechanically on every gate run
    /// instead of by ad-hoc stopwatching. Purely observational: no test
    /// asserts on it, and it never gates anything (the envelope is static,
    /// never a watchdog).
    #[serde(default)]
    pub timings_secs: Vec<(String, f64)>,
}

fn truncate(e: &str) -> String {
    e.chars().take(200).collect::<String>()
}

/// The generic gate entry point (design §4.4's `run_generated_family`).
/// Loads `spec`'s fixtures, then every visit (chain-then-connect for
/// symbolic-core visits), then the C0 composed theorem, then its forgery
/// probes — into the SAME cumulative `env` every hand-written arm loads
/// into, so E6 (dependency closure) and E7 (name uniqueness) hold against
/// the real cumulative state, not a fresh sandbox.
pub fn run_generated_family(
    env: &mut Environment,
    spec: &'static CfgFamilySpec,
    mode: BridgeGateMode,
) -> Result<GeneratedFamilyReport, BridgeGateError> {
    let plan = match plan_family(spec) {
        Ok(p) => p,
        Err(e) => {
            return Err(BridgeGateError::GeneratedFamilyEnvelopeRefused {
                family: spec.name.to_string(),
                detail: e.to_string(),
            });
        }
    };

    if spec.mode == ModeSlice::FullOnly && mode == BridgeGateMode::Spot {
        return Ok(GeneratedFamilyReport {
            name: spec.name.to_string(),
            visits_bridged: 0,
            visits_pinned_list: Vec::new(),
            visits_bridged_list: Vec::new(),
            composed_level: 0,
            composed: false,
            fail_closed_controls: 0,
            probes_rejected: 0,
            unbridged: vec!["skipped in Spot mode (ModeSlice::FullOnly)".to_string()],
            envelope: EnvelopeSummary { planned: true, error: None },
            timings_secs: Vec::new(),
        });
    }

    // E6/E7 for this family's own dependency citations: check that every
    // `bridge_<op>` a symbolic-core visit cites is already a loaded
    // constant, BEFORE emitting/loading anything — mechanizing the
    // catalog's manually-maintained load-order invariant.
    for visit in &plan.visits {
        if let Some(inst) = visit.inst {
            if inst.folded.is_none() {
                let lemma = inst.op.bridge_lemma();
                let present = clean_kernel::Name::from_str(lemma)
                    .ok()
                    .and_then(|n| env.get_const(&n).map(|_| ()))
                    .is_some();
                if !present {
                    return Err(BridgeGateError::GeneratedFamilyEnvelopeRefused {
                        family: spec.name.to_string(),
                        detail: EnvelopeError::DependencyMissing {
                            family: spec.name,
                            visit: visit.k,
                            lemma,
                        }
                        .to_string(),
                    });
                }
            }
        }
    }

    let emitted = emit_family(&plan);

    let mut visits_bridged_list: Vec<String> = Vec::new();
    let mut visits_pinned_list: Vec<String> = Vec::new();
    let mut timings_secs: Vec<(String, f64)> = Vec::new();
    let mut all_visits_ok = true;

    let fixtures_t0 = std::time::Instant::now();
    let fixtures_result = load_bridge_source(env, &emitted.fixtures_src);
    timings_secs.push(("fixtures".to_string(), fixtures_t0.elapsed().as_secs_f64()));
    match fixtures_result {
        Ok(_) => {
            for emitted_visit in &emitted.visits {
                let visit_t0 = std::time::Instant::now();
                let visit_result = load_bridge_source(env, &emitted_visit.src);
                timings_secs.push((emitted_visit.label.clone(), visit_t0.elapsed().as_secs_f64()));
                match visit_result {
                    Ok(_) => {
                        for name in &emitted_visit.names_owned {
                            require_empty_axiom_deps(env, name)?;
                        }
                        visits_bridged_list.push(emitted_visit.label.clone());
                    }
                    Err(e) => {
                        if std::env::var("TRUST_CFG_FAMILY_DEBUG").is_ok() {
                            eprintln!(
                                "=== M4 DEBUG {} / {} FULL ERROR ===\n{}\n=== SRC ===\n{}",
                                spec.name, emitted_visit.label, e, emitted_visit.src
                            );
                        }
                        all_visits_ok = false;
                        visits_pinned_list.push(format!(
                            "{}: {}",
                            emitted_visit.label,
                            truncate(&e)
                        ));
                    }
                }
            }
        }
        Err(e) => {
            all_visits_ok = false;
            visits_pinned_list.push(format!("fixtures: {}", truncate(&e)));
        }
    }

    let mut composed = false;
    if all_visits_ok {
        let composed_t0 = std::time::Instant::now();
        let composed_result = load_bridge_source(env, &emitted.composed_src);
        timings_secs.push(("composed".to_string(), composed_t0.elapsed().as_secs_f64()));
        match composed_result {
            Ok(_) => {
                require_empty_axiom_deps(env, &emitted.composed_name)?;
                composed = true;
            }
            Err(e) => visits_pinned_list.push(format!("composed: {}", truncate(&e))),
        }
    }
    if std::env::var("TRUST_CFG_FAMILY_DEBUG").is_ok() && !composed && all_visits_ok {
        // The composed statement failing while every visit proved is the
        // emitter-bug signature (e.g. the ∀/∧ precedence bug this debug aid
        // was used to diagnose) — dump the full source on request.
        eprintln!("=== M4 DEBUG {} / composed FULL SRC ===\n{}", spec.name, emitted.composed_src);
    }

    let probe_slice: &[(String, String)] = match mode {
        BridgeGateMode::Full => &emitted.probes,
        BridgeGateMode::Spot => &emitted.probes[..1.min(emitted.probes.len())],
    };
    let mut probes_rejected = 0usize;
    for (label, src) in probe_slice {
        let probe_t0 = std::time::Instant::now();
        let probe_result = load_bridge_source(env, src);
        timings_secs.push((format!("probe: {label}"), probe_t0.elapsed().as_secs_f64()));
        match probe_result {
            Ok(_) => {
                return Err(BridgeGateError::ForgeryAccepted {
                    probe: format!("{}::{}", spec.name, label),
                });
            }
            Err(_) => probes_rejected += 1,
        }
    }

    Ok(GeneratedFamilyReport {
        name: spec.name.to_string(),
        visits_bridged: visits_bridged_list.len(),
        visits_pinned_list,
        visits_bridged_list,
        composed_level: 0,
        composed,
        fail_closed_controls: probes_rejected,
        probes_rejected,
        unbridged: Vec::new(),
        envelope: EnvelopeSummary { planned: true, error: None },
        timings_secs,
    })
}

/// E7 over the whole registry — called once before any family in `specs`
/// is planned (`trustir_bridge.rs`'s gate step, before the loop over
/// [`super::GENERATED_FAMILIES`]).
pub fn check_registry(specs: &[CfgFamilySpec]) -> Result<(), BridgeGateError> {
    envelope::check_registry_unique(specs).map_err(|e| {
        BridgeGateError::GeneratedFamilyEnvelopeRefused {
            family: "GENERATED_FAMILIES".to_string(),
            detail: e.to_string(),
        }
    })
}
