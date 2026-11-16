//! A site's verdict from the evidence the host gathers per (root, site):
//! the join over every root that reaches the site (Critique C-4), with
//! "not refuted" admitted only under all of C-1's conditions, and a
//! refutation admitted only without over-approximating choices (C-9).
//!
//! The evidence for one (root, site) pair comes from the root's
//! [`crate::RootProgram::site_program`] — the program with only that site
//! under the policy — derived in EVERY library environment
//! ([`crate::env::library_envs`]) and checked twice in each: the fd-inherit
//! formula, and the per-site non-vacuity formula (`AG !policy_exec`, which
//! in the single-site program means "a child of THIS site exec'd"). A pair
//! is "not refuted" only with evidence from every environment, none
//! refuted, every exploration exhaustive and agreeing with ty, and the
//! site's exec witnessed in at least one.

use trust_platform_derive::explore::ExploreError;
use trust_platform_derive::interp::InterpError;
use trust_platform_derive::lower::LowerError;
use trust_platform_derive::property::violations;
use trust_platform_derive::{DeriveError, Derived};

use crate::{CensusOutput, CensusPremise, Refusal, SiteId};

/// How much of the state space ty explored (Critique C-1: a typed field
/// the engine must report; the host never parses diagnostic text).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Completeness {
    Exhaustive,
    Truncated { states: usize },
    Inconclusive { reason: String },
}

/// What checking the fd-inherit formula on a site program gave.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// ty refuted it and the trace replayed; `overapprox` lists the
    /// over-approximating choices the replay took (`Replay::overapprox`).
    Refuted { trace: Vec<String>, overapprox: Vec<String> },
    /// ty refuted it but the replay failed (a Trust defect).
    ReplayFailed { detail: String },
    /// No counterexample.
    NoCounterexample { completeness: Completeness },
    /// The derivation refused the program (budget, an unmodeled step, …).
    DeriveFailed { refusal: Refusal },
}

/// What the per-site non-vacuity check gave.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonVacuity {
    /// `AG !policy_exec` refuted with a replayed trace that takes no
    /// over-approximating choice: the program reaches the site's exec.
    Witnessed,
    /// Refuted only through over-approximating choices: no witness that the
    /// PROGRAM reaches the exec.
    OnlyOverapprox,
    /// Not refuted, or not checked.
    Missing,
}

/// The evidence for one (root, program site) pair in one environment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SiteEvidence {
    /// Index into [`CensusOutput::roots`].
    pub root: usize,
    pub program_site: usize,
    /// Index into [`crate::env::library_envs`].
    pub env: usize,
    pub outcome: Outcome,
    pub non_vacuity: NonVacuity,
    /// Whether the derivation's own exploration holds a violating state
    /// ([`derive_finds_violation`]): it must agree with ty.
    pub derive_violation: bool,
}

/// A site's verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiteVerdict {
    /// A replayed refutation with no over-approximating choice, under its
    /// named premises. A synthetic hook harness is not a default Command.
    Refuted {
        root: usize,
        program_site: usize,
        trace: Vec<String>,
        premises: Vec<CensusPremise>,
    },
    /// Not refuted (refutation-only), under these premises.
    NotRefuted {
        roots: Vec<usize>,
        premises: Vec<CensusPremise>,
    },
    Unanalysed(Vec<Refusal>),
}

/// Whether some explored state of `d` violates fd-inherit (the derivation's
/// side of C-1's engine-agreement condition).
#[must_use]
pub fn derive_finds_violation(d: &Derived) -> bool {
    d.graph().configs.iter().any(|c| !violations(d.core(), c).is_empty())
}

/// The named refusal for a derivation that did not produce a model.
#[must_use]
pub fn refusal_of(e: &DeriveError) -> Refusal {
    match e {
        DeriveError::Explore(ExploreError::Budget { states }) => Refusal::Budget {
            detail: format!("the derivation stopped at {states} states, its state budget"),
        },
        DeriveError::TooLarge { bytes } => Refusal::Budget {
            detail: format!("the derived model is {bytes} bytes, over the transport limit"),
        },
        DeriveError::Explore(ExploreError::Interp(InterpError::Bound { at, events })) => {
            Refusal::Budget {
                detail: format!(
                    "a forked child's macro step exceeded {events} events{}: a loop in the child \
                     the ForRange recognizer did not summarise",
                    at.map(|a| format!(" at {a}")).unwrap_or_default()
                ),
            }
        }
        DeriveError::Explore(ExploreError::Interp(i)) => Refusal::Unmodeled {
            symbol: "the derivation".into(),
            reason: format!("the model declined a step: {i}"),
        },
        DeriveError::Lower(LowerError::Unmodeled { effect, .. }) => {
            Refusal::Unmodeled { symbol: effect.symbol.clone(), reason: effect.reason.to_string() }
        }
        DeriveError::Lower(LowerError::Untracked { var, used_as, origin, .. }) => {
            Refusal::UntrackedFd {
                symbol: used_as.clone(),
                arg: format!("`{var}` (from {origin})"),
            }
        }
        other => Refusal::Internal {
            detail: format!("the derivation refused the census output: {other}"),
        },
    }
}

/// The verdict of `site` (C-4 join: Refuted > Unanalysed > NotRefuted).
#[must_use]
pub fn site_verdict(out: &CensusOutput, site: SiteId, evidence: &[SiteEvidence]) -> SiteVerdict {
    let mut refusals = out.refusals_for(site);
    let reaching = out.roots_reaching(site);
    if reaching.is_empty() {
        refusals.push(Refusal::NoRoot);
    }
    let mut checks = Vec::new();
    for r in &reaching {
        if let Some(i) = out.roots.iter().position(|p| p.root == *r) {
            for p in out.roots[i].policy_sites.iter().filter(|p| p.site == site) {
                checks.push((i, p.program_site));
            }
        }
    }
    checks.sort_unstable();
    checks.dedup();
    if checks.is_empty() && refusals.is_empty() {
        refusals.push(Refusal::NoRoot);
    }
    let envs = crate::env::library_envs().len();
    let mut ok_roots = Vec::new();
    for (root, ps) in &checks {
        let mut witnessed = false;
        let mut clean = true;
        for env in 0..envs {
            let Some(e) =
                evidence.iter().find(|e| e.root == *root && e.program_site == *ps && e.env == env)
            else {
                refusals.push(Refusal::Incomplete {
                    why: format!(
                        "no evidence for root {root}, program site {ps}, environment {env}"
                    ),
                });
                clean = false;
                continue;
            };
            match &e.outcome {
                Outcome::Refuted { trace, overapprox } => {
                    clean = false;
                    if !overapprox.is_empty() {
                        refusals.push(Refusal::Overapprox { choices: overapprox.clone() });
                    } else if !e.derive_violation {
                        refusals.push(Refusal::EngineDisagree {
                            detail: "ty refuted, the derivation's exploration has no violating \
                                     state"
                                .into(),
                        });
                    } else {
                        let mut premises = out.roots[*root].premises.clone();
                        premises.push(crate::env::premise());
                        premises.sort();
                        premises.dedup();
                        return SiteVerdict::Refuted {
                            root: *root,
                            program_site: *ps,
                            trace: trace.clone(),
                            premises,
                        };
                    }
                }
                Outcome::ReplayFailed { detail } => {
                    clean = false;
                    refusals.push(Refusal::Replay { detail: detail.clone() });
                }
                Outcome::DeriveFailed { refusal } => {
                    clean = false;
                    refusals.push(refusal.clone());
                }
                Outcome::NoCounterexample { completeness } => {
                    if *completeness != Completeness::Exhaustive {
                        clean = false;
                        refusals.push(Refusal::Incomplete {
                            why: format!(
                                "no counterexample, but the exploration was {completeness:?}"
                            ),
                        });
                    } else if e.derive_violation {
                        clean = false;
                        refusals.push(Refusal::EngineDisagree {
                            detail: "the derivation reached a violating state ty did not report"
                                .into(),
                        });
                    } else if e.non_vacuity == NonVacuity::Witnessed {
                        witnessed = true;
                    }
                }
            }
        }
        if clean && !witnessed {
            refusals.push(Refusal::Incomplete {
                why: "per-site non-vacuity was refuted in no environment: no witness that the \
                      program reaches this site's exec"
                    .into(),
            });
        } else if clean {
            ok_roots.push(*root);
        }
    }
    if !refusals.is_empty() {
        refusals.sort();
        refusals.dedup();
        return SiteVerdict::Unanalysed(refusals);
    }
    let mut premises: Vec<CensusPremise> =
        ok_roots.iter().flat_map(|r| out.roots[*r].premises.iter().cloned()).collect();
    premises.push(crate::env::premise());
    premises.sort();
    premises.dedup();
    ok_roots.sort_unstable();
    ok_roots.dedup();
    SiteVerdict::NotRefuted { roots: ok_roots, premises }
}
