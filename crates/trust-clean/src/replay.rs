// trust-clean/replay.rs: Proof replay engine for verifying proof certificates
//
// Replays a proof certificate step-by-step against a proof context,
// checking that each inference rule application is valid. This provides
// an independent verification layer on top of the clean kernel: the
// replayer checks structural validity of the proof tree, while clean
// kernel checks type-theoretic soundness.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::time::{Duration, Instant};

use trust_types::fx::FxHashMap;
use trust_types::{Formula, Sort};

use crate::reconstruction::LeanProofTerm;

// ---------------------------------------------------------------------------
// Proof context
// ---------------------------------------------------------------------------

/// A proof context tracks available axioms, lemmas, and definitions
/// for use during proof replay.
#[derive(Debug, Clone, Default)]
pub struct ProofContext {
    /// Named axioms available in the context.
    axioms: FxHashMap<String, Formula>,
    /// Named lemmas (previously proven results).
    lemmas: FxHashMap<String, Formula>,
    /// Named definitions (abbreviations).
    definitions: FxHashMap<String, Formula>,
}

impl ProofContext {
    /// Create an empty proof context.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an axiom to the context.
    pub fn add_axiom(&mut self, name: &str, formula: Formula) {
        self.axioms.insert(name.to_string(), formula);
    }

    /// Add a lemma (previously proven result) to the context.
    pub fn add_lemma(&mut self, name: &str, formula: Formula) {
        self.lemmas.insert(name.to_string(), formula);
    }

    /// Add a definition to the context.
    pub fn add_definition(&mut self, name: &str, formula: Formula) {
        self.definitions.insert(name.to_string(), formula);
    }

    /// Check whether a named axiom exists.
    #[must_use]
    pub fn has_axiom(&self, name: &str) -> bool {
        self.axioms.contains_key(name)
    }

    /// Check whether a named lemma exists.
    #[must_use]
    pub fn has_lemma(&self, name: &str) -> bool {
        self.lemmas.contains_key(name)
    }

    /// Look up an axiom by name.
    #[must_use]
    pub fn get_axiom(&self, name: &str) -> Option<&Formula> {
        self.axioms.get(name)
    }

    /// Look up a lemma by name.
    #[must_use]
    pub fn get_lemma(&self, name: &str) -> Option<&Formula> {
        self.lemmas.get(name)
    }

    /// Look up a definition by name.
    #[must_use]
    pub fn get_definition(&self, name: &str) -> Option<&Formula> {
        self.definitions.get(name)
    }

    /// Return total number of available facts (axioms + lemmas + definitions).
    #[must_use]
    pub fn fact_count(&self) -> usize {
        self.axioms.len() + self.lemmas.len() + self.definitions.len()
    }

    /// Return the names of all lemmas that are missing from this context
    /// but required by the given list of names.
    #[must_use]
    pub fn missing_lemmas(&self, required: &[String]) -> Vec<String> {
        required
            .iter()
            .filter(|name| {
                !self.axioms.contains_key(name.as_str())
                    && !self.lemmas.contains_key(name.as_str())
                    && !self.definitions.contains_key(name.as_str())
            })
            .cloned()
            .collect()
    }
}

// ---------------------------------------------------------------------------
// Replay step
// ---------------------------------------------------------------------------

/// A single step in a proof replay, recording which rule was applied
/// and what it derived.
#[derive(Debug, Clone)]
pub struct ReplayStep {
    /// The inference rule applied at this step.
    pub rule_applied: ReplayRule,
    /// Indices of premises (earlier steps) used by this step.
    pub premises: Vec<usize>,
    /// The conclusion derived at this step.
    pub conclusion: Formula,
    /// Human-readable justification string.
    pub justification: String,
}

/// Inference rules recognized by the replayer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ReplayRule {
    /// An axiom introduction.
    Axiom(String),
    /// Modus ponens (P, P -> Q |- Q).
    ModusPonens,
    /// Resolution on a pivot literal.
    Resolution,
    /// Equality rewriting.
    Rewrite,
    /// Universal instantiation.
    Instantiation,
    /// Congruence closure.
    Congruence,
    /// A reference to a named lemma in the context.
    LemmaRef(String),
    /// A reference to a named definition.
    DefinitionRef(String),
}

// ---------------------------------------------------------------------------
// Replay result
// ---------------------------------------------------------------------------

/// Result of replaying a proof certificate.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum ReplayResult {
    /// All steps verified successfully.
    Verified {
        /// Number of steps checked.
        steps_checked: usize,
    },
    /// A specific step failed verification.
    Failed {
        /// Index of the failing step.
        step_index: usize,
        /// Why it failed.
        reason: String,
    },
    /// The proof is incomplete: it depends on lemmas not in the context.
    Incomplete {
        /// Names of lemmas that are missing from the context.
        missing_lemmas: Vec<String>,
    },
}

impl ReplayResult {
    /// Returns `true` if the replay was fully verified.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, ReplayResult::Verified { .. })
    }
}

// ---------------------------------------------------------------------------
// Replay diagnostics
// ---------------------------------------------------------------------------

/// Detailed diagnostics from a proof replay with timing information.
#[derive(Debug, Clone)]
pub struct ReplayDiagnostics {
    /// Number of steps checked.
    pub steps_checked: usize,
    /// Time spent on each step.
    pub time_per_step: Vec<Duration>,
    /// Indices of steps that took disproportionately long.
    pub bottleneck_steps: Vec<usize>,
    /// Total replay wall time.
    pub total_time: Duration,
    /// The replay result.
    pub result: ReplayResult,
}

// ---------------------------------------------------------------------------
// Proof certificate (for replay)
// ---------------------------------------------------------------------------

/// A proof certificate structured for replay.
///
/// This is the replay-oriented view of a proof: an ordered sequence of
/// `ReplayStep`s plus metadata about what lemmas are required.
#[derive(Debug, Clone)]
pub struct ReplayCertificate {
    /// Ordered proof steps.
    pub steps: Vec<ReplayStep>,
    /// Names of lemmas required from the context.
    pub required_lemmas: Vec<String>,
}

// ---------------------------------------------------------------------------
// Proof replayer
// ---------------------------------------------------------------------------

/// Engine that replays proof certificates step-by-step, checking each
/// inference rule application against a proof context.
pub struct ProofReplayer {
    /// Conclusions established by already-verified steps.
    verified_conclusions: Vec<Formula>,
}

impl ProofReplayer {
    /// Create a new replayer.
    #[must_use]
    pub fn new() -> Self {
        ProofReplayer { verified_conclusions: Vec::new() }
    }

    /// Replay a proof certificate against a context.
    ///
    /// Checks every step in order. Returns `Verified` if all steps pass,
    /// `Failed` on the first bad step, or `Incomplete` if required lemmas
    /// are missing from the context.
    pub fn replay_proof(
        &mut self,
        certificate: &ReplayCertificate,
        context: &ProofContext,
    ) -> ReplayResult {
        // Check for missing lemmas first
        let missing = context.missing_lemmas(&certificate.required_lemmas);
        if !missing.is_empty() {
            return ReplayResult::Incomplete { missing_lemmas: missing };
        }

        self.verified_conclusions.clear();

        for (idx, step) in certificate.steps.iter().enumerate() {
            if let Err(reason) = self.check_step_detailed(step, context) {
                return ReplayResult::Failed {
                    step_index: idx,
                    reason: format!("step {idx} failed: {reason}"),
                };
            }
            self.verified_conclusions.push(step.conclusion.clone());
        }

        ReplayResult::Verified { steps_checked: certificate.steps.len() }
    }

    /// Check a single proof step against the context and already-verified steps.
    ///
    /// Returns `true` if the step is valid.
    #[must_use]
    pub fn check_step(&self, step: &ReplayStep, context: &ProofContext) -> bool {
        self.check_step_detailed(step, context).is_ok()
    }

    fn check_step_detailed(&self, step: &ReplayStep, context: &ProofContext) -> Result<(), String> {
        match &step.rule_applied {
            ReplayRule::Axiom(name) => {
                self.check_premise_count_and_bounds(step, 0)?;
                check_named_fact("axiom", name, context.get_axiom(name), step)
            }
            ReplayRule::LemmaRef(name) => {
                self.check_premise_count_and_bounds(step, 0)?;
                check_named_fact("lemma", name, context.get_lemma(name), step)
            }
            ReplayRule::DefinitionRef(name) => {
                self.check_premise_count_and_bounds(step, 0)?;
                check_named_fact("definition", name, context.get_definition(name), step)
            }
            ReplayRule::ModusPonens => {
                self.check_premise_count_and_bounds(step, 2)?;
                let left = &self.verified_conclusions[step.premises[0]];
                let right = &self.verified_conclusions[step.premises[1]];
                if modus_ponens_conclusion(left, right)
                    .is_some_and(|formula| formula == &step.conclusion)
                    || modus_ponens_conclusion(right, left)
                        .is_some_and(|formula| formula == &step.conclusion)
                {
                    Ok(())
                } else {
                    Err("modus ponens premises do not derive the stated conclusion".to_string())
                }
            }
            ReplayRule::Resolution => {
                self.check_premise_count_and_bounds(step, 2)?;
                let left = &self.verified_conclusions[step.premises[0]];
                let right = &self.verified_conclusions[step.premises[1]];
                if resolution_conclusions(left, right).iter().any(|f| f == &step.conclusion) {
                    Ok(())
                } else {
                    Err("resolution premises do not derive the stated conclusion".to_string())
                }
            }
            ReplayRule::Rewrite => {
                self.check_premise_count_and_bounds(step, 2)?;
                let equality = &self.verified_conclusions[step.premises[0]];
                let target = &self.verified_conclusions[step.premises[1]];
                if rewrite_conclusion(equality, target, &step.conclusion) {
                    Ok(())
                } else {
                    Err("rewrite equality does not transform target into conclusion".to_string())
                }
            }
            ReplayRule::Instantiation => {
                self.check_premise_count_and_bounds(step, 1)?;
                let quantified = &self.verified_conclusions[step.premises[0]];
                if instantiation_conclusion(quantified, &step.conclusion) {
                    Ok(())
                } else {
                    Err("instantiation conclusion is not the quantified body".to_string())
                }
            }
            ReplayRule::Congruence => {
                self.check_premise_count_and_bounds(step, 1)?;
                let premise = &self.verified_conclusions[step.premises[0]];
                if premise == &step.conclusion {
                    Ok(())
                } else {
                    Err("congruence step lacks evidence for a changed conclusion".to_string())
                }
            }
        }
    }

    fn check_premise_count_and_bounds(
        &self,
        step: &ReplayStep,
        expected: usize,
    ) -> Result<(), String> {
        if step.premises.len() != expected {
            return Err(format!(
                "{:?} requires {expected} premise(s), got {}",
                step.rule_applied,
                step.premises.len()
            ));
        }
        for &premise in &step.premises {
            if premise >= self.verified_conclusions.len() {
                return Err(format!(
                    "premise {premise} is not available; only {} prior step(s) verified",
                    self.verified_conclusions.len()
                ));
            }
        }
        Ok(())
    }

    /// Replay a proof certificate with detailed timing diagnostics.
    pub fn replay_with_diagnostics(
        &mut self,
        certificate: &ReplayCertificate,
        context: &ProofContext,
    ) -> ReplayDiagnostics {
        let overall_start = Instant::now();

        // Check for missing lemmas first
        let missing = context.missing_lemmas(&certificate.required_lemmas);
        if !missing.is_empty() {
            return ReplayDiagnostics {
                steps_checked: 0,
                time_per_step: Vec::new(),
                bottleneck_steps: Vec::new(),
                total_time: overall_start.elapsed(),
                result: ReplayResult::Incomplete { missing_lemmas: missing },
            };
        }

        self.verified_conclusions.clear();
        let mut time_per_step = Vec::with_capacity(certificate.steps.len());

        for (idx, step) in certificate.steps.iter().enumerate() {
            let step_start = Instant::now();
            let step_result = self.check_step_detailed(step, context);
            let elapsed = step_start.elapsed();
            time_per_step.push(elapsed);

            if let Err(reason) = step_result {
                let total_time = overall_start.elapsed();
                let bottleneck_steps = find_bottlenecks(&time_per_step);
                return ReplayDiagnostics {
                    steps_checked: idx,
                    time_per_step,
                    bottleneck_steps,
                    total_time,
                    result: ReplayResult::Failed {
                        step_index: idx,
                        reason: format!("step {idx} failed: {reason}"),
                    },
                };
            }
            self.verified_conclusions.push(step.conclusion.clone());
        }

        let total_time = overall_start.elapsed();
        let bottleneck_steps = find_bottlenecks(&time_per_step);
        ReplayDiagnostics {
            steps_checked: certificate.steps.len(),
            time_per_step,
            bottleneck_steps,
            total_time,
            result: ReplayResult::Verified { steps_checked: certificate.steps.len() },
        }
    }
}

impl Default for ProofReplayer {
    fn default() -> Self {
        Self::new()
    }
}

fn modus_ponens_conclusion<'a>(premise: &Formula, implication: &'a Formula) -> Option<&'a Formula> {
    let Formula::Implies(antecedent, consequent) = implication else {
        return None;
    };
    (antecedent.as_ref() == premise).then_some(consequent.as_ref())
}

fn check_named_fact(
    kind: &str,
    name: &str,
    formula: Option<&Formula>,
    step: &ReplayStep,
) -> Result<(), String> {
    let Some(formula) = formula else {
        return Err(format!("{kind} '{name}' is not present in the proof context"));
    };
    if formula == &step.conclusion {
        Ok(())
    } else {
        Err(format!("{kind} '{name}' conclusion does not match the proof step"))
    }
}

fn resolution_conclusions(left: &Formula, right: &Formula) -> Vec<Formula> {
    let left_clause = clause_literals(left);
    let right_clause = clause_literals(right);
    let mut conclusions = Vec::new();

    for (left_idx, left_lit) in left_clause.iter().enumerate() {
        for (right_idx, right_lit) in right_clause.iter().enumerate() {
            if !are_complements(left_lit, right_lit) {
                continue;
            }

            let mut resolvent = Vec::new();
            resolvent.extend(
                left_clause
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != left_idx)
                    .map(|(_, lit)| lit.clone()),
            );
            resolvent.extend(
                right_clause
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != right_idx)
                    .map(|(_, lit)| lit.clone()),
            );
            conclusions.push(formula_from_clause(resolvent));
        }
    }

    conclusions
}

fn clause_literals(formula: &Formula) -> Vec<Formula> {
    match formula {
        Formula::Or(literals) => literals.clone(),
        Formula::Bool(false) => Vec::new(),
        _ => vec![formula.clone()],
    }
}

fn formula_from_clause(mut literals: Vec<Formula>) -> Formula {
    match literals.len() {
        0 => Formula::Bool(false),
        1 => literals.pop().expect("single literal"),
        _ => Formula::Or(literals),
    }
}

fn are_complements(left: &Formula, right: &Formula) -> bool {
    match (left, right) {
        (Formula::Not(inner), other) | (other, Formula::Not(inner)) => inner.as_ref() == other,
        _ => false,
    }
}

fn rewrite_conclusion(equality: &Formula, target: &Formula, conclusion: &Formula) -> bool {
    let Formula::Eq(left, right) = equality else {
        return false;
    };

    rewrites_to(target, left, right, conclusion) || rewrites_to(target, right, left, conclusion)
}

fn rewrites_to(target: &Formula, from: &Formula, to: &Formula, conclusion: &Formula) -> bool {
    target != conclusion
        && target.clone().map(&mut |node| if &node == from { to.clone() } else { node })
            == *conclusion
}

fn instantiation_conclusion(quantified: &Formula, conclusion: &Formula) -> bool {
    match quantified {
        Formula::Forall(_, body) => body.as_ref() == conclusion,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Conversion from LeanProofTerm to ReplayCertificate
// ---------------------------------------------------------------------------

/// Build a `ReplayCertificate` from a `LeanProofTerm`.
///
/// Walks the proof term tree and extracts a linear sequence of replay steps.
/// This is the bridge between the reconstruction module's output and the
/// replay engine's input.
#[must_use]
pub fn certificate_from_proof_term(term: &LeanProofTerm) -> ReplayCertificate {
    let mut steps = Vec::new();
    let mut required_lemmas = Vec::new();
    extract_steps(term, &mut steps, &mut required_lemmas);
    ReplayCertificate { steps, required_lemmas }
}

/// Recursively extract replay steps from a proof term.
fn extract_steps(
    term: &LeanProofTerm,
    steps: &mut Vec<ReplayStep>,
    required_lemmas: &mut Vec<String>,
) -> usize {
    match term {
        LeanProofTerm::Const(name) => {
            let rule = if name.starts_with("Trust.Axiom.") {
                ReplayRule::Axiom(name.clone())
            } else {
                required_lemmas.push(name.clone());
                ReplayRule::LemmaRef(name.clone())
            };
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: rule,
                premises: Vec::new(),
                conclusion: formula_for_named_proof_constant(name),
                justification: format!("reference to {name}"),
            });
            idx
        }
        LeanProofTerm::App(f, a) => {
            let f_idx = extract_steps(f, steps, required_lemmas);
            let a_idx = extract_steps(a, steps, required_lemmas);
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::ModusPonens,
                premises: vec![f_idx, a_idx],
                conclusion: derived_application_conclusion(
                    &steps[f_idx].conclusion,
                    &steps[a_idx].conclusion,
                ),
                justification: format!("application of step {f_idx} to step {a_idx}"),
            });
            idx
        }
        LeanProofTerm::Lambda { binder_name, body, .. } => {
            let body_idx = extract_steps(body, steps, required_lemmas);
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::Instantiation,
                premises: vec![body_idx],
                conclusion: steps[body_idx].conclusion.clone(),
                justification: format!("lambda abstraction over {binder_name}"),
            });
            idx
        }
        LeanProofTerm::Let { name, value, body, .. } => {
            let val_idx = extract_steps(value, steps, required_lemmas);
            let body_idx = extract_steps(body, steps, required_lemmas);
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::Rewrite,
                premises: vec![val_idx, body_idx],
                conclusion: steps[body_idx].conclusion.clone(),
                justification: format!("let binding {name}"),
            });
            idx
        }
        LeanProofTerm::Var(i) => {
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::LemmaRef(format!("__var_{i}")),
                premises: Vec::new(),
                conclusion: Formula::Var(format!("__var_{i}"), Sort::Bool),
                justification: format!("variable reference {i}"),
            });
            required_lemmas.push(format!("__var_{i}"));
            idx
        }
        LeanProofTerm::ByAssumption { hypothesis_index } => {
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::LemmaRef(format!("__hyp_{hypothesis_index}")),
                premises: Vec::new(),
                conclusion: Formula::Var(format!("__hyp_{hypothesis_index}"), Sort::Bool),
                justification: format!("assumption {hypothesis_index}"),
            });
            required_lemmas.push(format!("__hyp_{hypothesis_index}"));
            idx
        }
        LeanProofTerm::ByDecidability { proposition } => {
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::Axiom("decidability".to_string()),
                premises: Vec::new(),
                conclusion: proposition.clone(),
                justification: "decidability".to_string(),
            });
            idx
        }
        LeanProofTerm::Sort(_) => {
            let idx = steps.len();
            steps.push(ReplayStep {
                rule_applied: ReplayRule::Axiom("sort".to_string()),
                premises: Vec::new(),
                conclusion: Formula::Var("sort".to_string(), Sort::Bool),
                justification: "sort/type".to_string(),
            });
            idx
        }
    }
}

fn formula_for_named_proof_constant(name: &str) -> Formula {
    match name {
        "True.intro" => Formula::Bool(true),
        "False" => Formula::Bool(false),
        _ => Formula::Var(name.to_string(), Sort::Bool),
    }
}

fn derived_application_conclusion(function: &Formula, argument: &Formula) -> Formula {
    modus_ponens_conclusion(argument, function)
        .cloned()
        .unwrap_or_else(|| Formula::Var(format!("app({function:?}, {argument:?})"), Sort::Bool))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Identify bottleneck steps: those taking more than 2x the average.
fn find_bottlenecks(times: &[Duration]) -> Vec<usize> {
    if times.is_empty() {
        return Vec::new();
    }
    let total: Duration = times.iter().sum();
    let avg_nanos = total.as_nanos() / times.len() as u128;
    let threshold = avg_nanos * 2;

    times.iter().enumerate().filter(|(_, t)| t.as_nanos() > threshold).map(|(i, _)| i).collect()
}

// ---------------------------------------------------------------------------
// Trust: Replay checkpoint — save/restore replay state
// ---------------------------------------------------------------------------

/// A checkpoint of the replay state, allowing save/restore during replay.
///
/// Captures the replayer's verified conclusions at a specific point so that
/// replay can be restarted from that point rather than from the beginning.
#[derive(Debug, Clone)]
pub struct ReplayCheckpoint {
    /// Index of the step at which this checkpoint was taken.
    pub step_index: usize,
    /// Verified conclusions up to the checkpoint step.
    pub verified_conclusions: Vec<Formula>,
}

/// Replay a proof certificate with checkpoint support.
///
/// If `checkpoint` is `Some`, resumes replay from that checkpoint rather
/// than from the beginning. Returns the result plus a new checkpoint at
/// the end of the successful replay (or at the failure point).
pub fn checkpoint_replay(
    certificate: &ReplayCertificate,
    context: &ProofContext,
    checkpoint: Option<&ReplayCheckpoint>,
) -> (ReplayResult, ReplayCheckpoint) {
    let mut replayer = ProofReplayer::new();

    let missing = context.missing_lemmas(&certificate.required_lemmas);
    if !missing.is_empty() {
        let cp = ReplayCheckpoint { step_index: 0, verified_conclusions: Vec::new() };
        return (ReplayResult::Incomplete { missing_lemmas: missing }, cp);
    }

    let start_index = if let Some(cp) = checkpoint {
        if cp.step_index > certificate.steps.len() {
            let checkpoint = ReplayCheckpoint {
                step_index: certificate.steps.len(),
                verified_conclusions: Vec::new(),
            };
            return (
                ReplayResult::Failed {
                    step_index: certificate.steps.len(),
                    reason: format!(
                        "checkpoint step {} is past certificate length {}",
                        cp.step_index,
                        certificate.steps.len()
                    ),
                },
                checkpoint,
            );
        }
        if cp.verified_conclusions.len() != cp.step_index {
            let checkpoint = ReplayCheckpoint { step_index: 0, verified_conclusions: Vec::new() };
            return (
                ReplayResult::Failed {
                    step_index: cp.step_index,
                    reason: format!(
                        "checkpoint has {} conclusion(s) for step index {}",
                        cp.verified_conclusions.len(),
                        cp.step_index
                    ),
                },
                checkpoint,
            );
        }

        for (idx, step) in certificate.steps.iter().take(cp.step_index).enumerate() {
            if let Err(reason) = replayer.check_step_detailed(step, context) {
                let checkpoint = ReplayCheckpoint {
                    step_index: idx,
                    verified_conclusions: replayer.verified_conclusions.clone(),
                };
                return (
                    ReplayResult::Failed {
                        step_index: idx,
                        reason: format!("checkpoint prefix step {idx} failed: {reason}"),
                    },
                    checkpoint,
                );
            }
            if cp.verified_conclusions[idx] != step.conclusion {
                let checkpoint = ReplayCheckpoint {
                    step_index: idx,
                    verified_conclusions: replayer.verified_conclusions.clone(),
                };
                return (
                    ReplayResult::Failed {
                        step_index: idx,
                        reason: "checkpoint conclusion does not match certificate".to_string(),
                    },
                    checkpoint,
                );
            }
            replayer.verified_conclusions.push(step.conclusion.clone());
        }
        cp.step_index
    } else {
        0
    };

    for (rel_idx, step) in certificate.steps.iter().enumerate().skip(start_index) {
        if let Err(reason) = replayer.check_step_detailed(step, context) {
            let cp = ReplayCheckpoint {
                step_index: rel_idx,
                verified_conclusions: replayer.verified_conclusions.clone(),
            };
            return (
                ReplayResult::Failed {
                    step_index: rel_idx,
                    reason: format!("step {rel_idx} failed: {reason}"),
                },
                cp,
            );
        }
        replayer.verified_conclusions.push(step.conclusion.clone());
    }

    let cp = ReplayCheckpoint {
        step_index: certificate.steps.len(),
        verified_conclusions: replayer.verified_conclusions.clone(),
    };
    (ReplayResult::Verified { steps_checked: certificate.steps.len() - start_index }, cp)
}

// ---------------------------------------------------------------------------
// Trust: Failure diagnosis — explain why a proof step failed
// ---------------------------------------------------------------------------

/// Diagnosis of why a particular replay step failed.
#[derive(Debug, Clone)]
pub struct FailureDiagnosis {
    /// Index of the failing step.
    pub step_index: usize,
    /// The rule that was applied.
    pub rule: ReplayRule,
    /// Human-readable explanation of the failure.
    pub explanation: String,
    /// Specific missing prerequisites (axioms, lemmas, or premise indices).
    pub missing_prerequisites: Vec<String>,
}

/// Diagnose why a specific proof step failed.
///
/// Examines the step's rule, premises, and the proof context to produce
/// a human-readable explanation of the failure cause.
#[must_use]
pub fn diagnose_failure(
    step_index: usize,
    certificate: &ReplayCertificate,
    context: &ProofContext,
    verified_count: usize,
) -> FailureDiagnosis {
    let step = match certificate.steps.get(step_index) {
        Some(s) => s,
        None => {
            return FailureDiagnosis {
                step_index,
                rule: ReplayRule::Axiom("unknown".to_string()),
                explanation: format!(
                    "step index {step_index} is out of bounds (total steps: {})",
                    certificate.steps.len()
                ),
                missing_prerequisites: vec![],
            };
        }
    };

    let mut missing = Vec::new();
    let explanation = match &step.rule_applied {
        ReplayRule::Axiom(name) => {
            if !context.has_axiom(name) {
                missing.push(format!("axiom:{name}"));
                format!("axiom '{name}' is not present in the proof context")
            } else {
                format!("axiom '{name}' exists but step failed for unknown reason")
            }
        }
        ReplayRule::LemmaRef(name) => {
            if !context.has_lemma(name) {
                missing.push(format!("lemma:{name}"));
                format!("lemma '{name}' is not present in the proof context")
            } else {
                format!("lemma '{name}' exists but step failed for unknown reason")
            }
        }
        ReplayRule::DefinitionRef(name) => {
            if context.get_definition(name).is_none() {
                missing.push(format!("definition:{name}"));
                format!("definition '{name}' is not present in the proof context")
            } else {
                format!("definition '{name}' exists but step failed for unknown reason")
            }
        }
        ReplayRule::ModusPonens | ReplayRule::Resolution | ReplayRule::Rewrite => {
            let needed = 2;
            if step.premises.len() != needed {
                format!(
                    "{:?} requires {} premises but got {}",
                    step.rule_applied,
                    needed,
                    step.premises.len()
                )
            } else {
                for &p in &step.premises {
                    if p >= verified_count {
                        missing.push(format!("premise:{p}"));
                    }
                }
                if missing.is_empty() {
                    format!(
                        "{:?} failed: premises are verified but conclusion does not follow",
                        step.rule_applied
                    )
                } else {
                    format!(
                        "{:?} failed: premise(s) {} not yet verified (only {} steps verified)",
                        step.rule_applied,
                        missing.join(", "),
                        verified_count
                    )
                }
            }
        }
        ReplayRule::Instantiation | ReplayRule::Congruence => {
            if step.premises.len() != 1 {
                format!(
                    "{:?} requires 1 premise but got {}",
                    step.rule_applied,
                    step.premises.len()
                )
            } else if step.premises[0] >= verified_count {
                missing.push(format!("premise:{}", step.premises[0]));
                format!(
                    "{:?} failed: premise {} not yet verified",
                    step.rule_applied, step.premises[0]
                )
            } else {
                format!(
                    "{:?} failed: premise is verified but conclusion does not follow",
                    step.rule_applied
                )
            }
        }
    };

    FailureDiagnosis {
        step_index,
        rule: step.rule_applied.clone(),
        explanation,
        missing_prerequisites: missing,
    }
}

// ---------------------------------------------------------------------------
// Trust: Fix suggestion — propose alternative proof steps
// ---------------------------------------------------------------------------

/// A suggested fix for a failed proof step.
#[derive(Debug, Clone)]
pub struct SuggestedFix {
    /// Index of the step this fix targets.
    pub target_step: usize,
    /// Description of the suggested change.
    pub description: String,
    /// The replacement step (if applicable).
    pub replacement: Option<ReplayStep>,
}

/// Suggest fixes for a failed proof step.
///
/// Analyzes the failure diagnosis and proposes alternative rules or
/// additional context that might make the step succeed.
#[must_use]
pub fn suggest_fix(diagnosis: &FailureDiagnosis, context: &ProofContext) -> Vec<SuggestedFix> {
    let mut suggestions = Vec::new();

    // Suggest adding missing prerequisites
    for prereq in &diagnosis.missing_prerequisites {
        if let Some(name) = prereq.strip_prefix("axiom:") {
            suggestions.push(SuggestedFix {
                target_step: diagnosis.step_index,
                description: format!("add axiom '{name}' to the proof context"),
                replacement: None,
            });
        } else if let Some(name) = prereq.strip_prefix("lemma:") {
            suggestions.push(SuggestedFix {
                target_step: diagnosis.step_index,
                description: format!("add lemma '{name}' to the proof context or prove it first"),
                replacement: None,
            });
        } else if let Some(name) = prereq.strip_prefix("definition:") {
            suggestions.push(SuggestedFix {
                target_step: diagnosis.step_index,
                description: format!("add definition '{name}' to the proof context"),
                replacement: None,
            });
        }
    }

    // Suggest alternative rules based on the failed rule
    match &diagnosis.rule {
        ReplayRule::ModusPonens => {
            // Suggest trying Resolution instead
            suggestions.push(SuggestedFix {
                target_step: diagnosis.step_index,
                description: "try Resolution instead of ModusPonens".to_string(),
                replacement: None,
            });
        }
        ReplayRule::Axiom(name) => {
            // Suggest similar axioms from context
            for (ax_name, _) in context.axioms.iter() {
                if ax_name != name && shared_prefix_len(ax_name, name) > 3 {
                    suggestions.push(SuggestedFix {
                        target_step: diagnosis.step_index,
                        description: format!("try axiom '{ax_name}' instead of '{name}'"),
                        replacement: Some(ReplayStep {
                            rule_applied: ReplayRule::Axiom(ax_name.clone()),
                            premises: Vec::new(),
                            conclusion: Formula::Bool(true),
                            justification: format!("suggested alternative axiom: {ax_name}"),
                        }),
                    });
                }
            }
        }
        _ => {}
    }

    if suggestions.is_empty() {
        suggestions.push(SuggestedFix {
            target_step: diagnosis.step_index,
            description: "no automatic fix available; manual proof editing required".to_string(),
            replacement: None,
        });
    }

    suggestions
}

/// Count the length of the shared prefix between two strings.
fn shared_prefix_len(a: &str, b: &str) -> usize {
    a.chars().zip(b.chars()).take_while(|(ca, cb)| ca == cb).count()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use trust_types::Sort;

    use super::*;

    // -----------------------------------------------------------------------
    // ProofContext tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_context_add_and_lookup_axiom() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax1", Formula::Bool(true));
        assert!(ctx.has_axiom("ax1"));
        assert!(!ctx.has_axiom("ax2"));
        assert_eq!(ctx.get_axiom("ax1"), Some(&Formula::Bool(true)));
    }

    #[test]
    fn test_context_add_and_lookup_lemma() {
        let mut ctx = ProofContext::new();
        ctx.add_lemma("lem1", Formula::Bool(false));
        assert!(ctx.has_lemma("lem1"));
        assert_eq!(ctx.get_lemma("lem1"), Some(&Formula::Bool(false)));
    }

    #[test]
    fn test_context_add_and_lookup_definition() {
        let mut ctx = ProofContext::new();
        ctx.add_definition("def1", Formula::Int(42));
        assert_eq!(ctx.get_definition("def1"), Some(&Formula::Int(42)));
    }

    #[test]
    fn test_context_fact_count() {
        let mut ctx = ProofContext::new();
        assert_eq!(ctx.fact_count(), 0);
        ctx.add_axiom("a", Formula::Bool(true));
        ctx.add_lemma("b", Formula::Bool(true));
        ctx.add_definition("c", Formula::Bool(true));
        assert_eq!(ctx.fact_count(), 3);
    }

    #[test]
    fn test_context_missing_lemmas() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax1", Formula::Bool(true));
        ctx.add_lemma("lem1", Formula::Bool(true));

        let required = vec!["ax1".to_string(), "lem1".to_string(), "missing1".to_string()];
        let missing = ctx.missing_lemmas(&required);
        assert_eq!(missing, vec!["missing1".to_string()]);
    }

    // -----------------------------------------------------------------------
    // ReplayResult tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_result_is_verified() {
        let verified = ReplayResult::Verified { steps_checked: 5 };
        assert!(verified.is_verified());

        let failed = ReplayResult::Failed { step_index: 0, reason: "bad".into() };
        assert!(!failed.is_verified());

        let incomplete = ReplayResult::Incomplete { missing_lemmas: vec!["x".into()] };
        assert!(!incomplete.is_verified());
    }

    // -----------------------------------------------------------------------
    // Replay valid proof
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_valid_proof() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax_p", Formula::Bool(true));
        ctx.add_axiom(
            "ax_imp",
            Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true))),
        );

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax_p".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "axiom".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax_imp".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Implies(
                        Box::new(Formula::Bool(true)),
                        Box::new(Formula::Bool(true)),
                    ),
                    justification: "implication axiom".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::ModusPonens,
                    premises: vec![0, 1],
                    conclusion: Formula::Bool(true),
                    justification: "mp".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(result.is_verified());
        if let ReplayResult::Verified { steps_checked } = result {
            assert_eq!(steps_checked, 3);
        }
    }

    // -----------------------------------------------------------------------
    // Replay detects invalid step
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_detects_invalid_step() {
        let ctx = ProofContext::new(); // no axioms

        let cert = ReplayCertificate {
            steps: vec![ReplayStep {
                rule_applied: ReplayRule::Axiom("nonexistent".to_string()),
                premises: Vec::new(),
                conclusion: Formula::Bool(true),
                justification: "bad axiom".into(),
            }],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(!result.is_verified());
        if let ReplayResult::Failed { step_index, .. } = result {
            assert_eq!(step_index, 0);
        } else {
            panic!("expected Failed, got {result:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Replay detects missing lemmas
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_detects_missing_lemmas() {
        let ctx = ProofContext::new();

        let cert =
            ReplayCertificate { steps: vec![], required_lemmas: vec!["needed_lemma".to_string()] };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        if let ReplayResult::Incomplete { missing_lemmas } = result {
            assert_eq!(missing_lemmas, vec!["needed_lemma".to_string()]);
        } else {
            panic!("expected Incomplete, got {result:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Replay with out-of-bounds premise
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_fails_on_out_of_bounds_premise() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax1", Formula::Bool(true));

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax1".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "axiom".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::ModusPonens,
                    premises: vec![0, 99], // 99 is out of bounds
                    conclusion: Formula::Bool(true),
                    justification: "bad ref".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        if let ReplayResult::Failed { step_index, .. } = result {
            assert_eq!(step_index, 1);
        } else {
            panic!("expected Failed, got {result:?}");
        }
    }

    // -----------------------------------------------------------------------
    // Replay with diagnostics
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_with_diagnostics_verified() {
        let mut ctx = ProofContext::new();
        let quantified =
            Formula::Forall(vec![("x".into(), Sort::Int)], Box::new(Formula::Bool(true)));
        ctx.add_axiom("ax1", quantified.clone());

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax1".to_string()),
                    premises: Vec::new(),
                    conclusion: quantified,
                    justification: "axiom".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Instantiation,
                    premises: vec![0],
                    conclusion: Formula::Bool(true),
                    justification: "instantiation".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let diag = replayer.replay_with_diagnostics(&cert, &ctx);
        assert_eq!(diag.steps_checked, 2);
        assert_eq!(diag.time_per_step.len(), 2);
        assert!(diag.result.is_verified());
    }

    #[test]
    fn test_replay_with_diagnostics_incomplete() {
        let ctx = ProofContext::new();
        let cert =
            ReplayCertificate { steps: vec![], required_lemmas: vec!["missing".to_string()] };

        let mut replayer = ProofReplayer::new();
        let diag = replayer.replay_with_diagnostics(&cert, &ctx);
        assert_eq!(diag.steps_checked, 0);
        assert!(!diag.result.is_verified());
    }

    // -----------------------------------------------------------------------
    // check_step unit tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_check_step_lemma_ref() {
        let mut ctx = ProofContext::new();
        ctx.add_lemma("lem1", Formula::Bool(true));

        let step = ReplayStep {
            rule_applied: ReplayRule::LemmaRef("lem1".to_string()),
            premises: Vec::new(),
            conclusion: Formula::Bool(true),
            justification: "lemma".into(),
        };

        let replayer = ProofReplayer::new();
        assert!(replayer.check_step(&step, &ctx));
    }

    #[test]
    fn test_check_step_definition_ref() {
        let mut ctx = ProofContext::new();
        ctx.add_definition("def1", Formula::Int(1));

        let step = ReplayStep {
            rule_applied: ReplayRule::DefinitionRef("def1".to_string()),
            premises: Vec::new(),
            conclusion: Formula::Int(1),
            justification: "def".into(),
        };

        let replayer = ProofReplayer::new();
        assert!(replayer.check_step(&step, &ctx));
    }

    #[test]
    fn test_named_fact_rules_reject_stray_premises() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax1", Formula::Bool(true));
        ctx.add_lemma("lem1", Formula::Bool(true));
        ctx.add_definition("def1", Formula::Bool(true));

        let replayer = ProofReplayer::new();
        for step in [
            ReplayStep {
                rule_applied: ReplayRule::Axiom("ax1".to_string()),
                premises: vec![0],
                conclusion: Formula::Bool(true),
                justification: "axiom with bogus premise".into(),
            },
            ReplayStep {
                rule_applied: ReplayRule::LemmaRef("lem1".to_string()),
                premises: vec![0],
                conclusion: Formula::Bool(true),
                justification: "lemma with bogus premise".into(),
            },
            ReplayStep {
                rule_applied: ReplayRule::DefinitionRef("def1".to_string()),
                premises: vec![0],
                conclusion: Formula::Bool(true),
                justification: "definition with bogus premise".into(),
            },
        ] {
            assert!(
                !replayer.check_step(&step, &ctx),
                "named fact step with premises must be rejected: {step:?}"
            );
        }
    }

    #[test]
    fn test_check_step_congruence() {
        // Congruence needs 1 premise that is in verified_conclusions
        let replayer = ProofReplayer::new(); // empty verified_conclusions

        let step = ReplayStep {
            rule_applied: ReplayRule::Congruence,
            premises: vec![0],
            conclusion: Formula::Bool(true),
            justification: "cong".into(),
        };
        // No verified conclusions yet, so premise 0 is out of range
        assert!(!replayer.check_step(&step, &ProofContext::new()));
    }

    // -----------------------------------------------------------------------
    // certificate_from_proof_term
    // -----------------------------------------------------------------------

    #[test]
    fn test_certificate_from_const() {
        let term = LeanProofTerm::Const("Trust.Axiom.foo".to_string());
        let cert = certificate_from_proof_term(&term);
        assert_eq!(cert.steps.len(), 1);
        assert_eq!(cert.steps[0].rule_applied, ReplayRule::Axiom("Trust.Axiom.foo".to_string()));
        assert_eq!(
            cert.steps[0].conclusion,
            Formula::Var("Trust.Axiom.foo".to_string(), Sort::Bool)
        );
        assert!(cert.required_lemmas.is_empty());
    }

    #[test]
    fn test_certificate_from_app() {
        let term = LeanProofTerm::App(
            Box::new(LeanProofTerm::Const("Trust.Axiom.a".to_string())),
            Box::new(LeanProofTerm::Const("Trust.Axiom.b".to_string())),
        );
        let cert = certificate_from_proof_term(&term);
        // 2 consts + 1 app = 3 steps
        assert_eq!(cert.steps.len(), 3);
        assert_eq!(cert.steps[2].rule_applied, ReplayRule::ModusPonens);
        assert_eq!(cert.steps[2].premises, vec![0, 1]);
    }

    #[test]
    fn test_certificate_from_decidability() {
        let f = Formula::Var("x".into(), Sort::Bool);
        let term = LeanProofTerm::ByDecidability { proposition: f.clone() };
        let cert = certificate_from_proof_term(&term);
        assert_eq!(cert.steps.len(), 1);
        assert_eq!(cert.steps[0].rule_applied, ReplayRule::Axiom("decidability".to_string()));
        assert_eq!(cert.steps[0].conclusion, f);
    }

    // -----------------------------------------------------------------------
    // ProofReplayer::default
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_replayer_default() {
        let r = ProofReplayer::default();
        assert!(r.verified_conclusions.is_empty());
    }

    // -----------------------------------------------------------------------
    // find_bottlenecks
    // -----------------------------------------------------------------------

    #[test]
    fn test_find_bottlenecks_empty() {
        assert!(find_bottlenecks(&[]).is_empty());
    }

    #[test]
    fn test_find_bottlenecks_uniform() {
        let times = vec![Duration::from_micros(10); 5];
        // All equal, none > 2x average
        assert!(find_bottlenecks(&times).is_empty());
    }

    #[test]
    fn test_find_bottlenecks_with_outlier() {
        let mut times = vec![Duration::from_micros(10); 4];
        times.push(Duration::from_micros(1000)); // big outlier
        let bottlenecks = find_bottlenecks(&times);
        assert!(bottlenecks.contains(&4));
    }

    // -----------------------------------------------------------------------
    // Multi-step replay with lemma and resolution
    // -----------------------------------------------------------------------

    #[test]
    fn test_replay_multi_step_with_resolution() {
        let mut ctx = ProofContext::new();
        let pivot = Formula::Var("p".to_string(), Sort::Bool);
        let left_rest = Formula::Var("left".to_string(), Sort::Bool);
        let right_rest = Formula::Var("right".to_string(), Sort::Bool);
        let left_clause = Formula::Or(vec![left_rest.clone(), pivot.clone()]);
        let right_clause = Formula::Or(vec![Formula::Not(Box::new(pivot)), right_rest.clone()]);
        let conclusion = Formula::Or(vec![left_rest, right_rest]);
        ctx.add_axiom("ax_pos", left_clause.clone());
        ctx.add_axiom("ax_neg", right_clause.clone());

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax_pos".to_string()),
                    premises: Vec::new(),
                    conclusion: left_clause,
                    justification: "positive clause".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax_neg".to_string()),
                    premises: Vec::new(),
                    conclusion: right_clause,
                    justification: "negative clause".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Resolution,
                    premises: vec![0, 1],
                    conclusion,
                    justification: "resolve".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(result.is_verified());
    }

    #[test]
    fn test_resolution_rejects_arbitrary_conclusion() {
        let mut ctx = ProofContext::new();
        let pivot = Formula::Var("p".to_string(), Sort::Bool);
        let left_clause =
            Formula::Or(vec![Formula::Var("a".to_string(), Sort::Bool), pivot.clone()]);
        let right_clause = Formula::Or(vec![
            Formula::Not(Box::new(pivot)),
            Formula::Var("b".to_string(), Sort::Bool),
        ]);
        ctx.add_axiom("left", left_clause.clone());
        ctx.add_axiom("right", right_clause.clone());

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("left".to_string()),
                    premises: Vec::new(),
                    conclusion: left_clause,
                    justification: "left".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("right".to_string()),
                    premises: Vec::new(),
                    conclusion: right_clause,
                    justification: "right".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Resolution,
                    premises: vec![0, 1],
                    conclusion: Formula::Bool(true),
                    justification: "bad resolvent".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(matches!(result, ReplayResult::Failed { step_index: 2, .. }));
    }

    #[test]
    fn test_rewrite_rejects_arbitrary_conclusion() {
        let mut ctx = ProofContext::new();
        let equality = Formula::Eq(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Var("b".to_string(), Sort::Int)),
        );
        let target = Formula::Eq(
            Box::new(Formula::Var("a".to_string(), Sort::Int)),
            Box::new(Formula::Int(1)),
        );
        ctx.add_axiom("eq", equality.clone());
        ctx.add_axiom("target", target.clone());

        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("eq".to_string()),
                    premises: Vec::new(),
                    conclusion: equality,
                    justification: "eq".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("target".to_string()),
                    premises: Vec::new(),
                    conclusion: target,
                    justification: "target".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Rewrite,
                    premises: vec![0, 1],
                    conclusion: Formula::Bool(true),
                    justification: "bad rewrite".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(matches!(result, ReplayResult::Failed { step_index: 2, .. }));
    }

    #[test]
    fn test_instantiation_rejects_non_quantified_premise() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("plain", Formula::Bool(true));
        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("plain".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "plain".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Instantiation,
                    premises: vec![0],
                    conclusion: Formula::Bool(true),
                    justification: "bad instantiation".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(matches!(result, ReplayResult::Failed { step_index: 1, .. }));
    }

    #[test]
    fn test_congruence_rejects_changed_conclusion_without_evidence() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("plain", Formula::Bool(true));
        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("plain".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "plain".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Congruence,
                    premises: vec![0],
                    conclusion: Formula::Bool(false),
                    justification: "bad congruence".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };

        let mut replayer = ProofReplayer::new();
        let result = replayer.replay_proof(&cert, &ctx);
        assert!(matches!(result, ReplayResult::Failed { step_index: 1, .. }));
    }

    // -----------------------------------------------------------------------
    // checkpoint_replay tests
    // -----------------------------------------------------------------------

    fn make_axiom_cert(ctx: &mut ProofContext) -> ReplayCertificate {
        ctx.add_axiom("ax1", Formula::Bool(true));
        let ax2 = Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true)));
        ctx.add_axiom("ax2", ax2.clone());
        ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax1".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "axiom 1".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax2".to_string()),
                    premises: Vec::new(),
                    conclusion: ax2.clone(),
                    justification: "axiom 2".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::ModusPonens,
                    premises: vec![0, 1],
                    conclusion: Formula::Bool(true),
                    justification: "mp".into(),
                },
            ],
            required_lemmas: Vec::new(),
        }
    }

    #[test]
    fn test_checkpoint_replay_from_scratch() {
        let mut ctx = ProofContext::new();
        let cert = make_axiom_cert(&mut ctx);
        let (result, cp) = checkpoint_replay(&cert, &ctx, None);
        assert!(result.is_verified());
        assert_eq!(cp.step_index, 3);
        assert_eq!(cp.verified_conclusions.len(), 3);
    }

    #[test]
    fn test_checkpoint_replay_from_checkpoint() {
        let mut ctx = ProofContext::new();
        let cert = make_axiom_cert(&mut ctx);

        // First, replay to get a checkpoint at step 2
        let checkpoint = ReplayCheckpoint {
            step_index: 2,
            verified_conclusions: vec![
                Formula::Bool(true),
                Formula::Implies(Box::new(Formula::Bool(true)), Box::new(Formula::Bool(true))),
            ],
        };

        let (result, cp) = checkpoint_replay(&cert, &ctx, Some(&checkpoint));
        assert!(result.is_verified());
        // Should have checked only step 2 (the last one)
        if let ReplayResult::Verified { steps_checked } = result {
            assert_eq!(steps_checked, 1);
        }
        assert_eq!(cp.step_index, 3);
    }

    #[test]
    fn test_checkpoint_replay_missing_lemmas() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate { steps: vec![], required_lemmas: vec!["needed".to_string()] };
        let (result, cp) = checkpoint_replay(&cert, &ctx, None);
        assert!(!result.is_verified());
        assert_eq!(cp.step_index, 0);
    }

    #[test]
    fn test_checkpoint_replay_failure_returns_checkpoint() {
        let ctx = ProofContext::new(); // no axioms
        let cert = ReplayCertificate {
            steps: vec![ReplayStep {
                rule_applied: ReplayRule::Axiom("missing".to_string()),
                premises: Vec::new(),
                conclusion: Formula::Bool(true),
                justification: "bad".into(),
            }],
            required_lemmas: Vec::new(),
        };
        let (result, cp) = checkpoint_replay(&cert, &ctx, None);
        assert!(!result.is_verified());
        assert_eq!(cp.step_index, 0);
    }

    #[test]
    fn test_checkpoint_replay_revalidates_checkpoint_prefix() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("missing".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "missing axiom".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::Congruence,
                    premises: vec![0],
                    conclusion: Formula::Bool(true),
                    justification: "would pass if prefix were trusted".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };
        let forged =
            ReplayCheckpoint { step_index: 1, verified_conclusions: vec![Formula::Bool(true)] };

        let (result, cp) = checkpoint_replay(&cert, &ctx, Some(&forged));
        assert!(matches!(result, ReplayResult::Failed { step_index: 0, .. }));
        assert_eq!(cp.step_index, 0);
    }

    // -----------------------------------------------------------------------
    // diagnose_failure tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_diagnose_failure_missing_axiom() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate {
            steps: vec![ReplayStep {
                rule_applied: ReplayRule::Axiom("missing_ax".to_string()),
                premises: Vec::new(),
                conclusion: Formula::Bool(true),
                justification: "bad".into(),
            }],
            required_lemmas: Vec::new(),
        };
        let diag = diagnose_failure(0, &cert, &ctx, 0);
        assert_eq!(diag.step_index, 0);
        assert!(diag.explanation.contains("missing_ax"));
        assert!(diag.missing_prerequisites.contains(&"axiom:missing_ax".to_string()));
    }

    #[test]
    fn test_diagnose_failure_missing_lemma() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate {
            steps: vec![ReplayStep {
                rule_applied: ReplayRule::LemmaRef("missing_lem".to_string()),
                premises: Vec::new(),
                conclusion: Formula::Bool(true),
                justification: "bad".into(),
            }],
            required_lemmas: Vec::new(),
        };
        let diag = diagnose_failure(0, &cert, &ctx, 0);
        assert!(diag.explanation.contains("missing_lem"));
        assert!(diag.missing_prerequisites.contains(&"lemma:missing_lem".to_string()));
    }

    #[test]
    fn test_diagnose_failure_out_of_bounds_step() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate { steps: vec![], required_lemmas: Vec::new() };
        let diag = diagnose_failure(99, &cert, &ctx, 0);
        assert!(diag.explanation.contains("out of bounds"));
    }

    #[test]
    fn test_diagnose_failure_modus_ponens_bad_premise() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("ax1", Formula::Bool(true));
        let cert = ReplayCertificate {
            steps: vec![
                ReplayStep {
                    rule_applied: ReplayRule::Axiom("ax1".to_string()),
                    premises: Vec::new(),
                    conclusion: Formula::Bool(true),
                    justification: "ok".into(),
                },
                ReplayStep {
                    rule_applied: ReplayRule::ModusPonens,
                    premises: vec![0, 5], // 5 is out of range
                    conclusion: Formula::Bool(true),
                    justification: "bad".into(),
                },
            ],
            required_lemmas: Vec::new(),
        };
        // Only 1 step verified (step 0)
        let diag = diagnose_failure(1, &cert, &ctx, 1);
        assert!(diag.missing_prerequisites.contains(&"premise:5".to_string()));
    }

    #[test]
    fn test_diagnose_failure_instantiation_bad_premise() {
        let ctx = ProofContext::new();
        let cert = ReplayCertificate {
            steps: vec![ReplayStep {
                rule_applied: ReplayRule::Instantiation,
                premises: vec![99],
                conclusion: Formula::Bool(true),
                justification: "bad".into(),
            }],
            required_lemmas: Vec::new(),
        };
        let diag = diagnose_failure(0, &cert, &ctx, 0);
        assert!(diag.explanation.contains("not yet verified"));
    }

    // -----------------------------------------------------------------------
    // suggest_fix tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_suggest_fix_missing_axiom() {
        let ctx = ProofContext::new();
        let diag = FailureDiagnosis {
            step_index: 0,
            rule: ReplayRule::Axiom("foo".to_string()),
            explanation: "axiom 'foo' not present".into(),
            missing_prerequisites: vec!["axiom:foo".to_string()],
        };
        let fixes = suggest_fix(&diag, &ctx);
        assert!(!fixes.is_empty());
        assert!(fixes[0].description.contains("add axiom"));
    }

    #[test]
    fn test_suggest_fix_missing_lemma() {
        let ctx = ProofContext::new();
        let diag = FailureDiagnosis {
            step_index: 0,
            rule: ReplayRule::LemmaRef("bar".to_string()),
            explanation: "lemma 'bar' not present".into(),
            missing_prerequisites: vec!["lemma:bar".to_string()],
        };
        let fixes = suggest_fix(&diag, &ctx);
        assert!(!fixes.is_empty());
        assert!(fixes[0].description.contains("add lemma"));
    }

    #[test]
    fn test_suggest_fix_alternative_axiom() {
        let mut ctx = ProofContext::new();
        ctx.add_axiom("tRust_overflow_add", Formula::Bool(true));
        let diag = FailureDiagnosis {
            step_index: 0,
            rule: ReplayRule::Axiom("tRust_overflow_sub".to_string()),
            explanation: "axiom not present".into(),
            missing_prerequisites: vec!["axiom:tRust_overflow_sub".to_string()],
        };
        let fixes = suggest_fix(&diag, &ctx);
        // Should suggest the similar axiom "tRust_overflow_add"
        let has_alt = fixes.iter().any(|f| f.description.contains("tRust_overflow_add"));
        assert!(has_alt, "should suggest similar axiom, got: {fixes:?}");
    }

    #[test]
    fn test_suggest_fix_modus_ponens_suggests_resolution() {
        let ctx = ProofContext::new();
        let diag = FailureDiagnosis {
            step_index: 0,
            rule: ReplayRule::ModusPonens,
            explanation: "failed".into(),
            missing_prerequisites: vec![],
        };
        let fixes = suggest_fix(&diag, &ctx);
        let has_resolution = fixes.iter().any(|f| f.description.contains("Resolution"));
        assert!(has_resolution, "should suggest Resolution alternative");
    }

    #[test]
    fn test_suggest_fix_no_suggestions_gives_manual() {
        let ctx = ProofContext::new();
        let diag = FailureDiagnosis {
            step_index: 0,
            rule: ReplayRule::Congruence,
            explanation: "failed".into(),
            missing_prerequisites: vec![],
        };
        let fixes = suggest_fix(&diag, &ctx);
        assert!(!fixes.is_empty());
        assert!(fixes[0].description.contains("manual proof editing"));
    }

    // -----------------------------------------------------------------------
    // shared_prefix_len
    // -----------------------------------------------------------------------

    #[test]
    fn test_shared_prefix_len_identical() {
        assert_eq!(shared_prefix_len("hello", "hello"), 5);
    }

    #[test]
    fn test_shared_prefix_len_partial() {
        assert_eq!(shared_prefix_len("hello", "help"), 3);
    }

    #[test]
    fn test_shared_prefix_len_none() {
        assert_eq!(shared_prefix_len("abc", "xyz"), 0);
    }
}
