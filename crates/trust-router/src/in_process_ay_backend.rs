// trust-router/in_process_ay_backend.rs: In-process ay-dpll SMT backend.
//
// Trust: This backend replaces the subprocess SMT path (incremental_ay.rs,
// smtlib_backend.rs) for L0 safety obligations. Instead of serializing the VC
// formula to textual SMT-LIB2 and shelling out to the `ay` binary — which
// discards ay's in-process proof artifacts — this backend solves the VC
// directly against the linked ay-dpll library and captures ay's real
// `UnsatProofArtifact`.
//
// ## Soundness boundary (the one load-bearing rule)
//
// `verify()` returns `VerificationResult::Proved` IF AND ONLY IF:
//   1. ay reports the violation formula UNSAT (`ExecuteTypedResult::Verified`), AND
//   2. there is an `unsat_proof` whose `strict_verdict` is
//      `StrictProofVerdict::Verified(_)`.
//
// In every other case (UNSAT but artifact `None`, UNSAT but strict verdict
// `Rejected`, `Unknown`, `ExecuteError`, empty result vector, any guarded
// failure) the backend returns `Unknown` — NEVER `Proved`. A SAT result
// (`Counterexample`) returns `Failed`. This guarantees the backend can never
// false-PROVE: a reported `Proved` always carries a strict-checked ay
// refutation proof.
//
// ## VC convention
//
// The VC formula IS the violation / failure condition (the same convention the
// subprocess `smtlib_backend::parse_solver_output` uses: unsat => Proved, sat
// => Failed). We assert the formula and check satisfiability. UNSAT (no
// violation reachable) => candidate PROVED. SAT (violation witnessed) => Failed.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;
use std::time::Instant;

use ay::{
    ProofAcceptanceMode, StrictProofVerdict, UnsatProofArtifact, is_reserved_symbol,
    panic_payload_to_string,
};
use ay_bindings::execute_direct::{self, ExecuteCounterexample, ExecuteTypedResult, ModelValue};
use ay_bindings::{AYProgram, Constraint, Sort as AYSort, SortInner as AYSortInner};
use sha2::{Digest, Sha256};
use trust_types::ay_bridge::{formula_to_expr, sort_to_ay};
use trust_types::{
    Counterexample, CounterexampleValue, Formula, ProofStrength, Sort, VcKind,
    VerificationCondition, VerificationResult, check_formula_sort, pred_arg_sorts,
};

// Trust: scoped suppression of solver-internal tracing diagnostics (see ay_log.rs).
use crate::ay_log::with_ay_diagnostics_policy;
use crate::backend_trait::unsupported_mir_unknown;
use crate::{BackendRole, VerificationBackend, smt2_export};

/// Stable solver name reported in every `VerificationResult` this backend emits.
const SOLVER_NAME: &str = "ay-in-process";

/// Process-global lock serializing in-process ay executions. The `ay-dpll`
/// direct-execution path carries shared/non-reentrant state, so concurrent
/// `execute_incremental` calls (e.g. parallel test threads, or a rayon-parallel
/// router dispatch) can race and produce nondeterministic verdicts. Routing the
/// refinement-validation VC class to this backend increased that concurrency and
/// surfaced the latent flakiness; serializing the actual solve keeps every verdict
/// deterministic. The lock is held only across the solve, not VC construction.
static AY_EXEC_LOCK: Mutex<()> = Mutex::new(());

/// In-process ay-dpll SMT backend for L0 safety verification conditions.
///
/// Dispatches the VC's violation formula to the linked `ay-dpll` library via
/// [`ay_bindings::execute_direct`], with proof production enabled so an UNSAT
/// result carries a strict-checked [`ay::UnsatProofArtifact`]. The backend only
/// returns [`VerificationResult::Proved`] when that artifact's strict verdict is
/// [`StrictProofVerdict::Verified`] — see the module docs for the full
/// soundness boundary.
#[derive(Debug, Clone)]
pub struct InProcessAyBackend {
    timeout_ms: u64,
}

/// Canonical SMT-LIB2 rendering of the exact constraint program this backend
/// asserts for a VC violation formula: one `(set-logic ...)` (same
/// `smt2_export::detect_logic` the solve uses), one declaration per free
/// variable / predicate symbol (same `collect_free_vars` / `collect_pred_symbols`
/// sets `build_program` declares), one `(assert ...)` of the violation formula,
/// then `(check-sat)`.
///
/// This is the textual transcript of the in-process solve: `build_program`
/// constructs the identical logical program natively (via `formula_to_expr`)
/// from the same formula, so this rendering is a faithful, reproducible record
/// of the query ay decided. Callers that hold a strict-checked ay verdict for
/// `formula` may digest these bytes as the solve's solver-transcript evidence
/// artifact (the same text the Carcara N-version cross-check replays). It is a
/// pure function of the formula — it never invents solver output.
#[must_use]
pub fn problem_smt2(formula: &Formula) -> String {
    let mut out = String::new();
    out.push_str(&format!("(set-logic {})\n", smt2_export::detect_logic(formula)));
    for decl in smt2_export::emit_declarations(formula) {
        out.push_str(&decl);
        out.push('\n');
    }
    out.push_str(&format!("(assert {})\n", smt2_export::formula_to_smt2(formula)));
    out.push_str("(check-sat)\n");
    out
}

/// Domain-separation tag for the revalidation problem digest, so a bare
/// `problem_smt2` hash computed elsewhere can never be mistaken for a
/// revalidation receipt's digest.
const SMT_REVALIDATION_DIGEST_DOMAIN: &[u8] = b"trust.smt-revalidation.v1\0";

/// Public revalidation requests are capped at the backend's maintained
/// per-query ceiling. This limits the AY `:timeout` value; it is not a hard
/// wall-clock deadline because formula construction and waiting for the
/// process-global AY execution lock happen outside the solver query.
const MAX_SMT_REVALIDATION_BUDGET_MS: u64 = 90_000;

/// Sealed-authority S1 (SolverReplayAuthority, SMT lane): the outcome of the
/// gate's OWN fresh strict re-solve of a violation `Formula`.
///
/// Zero-authority data cannot construct this: the fields are private, there is
/// no serde, no `Default`, and no public constructor. The ONLY producer is
/// [`revalidate_vc_unsat_strict`], which runs a fresh in-process ay solve and
/// applies the strict solver-proof bar (`StrictProofVerdict::Verified` plus
/// consumer acceptance) to the artifact of THAT solve — never to any carried
/// field. The normal backend's bounded finite-domain fallback is deliberately
/// disabled here: it is sound evidence, but it is not an AY solver-proof
/// replay. Holding a value is proof the check ran in this invocation. It
/// records only the canonical problem bytes and their domain-separated digest
/// for the mint site to bind against the row; it grants nothing on its own
/// (constitution U6: carried data is a reject-only pre-filter, authority flows
/// from the gate's own verdict).
#[derive(Debug, Clone)]
pub struct SmtRevalidationOutcome {
    canonical_problem: String,
    canonical_problem_sha256: String,
    time_ms: u64,
}

impl SmtRevalidationOutcome {
    /// The canonical `.smt2` rendering of the formula the gate re-solved.
    #[must_use]
    pub fn canonical_problem(&self) -> &str {
        &self.canonical_problem
    }

    /// Domain-separated SHA-256 of [`Self::canonical_problem`].
    #[must_use]
    pub fn canonical_problem_sha256(&self) -> &str {
        &self.canonical_problem_sha256
    }

    /// Wall time of the fresh re-solve, in milliseconds.
    #[must_use]
    pub fn time_ms(&self) -> u64 {
        self.time_ms
    }
}

/// Gate-side revalidation of a VC that some producer labeled `Proved`: re-encode
/// `formula` and run a FRESH in-process ay solve with an AY query timeout of
/// `budget_ms`, capped at `MAX_SMT_REVALIDATION_BUDGET_MS`. Zero is invalid
/// and fails closed. The timeout starts after AY's process-global execution
/// lock is acquired, so callers that require a hard end-to-end deadline must
/// enforce it outside this synchronous API.
///
/// Returns `Some` ONLY when that fresh solve independently reaches `Proved`
/// through an UNSAT result carrying a strict-checked proof. Every other outcome
/// returns `None`, which is the status quo (demotion), and is the ONLY behavior for:
/// - `Failed` — the fresh solve found the violation SATISFIABLE, i.e. the
///   producer's `Proved` was wrong; revalidation must NEVER mint here
///   (refutation immunity: authority can only be granted, never used to override
///   a real counterexample);
/// - `Unknown` / timeout / a `budget_ms` too small to finish — no mint.
///
/// Authority flows from THIS solve's verdict, never from any field the caller
/// carried in. The returned outcome is not itself an authority — it records the
/// canonical problem bytes + digest the gate checked, for the mint site to bind
/// to the exact VC row.
#[must_use]
pub fn revalidate_vc_unsat_strict(
    formula: &Formula,
    budget_ms: u64,
) -> Option<SmtRevalidationOutcome> {
    if budget_ms == 0 {
        return None;
    }
    let backend =
        InProcessAyBackend::new().with_timeout(budget_ms.min(MAX_SMT_REVALIDATION_BUDGET_MS));
    let start = Instant::now();
    // The gate's OWN fresh, contained solve of the row's own formula. This path
    // suppresses solver diagnostics, catches panics, and disables the normal
    // bounded-finite fallback: only a strict-checked AY proof can mint S1.
    if !matches!(backend.run_strict(formula), VerificationResult::Proved { .. }) {
        return None;
    }
    let canonical_problem = problem_smt2(formula);
    let mut hasher = Sha256::new();
    hasher.update(SMT_REVALIDATION_DIGEST_DOMAIN);
    hasher.update(canonical_problem.as_bytes());
    Some(SmtRevalidationOutcome {
        canonical_problem,
        canonical_problem_sha256: format!("{:x}", hasher.finalize()),
        time_ms: start.elapsed().as_millis() as u64,
    })
}

impl InProcessAyBackend {
    /// Create a new in-process ay backend.
    #[must_use]
    pub fn new() -> Self {
        Self { timeout_ms: 90_000 }
    }

    /// Set the explicit per-obligation timeout. Zero disables the solver
    /// timeout for library callers that deliberately need an unbounded run.
    #[must_use]
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Build an [`AYProgram`] for the VC's violation formula with proof
    /// production enabled and every free variable declared.
    fn build_program(&self, formula: &Formula) -> AYProgram {
        let mut program = AYProgram::new();

        // Enable proof production. Without this option the executor produces no
        // proof artifact and `unsat_proof` is `None`, which under our soundness
        // rule degrades any UNSAT to `Unknown`. Mirrors the proof-witness path
        // exercised in ay-bindings' execute_direct tests.
        program.add_constraint(Constraint::set_option(":produce-proofs", "true"));

        // Bound every in-process check-sat with a per-obligation wall-clock
        // deadline. Without it a hard bit-vector VC (e.g. FxHash-style
        // wrapping_mul/xor/rotate over u32/u64) bit-blasts to a SAT instance
        // that runs UNBOUNDED: the solve never reaches a fixpoint, the
        // PersistentBvCache repeatedly hits its cap and full-clears (re-blast
        // thrash) and the clause trace overruns its budget, so the obligation
        // never returns a verdict and the whole `check` run is killed.
        //
        // `(set-option :timeout <ms>)` is honored by ay's executor as a real
        // per-check-sat deadline polled inside the CDCL/theory loops, which
        // degrades a non-converging solve to UNKNOWN. That is SOUND here: this
        // backend only emits `Proved` on a strict-checked UNSAT proof, so an
        // Unknown (timeout) outcome can never be reported as Proved.
        //
        if self.timeout_ms > 0 {
            program
                .add_constraint(Constraint::set_option(":timeout", &self.timeout_ms.to_string()));
        }

        // Pick the SMT logic from the formula's theory features, reusing the
        // same detection the subprocess SMT export uses.
        program.set_logic(smt2_export::detect_logic(formula));

        // Lever A: register any algebraic-datatype sorts BEFORE declaring consts
        // of those sorts, so ay applies the datatype theory (constructor/selector/
        // tester axioms). A by-name back-edge reference (empty constructors)
        // carries no definition and ay maps it to an unconstrained uninterpreted
        // sort — SOUND (a fresh datatype/uninterpreted const can never make the
        // context vacuously UNSAT). `declare_datatype` is idempotent (deduped by
        // name) and `upgrade_logic_for_datatypes` keeps the logic datatype-capable.
        //
        // The sorts come from `visit_datatype_bearing_sorts`, the SAME walker the
        // text exporter's preamble uses, NOT from the free vars: a ground
        // `Ctor`/`Sel`/`IsCtor` term carries a datatype sort that no `Var`
        // mentions, and keying off free vars alone would assert a term over a
        // datatype this program never declared.
        smt2_export::visit_datatype_bearing_sorts(formula, &mut |sort| {
            Self::declare_datatype_sorts(&mut program, sort);
        });
        program.upgrade_logic_for_datatypes();

        let free_vars = smt2_export::collect_free_vars(formula);

        // Declare each free (non-quantifier-bound) variable exactly once before
        // the assertion, mirroring how smt2_export emits declarations.
        for (name, sort) in free_vars {
            let _ = program.declare_const(name, sort_to_ay(&sort));
        }

        // Declare uninterpreted predicate symbols used by Formula::Pred. The
        // text SMT exporter emits matching arity declarations; the direct AY
        // bridge requires them too before any FuncApp assertion is translated.
        for (name, arg_sorts) in collect_pred_symbols(formula) {
            let ay_arg_sorts = arg_sorts.iter().map(sort_to_ay).collect();
            program.declare_fun(name, ay_arg_sorts, AYSort::bool());
        }

        // Assert the violation formula and check satisfiability.
        program.assert(formula_to_expr(formula));
        program.check_sat();

        program
    }

    /// Recursively register every FULL algebraic-datatype definition reachable
    /// from `sort` with `program` (deduped by name; nested datatypes declared
    /// before the datatypes that use them). A by-name back-edge reference (empty
    /// constructors) carries no definition and is skipped — ay handles it as an
    /// unconstrained uninterpreted sort.
    ///
    /// This registers the same datatype NAMES as the text path's
    /// `Sort::datatype_declarations`, but NOT structurally the same sorts. The
    /// text path emits a genuinely inductive
    /// `(declare-datatype Expr ((App (f Expr) (x Expr)) …))`, whose recursive
    /// field sort IS `Expr` — so the solver's datatype theory supplies the
    /// constructor/selector/tester axioms AND the acyclicity (well-foundedness)
    /// of the term algebra. Here `sort_to_ay` maps the by-name child to
    /// `AYSort::uninterpreted(name)` (see `trust_types::ay_bridge::sort_to_ay`),
    /// which carries no constructors, no selectors, no testers, and no
    /// acyclicity: the registered ay datatype is FLAT, its recursive positions
    /// opaque. The gap is strictly FEWER facts than the text path, which is the
    /// sound direction (an unconstrained sort can never make the context
    /// vacuously UNSAT — see the soundness note above): an obligation that needs
    /// the inductive structure reports Unknown on this lane instead of proving.
    fn declare_datatype_sorts(program: &mut AYProgram, sort: &Sort) {
        match sort {
            Sort::Array(idx, elem) => {
                Self::declare_datatype_sorts(program, idx);
                Self::declare_datatype_sorts(program, elem);
            }
            Sort::Datatype { name, constructors } => {
                // A by-name reference has nothing to declare.
                if constructors.is_empty() || program.is_datatype_declared(name) {
                    return;
                }
                // Declare nested datatype field definitions first.
                for (_, fields) in constructors {
                    for (_, fsort) in fields {
                        Self::declare_datatype_sorts(program, fsort);
                    }
                }
                // Build and register THIS datatype. `sort_to_ay` of a full
                // `Sort::Datatype` yields an ay datatype sort whose inner
                // `DatatypeSort` carries the constructors/fields.
                if let AYSortInner::Datatype(dt) = sort_to_ay(sort).inner() {
                    let _ = program.declare_datatype(dt.clone());
                }
            }
            _ => {}
        }
    }

    /// Map an UNSAT outcome's proof artifact to `Proved` only when it is
    /// strict-Verified; otherwise `Unknown`. This is the load-bearing soundness
    /// gate. Takes the artifact directly (rather than the `#[non_exhaustive]`
    /// `CheckSatOutcome`) so the `None` path is unit-testable.
    ///
    /// `formula` is the violation formula that was asserted to ay; it is used
    /// only under the `carcara-crosscheck` feature to rebuild the problem .smt2
    /// for the N-version Carcara cross-check (see [`Self::apply_carcara_gate`]).
    /// On default and single-feature builds it is unused.
    fn unsat_to_result(
        unsat_proof: Option<&UnsatProofArtifact>,
        time_ms: u64,
        formula: &Formula,
    ) -> VerificationResult {
        match unsat_proof {
            Some(artifact) => match &artifact.strict_verdict {
                StrictProofVerdict::Verified(_) => {
                    // Defense in depth: the consumer-facing acceptance check must
                    // also pass before we hand out a trust seal.
                    if artifact.accept_for_consumer(ProofAcceptanceMode::Strict).is_ok() {
                        let proved = VerificationResult::Proved {
                            solver: SOLVER_NAME.into(),
                            time_ms,
                            // The UNSAT proof passed ay's strict proof checker
                            // (StrictProofVerdict::Verified + the consumer-facing
                            // accept gate), so this earns SmtBacked assurance --
                            // strictly above the Unchecked subprocess path. It is
                            // deliberately NOT Certified: ay's checker is trusted
                            // code (and has had meta-soundness bugs), so a kernel
                            // reconstruction is required for true-proof Certified.
                            strength: ProofStrength::smt_unsat_strict_checked(),
                            proof_certificate: artifact.lrat_certificate.clone(),
                            solver_warnings: None,
                            native_proof_envelope: None,
                        };

                        // Certification transport gate (D.9).  On an `ay-certify`
                        // build this promotes to `Certified` for the fragments
                        // Clean can reconstruct — but only after the kernel has
                        // certified the refutation from this VC alone AND the
                        // packaged envelope has been replayed back to the same
                        // verdict.  ay's LRAT bytes are carried through unchanged;
                        // the kernel payload rides in the typed
                        // `native_proof_envelope` slot beside them.  Every other
                        // build, and every declining step, keeps the honest
                        // strict-checked SmtBacked result.
                        let proved = Self::promote_to_certified(proved, formula, time_ms);

                        // Track D increment 2: N-version cross-check. ay accepted
                        // this UNSAT proof under its OWN strict checker; before we
                        // surface it as Proved, re-check the SAME Alethe proof with
                        // Carcara, an independently implemented Alethe checker. The
                        // gate is MONOTONE: it may only downgrade Proved -> Unknown
                        // (on Carcara Reject), never strengthen. Carcara Unavailable
                        // is NOT disagreement and keeps ay's strict-checked Proved,
                        // so an absent Carcara never introduces a false-FAIL. On
                        // builds without the cross-check feature this is an identity.
                        Self::carcara_cross_check_proved(proved, formula, artifact, time_ms)
                    } else {
                        VerificationResult::Unknown {
                            solver: SOLVER_NAME.into(),
                            time_ms,
                            reason: "UNSAT proof artifact rejected at strict consumer boundary"
                                .to_string(),
                        }
                    }
                }
                StrictProofVerdict::Rejected(reason) => VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms,
                    reason: format!("UNSAT but strict proof verdict rejected: {reason}"),
                },
                // `StrictProofVerdict` is #[non_exhaustive]. Any future verdict
                // that is not `Verified(_)` must fail closed to Unknown — never
                // a trust seal.
                _ => VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms,
                    reason: "UNSAT but strict proof verdict was not Verified".to_string(),
                },
            },
            None => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: "UNSAT but no strict-checked proof artifact was produced".to_string(),
            },
        }
    }

    /// Carcara N-version cross-check dispatcher (Track D increment 2).
    ///
    /// Identity on builds WITHOUT the `carcara-crosscheck` feature: the input
    /// `proved` (already strict-checked by ay) is returned unchanged. This arm
    /// keeps the default and single-feature builds byte-for-byte identical to
    /// the pre-increment behaviour.
    #[cfg(not(all(feature = "ay-backend", feature = "carcara-crosscheck")))]
    fn carcara_cross_check_proved(
        proved: VerificationResult,
        _formula: &Formula,
        _artifact: &UnsatProofArtifact,
        _time_ms: u64,
    ) -> VerificationResult {
        proved
    }

    /// Certification transport gate.  Builds without the experimental Clean
    /// reconstruction feature keep the strict-checked `SmtBacked` verdict.
    #[cfg(not(feature = "ay-certify"))]
    fn promote_to_certified(
        proved: VerificationResult,
        _formula: &Formula,
        _time_ms: u64,
    ) -> VerificationResult {
        proved
    }

    /// Fail-closed certification transport gate for builds with experimental
    /// Clean reconstruction enabled (D.9).
    ///
    /// This gate was an identity for as long as the result carrier had only the
    /// single opaque `proof_certificate` byte vector — already occupied by ay's
    /// LRAT bytes. Changing `strength` alone would have dropped the Clean
    /// payload on the floor and advertised replayable kernel evidence that no
    /// consumer could replay. `Proved` now carries a second, typed slot
    /// (`native_proof_envelope`), so the payload has somewhere honest to go and
    /// the LRAT bytes are preserved rather than displaced.
    ///
    /// Promotion requires ALL of:
    ///
    /// 1. the VC is the recognized fragment and the Clean kernel certifies its
    ///    refutation from the VC ALONE (`certify_lia_violation_formula` rebuilds
    ///    the context from the recognized bounds — nothing is taken on trust);
    /// 2. the payload packages into a structurally accepted envelope;
    /// 3. **the envelope replays** — we re-derive the context from the formula a
    ///    second time and watch the kernel re-accept the very bytes we are about
    ///    to ship. We refuse to stamp `Certified` on evidence that does not
    ///    reproduce the verdict, so an envelope that would fail at a downstream
    ///    consumer never leaves here labelled as proof.
    ///
    /// Any step declining returns the honest strict-checked `SmtBacked` verdict
    /// unchanged. Non-fragment formulas exit at the cheap syntactic recognizer,
    /// so the kernel work is confined to the class that can actually certify.
    #[cfg(feature = "ay-certify")]
    fn promote_to_certified(
        proved: VerificationResult,
        formula: &Formula,
        _time_ms: u64,
    ) -> VerificationResult {
        if !matches!(proved, VerificationResult::Proved { .. }) {
            return proved;
        }
        // (1) Certify from the VC itself.
        let Ok(Some(crate::ay_certify::CertifyOutcome::Certified(payload))) =
            crate::ay_certify::certify_lia_violation_formula(formula)
        else {
            return proved;
        };
        // (2) Package into the typed, zero-authority carrier.
        let Some(envelope) = crate::ay_certify::certified_envelope_for(formula, &payload) else {
            return proved;
        };
        // (3) Independently replay what we are about to ship.
        if !crate::ay_certify::replay_certified_envelope(formula, &envelope).is_replayed() {
            return proved;
        }
        // (4) Promote, PRESERVING ay's LRAT certificate and every other field.
        match proved {
            VerificationResult::Proved {
                solver,
                time_ms,
                proof_certificate,
                solver_warnings,
                ..
            } => VerificationResult::Proved {
                solver,
                time_ms,
                strength: ProofStrength::smt_unsat_certified(),
                proof_certificate,
                solver_warnings,
                native_proof_envelope: Some(envelope),
            },
            other => other,
        }
    }

    /// Carcara N-version cross-check dispatcher (Track D increment 2).
    ///
    /// With the `carcara-crosscheck` feature on: rebuild the problem .smt2 from
    /// the violation formula, hand it plus the artifact's Alethe text and
    /// residual trust-rule count to [`carcara_cross_check`], then apply the
    /// MONOTONE [`Self::apply_carcara_gate`] (which may only downgrade
    /// `Proved -> Unknown`).
    ///
    /// [`carcara_cross_check`]: crate::carcara_cross_check::carcara_cross_check
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn carcara_cross_check_proved(
        proved: VerificationResult,
        formula: &Formula,
        artifact: &UnsatProofArtifact,
        time_ms: u64,
    ) -> VerificationResult {
        let problem_smt2 = Self::build_problem_smt2(formula);
        let cross = crate::carcara_cross_check::carcara_cross_check(
            &problem_smt2,
            &artifact.alethe,
            artifact.quality.trust_count,
        );
        Self::apply_carcara_gate(proved, cross, time_ms)
    }

    /// Rebuild the SMT-LIB2 problem text (set-logic + declarations + the
    /// asserted violation formula + check-sat) that was handed to ay, in the
    /// exact shape Carcara needs as the second input to its cross-check.
    ///
    /// This mirrors the assembly the subprocess SMT path uses
    /// (`incremental_ay`/`smt2_export`): one `(set-logic ...)`, one
    /// `(declare-fun ...)` per free var + predicate symbol, one `(assert ...)`
    /// of the violation formula, then `(check-sat)`.
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn build_problem_smt2(formula: &Formula) -> String {
        problem_smt2(formula)
    }

    /// Pure, side-effect-free decision for the Carcara N-version cross-check.
    ///
    /// Track D increment 2 soundness contract — the gate is MONOTONE, it may
    /// only downgrade `Proved -> Unknown`, never strengthen:
    /// * [`CrossCheck::Reject`] -> DOWNGRADE to `Unknown` (fail-closed): ay and
    ///   Carcara disagree, or the proof carried an unreconstructed trust rule.
    /// * [`CrossCheck::Accept`] -> keep the input `proved` (both checkers agree).
    /// * [`CrossCheck::Unavailable`] -> keep the input `proved`: Carcara is not
    ///   present / there was no proof text. Unavailable is NOT disagreement, so
    ///   it must never introduce a false-FAIL — ay's own strict check (already
    ///   passed before we reach here) still gates the Proved.
    ///
    /// Factored out (taking the already-built `proved` result and the cross-check
    /// verdict) so the decision logic is unit-testable WITHOUT driving a live
    /// solver or a live Carcara binary.
    #[cfg(all(feature = "ay-backend", feature = "carcara-crosscheck"))]
    fn apply_carcara_gate(
        proved: VerificationResult,
        cross: crate::carcara_cross_check::CrossCheck,
        time_ms: u64,
    ) -> VerificationResult {
        use crate::carcara_cross_check::CrossCheck;
        match cross {
            // Disagreement (or an unreconstructed trust rule): fail closed.
            CrossCheck::Reject => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: "carcara N-version cross-check rejected the ay UNSAT proof (or it \
                         contained unreconstructed trust rules); downgraded fail-closed"
                    .to_string(),
            },
            // Both independent checkers agree: keep the strict-checked Proved.
            CrossCheck::Accept => proved,
            // Carcara not present / no proof text: not disagreement. Keep ay's
            // strict-checked Proved — never downgrade on Unavailable.
            CrossCheck::Unavailable => proved,
        }
    }

    /// Run the VC's violation formula in-process and classify the outcome.
    ///
    /// The whole solve, including the strict proof check, runs under
    /// [`with_ay_diagnostics_policy`]: ay's solver-internal tracing
    /// diagnostics are suppressed by default so they never leak onto the
    /// embedding compiler's stderr; `TRUST_AY_LOG` opts back in.
    fn run(&self, formula: &Formula) -> VerificationResult {
        self.run_with_policy(formula, true)
    }

    /// Run the fresh-revalidation lane under the same containment boundary as
    /// the normal backend while refusing the non-solver bounded-finite proof
    /// fallback.
    fn run_strict(&self, formula: &Formula) -> VerificationResult {
        self.run_with_policy(formula, false)
    }

    fn run_with_policy(&self, formula: &Formula, allow_bounded_finite: bool) -> VerificationResult {
        // Trust (#int2bv-ice): a panic anywhere inside the in-process solve —
        // ay's bridge/translation `expect`s, the strict proof checker (the
        // `declare_fun("int2bv")` reserved-symbol ICE class), a solver-internal
        // assertion — must NOT unwind into (and abort) the embedding compiler.
        // Contain it and fail closed to Unknown: no proof, no refutation, so
        // soundness is unaffected. The panic message is preserved in the reason
        // for diagnosis. (`AY_EXEC_LOCK` is unwind-tolerant: acquisition
        // recovers a poisoned lock via `into_inner`.)
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            with_ay_diagnostics_policy(|| {
                self.solve_and_classify_with_policy(formula, allow_bounded_finite)
            })
        }));
        match outcome {
            Ok(result) => result,
            Err(payload) => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: format!(
                    "in-process ay solve panicked ({}); failing closed",
                    panic_payload_to_string(&*payload)
                ),
            },
        }
    }

    /// The actual solve + outcome classification (see [`Self::run`]).
    fn solve_and_classify_with_policy(
        &self,
        formula: &Formula,
        allow_bounded_finite: bool,
    ) -> VerificationResult {
        // A malformed VC formula — a comparison whose two operands have DIFFERENT sorts
        // (e.g. `Eq(Bool, Int)` from a discriminant-/aggregate-derived obligation) — would
        // PANIC inside `formula_to_expr`'s `.eq()`/`.int_lt()` ("same sort" assert) and ICE
        // the compiler. A solver backend must never crash on an ill-typed obligation:
        // DECLINE it as Unknown (sound — it emits no proof and no refutation) rather than
        // asserting a sort-inconsistent term.
        if !formula_comparisons_well_sorted(formula) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: "in-process ay declined: VC formula has a sort-mismatched comparison"
                    .to_string(),
            };
        }
        // A `Formula::FpFromBits`/`Formula::BvExtract` whose operand does not actually
        // infer to the BitVec sort (and width) the reinterpretation/extraction requires
        // — e.g. a vcgen-constructed `bits` operand that fell back to `Sort::Int` instead
        // of a same-width `Sort::BitVec` (the f128::clamp_magnitude census ICE #2 shape) —
        // would PANIC inside `formula_to_expr`'s `.extract()` calls (`Expr::extract`'s
        // infallible convenience wrapper: `ay-bindings` fixed the underlying `try_extract`
        // to fail closed with `SortError::Mismatch`, but the panicking wrapper is kept by
        // design for genuinely-internal invariants, so a malformed embedder-constructed
        // Formula still reaches it). DECLINE it as Unknown (sound: emits neither a proof
        // nor a refutation) instead of ICE-ing — mirrors `formula_comparisons_well_sorted`.
        if let Some(reason) = formula_bitcast_mismatch(formula) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: format!("in-process ay declined: {reason}"),
            };
        }
        // The specialized checks above retain stable diagnostics for two
        // historically observed crash classes.  The shared recursive sort
        // checker closes the rest of the translation boundary (notably a
        // non-Bool ITE condition, unequal ITE branch sorts, malformed array/BV
        // terms, or a non-predicate top-level formula).  Never rely on
        // `catch_unwind` for input validation: a caught panic still runs the
        // process-global panic hook and can leak a false compiler-ICE-looking
        // diagnostic to stderr.
        match check_formula_sort(formula) {
            Ok(Sort::Bool) => {}
            Ok(actual) => {
                return VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms: 0,
                    reason: format!(
                        "in-process ay declined: VC formula has top-level sort {actual:?}, expected Bool"
                    ),
                };
            }
            Err(error) => {
                return VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms: 0,
                    reason: format!("in-process ay declined: VC formula is sort-invalid: {error}"),
                };
            }
        }
        if let Some((name, first, second)) = free_variable_sort_conflict(formula) {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: format!(
                    "in-process ay declined: free variable `{name}` has conflicting sorts {first:?} and {second:?}"
                ),
            };
        }
        // A `Formula::Pred` whose name collides with one of ay's RESERVED builtin
        // theory-operator names (`int2bv`, `bv2nat`, `select`, …) must never be
        // declared as an uninterpreted function: ay's elaborator rejects the
        // declaration (`ReservedSymbol`), and the direct-execution declaration path
        // turns that rejection into a PANIC (`context.declare_or_get_fun`) that
        // would ICE the embedding compiler (the int2bv verify-time crash class).
        // Renaming is not an option either — an uninterpreted stand-in silently
        // drops the builtin's semantics. DECLINE the obligation instead (sound:
        // it emits neither a proof nor a refutation). Int<->BV conversions that
        // arrive as proper `Formula::IntToBv`/`BvToInt` nodes are unaffected —
        // `formula_to_expr` lowers those to ay's NATIVE operators.
        if let Some(name) =
            collect_pred_symbols(formula).into_keys().find(|name| is_reserved_symbol(name))
        {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms: 0,
                reason: format!(
                    "in-process ay declined: predicate symbol '{name}' is a reserved ay \
                     builtin theory-operator name and cannot be declared as an \
                     uninterpreted function"
                ),
            };
        }
        let program = self.build_program(formula);
        let start = Instant::now();

        // execute_incremental preserves the per-check-sat `unsat_proof` artifact
        // (execute_all / execute drop it), so it is the correct entry point for
        // capturing ay's in-process refutation proof.
        // Serialize the solve: ay-dpll's direct path is not reentrant (see
        // AY_EXEC_LOCK). Recover from a poisoned lock — a panic in another solve
        // must not wedge every subsequent obligation.
        let _ay_guard = AY_EXEC_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let outcomes = match execute_direct::execute_incremental(&program) {
            Ok(outcomes) => outcomes,
            Err(err) => {
                return VerificationResult::Unknown {
                    solver: SOLVER_NAME.into(),
                    time_ms: start.elapsed().as_millis() as u64,
                    reason: format!("in-process ay execution error: {err}"),
                };
            }
        };

        let time_ms = start.elapsed().as_millis() as u64;

        // The program has exactly one check-sat, so expect exactly one outcome.
        // An empty vector is a guarded failure: never Proved.
        let Some(outcome) = outcomes.last() else {
            return VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: "in-process ay produced no check-sat outcome".to_string(),
            };
        };

        match &outcome.result {
            // UNSAT: no violation reachable. Proved only with a strict proof.
            ExecuteTypedResult::Verified => {
                let base = Self::unsat_to_result(outcome.unsat_proof.as_ref(), time_ms, formula);
                Self::finish_verified_result(base, formula, time_ms, allow_bounded_finite)
            }
            // SAT: a violation witness exists. Surface ay's concrete model as the
            // counterexample (previously discarded as `None`, leaving a refuted
            // refinement un-witnessed — the divergence was found but its inputs
            // were not reported to the driver/agent).
            ExecuteTypedResult::Counterexample(cex) => VerificationResult::Failed {
                solver: SOLVER_NAME.into(),
                time_ms,
                counterexample: Some(counterexample_from_ay_model(cex)),
            },
            // Solver could not decide, or direct execution needs fallback.
            ExecuteTypedResult::Unknown(reason) => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: format!("in-process ay returned unknown: {reason}"),
            },
            ExecuteTypedResult::NeedsFallback(reason) => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: format!("in-process ay requires fallback: {reason}"),
            },
            // `ExecuteTypedResult` is #[non_exhaustive]. Any future outcome that
            // is not an explicit Verified (UNSAT) must fail closed to Unknown —
            // only the Verified arm above can ever yield Proved.
            _ => VerificationResult::Unknown {
                solver: SOLVER_NAME.into(),
                time_ms,
                reason: "in-process ay returned an unrecognized outcome".to_string(),
            },
        }
    }

    /// Apply the ordinary backend's complete finite-domain fallback only when
    /// policy permits it. Fresh S1 revalidation passes `false`, so an AY UNSAT
    /// result without a strict-accepted AY artifact remains `Unknown` even when
    /// a separate exhaustive proof could establish the formula.
    fn finish_verified_result(
        base: VerificationResult,
        formula: &Formula,
        time_ms: u64,
        allow_bounded_finite: bool,
    ) -> VerificationResult {
        if matches!(base, VerificationResult::Proved { .. }) || !allow_bounded_finite {
            return base;
        }

        // ay decided UNSAT but produced no strict-checked proof artifact for
        // this formula. For a finite-domain violation formula the bounded
        // exhaustive enumeration is an independent complete proof. It remains
        // available to the ordinary backend but is intentionally not solver
        // replay authority.
        bounded_finite_unsat_proof(formula, time_ms).unwrap_or(base)
    }
}

impl Default for InProcessAyBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl VerificationBackend for InProcessAyBackend {
    fn name(&self) -> &str {
        SOLVER_NAME
    }

    fn role(&self) -> BackendRole {
        BackendRole::SmtSolver
    }

    fn can_handle(&self, vc: &VerificationCondition) -> bool {
        // Only the L0 safety obligations the in-process SMT path can decide,
        // and only when direct execution is actually available. UnsupportedMir
        // and all contract/temporal/L1+/L2 kinds are excluded by construction:
        // they are simply not in this match arm.
        let kind_ok = matches!(
            &vc.kind,
            VcKind::ArithmeticOverflow { .. }
                | VcKind::ShiftOverflow { .. }
                | VcKind::NegationOverflow { .. }
                | VcKind::DivisionByZero
                | VcKind::RemainderByZero
                | VcKind::IndexOutOfBounds
                | VcKind::SliceBoundsCheck
                // The unbounded-allocation (#nia-oom) obligation's failure formula
                // is `Ge(count, CEILING)` conjoined with reaching block-defs — a
                // plain QF_LIA integer comparison squarely in ay's wheelhouse.
                // Without this arm the VC routes to "no backend can handle this"
                // and returns `unknown` instead of being refuted with a witness.
                | VcKind::UnboundedAllocation { .. }
                | VcKind::Assertion { .. }
                // Trust: translation-validation refinement obligations. The
                // data-flow/return checks emit `Not(Eq(src_expr, tgt_expr))` and the
                // control-flow check a definite-violation literal — QF_BV / QF_LIA
                // formulas ay decides. Without these arms a SAT refinement (a real
                // port-vs-reference divergence, e.g. ATERM-FINDINGS class 4) routes
                // only to the constant-folder, which returns `unknown` on any
                // symbolic formula, so the divergence is MISSED (inconclusive) and a
                // genuine refinement is left at the constant-folder's `Sound` tier
                // instead of ay's strict-checked `SmtBacked`. ay's UNSAT strict gate
                // (StrictProofVerdict::Verified) keeps PROVE sound; SAT yields the
                // counterexample witness. Multi-block refinement VCs (which the
                // single-block straight-line detector never reaches) need this.
                | VcKind::RefinementViolation { .. }
                | VcKind::TranslationValidation { .. }
                // Trust (#5-PRE-A): a caller-side PRECONDITION obligation. Its violation
                // formula is `Not(P[σ])` — P with the call's actual arguments substituted
                // (e.g. `!(5 < 10)` for an established constant precondition, or `i >= 4`
                // for a free-input violation). That is exactly the QF_LIA / QF_BV fragment
                // ay decides: UNSAT ⇒ Proved (the caller established the precondition),
                // SAT ⇒ Failed (a real input violates it, e.g. `a[i]` with `i >= len`). Any
                // OPAQUE / non-linear predicate ay cannot decide stays Unknown and is
                // fail-closed by the `build_proof_results` reclassify. Without this arm the
                // caller-side precondition VC routed ONLY to trust-wp (Unsupported →
                // permanent Unknown) even when it was a decidable comparison, so an
                // ESTABLISHED linear precondition never PROVED and the reclassify would
                // over-reject valid Rust. `verify()` is kind-agnostic (`run(&vc.formula)`),
                // so admitting the kind is sufficient.
                | VcKind::Precondition { .. }
                // Trust (contract-completeness inc-1): a DEFINITION-SITE postcondition
                // obligation. `generate_v2_contract_vcs` builds this VC's `formula` as a
                // SELF-CONTAINED violation goal that already conjoins the return-value pin
                // and the body/guard/precondition facts with `Not(predicate)` — e.g.
                // `And([_0 == x + 1, x < 100, Not(_0 > x)])`. Unlike the caller-side
                // postcondition-ASSUME scenario (where `_0` needs the callee's return
                // value and is not in scope), here the function's OWN body pins `_0`, so
                // the formula is a complete ∀-inputs proof goal ay decides by strict
                // UNSAT: UNSAT ⇒ Proved (the postcondition holds for every input), a
                // strict-checked (Gate A) certificate identical to the L0 kinds above.
                //
                // SOUNDNESS: this arm only lets ay REACH `verify`; it grants no new
                // trust. `verify` mints `Proved` ONLY on a strict-checked UNSAT proof.
                // A SATisfiable violation yields `Failed`, but the postcondition VC can
                // be SAT for a *valid* contract whose body facts the formula
                // under-approximates (e.g. the `postcondition_references_mutated_param`
                // fail-closed shape emits `Not(post)` with FREE params). So the v1/ay
                // BRIDGE (`trust_verify.rs`) substitutes ONLY an ay `Proved` for the
                // Postcondition kind and leaves a SAT/Unknown fail-closed — never a false
                // REFUTE. This arm is therefore purely ADDITIVE over the fail-closed
                // backstop: it can only turn a fail-closed Unknown into a
                // strict-UNSAT-checked Proved.
                | VcKind::Postcondition
        );
        kind_ok && execute_direct::is_available()
    }

    fn verify(&self, vc: &VerificationCondition) -> VerificationResult {
        // Defensive: UnsupportedMir must never reach a solver. can_handle already
        // excludes it, but guard here too so a direct verify() call is safe.
        if let Some(result) = unsupported_mir_unknown(vc, SOLVER_NAME, 0) {
            return result;
        }
        self.run(&vc.formula)
    }
}

/// Convert ay's SAT model into a Trust [`Counterexample`] so a refuted refinement
/// (or any refuted obligation) carries the concrete witness assignments. ay reports
/// the model in `ExecuteCounterexample::model` (with `values` as the explicitly
/// requested subset); we prefer the full model and fall back to `values`. Assignments
/// are sorted for deterministic output.
fn counterexample_from_ay_model(cex: &ExecuteCounterexample) -> Counterexample {
    let src = if cex.model.is_empty() { &cex.values } else { &cex.model };
    let mut assignments: Vec<(String, CounterexampleValue)> =
        src.iter().map(|(name, v)| (name.clone(), model_value_to_cex(v))).collect();
    assignments.sort_by(|a, b| a.0.cmp(&b.0));
    Counterexample::new(assignments)
}

/// Map a single ay `ModelValue` to a Trust [`CounterexampleValue`]. Big integers are
/// stringified-then-parsed so no `num-traits` dependency leaks in; an out-of-`i128`/
/// `u128`-range value (e.g. a >128-bit bitvector) degrades to `0` rather than panic.
fn model_value_to_cex(v: &ModelValue) -> CounterexampleValue {
    match v {
        ModelValue::Bool(b) => CounterexampleValue::Bool(*b),
        ModelValue::Int(i) => CounterexampleValue::Int(i.to_string().parse().unwrap_or(0)),
        ModelValue::BitVec { value, .. } => {
            CounterexampleValue::Uint(value.to_string().parse().unwrap_or(0))
        }
        // Reals/strings do not arise in the integer/bitvector refinement fragment;
        // surface a stable placeholder rather than dropping the binding.
        _ => CounterexampleValue::Int(0),
    }
}

/// True iff `formula` is GROUND — it contains no free (non-quantifier-bound)
/// variables, so every leaf is a literal/constant and its truth value is fully
/// determined with no unknown inputs.
///
/// Used by the default-lane safety-escalation gate in `rustc_mir_transform`:
/// a `Failed` verdict on a GROUND, refutable L0 safety obligation is a
/// GUARANTEED violation (e.g. `1 << 28 >= 1 << 28` for the nn OOM), so it may be
/// promoted from a warning to a hard build error. A formula with a free variable
/// (e.g. `a + b` overflow, `s[0]` bounds) is only conditionally violating and
/// must stay a warning — promoting it would over-fire on valid Rust.
pub fn formula_is_ground(formula: &Formula) -> bool {
    smt2_export::collect_free_vars(formula).is_empty()
}

/// True iff every COMPARISON subformula (`Eq`/`Lt`/`Le`/`Gt`/`Ge`) compares two operands
/// of the SAME inferred sort. `formula_to_expr` lowers these via `.eq()`/`.int_lt()`/…,
/// which `assert` matching sorts and PANIC on a mismatch (a Bool-vs-Int compare from a
/// malformed discriminant/aggregate obligation). Checking this first lets the backend
/// DECLINE such a VC (Unknown) instead of ICE-ing — a backend must never crash on an
/// ill-typed obligation. SOUNDNESS: declining emits neither a proof nor a refutation.
fn formula_comparisons_well_sorted(formula: &Formula) -> bool {
    use trust_types::smt_logic::infer_sort;
    let mut ok = true;
    formula.visit(&mut |sub| {
        if let Formula::Eq(a, b)
        | Formula::Lt(a, b)
        | Formula::Le(a, b)
        | Formula::Gt(a, b)
        | Formula::Ge(a, b) = sub
            && infer_sort(a) != infer_sort(b)
        {
            ok = false;
        }
    });
    ok
}

/// `Some(reason)` iff `formula` contains a `FpFromBits`/`BvExtract` node whose
/// operand does not infer to a BitVec sort with the width the reinterpretation
/// (`FpFromBits`) or extraction (`BvExtract`) actually requires.
///
/// `formula_to_expr` lowers `FpFromBits { bits, eb, sb }` via three
/// `.extract()` calls on `formula_to_expr(bits)` (the sign/exponent/significand
/// fields, each expected to slice an `(eb+sb)`-wide BitVec) and
/// `BvExtract { inner, high, low }` via one `.extract()` call on
/// `formula_to_expr(inner)`. `Expr::extract` is the INFALLIBLE convenience
/// wrapper (`try_extract(..).expect(..)`) — it panics (not returns an error) on
/// a non-BitVec operand or an out-of-range bit range. A malformed obligation
/// (`bits`/`inner` inferring to `Sort::Int` instead of the expected
/// `Sort::BitVec` — the trust m6 census ICE #2 shape: f128::clamp_magnitude's
/// magnitude-bits operand) must never reach that panic. Checked ahead of
/// `formula_to_expr` so the backend can DECLINE (Unknown — sound, since it
/// emits neither a proof nor a refutation) with the mismatch named, instead of
/// crashing the embedding compiler.
fn formula_bitcast_mismatch(formula: &Formula) -> Option<String> {
    use trust_types::smt_logic::infer_sort;
    let mut mismatch: Option<String> = None;
    formula.visit(&mut |sub| {
        if mismatch.is_some() {
            return;
        }
        match sub {
            Formula::FpFromBits { bits, eb, sb } => {
                let expected = Sort::BitVec(eb + sb);
                let actual = infer_sort(bits);
                if actual != expected {
                    mismatch = Some(format!(
                        "FpFromBits(eb={eb}, sb={sb}) requires its bits operand to be \
                         {expected:?}, but it infers to {actual:?}"
                    ));
                }
            }
            Formula::BvExtract { inner, high, low } => match infer_sort(inner) {
                Sort::BitVec(w) if low <= high && *high < w => {}
                actual => {
                    mismatch = Some(format!(
                        "BvExtract(high={high}, low={low}) requires its inner operand to be \
                         a BitVec sort with width > {high}, but it infers to {actual:?}"
                    ));
                }
            },
            _ => {}
        }
    });
    mismatch
}

/// Return the first free variable name used at two different sorts. SMT-LIB and
/// AY both have one declaration per symbol, so accepting such a formula would
/// make the native program and canonical transcript ambiguous. Quantifier-local
/// shadowing is already excluded by `collect_free_vars` and remains valid.
fn free_variable_sort_conflict(formula: &Formula) -> Option<(String, Sort, Sort)> {
    let mut sorts = BTreeMap::<String, Sort>::new();
    for (name, sort) in smt2_export::collect_free_vars(formula) {
        if let Some(previous) = sorts.insert(name.clone(), sort.clone()) {
            if previous != sort {
                return Some((name, previous, sort));
            }
        }
    }
    None
}

/// A concrete value produced by the bounded finite-domain evaluator. Mathematical
/// `Int` covers every integer/cast/`%`/`Ite` term in an LIA violation formula (the
/// SMT `Int` theory is unbounded, matching `i128` for the small magnitudes that
/// arise from bool->int casts and their sums); `Bool` covers the propositional
/// skeleton and the free bool inputs.
#[derive(Clone, Debug, PartialEq, Eq)]
enum EnumValue {
    Bool(bool),
    Int(i128),
}

/// Bounded exhaustive-enumeration proof for a FINITE-domain violation formula.
///
/// This is the bounded-model-check route for finite functional asserts: when ay
/// decides the violation formula UNSAT but cannot emit a strict-checked proof
/// artifact (an LIA `%`/`Ite`/bool-eq mix its in-process proof producer does not
/// certify), and every free variable ranges over a finitely-enumerable sort, the
/// enumeration is an INDEPENDENT, complete decision procedure: it evaluates the
/// ground violation formula on EVERY assignment of the cartesian product of the
/// free-variable domains.
///
/// Returns `Proved` (`ReasoningKind::ExhaustiveFinite` / `AssuranceLevel::Sound`)
/// IFF the violation formula evaluated to `false` on the COMPLETE finite domain —
/// i.e. no input reaches the failure block, so the asserted property holds for all
/// inputs. The attached certificate records the enumerated domain and case count
/// and is strict / re-checkable by replaying the same deterministic enumeration.
///
/// Returns `None` — DECLINE, fail-closed — in every other situation:
///   * a free variable whose sort is not finitely enumerable (Int/Array/Float/…);
///   * a total domain size above `MAX_CASES` (keeps the route bounded-cost);
///   * the evaluator cannot reduce the ground formula to a definite Bool for some
///     assignment (an unsupported node), so exhaustiveness is NOT established;
///   * any assignment SATISFIES the violation formula (a model exists), so it is
///     not a proof.
///
/// SOUNDNESS: a `Proved` is returned ONLY after the ground formula was evaluated
/// to a definite `false` on the COMPLETE finite domain by a TOTAL evaluator, so it
/// is a genuine ∀-inputs refutation of the violation — never a partial result and
/// never a trusted-solver verdict. Symmetrically it never false-REFUTES: a
/// satisfying assignment declines (returns `None`) rather than emitting `Failed`.
fn bounded_finite_unsat_proof(formula: &Formula, time_ms: u64) -> Option<VerificationResult> {
    // ~4.2M ground evaluations — a hard cost bound on the enumeration.
    const MAX_CASES: u128 = 1 << 22;
    let debug = std::env::var("TRUST_BOUNDED_MC_DEBUG").is_ok();
    let free: Vec<(String, Sort)> = smt2_export::collect_free_vars(formula).into_iter().collect();
    if debug {
        eprintln!("[BOUNDED_MC] free vars (name, sort): {free:?}");
    }

    // vcgen conjoins DEFINITIONAL equalities `var == expr` that pin each computed
    // intermediate (a bool->int `Ite` cast, a `+` sum, a `%` reduction, the xor
    // result, a checked-add overflow flag) to a function of the free inputs. Such a
    // var is FUNCTIONALLY DETERMINED: in any model the definitional conjunct forces
    // it to its defining value. So we need not (and cannot, for unbounded `Int`)
    // enumerate it — we RESOLVE it from the free-input assignment. Only the
    // truly-free, finitely-enumerable inputs are enumerated. SOUNDNESS: every model
    // assigns a defined var to its forced value (else its conjunct is false, so the
    // formula is false there anyway), so {enumerated inputs} × {forced defs} covers
    // the ENTIRE model space — all-false over it is a complete UNSAT proof.
    let defs = collect_conjunct_definitions(formula);

    // Partition the free vars: enumerate the finitely-enumerable ones WITHOUT a
    // definition; the rest must be resolvable from `defs`. A free var that is
    // neither finitely enumerable NOR defined is an unbounded free input we cannot
    // exhaust — decline (fail-closed).
    let mut domains: Vec<(String, Vec<EnumValue>)> = Vec::new();
    let mut total: u128 = 1;
    for (name, sort) in &free {
        if defs.contains_key(name) {
            continue; // resolved from its definition during evaluation
        }
        let Some(dom) = finite_domain(sort) else {
            if debug {
                eprintln!(
                    "[BOUNDED_MC] declined: free var `{name}` has non-finite sort {sort:?} and no definition"
                );
            }
            return None;
        };
        total = total.checked_mul(dom.len() as u128)?;
        if total > MAX_CASES {
            if debug {
                eprintln!("[BOUNDED_MC] declined: domain {total} exceeds budget {MAX_CASES}");
            }
            return None;
        }
        domains.push((name.clone(), dom));
    }
    if debug {
        let enumerated: Vec<&String> = domains.iter().map(|(n, _)| n).collect();
        eprintln!(
            "[BOUNDED_MC] enumerating {enumerated:?} ({total} cases); resolving {} defined vars",
            defs.len()
        );
    }

    // Mixed-radix enumeration of the full cartesian product of the enumerated
    // free-input domains.
    let n = domains.len();
    let mut idx = vec![0usize; n];
    let mut cases: u64 = 0;
    loop {
        let mut assignment: BTreeMap<String, EnumValue> = BTreeMap::new();
        for (i, (name, dom)) in domains.iter().enumerate() {
            assignment.insert(name.clone(), dom[idx[i]].clone());
        }
        // Resolve every defined var to its forced value by fixpoint (handles
        // dependency order; a cycle or an unresolvable dependency simply leaves the
        // var unbound, which makes `eval_ground` return `None` below -> decline).
        resolve_definitions(&defs, &mut assignment);

        match eval_ground(formula, &assignment) {
            // No violation in this case — continue enumerating.
            Some(EnumValue::Bool(false)) => {}
            // A satisfying assignment: the violation IS reachable, so this is not a
            // proof. Decline (fail-closed) rather than emit a refutation here — the
            // refute direction stays with ay's strict-checked SAT path.
            Some(EnumValue::Bool(true)) => {
                if debug {
                    eprintln!("[BOUNDED_MC] declined: found a satisfying assignment (not a proof)");
                }
                return None;
            }
            // A non-Bool top value or an unsupported/unresolved node: exhaustiveness
            // cannot be established for this formula. Decline.
            _ => {
                if debug {
                    eprintln!("[BOUNDED_MC] declined: formula did not reduce to a definite Bool");
                }
                return None;
            }
        }
        cases += 1;

        // Advance the mixed-radix counter; break when it wraps past the last digit.
        if n == 0 {
            break; // ground formula: the single empty assignment is the whole domain.
        }
        let mut pos = 0usize;
        let mut wrapped = false;
        loop {
            idx[pos] += 1;
            if idx[pos] < domains[pos].1.len() {
                break;
            }
            idx[pos] = 0;
            pos += 1;
            if pos == n {
                wrapped = true;
                break;
            }
        }
        if wrapped {
            break;
        }
    }

    let enumerated_free: Vec<(String, Sort)> =
        free.iter().filter(|(name, _)| !defs.contains_key(name)).cloned().collect();
    let certificate = bounded_finite_certificate(&enumerated_free, total, cases);
    if std::env::var("TRUST_BOUNDED_MC_DEBUG").is_ok() {
        eprintln!("[BOUNDED_MC] PROVED by exhaustion: {cases} cases all-false (domain={total})");
    }
    Some(VerificationResult::Proved {
        solver: SOLVER_NAME.into(),
        time_ms,
        strength: trust_types::ProofStrength {
            reasoning: trust_types::ReasoningKind::ExhaustiveFinite(cases),
            // Complete + sound for the finite domain: the property holds for ALL
            // inputs. `Sound` (strength_order 2, == SmtBacked) satisfies the
            // static-trust bar (`proof_strength_satisfies_static_trust`:
            // !bounded && reasoning.is_complete() && assurance >= Sound).
            assurance: trust_types::AssuranceLevel::Sound,
        },
        proof_certificate: Some(certificate.into_bytes()),
        solver_warnings: None,
        native_proof_envelope: None,
    })
}

/// The finitely-enumerable value domain for a sort, or `None` when the sort is not
/// finite-and-enumerable here (so the caller declines, fail-closed). `Bool` is the
/// only sort enumerated: it covers the free inputs / flags of a bounded functional
/// assert. Other sorts (`Int`, `Array`, `Float`, datatypes, …) are NOT enumerated —
/// an unbounded `Int` cannot be exhausted, and the rest are out of this route's
/// scope — so the proof is declined rather than risk an incomplete domain.
fn finite_domain(sort: &Sort) -> Option<Vec<EnumValue>> {
    match sort {
        Sort::Bool => Some(vec![EnumValue::Bool(false), EnumValue::Bool(true)]),
        _ => None,
    }
}

/// Evaluate a GROUND formula (every leaf either a literal or a variable bound in
/// `env`) to a concrete [`EnumValue`]. Returns `None` for any node this evaluator
/// does not handle, or any sub-term that is not well-typed for the operator — the
/// caller treats `None` as "cannot establish exhaustiveness" and declines, so a
/// gap here can only LOSE a proof, never manufacture a false one.
///
/// Integer arithmetic uses checked `i128` ops (`%`/`/` reject a zero divisor):
/// an overflow or division-by-zero yields `None` (decline) rather than a wrong
/// value. Mathematical `Int` semantics match the SMT `Int` theory the LIA
/// violation formula is built in.
fn eval_ground(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<EnumValue> {
    use EnumValue::{Bool, Int};
    Some(match formula {
        Formula::Bool(b) => Bool(*b),
        Formula::Int(v) => Int(*v),
        Formula::UInt(v) => Int(i128::try_from(*v).ok()?),
        Formula::BitVec { value, .. } => Int(*value),
        Formula::Var(name, _) => env.get(name)?.clone(),
        Formula::SymVar(sym, _) => env.get(sym.as_str())?.clone(),
        Formula::Not(a) => Bool(!eval_bool(a, env)?),
        Formula::And(terms) => {
            let mut acc = true;
            for t in terms {
                acc &= eval_bool(t, env)?;
            }
            Bool(acc)
        }
        Formula::Or(terms) => {
            let mut acc = false;
            for t in terms {
                acc |= eval_bool(t, env)?;
            }
            Bool(acc)
        }
        Formula::Implies(a, b) => Bool(!eval_bool(a, env)? || eval_bool(b, env)?),
        Formula::Eq(a, b) => Bool(eval_equal(&eval_ground(a, env)?, &eval_ground(b, env)?)?),
        Formula::Lt(a, b) => Bool(eval_int(a, env)? < eval_int(b, env)?),
        Formula::Le(a, b) => Bool(eval_int(a, env)? <= eval_int(b, env)?),
        Formula::Gt(a, b) => Bool(eval_int(a, env)? > eval_int(b, env)?),
        Formula::Ge(a, b) => Bool(eval_int(a, env)? >= eval_int(b, env)?),
        Formula::Add(a, b) => Int(eval_int(a, env)?.checked_add(eval_int(b, env)?)?),
        Formula::Sub(a, b) => Int(eval_int(a, env)?.checked_sub(eval_int(b, env)?)?),
        Formula::Mul(a, b) => Int(eval_int(a, env)?.checked_mul(eval_int(b, env)?)?),
        Formula::Div(a, b) => {
            let d = eval_int(b, env)?;
            if d == 0 {
                return None;
            }
            Int(eval_int(a, env)?.checked_div(d)?)
        }
        Formula::Rem(a, b) => {
            let d = eval_int(b, env)?;
            if d == 0 {
                return None;
            }
            Int(eval_int(a, env)?.checked_rem(d)?)
        }
        Formula::Neg(a) => Int(eval_int(a, env)?.checked_neg()?),
        Formula::Ite(c, t, e) => {
            if eval_bool(c, env)? {
                eval_ground(t, env)?
            } else {
                eval_ground(e, env)?
            }
        }
        // Any other node (Bv*, Fp*, Select/Store, Pred, quantifiers, …) is outside
        // this evaluator: decline so the caller cannot claim a partial exhaustion.
        _ => return None,
    })
}

fn eval_bool(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<bool> {
    match eval_ground(formula, env)? {
        EnumValue::Bool(b) => Some(b),
        EnumValue::Int(_) => None,
    }
}

fn eval_int(formula: &Formula, env: &BTreeMap<String, EnumValue>) -> Option<i128> {
    match eval_ground(formula, env)? {
        EnumValue::Int(v) => Some(v),
        EnumValue::Bool(_) => None,
    }
}

/// Structural equality of two evaluated values, defined only between like-typed
/// operands (`Bool`/`Bool` or `Int`/`Int`). A cross-typed `Eq` is ill-formed and
/// yields `None` (decline) rather than a silent `false`.
fn eval_equal(lhs: &EnumValue, rhs: &EnumValue) -> Option<bool> {
    match (lhs, rhs) {
        (EnumValue::Bool(a), EnumValue::Bool(b)) => Some(a == b),
        (EnumValue::Int(a), EnumValue::Int(b)) => Some(a == b),
        _ => None,
    }
}

/// Collect DEFINITIONAL equalities from the top-level conjuncts of `formula`: a
/// conjunct `Eq(Var(name), rhs)` (or the symmetric `Eq(rhs, Var(name))`) defines
/// `name := rhs`. These are the vcgen-conjoined pins of computed intermediates
/// (casts, sums, `%`, the xor result, overflow flags). A name with TWO different
/// definitions is treated as undefined (removed) — resolving via one could mask the
/// other constraint, so we fall back to enumerating/declining it (fail-closed).
///
/// Only top-level conjuncts are mined (an `And`, recursively flattened). A
/// definition nested under `Or`/`Ite`/negation is NOT unconditionally true, so it
/// is not mined — leaving its var to be enumerated or to force a decline.
fn collect_conjunct_definitions(formula: &Formula) -> BTreeMap<String, Formula> {
    fn flatten<'a>(f: &'a Formula, out: &mut Vec<&'a Formula>) {
        match f {
            Formula::And(terms) => {
                for t in terms {
                    flatten(t, out);
                }
            }
            other => out.push(other),
        }
    }
    let mut conjuncts = Vec::new();
    flatten(formula, &mut conjuncts);

    let mut defs: BTreeMap<String, Formula> = BTreeMap::new();
    let mut ambiguous: BTreeSet<String> = BTreeSet::new();
    let mut consider = |name: &str, rhs: &Formula| {
        if ambiguous.contains(name) {
            return;
        }
        match defs.get(name) {
            Some(existing) if existing == rhs => {} // identical re-definition is fine
            Some(_) => {
                defs.remove(name);
                ambiguous.insert(name.to_string());
            }
            None => {
                defs.insert(name.to_string(), rhs.clone());
            }
        }
    };
    for conjunct in conjuncts {
        if let Formula::Eq(a, b) = conjunct {
            match (a.as_ref(), b.as_ref()) {
                // `var == var` is a binding either way; bind the left to the right.
                (Formula::Var(name, _), _) if !matches!(b.as_ref(), Formula::Var(n, _) if n == name) =>
                {
                    consider(name, b);
                }
                (_, Formula::Var(name, _)) => {
                    consider(name, a);
                }
                _ => {}
            }
        }
    }
    defs
}

/// Resolve every defined var in `defs` to a concrete [`EnumValue`] under the partial
/// `env` (the enumerated free-input assignment), by fixpoint. Each pass evaluates
/// any still-unresolved definition whose dependencies are now known; iteration stops
/// at a fixpoint. A var whose definition is cyclic or depends on an unresolved var
/// is simply left unbound — `eval_ground` then returns `None` for it, so the caller
/// declines (never a false proof).
fn resolve_definitions(defs: &BTreeMap<String, Formula>, env: &mut BTreeMap<String, EnumValue>) {
    loop {
        let mut progress = false;
        for (name, rhs) in defs {
            if env.contains_key(name) {
                continue;
            }
            if let Some(value) = eval_ground(rhs, env) {
                env.insert(name.clone(), value);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
}

/// Build the strict, re-checkable certificate text for an exhaustive finite-domain
/// proof. It records the enumerated free variables, the total domain cardinality,
/// and the number of cases evaluated (which equals the cardinality on a complete
/// enumeration). Re-checking is replaying the same deterministic enumeration.
fn bounded_finite_certificate(free: &[(String, Sort)], total: u128, cases: u64) -> String {
    let mut vars: Vec<String> = free.iter().map(|(n, s)| format!("{n}:{s:?}")).collect();
    vars.sort();
    format!(
        "trust-router.bounded-finite-exhaustive.v1\n\
         method: exhaustive enumeration over the complete finite free-variable domain\n\
         free_vars: [{}]\n\
         domain_cardinality: {total}\n\
         cases_evaluated: {cases}\n\
         result: violation formula evaluated to false on every assignment (UNSAT over the finite domain)\n\
         recheck: re-run the same deterministic enumeration — complete and sound for the finite domain\n",
        vars.join(", ")
    )
}

fn collect_pred_symbols(formula: &Formula) -> BTreeMap<String, Vec<Sort>> {
    let mut preds = BTreeMap::new();
    formula.visit(&mut |node| {
        if let Formula::Pred(name, args) = node {
            let arg_sorts = pred_arg_sorts(name.as_str())
                .map(<[Sort]>::to_vec)
                .unwrap_or_else(|| vec![Sort::Int; args.len()]);
            preds.entry(name.as_str().to_string()).or_insert(arg_sorts);
        }
    });
    preds
}

#[cfg(test)]
mod tests {
    use trust_types::{SourceSpan, Symbol};

    use super::*;

    fn int_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Int)
    }

    // Lever A: a recursive `Expr`-shaped datatype sort with a `Const(c: bv32)`
    // leaf and a binary `App(f: Expr, x: Expr)` node (children are by-name refs).
    fn expr_dt_sort() -> Sort {
        let r = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        Sort::Datatype {
            name: "Expr".into(),
            constructors: vec![
                ("Const".into(), vec![("c".into(), Sort::BitVec(32))]),
                ("App".into(), vec![("f".into(), r.clone()), ("x".into(), r)]),
            ],
        }
    }

    fn bool_var(name: &str) -> Formula {
        Formula::Var(name.into(), Sort::Bool)
    }

    fn boxed(f: Formula) -> Box<Formula> {
        Box::new(f)
    }

    /// `b as u8` lowering used by vcgen: `Ite(b, 1, 0)` (a mathematical-`Int` term).
    fn bool_to_int(b: &str) -> Formula {
        Formula::Ite(boxed(bool_var(b)), boxed(Formula::Int(1)), boxed(Formula::Int(0)))
    }

    /// The xor_collapse parity VIOLATION formula over two bool inputs `a`, `b`, the
    /// xor result `r`, restricted to two contributions for a compact, hand-checkable
    /// case: `r == (a ^ b)` (path def) conjoined with the NEGATED assert
    /// `!(r == (((a as u8)+(b as u8)) % 2 == 1))`. It is UNSAT — the assert is a
    /// true identity — so the bounded enumeration must PROVE it (all 2^3 cases false).
    fn parity_violation_two_inputs() -> Formula {
        let r_def = Formula::Eq(
            boxed(bool_var("r")),
            boxed(Formula::Not(boxed(Formula::Eq(boxed(bool_var("a")), boxed(bool_var("b")))))),
        );
        let sum = Formula::Add(boxed(bool_to_int("a")), boxed(bool_to_int("b")));
        let parity = Formula::Eq(
            boxed(Formula::Rem(boxed(sum), boxed(Formula::Int(2)))),
            boxed(Formula::Int(1)),
        );
        let assert_holds = Formula::Eq(boxed(bool_var("r")), boxed(parity));
        Formula::And(vec![r_def, Formula::Not(boxed(assert_holds))])
    }

    /// The bounded finite-domain route PROVES the parity functional-equality assert:
    /// every assignment of the finite (3 bool) domain evaluates the violation formula
    /// to false, so it returns a `Proved` carrying an `ExhaustiveFinite`/`Sound`
    /// strength and a strict re-checkable certificate.
    #[test]
    fn bounded_finite_proves_parity_violation_unsat() {
        let result = bounded_finite_unsat_proof(&parity_violation_two_inputs(), 0)
            .expect("finite parity violation must be proved UNSAT by exhaustion");
        match result {
            VerificationResult::Proved { strength, proof_certificate, .. } => {
                // `r` is a DEFINED var (resolved from `r == a^b`), so only the two
                // truly-free bool inputs `a`, `b` are enumerated => 2^2 = 4 cases.
                assert!(matches!(
                    strength.reasoning,
                    trust_types::ReasoningKind::ExhaustiveFinite(4)
                ));
                assert_eq!(strength.assurance, trust_types::AssuranceLevel::Sound);
                // Honors the downstream static-trust bar (complete, unbounded, >=Sound).
                assert!(!strength.is_bounded() && strength.reasoning.is_complete());
                let cert = String::from_utf8(proof_certificate.expect("certificate")).unwrap();
                assert!(cert.contains("bounded-finite-exhaustive"));
                assert!(cert.contains("cases_evaluated: 4"));
            }
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    /// The route resolves FREE `Int` temporaries that carry a definitional equality
    /// (the real xor_collapse shape: bool->int `Ite` casts pinned to the inputs),
    /// enumerating only the truly-free bool inputs. Here `t == (a as int)` and the
    /// violation `!(t == t)` is UNSAT; `t` is resolved (not enumerated), `a` is the
    /// single enumerated input => 2 cases, all false => Proved.
    #[test]
    fn bounded_finite_resolves_defined_int_temps() {
        let t_def = Formula::Eq(boxed(int_var("t")), boxed(bool_to_int("a")));
        let bad = Formula::Not(boxed(Formula::Eq(boxed(int_var("t")), boxed(int_var("t")))));
        let violation = Formula::And(vec![t_def, bad]);
        let result = bounded_finite_unsat_proof(&violation, 0)
            .expect("defined Int temp must be resolved and the formula proved UNSAT");
        match result {
            VerificationResult::Proved { strength, .. } => assert!(matches!(
                strength.reasoning,
                trust_types::ReasoningKind::ExhaustiveFinite(2)
            )),
            other => panic!("expected Proved, got {other:?}"),
        }
    }

    /// SOUNDNESS (never false-PROVE): a genuinely SATISFIABLE finite violation
    /// formula (`a` alone — reachable at `a = true`) must DECLINE, not prove.
    #[test]
    fn bounded_finite_declines_satisfiable_violation() {
        assert!(bounded_finite_unsat_proof(&bool_var("a"), 0).is_none());
    }

    /// SOUNDNESS (never claim a partial exhaustion): a free variable over a
    /// non-finite sort (`Int`) is not enumerable, so the route DECLINES even though
    /// the formula (`x != x`) is UNSAT — the strict ay path handles it instead.
    #[test]
    fn bounded_finite_declines_non_finite_domain() {
        let unsat = Formula::Not(boxed(Formula::Eq(boxed(int_var("x")), boxed(int_var("x")))));
        assert!(bounded_finite_unsat_proof(&unsat, 0).is_none());
    }

    /// An unsupported node (here `BvAdd`) makes the evaluator decline rather than
    /// claim exhaustiveness from a partial evaluation.
    #[test]
    fn bounded_finite_declines_unsupported_node() {
        // `!(bvadd(a,a) == bvadd(a,a))` is UNSAT but uses a Bv op the evaluator does
        // not model, so the route must decline (return None), not prove.
        let bv = Formula::BvAdd(boxed(int_var("a")), boxed(int_var("a")), 8);
        let unsat = Formula::Not(boxed(Formula::Eq(boxed(bv.clone()), boxed(bv))));
        assert!(bounded_finite_unsat_proof(&unsat, 0).is_none());
    }

    fn safety_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::DivisionByZero,
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// A minimal WARN-default subscriber standing in for rustc's global one
    /// (`rustc_log::init_logger` installs a bare `LevelFilter::WARN`
    /// subscriber even without `RUSTC_LOG`): counts every WARN-or-more-severe
    /// event that reaches it.
    struct WarnCounter(std::sync::Arc<std::sync::atomic::AtomicUsize>);

    impl tracing::Subscriber for WarnCounter {
        fn enabled(&self, metadata: &tracing::Metadata<'_>) -> bool {
            *metadata.level() <= tracing::Level::WARN
        }
        fn new_span(&self, _: &tracing::span::Attributes<'_>) -> tracing::span::Id {
            tracing::span::Id::from_u64(1)
        }
        fn record(&self, _: &tracing::span::Id, _: &tracing::span::Record<'_>) {}
        fn record_follows_from(&self, _: &tracing::span::Id, _: &tracing::span::Id) {}
        fn event(&self, _: &tracing::Event<'_>) {
            self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        fn enter(&self, _: &tracing::span::Id) {}
        fn exit(&self, _: &tracing::span::Id) {}
    }

    /// Trust (#ay-log-silence): ay's solver-internal `tracing::warn!` events
    /// must NOT reach the embedding process's ambient subscriber during an
    /// in-process solve — inside trustc, rustc's global subscriber enables
    /// WARN for all targets by default, which leaked "ay_dpll WARN" spam onto
    /// every compile's stderr. Suppressed by default; `TRUST_AY_LOG` opts back
    /// in. All phases live in ONE test so the env-var toggling cannot race a
    /// parallel test's solve.
    #[test]
    #[allow(unknown_lints, env_mutation)] // lock-serialized env helper (see the acquired *_ENV_LOCK); the single audited boundary.
    fn ay_diagnostics_suppressed_by_default_and_env_opt_in() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering};

        use crate::ay_log::with_ay_diagnostics_policy_choice;

        let count = Arc::new(AtomicUsize::new(0));

        // (1) Mechanism: a WARN emitted inside the policy scope is dropped,
        // not forwarded to the ambient (thread-default) subscriber.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(false, || {
                tracing::warn!("solver-internal diagnostic");
            });
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 0, "ay diagnostics must not reach the ambient subscriber by default");

        // (2) A REAL in-process solve leaks nothing either: whatever warns
        // ay-dpll emits internally must stay inside the policy scope.
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
        ]);
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            let _ = with_ay_diagnostics_policy_choice(false, || {
                backend.solve_and_classify_with_policy(&formula, true)
            });
            count.load(Ordering::Relaxed)
        });
        assert_eq!(
            n, 0,
            "an in-process ay solve must not leak WARN events to the ambient subscriber"
        );

        // (3) A resolved TRUST_AY_LOG=warn decision re-enables the flow to the
        // ambient subscriber. The value parser is covered in ay_log's unit
        // tests, so this test never mutates the process environment.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(true, || tracing::warn!("opted-in diagnostic"));
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 1, "TRUST_AY_LOG=warn must let ay diagnostics through");

        // (4) An explicit off decision keeps them suppressed.
        let n = tracing::subscriber::with_default(WarnCounter(Arc::clone(&count)), || {
            with_ay_diagnostics_policy_choice(false, || tracing::warn!("suppressed again"));
            count.load(Ordering::Relaxed)
        });
        assert_eq!(n, 1, "TRUST_AY_LOG=off must keep diagnostics suppressed");
    }

    /// Trust #soundness (i128 add false-PROVE repro): the signed-128 overflow
    /// violation `MIN<=a<=MAX ∧ MIN<=b<=MAX ∧ (a+b<MIN ∨ a+b>MAX)` is SAT
    /// (a=b=i128::MAX overflows), so the in-process bridge must NOT prove it.
    /// If `int_const(i128::MAX)` is treated as the solver's integer ceiling
    /// (so `a+b>i128::MAX` is vacuously false), this would falsely return
    /// Proved — exactly the fuzzer-found `fn f(a:i128,b:i128){a+b}` regression.
    #[test]
    fn i128_add_overflow_violation_is_not_proved() {
        let backend = InProcessAyBackend::new();
        let min = Formula::Int(i128::MIN);
        let max = Formula::Int(i128::MAX);
        let a = int_var("a");
        let b = int_var("b");
        let sum = Formula::Add(Box::new(a.clone()), Box::new(b.clone()));
        let range = |v: &Formula| {
            Formula::And(vec![
                Formula::Le(Box::new(min.clone()), Box::new(v.clone())),
                Formula::Le(Box::new(v.clone()), Box::new(max.clone())),
            ])
        };
        let body = Formula::And(vec![
            range(&a),
            range(&b),
            Formula::Or(vec![
                Formula::Lt(Box::new(sum.clone()), Box::new(min.clone())),
                Formula::Gt(Box::new(sum.clone()), Box::new(max.clone())),
            ]),
        ]);
        // The shape vcgen actually emits: conjoin_arg_type_ranges wraps the
        // inner overflow body with a duplicate range per int param.
        let formula = Formula::And(vec![range(&a), range(&b), body]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "signed-128 add CAN overflow (a=b=i128::MAX), so the violation is SAT and \
             must NOT be Proved; got: {result:?}"
        );
    }

    /// (1) Trivially-UNSAT violation: x > 10 AND x < 5 has no model. The
    /// backend may return Proved only if ay's strict proof checker accepts the
    /// artifact; otherwise it must degrade to Unknown instead of handing out a
    /// trust seal.
    #[test]
    fn unsat_violation_respects_strict_proof_gate() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
        ]);
        let result = backend.verify(&safety_vc(formula));

        match &result {
            VerificationResult::Proved { solver, proof_certificate, strength, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // Without `ay-certify`: strict-checked proof => SmtBacked
                // assurance (above the Unchecked subprocess path, below
                // kernel-Certified).
                #[cfg(not(feature = "ay-certify"))]
                {
                    assert_eq!(*strength, ProofStrength::smt_unsat_strict_checked());
                    assert_eq!(strength.assurance, trust_types::AssuranceLevel::SmtBacked);
                }
                // With `ay-certify` (D.9), this fragment reconstructs and the
                // verdict IS upgraded — but only because the row now carries a
                // typed envelope that binds to this VC and replays. Assert the
                // evidence, not merely the label: a `Certified` we cannot replay
                // is exactly what the old identity gate existed to prevent.
                #[cfg(feature = "ay-certify")]
                {
                    assert_eq!(*strength, ProofStrength::smt_unsat_certified());
                    assert_eq!(strength.assurance, trust_types::AssuranceLevel::Certified);
                    let VerificationResult::Proved {
                        native_proof_envelope: Some(envelope), ..
                    } = &result
                    else {
                        panic!("a Certified row must carry replayable evidence");
                    };
                    assert_eq!(
                        crate::ay_certify::replay_certified_envelope(
                            &safety_vc(Formula::And(vec![
                                Formula::Gt(
                                    Box::new(int_var("x")),
                                    Box::new(Formula::Int(10))
                                ),
                                Formula::Lt(Box::new(int_var("x")), Box::new(Formula::Int(5))),
                            ]))
                            .formula,
                            envelope
                        ),
                        crate::ay_certify::ReplayOutcome::Replayed,
                        "the end-to-end Certified row's evidence must replay against its VC"
                    );
                }
                assert!(
                    proof_certificate.as_ref().is_some_and(|bytes| !bytes.is_empty()),
                    "strict-Verified Proved must carry a non-empty proof certificate"
                );
            }
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("UNSAT"),
                    "UNSAT without an accepted strict proof should explain the fail-closed downgrade: {result:?}"
                );
            }
            other => {
                panic!("UNSAT violation must be Proved or fail-closed Unknown, got: {other:?}")
            }
        }
    }

    /// The mutable-collection E4 lane lowers `xs[i] = value` to the array
    /// post-state `store(xs, i, value)`. Exercise AY's proof checker on the
    /// corresponding read-after-write theorem itself: a backend verdict is not
    /// enough for this regression; the exact solve must carry an artifact whose
    /// strict checker verdict is `Verified`.
    #[test]
    fn array_store_select_uses_a_strict_verified_ay_proof_and_tampering_refutes() {
        let backend = InProcessAyBackend::new();
        let array_sort = Sort::Array(Box::new(Sort::Int), Box::new(Sort::Int));
        let array = Formula::Var("xs".into(), array_sort);
        let index = int_var("index");
        let value = int_var("value");
        let store =
            Formula::Store(boxed(array.clone()), boxed(index.clone()), boxed(value.clone()));
        let violation = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(boxed(store), boxed(index.clone()))),
            boxed(value.clone()),
        )));

        let program = backend.build_program(&violation);
        let _ay_guard = AY_EXEC_LOCK.lock().unwrap_or_else(|error| error.into_inner());
        let outcomes = execute_direct::execute_incremental(&program)
            .expect("the exact array read-after-write query must execute in-process");
        let outcome = outcomes.last().expect("the program contains one check-sat");
        assert!(
            matches!(outcome.result, ExecuteTypedResult::Verified),
            "read(store(xs, index, value), index) == value must be UNSAT as a violation: \
             {outcome:?}",
        );
        let artifact =
            outcome.unsat_proof.as_ref().expect("UNSAT must carry AY's checked proof artifact");
        assert!(
            matches!(&artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "the array-theory proof must pass AY's strict proof checker: {artifact:?}",
        );
        artifact
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .expect("the strict consumer gate must accept the same checked artifact");
        drop(_ay_guard);

        // Same-sorted but different locals are not interchangeable. Changing
        // either the store index or value makes the violation satisfiable, so
        // neither tampered query may retain proof authority.
        let other_index = int_var("other_index");
        let wrong_index = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(
                boxed(Formula::Store(
                    boxed(array.clone()),
                    boxed(other_index),
                    boxed(value.clone()),
                )),
                boxed(index.clone()),
            )),
            boxed(value.clone()),
        )));
        let wrong_value = Formula::Not(boxed(Formula::Eq(
            boxed(Formula::Select(
                boxed(Formula::Store(
                    boxed(array),
                    boxed(index.clone()),
                    boxed(int_var("other_value")),
                )),
                boxed(index),
            )),
            boxed(value),
        )));
        for tampered in [wrong_index, wrong_value] {
            let result = backend.run_strict(&tampered);
            assert!(
                result.is_failed(),
                "a satisfiable tampered Store/Select query must be refuted, never proved: \
                 {result:?}",
            );
        }
    }

    /// Trust #soundness (round-18): Rust `%` is TRUNCATED, so the violation
    /// `r == x % 256 AND r < 0` is SATISFIABLE (x = -1 => r = -1 < 0) and must NOT
    /// be Proved. The in-process backend lowers via `ay_bridge`; if that used ay's
    /// EUCLIDEAN `int_mod` (r in [0,256) so r >= 0 always), the violation would be
    /// UNSAT and `#[ensures(result >= 0)] fn f(x:i32){ x % 256 }` would be falsely
    /// Proved. The truncated lowering keeps the violation reachable.
    #[test]
    fn truncated_rem_negative_dividend_violation_is_not_proved() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::And(vec![
            Formula::Eq(
                Box::new(int_var("r")),
                Box::new(Formula::Rem(Box::new(int_var("x")), Box::new(Formula::Int(256)))),
            ),
            Formula::Lt(Box::new(int_var("r")), Box::new(Formula::Int(0))),
        ]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "truncated `x % 256` admits a negative result (x = -1), so the violation is \
             reachable and must NOT be Proved (Euclidean int_mod would wrongly prove it); \
             got {result:?}"
        );
    }

    /// (2) SAT violation: x > 0 is satisfiable, so the violation is reachable
    /// => Failed.
    #[test]
    fn sat_violation_is_failed() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0)));
        let result = backend.verify(&safety_vc(formula));

        assert!(result.is_failed(), "SAT violation must be Failed (never Proved), got: {result:?}");
        assert_eq!(result.solver_name(), SOLVER_NAME);
    }

    /// (3) The mapping returns Unknown (never Proved) when there is no
    /// strict-Verified artifact: an UNSAT outcome whose `unsat_proof` is `None`
    /// must degrade to Unknown.
    #[test]
    fn unsat_without_proof_artifact_is_unknown_not_proved() {
        // An UNSAT outcome whose `unsat_proof` is None must degrade to Unknown:
        // the soundness gate only ever yields Proved with a strict-Verified
        // artifact. (We feed None directly; ay's CheckSatOutcome /
        // UnsatProofArtifact are #[non_exhaustive] and cannot be fabricated.)
        let result = InProcessAyBackend::unsat_to_result(None, 0, &Formula::Bool(false));
        assert!(
            !result.is_proved(),
            "UNSAT without a strict proof artifact must NOT be Proved, got: {result:?}"
        );
        assert!(
            matches!(result, VerificationResult::Unknown { .. }),
            "UNSAT without a strict proof artifact must be Unknown, got: {result:?}"
        );
    }

    #[test]
    fn predicate_applications_are_declared_for_direct_execution() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Pred(Symbol::intern("dir_open"), vec![int_var("d")]);
        let program = backend.build_program(&formula);
        assert_eq!(program.get_logic(), Some("QF_UFLIA"));

        let result = backend.verify(&safety_vc(formula));
        assert!(
            result.is_failed(),
            "opaque predicate violation is satisfiable and should execute directly, got: {result:?}"
        );
    }

    #[test]
    fn configured_timeout_is_encoded_into_the_exact_ay_program() {
        let formula = Formula::Bool(false);
        let bounded = InProcessAyBackend::new().with_timeout(1_234);
        let bounded_program = bounded.build_program(&formula).to_string();
        assert!(
            bounded_program.contains("(set-option :timeout 1234)"),
            "tracked timeout must reach AY's executable program: {bounded_program}"
        );

        let unbounded = InProcessAyBackend::new().with_timeout(0);
        let unbounded_program = unbounded.build_program(&formula).to_string();
        assert!(
            !unbounded_program.contains(":timeout"),
            "zero deliberately disables AY's per-query timeout: {unbounded_program}"
        );
    }

    #[test]
    fn backend_identity() {
        let backend = InProcessAyBackend::new();
        assert_eq!(backend.name(), SOLVER_NAME);
        assert_eq!(backend.role(), BackendRole::SmtSolver);
    }

    #[test]
    fn can_handle_l0_safety_kinds_only() {
        let backend = InProcessAyBackend::new();

        // Accepted L0 safety kinds.
        assert!(backend.can_handle(&safety_vc(Formula::Bool(false))));

        // UnsupportedMir is L0Safety but must be rejected.
        let unsupported = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "Foo".into(), detail: "bar".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!backend.can_handle(&unsupported));

        // Trust (contract-completeness inc-1): the definition-site Postcondition
        // (L1) contract obligation is now ACCEPTED — its self-contained
        // body-fact-conjoined violation formula is ay-decidable by strict UNSAT.
        // (`verify` still mints Proved only on a strict-checked UNSAT; the v1/ay
        // bridge substitutes only a Proved for this kind, never a Failed.)
        let postcondition = VerificationCondition {
            kind: VcKind::Postcondition,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(backend.can_handle(&postcondition));

        // Temporal/L2 kind must be rejected.
        let deadlock = VerificationCondition {
            kind: VcKind::Deadlock,
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        assert!(!backend.can_handle(&deadlock));
    }

    /// UnsupportedMir reaching verify() directly must be Unknown, never Proved.
    #[test]
    fn verify_unsupported_mir_is_unknown() {
        let backend = InProcessAyBackend::new();
        let vc = VerificationCondition {
            kind: VcKind::UnsupportedMir { kind: "Foo".into(), detail: "bar".into() },
            function: "f".into(),
            location: SourceSpan::default(),
            formula: Formula::Bool(false),
            contract_metadata: None,
            obligation: None,
        };
        let result = backend.verify(&vc);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
    }

    /// Free-variable collection gathers Var/SymVar and excludes quantifier-bound
    /// names so we never declare a bound variable at top level.
    #[test]
    fn free_var_collection_excludes_bound_names() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
            Formula::Forall(
                vec![("q".into(), Sort::Int)],
                Box::new(Formula::Eq(
                    Box::new(Formula::Var("q".into(), Sort::Int)),
                    Box::new(Formula::Int(0)),
                )),
            ),
        ]);
        let vars = smt2_export::collect_free_vars(&formula);
        assert!(vars.contains(&("x".to_string(), Sort::Int)), "free var x must be collected");
        assert!(
            !vars.iter().any(|(name, _)| name == "q"),
            "quantifier-bound q must not be a free var"
        );
    }

    /// The element-count ceiling the vcgen recognizer flags at (`1 << 28`). Kept
    /// local to the test so the regression does not depend on a vcgen export.
    const ALLOC_CEILING: i128 = 1 << 28;

    fn unbounded_alloc_vc(formula: Formula) -> VerificationCondition {
        VerificationCondition {
            kind: VcKind::UnboundedAllocation {
                callee: "Vec::with_capacity".into(),
                count: "n".into(),
                detail: "test".into(),
            },
            function: "test_fn".into(),
            location: SourceSpan::default(),
            formula,
            contract_metadata: None,
            obligation: None,
        }
    }

    /// Regression: an `UnboundedAllocation` VC must be ACCEPTED by the in-process
    /// ay backend (its kind was generated + proof-level-wired but never added to
    /// any backend's `can_handle`, so it routed to "no backend can handle this" =>
    /// `unknown`). Confirm `can_handle` now claims it so the QF_LIA `Ge(count,
    /// CEILING)` formula actually reaches the solver.
    #[test]
    fn can_handle_accepts_unbounded_allocation() {
        let backend = InProcessAyBackend::new();
        let vc = unbounded_alloc_vc(Formula::Ge(
            Box::new(int_var("n")),
            Box::new(Formula::Int(ALLOC_CEILING)),
        ));
        assert!(
            backend.can_handle(&vc),
            "UnboundedAllocation must be routable to the in-process ay backend, got rejected"
        );
    }

    /// Regression (the decisive gate): an UNGUARDED bulk allocation whose element
    /// count is bound to exactly the ceiling (`n == 1 << 28`) with the failure
    /// condition `Ge(n, CEILING)` is SATISFIABLE (n = 1 << 28 witnesses it), so the
    /// obligation must be DECIDED `Failed` (refuted with a counterexample), NOT
    /// `unknown`. This is the nn-dsl OOM shape: `Vec::with_capacity(1 << 28)` with
    /// no dominating budget check.
    #[test]
    fn unbounded_allocation_at_ceiling_is_refuted_not_unknown() {
        let backend = InProcessAyBackend::new();
        // Failure formula conjoined with the block-def binding `n == 1 << 28`.
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(ALLOC_CEILING))),
            Formula::Ge(Box::new(int_var("n")), Box::new(Formula::Int(ALLOC_CEILING))),
        ]);
        let vc = unbounded_alloc_vc(formula);
        assert!(
            backend.can_handle(&vc),
            "precondition: backend must accept the UnboundedAllocation kind"
        );
        let result = backend.verify(&vc);
        assert!(
            result.is_failed(),
            "an unguarded `1 << 28`-element allocation reaches the ceiling, so the failure \
             condition is satisfiable and the obligation must be DECIDED Failed (refuted), \
             not unknown; got {result:?}"
        );
        assert_eq!(result.solver_name(), SOLVER_NAME);
    }

    /// Regression (shift binding reaches the solver): the count is symbolic
    /// `(- end start)` where `end` is bound to a SEPARATE `Shl(1, 28)` statement
    /// reconstructed into the VC as a bitvector-bridged block-def. With `start = 0`
    /// and `end == 1 << 28`, the count is `1 << 28`, so `Ge(count, CEILING)` is
    /// satisfiable and the obligation is refuted. If the shift value did NOT reach
    /// the solver, `end` would be unconstrained and the result could not be a
    /// decisive `Failed`. The shift block-def is lowered via `try_binop_to_formula`
    /// (BvShl) and the ay bridge supports `IntToBv`/`BvShl`/`BvToInt`.
    #[test]
    fn unbounded_allocation_symbolic_shift_count_is_refuted() {
        let backend = InProcessAyBackend::new();
        // end == BvToInt(BvShl(IntToBv(1, 64), IntToBv(28, 64))) == 1 << 28.
        let shl = Formula::BvToInt(
            Box::new(Formula::BvShl(
                Box::new(Formula::IntToBv(Box::new(Formula::Int(1)), 64)),
                Box::new(Formula::IntToBv(Box::new(Formula::Int(28)), 64)),
                64,
            )),
            64,
            false,
        );
        // count == end - start, with start == 0.
        let count = Formula::Sub(Box::new(int_var("end")), Box::new(int_var("start")));
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("end")), Box::new(shl)),
            Formula::Eq(Box::new(int_var("start")), Box::new(Formula::Int(0))),
            Formula::Ge(Box::new(count), Box::new(Formula::Int(ALLOC_CEILING))),
        ]);
        let vc = unbounded_alloc_vc(formula);
        let result = backend.verify(&vc);
        assert!(
            result.is_failed(),
            "the shift-derived count `(1 << 28) - 0` reaches the ceiling, so with the shift \
             binding propagated to the solver the obligation is refuted (Failed); an unknown \
             here would mean the `_3 == 1 << 28` block-def never reached the solver; got {result:?}"
        );
    }

    /// Regression (#int2bv-ice, the `wide_unsigned_accumulator.rs` falsification
    /// fixture): the per-add overflow VC of `t += (x as u128) << 4` bridges the
    /// shift through `IntToBv`/`BvShl`/`BvToInt` at width 128 and compares the
    /// sum against the `UInt(u128::MAX)` threshold. Solving this shape used to
    /// PANIC inside ay ("Failed to declare function 'int2bv': … symbol 'int2bv'
    /// is reserved") when the strict UNSAT proof checker re-declared the
    /// int<->BV bridge ops as uninterpreted functions, ICE-ing the compiler.
    /// The violation is UNSAT (`t` and `x << 4` are bounded far below
    /// `u128::MAX`), so the backend must return Proved or fail-closed Unknown —
    /// never panic, never Failed.
    #[test]
    fn wide_unsigned_accumulator_int2bv_vc_never_panics() {
        let backend = InProcessAyBackend::new();
        // x in [0, 255] (a u8 element); t bounded by 15 prior adds of (255 << 4).
        let x_range = Formula::And(vec![
            Formula::Le(boxed(Formula::Int(0)), boxed(int_var("x"))),
            Formula::Le(boxed(int_var("x")), boxed(Formula::Int(255))),
        ]);
        let t_range = Formula::And(vec![
            Formula::Le(boxed(Formula::Int(0)), boxed(int_var("t"))),
            Formula::Le(boxed(int_var("t")), boxed(Formula::Int(15 * (255 << 4)))),
        ]);
        // (x as u128) << 4, lowered the way vcgen bridges shifts into the
        // integer VC: BvToInt(BvShl(IntToBv(x, 128), IntToBv(4, 128)), unsigned).
        let shifted = Formula::BvToInt(
            boxed(Formula::BvShl(
                boxed(Formula::IntToBv(boxed(int_var("x")), 128)),
                boxed(Formula::IntToBv(boxed(Formula::Int(4)), 128)),
                128,
            )),
            128,
            false,
        );
        // Violation: the per-add sum exceeds the UInt(u128::MAX) overflow threshold.
        let violation = Formula::Gt(
            boxed(Formula::Add(boxed(int_var("t")), boxed(shifted))),
            boxed(Formula::UInt(u128::MAX)),
        );
        let formula = Formula::And(vec![x_range, t_range, violation]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            matches!(
                result,
                VerificationResult::Proved { .. } | VerificationResult::Unknown { .. }
            ),
            "the UNSAT wide-accumulator int2bv VC must be Proved or fail-closed Unknown \
             (and must never panic / ICE / be Failed), got: {result:?}"
        );
    }

    /// Regression (#int2bv-ice, Trust-side declaration lane): a `Formula::Pred`
    /// whose name collides with a reserved ay builtin theory-operator name must
    /// be DECLINED as Unknown before `build_program` declares it — the
    /// direct-execution declaration path turns the elaborator's ReservedSymbol
    /// rejection into a panic, which would ICE the compiler.
    #[test]
    fn reserved_pred_symbol_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Pred(Symbol::intern("int2bv"), vec![int_var("x")]);
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("reserved"),
                    "the decline reason must name the reserved-symbol collision: {reason}"
                );
            }
            other => panic!(
                "a reserved predicate symbol must fail closed as Unknown (never panic, \
                 never prove), got: {other:?}"
            ),
        }
    }

    /// Defense in depth (#int2bv-ice): a panic ANYWHERE inside the in-process
    /// solve must be contained by `run`'s unwind boundary and degrade to
    /// fail-closed Unknown instead of aborting the embedding compiler. The
    /// ill-sorted `BvAnd(Bool, Bool)` operand shape slips past the
    /// comparison-sort pre-check (`infer_sort` takes the BV width from the
    /// variant), then panics inside `formula_to_expr`'s `.bvand` ("bvand
    /// requires same BitVec sorts") — a stand-in for the whole solver-panic
    /// class (e.g. the reserved-symbol `declare_fun` ICE).
    #[test]
    fn solver_panic_is_contained_as_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let formula = Formula::Eq(
            boxed(Formula::BvAnd(boxed(bool_var("a")), boxed(bool_var("b")), 8)),
            boxed(Formula::IntToBv(boxed(Formula::Int(0)), 8)),
        );
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // Either the panic is caught inside the unwind boundary and surfaced
                // ("panicked"), or — as ay's sort pre-checks have grown more complete —
                // the ill-sorted shape is now DECLINED before it can panic. Both are the
                // required fail-closed Unknown (never an ICE, never a spurious prove);
                // the pre-check path is strictly the safer of the two.
                assert!(
                    reason.contains("panicked") || reason.contains("declined"),
                    "the contained panic or pre-check decline must be surfaced in the Unknown reason: {reason}"
                );
            }
            other => panic!(
                "a solve-internal panic must be contained as fail-closed Unknown, got: {other:?}"
            ),
        }
    }

    /// Regression (trust m6 census ICE #2, f128::clamp_magnitude): a
    /// `Formula::FpFromBits { bits, eb, sb }` whose `bits` operand infers to
    /// `Sort::Int` instead of the required `Sort::BitVec(eb + sb)` — the exact
    /// shape a vcgen fallback produced for f128's magnitude-bits obligation
    /// (f128 is eb=15/sb=113, so its `bits` must be a 128-wide BitVec) — must
    /// be DECLINED as Unknown by the explicit `formula_bitcast_mismatch`
    /// pre-check named in the reason, not merely caught after a panic.
    #[test]
    fn fp_from_bits_int_operand_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        // Quad precision (f128): eb=15, sb=113, so `bits` must be BitVec(128).
        let bad_bits = Formula::FpFromBits { bits: boxed(int_var("x")), eb: 15, sb: 113 };
        let formula = Formula::FpIsNaN(boxed(bad_bits));
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert!(
                    reason.contains("FpFromBits") && reason.contains("BitVec"),
                    "the decline reason must name the FpFromBits/BitVec mismatch: {reason}"
                );
                assert!(
                    !reason.contains("panicked"),
                    "the explicit pre-check must decline BEFORE any panic is reached: {reason}"
                );
            }
            other => panic!(
                "an Int-sorted FpFromBits bits operand must fail closed as Unknown \
                 (never panic, never prove), got: {other:?}"
            ),
        }
    }

    /// Sibling of the above for `Formula::BvExtract`: an `inner` operand that
    /// infers to `Sort::Int` (rather than a BitVec wide enough for `high`) must
    /// be declined the same way — `formula_to_expr`'s `BvExtract` arm lowers via
    /// the same infallible `Expr::extract` convenience wrapper.
    #[test]
    fn bv_extract_int_operand_is_declined_unknown_not_ice() {
        let backend = InProcessAyBackend::new();
        let bad_extract = Formula::BvExtract { inner: boxed(int_var("x")), high: 7, low: 0 };
        let formula =
            Formula::Eq(boxed(bad_extract), boxed(Formula::BitVec { value: 0, width: 8 }));
        let result = backend.verify(&safety_vc(formula));
        match result {
            VerificationResult::Unknown { solver, reason, .. } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                // The BvExtract-specific bitcast pre-check names "BvExtract"/"BitVec";
                // the more general comparison-sort pre-check (which now fires first for
                // this shape, since the ill-sorted BvExtract inner poisons the Eq's
                // operand sorts) names the sort mismatch. Either declines it fail-closed
                // as Unknown — never ICE, never prove.
                assert!(
                    (reason.contains("BvExtract") && reason.contains("BitVec"))
                        || reason.contains("sort-mismatched"),
                    "the decline reason must name the BvExtract/BitVec or sort mismatch: {reason}"
                );
                assert!(
                    !reason.contains("panicked"),
                    "the explicit pre-check must decline BEFORE any panic is reached: {reason}"
                );
            }
            other => panic!(
                "an Int-sorted BvExtract inner operand must fail closed as Unknown \
                 (never panic, never prove), got: {other:?}"
            ),
        }
    }

    // -- Lever A: recursive-datatype encoding soundness (the load-bearing gate) --
    //
    // The CARDINAL risk of datatype modeling is a false-PROVE: an encoding that
    // makes the solver context vacuously UNSAT would "prove" every obligation.
    // These tests assert through the REAL ay solver that (1) declaring a
    // datatype-sorted variable does NOT vacuously prove a satisfiable violation,
    // and (2) the program still builds well-formed (the datatype is declared
    // before the const that uses it).

    /// A program with a datatype-sorted free variable plus a SATISFIABLE integer
    /// violation (`x > 0`) must be refuted (Failed), NOT proved. If declaring the
    /// recursive `Expr` datatype poisoned the context to UNSAT, this would falsely
    /// return Proved — the exact false-PROVE the guard must prevent.
    #[test]
    fn datatype_var_does_not_vacuously_prove_a_sat_violation() {
        let backend = InProcessAyBackend::new();
        // The datatype var is unused by the violation, but it IS declared (it
        // appears as a free Var), so the preamble must declare `Expr` and a
        // const of that sort without making the context UNSAT.
        let formula = Formula::And(vec![
            // touch the datatype var so it is a free var that gets declared
            Formula::Eq(
                Box::new(Formula::Var("e".into(), expr_dt_sort())),
                Box::new(Formula::Var("e".into(), expr_dt_sort())),
            ),
            Formula::Gt(Box::new(int_var("x")), Box::new(Formula::Int(0))),
        ]);
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "declaring a recursive datatype var must not vacuously prove a SAT violation \
             (x>0 is satisfiable); a Proved here is the false-PROVE we guard against; got {result:?}"
        );
    }

    /// `build_program` over a datatype-sorted var must select a datatype-capable
    /// logic and register the datatype before declaring the const. We check the
    /// logic was upgraded to a `*DT*`/`ALL` family (never a non-datatype logic
    /// that would reject the declaration).
    #[test]
    fn datatype_var_program_uses_datatype_capable_logic() {
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
        );
        let program = InProcessAyBackend::new().build_program(&formula);
        let logic = program.get_logic().expect("a logic must be set");
        assert!(
            logic == "ALL" || logic.contains("DT"),
            "a datatype-bearing VC must use a datatype-capable logic, got: {logic}"
        );
        assert!(
            program.is_datatype_declared("Expr"),
            "the Expr datatype must be registered before any const of that sort"
        );
    }

    /// A BY-NAME datatype back-edge (empty constructors) carries no definition:
    /// it must NOT be registered as a datatype, and the logic must still be
    /// datatype-capable — `detect_logic` (not `upgrade_logic_for_datatypes`,
    /// which only fires once a datatype has actually been declared) is what
    /// carries that case.
    #[test]
    fn by_name_datatype_ref_is_uninterpreted_but_keeps_a_capable_logic() {
        let by_name = Sort::Datatype { name: "Expr".into(), constructors: Vec::new() };
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), by_name.clone())),
            Box::new(Formula::Var("e".into(), by_name)),
        );
        let program = InProcessAyBackend::new().build_program(&formula);
        assert_eq!(program.get_logic(), Some("ALL"), "a datatype-bearing VC must use ALL");
        assert!(
            !program.is_datatype_declared("Expr"),
            "a by-name back-edge has no definition to declare; it is an uninterpreted sort"
        );
    }

    /// The in-process twin of the text lane's ground-`Ctor` regression: a
    /// formula whose ONLY datatype content is a ground constructor term has no
    /// datatype-sorted free variable, so the old free-var-keyed registration
    /// declared nothing and asserted a `Const` term over a datatype ay had
    /// never seen. `build_program` must register `Expr` and keep the logic
    /// datatype-capable.
    #[test]
    fn ground_ctor_only_datatype_is_registered_by_build_program() {
        let ground = Formula::Ctor {
            ctor: "Const".into(),
            args: vec![Formula::BitVec { value: 1, width: 32 }],
            sort: expr_dt_sort(),
        };
        let formula = Formula::And(vec![
            Formula::Eq(Box::new(int_var("n")), Box::new(Formula::Int(0))),
            Formula::Eq(Box::new(ground.clone()), Box::new(ground)),
        ]);
        assert!(
            smt2_export::collect_free_vars(&formula).iter().all(|(_, s)| !s.contains_datatype()),
            "this test is only meaningful when no FREE VAR carries a datatype sort"
        );

        let program = InProcessAyBackend::new().build_program(&formula);
        let logic = program.get_logic().expect("a logic must be set");
        assert!(
            logic == "ALL" || logic.contains("DT"),
            "a ground-Ctor VC must use a datatype-capable logic, got: {logic}"
        );
        assert!(
            program.is_datatype_declared("Expr"),
            "the Ctor's datatype must be registered even with no datatype-sorted free var"
        );
    }

    /// A satisfiable datatype formula must never come back Proved. `e == e` is a
    /// TAUTOLOGY, so as a *violation* formula it is trivially SAT — the honest
    /// verdict is Failed/Unknown. Gated behind `is_available` so it is skipped
    /// where the direct ay lane is absent.
    #[test]
    fn satisfiable_datatype_formula_is_never_proved() {
        if !execute_direct::is_available() {
            return;
        }
        let backend = InProcessAyBackend::new();
        let formula = Formula::Eq(
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
            Box::new(Formula::Var("e".into(), expr_dt_sort())),
        );
        let result = backend.verify(&safety_vc(formula));
        assert!(
            !matches!(result, VerificationResult::Proved { .. }),
            "a satisfiable datatype formula must not be Proved; got {result:?}"
        );
    }
}

/// Fail-closed authority tests for the router certification transport seam
/// [`InProcessAyBackend::promote_to_certified`].
///
/// No live solver is required.  BV-multiply and BV-shift candidates, satisfiable
/// formulas, and out-of-fragment formulas MUST all retain the exact SmtBacked
/// verdict and ay certificate: the Clean kernel cannot certify them from the VC
/// alone, so there is nothing replayable to promote on.  Since D.9 the
/// recognized LIA candidate IS promoted on an `ay-certify` build, and the
/// batteries below pin that the promotion carries evidence which replays
/// against its own VC and is refused against any other.
// This module intentionally runs in the base `ay-backend` build as well as
// `ay-certify`: S1 is an AY replay gate, and feature placement must not hide its
// falsification battery from the configuration that exports it.
#[cfg(test)]
mod certification_transport_gate_tests {
    use trust_types::Symbol;

    use super::*;

    /// Build the strict-checked `SmtBacked` Proved the promotion seam receives.
    fn strict_proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: SOLVER_NAME.into(),
            time_ms: 3,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(vec![9, 9, 9]),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    fn x_gt10_lt5() -> Formula {
        Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(5))),
        ])
    }

    fn assert_unchanged_smtbacked(formula: &Formula) {
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), formula, 99);
        match out {
            VerificationResult::Proved {
                solver,
                time_ms,
                strength,
                proof_certificate,
                solver_warnings,
                native_proof_envelope,
            } => {
                assert_eq!(solver.as_str(), SOLVER_NAME);
                assert_eq!(time_ms, 3, "the gate must preserve the original timing evidence");
                assert_eq!(strength, ProofStrength::smt_unsat_strict_checked());
                assert_eq!(strength.assurance, trust_types::AssuranceLevel::SmtBacked);
                assert_eq!(proof_certificate.as_deref(), Some(&[9, 9, 9][..]));
                assert_eq!(solver_warnings, None);
                assert_eq!(native_proof_envelope, None);
            }
            other => panic!("the gate must preserve Proved SmtBacked, got {other:?}"),
        }
    }

    /// Without the Clean reconstruction feature there is no kernel to certify
    /// with, so even a recognized LIA candidate keeps the honest SmtBacked
    /// verdict.
    #[cfg(not(feature = "ay-certify"))]
    #[test]
    fn recognized_lia_stays_smtbacked_without_clean_payload_transport() {
        assert_unchanged_smtbacked(&x_gt10_lt5());
    }

    /// D.9: on an `ay-certify` build the recognized LIA candidate IS promoted —
    /// and the promotion carries replayable evidence rather than a bare label.
    ///
    /// This pins the three things the old identity gate existed to prevent:
    /// ay's LRAT bytes are not displaced, the kernel payload is present in its
    /// own typed slot, and that payload independently replays against this VC.
    #[cfg(feature = "ay-certify")]
    #[test]
    fn recognized_lia_is_promoted_with_replayable_evidence() {
        let formula = x_gt10_lt5();
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), &formula, 99);
        let VerificationResult::Proved {
            strength, proof_certificate, native_proof_envelope, time_ms, ..
        } = out
        else {
            panic!("promotion must stay Proved");
        };
        assert_eq!(strength, ProofStrength::smt_unsat_certified());
        assert_eq!(strength.assurance, trust_types::AssuranceLevel::Certified);
        assert_eq!(
            proof_certificate.as_deref(),
            Some(&[9, 9, 9][..]),
            "ay's LRAT certificate must be PRESERVED, not displaced by the kernel payload"
        );
        assert_eq!(time_ms, 3, "the gate must preserve the original timing evidence");
        let envelope = native_proof_envelope.expect("a Certified row must carry its evidence");
        assert!(envelope.accepted());
        assert_eq!(
            crate::ay_certify::replay_certified_envelope(&formula, &envelope),
            crate::ay_certify::ReplayOutcome::Replayed,
            "the shipped envelope must independently replay against this VC"
        );
    }

    /// D.9: the promotion is BOUND. The envelope minted for one VC does not
    /// replay against another, so a `Certified` row cannot be laundered onto a
    /// different obligation by copying its evidence across.
    #[cfg(feature = "ay-certify")]
    #[test]
    fn promoted_evidence_does_not_replay_against_another_vc() {
        let out = InProcessAyBackend::promote_to_certified(strict_proved(), &x_gt10_lt5(), 99);
        let VerificationResult::Proved { native_proof_envelope: Some(envelope), .. } = out else {
            panic!("expected a promoted row carrying an envelope");
        };
        let other = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(20))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(7))),
        ]);
        assert_eq!(
            crate::ay_certify::replay_certified_envelope(&other, &envelope),
            crate::ay_certify::ReplayOutcome::KernelRejected
        );
    }

    /// The same hard block applies to the recognized BV-multiply candidate.
    #[test]
    fn recognized_bvmul_stays_smtbacked_without_clean_payload_transport() {
        let w = 2;
        let a = Formula::Var("A0".into(), Sort::BitVec(w));
        let b = Formula::Var("B0".into(), Sort::BitVec(w));
        let product = Formula::BvMul(Box::new(a), Box::new(b), w);
        let readout = Formula::BvExtract {
            inner: Box::new(Formula::BvZeroExt(Box::new(product.clone()), w)),
            high: w - 1,
            low: 0,
        };
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(readout), Box::new(product))));
        assert_unchanged_smtbacked(&formula);
    }

    /// The same hard block applies to the recognized BV-shift candidate.
    #[test]
    fn recognized_bvshift_stays_smtbacked_without_clean_payload_transport() {
        let w = 2;
        let value = Formula::Var("V0".into(), Sort::BitVec(w));
        let amount = Formula::Var("S0".into(), Sort::BitVec(w));
        let shift = Formula::BvShl(Box::new(value), Box::new(amount), w);
        let readout = Formula::BvOr(
            Box::new(Formula::BitVec { value: 0, width: w }),
            Box::new(shift.clone()),
            w,
        );
        let formula = Formula::Not(Box::new(Formula::Eq(Box::new(readout), Box::new(shift))));
        assert_unchanged_smtbacked(&formula);
    }

    /// A SATISFIABLE formula (`x > 2 ∧ x < 9`) is NOT promoted — the honest
    /// `SmtBacked` verdict survives.
    #[test]
    fn promote_declines_satisfiable_formula_keeps_smtbacked() {
        let formula = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        assert_unchanged_smtbacked(&formula);
    }

    /// A formula outside the reconstruction fragment keeps `SmtBacked`.
    #[test]
    fn promote_declines_out_of_fragment_keeps_smtbacked() {
        let formula =
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(10)));
        assert_unchanged_smtbacked(&formula);
    }

    // ---- Sealed-authority S1: `revalidate_vc_unsat_strict` falsification battery.
    // The cardinal property (constitution #17 anti-no-op): the gate must FIRE
    // (re-prove) rather than rubber-stamp — so a genuinely-UNSAT violation mints
    // an outcome while a SATISFIABLE one (a real counterexample) does NOT.

    /// A satisfiable violation formula (`x > 2 ∧ x < 9`): the fresh solve returns
    /// `Failed`, so revalidation refuses to mint. This is the anti-forgery /
    /// refutation-immunity heart — a producer's bare `Proved` on a false formula
    /// cannot be laundered into authority.
    #[test]
    fn revalidate_declines_satisfiable_violation() {
        let sat = Formula::And(vec![
            Formula::Gt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(2))),
            Formula::Lt(Box::new(Formula::Var("x".into(), Sort::Int)), Box::new(Formula::Int(9))),
        ]);
        assert!(revalidate_vc_unsat_strict(&sat, 90_000).is_none());
    }

    #[test]
    fn revalidate_rejects_zero_budget() {
        assert!(
            revalidate_vc_unsat_strict(&x_gt10_lt5(), 0).is_none(),
            "zero must never disable the timeout on an authority-minting path"
        );
    }

    #[test]
    fn revalidate_rejects_malformed_ite_before_translation() {
        // AY's ITE constructor requires equal branch sorts. The shared sort
        // boundary must reject this before AY translation, avoiding both an
        // unwind and the process-global panic hook's stderr output.
        let malformed = Formula::Ite(
            Box::new(Formula::Bool(true)),
            Box::new(Formula::Bool(false)),
            Box::new(Formula::Int(0)),
        );
        let result = InProcessAyBackend::new().run_strict(&malformed);
        assert!(matches!(
            result,
            VerificationResult::Unknown { ref reason, .. }
                if reason.contains("sort-invalid") && reason.contains("if-then-else")
        ));
        assert!(revalidate_vc_unsat_strict(&malformed, 1_000).is_none());
    }

    #[test]
    fn revalidate_rejects_conflicting_free_variable_sorts() {
        let malformed = Formula::And(vec![
            Formula::Var("same".into(), Sort::Bool),
            Formula::Eq(
                Box::new(Formula::Var("same".into(), Sort::Int)),
                Box::new(Formula::Int(0)),
            ),
        ]);
        let result = InProcessAyBackend::new().run_strict(&malformed);
        assert!(matches!(
            result,
            VerificationResult::Unknown { ref reason, .. }
                if reason.contains("conflicting sorts") && reason.contains("`same`")
        ));
        assert!(revalidate_vc_unsat_strict(&malformed, 1_000).is_none());
    }

    #[test]
    fn revalidation_policy_never_mints_from_bounded_finite_only() {
        // A ground false violation has a complete one-case finite-domain proof,
        // which is sufficient to exercise the policy without relying on AY's
        // current proof-production coverage for a particular theory fragment.
        let formula = Formula::Bool(false);
        let base = VerificationResult::Unknown {
            solver: SOLVER_NAME.into(),
            time_ms: 0,
            reason: "UNSAT without a strict AY artifact".into(),
        };
        assert!(matches!(
            InProcessAyBackend::finish_verified_result(base.clone(), &formula, 0, true),
            VerificationResult::Proved { .. }
        ));
        assert!(matches!(
            InProcessAyBackend::finish_verified_result(base, &formula, 0, false),
            VerificationResult::Unknown { .. }
        ));
    }

    #[test]
    fn revalidation_problem_declares_symbol_variables_exactly() {
        let formula = Formula::Eq(
            Box::new(Formula::SymVar(Symbol::intern("s1_bits"), Sort::BitVec(8))),
            Box::new(Formula::BitVec { value: 7, width: 8 }),
        );
        let problem = problem_smt2(&formula);
        assert!(problem.starts_with("(set-logic QF_BV)\n"), "{problem}");
        assert!(problem.contains("(declare-fun s1_bits () (_ BitVec 8))\n"), "{problem}");
        assert_eq!(problem.matches("declare-fun s1_bits").count(), 1);
    }

    /// An unsatisfiable violation formula (`x > 10 ∧ x < 5`): the fresh solve
    /// re-proves UNSAT, so revalidation mints an outcome carrying the exact
    /// canonical problem bytes it checked and their domain-separated digest.
    #[test]
    fn revalidate_mints_on_unsatisfiable_violation() {
        let out = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000)
            .expect("an unsatisfiable violation must re-prove and mint");
        assert_eq!(out.canonical_problem(), problem_smt2(&x_gt10_lt5()));
        assert_eq!(out.canonical_problem_sha256().len(), 64, "sha-256 hex");
        assert!(out.canonical_problem_sha256().bytes().all(|b| b.is_ascii_hexdigit()));
    }

    /// Determinism: the same formula re-solves to the same canonical bytes and
    /// digest, so the mint site's row binding is stable across runs.
    #[test]
    fn revalidate_digest_is_deterministic() {
        let a = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000).expect("mint a");
        let b = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000).expect("mint b");
        assert_eq!(a.canonical_problem_sha256(), b.canonical_problem_sha256());
        assert_eq!(a.canonical_problem(), b.canonical_problem());
    }

    /// The digest is domain-separated: it is NOT the bare SHA-256 of the problem
    /// bytes, so a digest computed elsewhere over `problem_smt2` cannot be passed
    /// off as a revalidation receipt digest.
    #[test]
    fn revalidate_digest_is_domain_separated() {
        let out = revalidate_vc_unsat_strict(&x_gt10_lt5(), 90_000).expect("mint");
        let mut bare = Sha256::new();
        bare.update(out.canonical_problem().as_bytes());
        let bare_hex = format!("{:x}", bare.finalize());
        assert_ne!(out.canonical_problem_sha256(), bare_hex);
    }
}

/// Track D increment 2: unit tests for the MONOTONE Carcara cross-check gate.
///
/// These exercise the pure decision logic [`InProcessAyBackend::apply_carcara_gate`]
/// directly — they construct a `Proved` result and feed each [`CrossCheck`]
/// verdict, so NO live solver and NO live Carcara binary are required. The
/// cardinal rule under test: a `Reject` downgrades to `Unknown` (fail-closed),
/// while `Accept` and `Unavailable` both keep the strict-checked `Proved` (an
/// absent Carcara must never introduce a false-FAIL).
#[cfg(all(test, feature = "ay-backend", feature = "carcara-crosscheck"))]
mod carcara_gate_tests {
    use super::*;
    use crate::carcara_cross_check::CrossCheck;

    /// Build the strict-checked `Proved` result the gate receives (the same shape
    /// `unsat_to_result` constructs once ay's strict checker has accepted).
    fn strict_proved() -> VerificationResult {
        VerificationResult::Proved {
            solver: SOLVER_NAME.into(),
            time_ms: 7,
            strength: ProofStrength::smt_unsat_strict_checked(),
            proof_certificate: Some(vec![1, 2, 3]),
            solver_warnings: None,
            native_proof_envelope: None,
        }
    }

    /// (a) Proved + Reject -> the result is NOT proved (downgraded to Unknown,
    /// fail-closed). This is the load-bearing soundness case: ay and Carcara
    /// disagree, so we refuse to surface the PROVE.
    #[test]
    fn apply_carcara_gate_reject_downgrades_to_unknown() {
        let result = InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Reject, 7);
        assert!(
            !result.is_proved(),
            "Carcara Reject must downgrade Proved to non-proved (fail-closed), got: {result:?}"
        );
        match result {
            VerificationResult::Unknown { reason, .. } => {
                assert!(
                    reason.contains("carcara") && reason.contains("fail-closed"),
                    "downgrade reason must name the carcara cross-check fail-closed downgrade: \
                     {reason}"
                );
            }
            other => panic!("Reject must yield Unknown, got: {other:?}"),
        }
    }

    /// (b) Proved + Accept -> still Proved (both checkers agree). The gate is
    /// monotone: Accept never strengthens, it only preserves the input verdict.
    #[test]
    fn apply_carcara_gate_accept_keeps_proved() {
        let result = InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Accept, 7);
        assert!(
            result.is_proved(),
            "Carcara Accept must keep the strict-checked Proved, got: {result:?}"
        );
        match result {
            VerificationResult::Proved { strength, .. } => {
                assert_eq!(
                    strength,
                    ProofStrength::smt_unsat_strict_checked(),
                    "Accept must NOT strengthen the assurance level beyond ay's strict check"
                );
            }
            other => panic!("Accept must keep Proved, got: {other:?}"),
        }
    }

    /// (c) Proved + Unavailable -> still Proved. Carcara being absent is NOT
    /// disagreement; ay's own strict check already gated the Proved, so an
    /// unavailable second checker must NEVER introduce a false-FAIL.
    #[test]
    fn apply_carcara_gate_unavailable_keeps_proved_no_false_fail() {
        let result =
            InProcessAyBackend::apply_carcara_gate(strict_proved(), CrossCheck::Unavailable, 7);
        assert!(
            result.is_proved(),
            "Carcara Unavailable must keep ay's strict-checked Proved (no false-FAIL when \
             carcara is absent), got: {result:?}"
        );
    }
}
